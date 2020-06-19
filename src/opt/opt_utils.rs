//! Utilities for implementing optimizations.
//!
//! You can add here utilities commonly used in the implementation of multiple optimizations.

use crate::ir::*;
use crate::*;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::ops::DerefMut;

pub type CFG = HashMap<BlockId, Vec<JumpArg>>;
pub type ReverseCFG = HashMap<BlockId, Vec<(BlockId, JumpArg)>>;

#[derive(Debug, PartialEq, Clone)]
pub enum OperandVar {
    Operand(Operand),
    Phi((usize, BlockId)),
}
impl OperandVar {
    pub fn lookup(
        &self,
        dtype: &Dtype,
        phinode_indices: &HashMap<(usize, BlockId), usize>,
    ) -> Operand {
        match self {
            Self::Operand(o) => o.clone(),
            Self::Phi(var) => {
                if let Some(index) = phinode_indices.get(var) {
                    Operand::register(RegisterId::arg(var.1, *index), dtype.clone())
                } else {
                    Operand::constant(Constant::undef(dtype.clone()))
                }
            }
        }
    }
}

pub fn make_cfg(fdef: &FunctionDefinition) -> CFG {
    fdef.blocks
        .iter()
        .map(|(bid, block)| {
            let mut args = Vec::new();

            match &block.exit {
                BlockExit::Jump { arg } => args.push(arg.clone()),
                BlockExit::ConditionalJump {
                    arg_then, arg_else, ..
                } => {
                    args.push(arg_then.as_ref().clone());
                    args.push(arg_else.as_ref().clone());
                }
                BlockExit::Switch { default, cases, .. } => {
                    args.push(default.as_ref().clone());
                    for (_, arg) in cases {
                        args.push(arg.clone());
                    }
                }
                _ => {}
            }
            (*bid, args)
        })
        .collect()
}

pub fn reverse_cfg(cfg: &CFG) -> ReverseCFG {
    let mut reverse_cfg: ReverseCFG = HashMap::new();
    for (bid, jumps) in cfg {
        for jump in jumps {
            reverse_cfg
                .entry(jump.bid)
                .or_insert_with(Vec::new)
                .push((*bid, jump.clone()));
        }
    }
    reverse_cfg
}

// PostOrder
struct PostOrder<'c> {
    visited: HashSet<BlockId>,
    cfg: &'c CFG,
    traversed: Vec<BlockId>,
}
impl<'c> PostOrder<'c> {
    fn traverse(&mut self, bid: BlockId) {
        for jump in self.cfg.get(&bid).unwrap() {
            if self.visited.insert(jump.bid) {
                self.traverse(jump.bid);
            }
        }
        self.traversed.push(bid);
    }
}
pub fn traverse_post_order(bid_init: BlockId, cfg: &CFG) -> Vec<BlockId> {
    let mut post_order = PostOrder {
        visited: HashSet::new(),
        cfg,
        traversed: Vec::new(),
    };
    post_order.visited.insert(bid_init);
    post_order.traverse(bid_init);
    post_order.traversed
}

// Domtree

#[derive(Debug)]
pub struct Domtree {
    idoms: HashMap<BlockId, BlockId>,
    frontiers: HashMap<BlockId, Vec<BlockId>>,
    reverse_post_order: Vec<BlockId>,
}

impl Domtree {
    pub fn new(
        bid_init: BlockId,
        cfg: &CFG,
        reverse_cfg: &HashMap<BlockId, Vec<(BlockId, JumpArg)>>,
    ) -> Self {
        // construction of the RPO sequence
        let mut reverse_post_order = traverse_post_order(bid_init, cfg);
        reverse_post_order.reverse();
        let inversed_reverse_post_order = reverse_post_order
            .iter()
            .enumerate()
            .map(|(i, bid)| (*bid, i))
            .collect();

        let mut idoms = HashMap::<BlockId, BlockId>::new();

        loop {
            let mut changed = false;

            for bid in &reverse_post_order {
                if *bid == bid_init {
                    continue;
                }

                let mut idom = None;
                for (bid_prev, _) in reverse_cfg.get(bid).unwrap() {
                    if *bid_prev == bid_init || idoms.get(bid_prev).is_some() {
                        idom = Some(intersect_idom(
                            idom,
                            *bid_prev,
                            &inversed_reverse_post_order,
                            &idoms,
                        ));
                    }
                }

                if let Some(idom) = idom {
                    idoms
                        .entry(*bid)
                        .and_modify(|v| {
                            if *v != idom {
                                changed = true;
                                *v = idom;
                            }
                        })
                        .or_insert_with(|| {
                            changed = true;
                            idom
                        });
                }
            }

            if !changed {
                break;
            }
        }

        let mut frontiers = HashMap::new();
        for (bid, prevs) in reverse_cfg {
            if prevs.len() <= 1 {
                continue;
            }

            let _ = *some_or!(idoms.get(bid), continue);

            for (bid_prev, _) in prevs {
                let mut runner = *bid_prev;
                while !Self::dominates(&idoms, runner, *bid) {
                    frontiers.entry(runner).or_insert_with(Vec::new).push(*bid);
                    // println!("runner: {}, bid: {}, idom: {}", runner, bid, idom);
                    runner = *idoms.get(&runner).unwrap();
                }
            }
        }

        Self {
            idoms,
            frontiers,
            reverse_post_order,
        }
    }

    pub fn idom(&self, bid: BlockId) -> Option<BlockId> {
        self.idoms.get(&bid).cloned()
    }

    pub fn dominates(idoms: &HashMap<BlockId, BlockId>, bid1: BlockId, mut bid2: BlockId) -> bool {
        loop {
            bid2 = *some_or!(idoms.get(&bid2), return false);
            if bid1 == bid2 {
                return true;
            }
        }
    }

    pub fn frontiers(&self, bid: BlockId) -> Option<&Vec<BlockId>> {
        self.frontiers.get(&bid)
    }
}

fn intersect_idom(
    lhs: Option<BlockId>,
    mut rhs: BlockId,
    inversed_reverse_post_order: &HashMap<BlockId, usize>,
    idoms: &HashMap<BlockId, BlockId>,
) -> BlockId {
    let mut lhs = some_or!(lhs, return rhs);

    loop {
        if lhs == rhs {
            return lhs;
        }

        let lhs_index = inversed_reverse_post_order.get(&lhs).unwrap();
        let rhs_index = inversed_reverse_post_order.get(&rhs).unwrap();

        match lhs_index.cmp(rhs_index) {
            Ordering::Less => rhs = *idoms.get(&rhs).unwrap(),
            Ordering::Greater => lhs = *idoms.get(&lhs).unwrap(),
            _ => panic!("lhs != rhs"),
        }
    }
}

impl FunctionDefinition {
    pub fn walk<F>(&mut self, walker: F) -> bool
    where
        F: Fn(&mut Operand) -> bool + Copy,
    {
        let mut total = false;
        loop {
            let mut result = false;
            for (_, block) in self.blocks.iter_mut() {
                for named_instr in block.instructions.iter_mut() {
                    result = result || walk_instruction(named_instr, walker);
                }
                result = result || walk_exit(&mut block.exit, walker);
            }
            total = total || result;
            if !result {
                break;
            }
        }
        total
    }
}

fn walk_instruction<F>(instr: &mut Named<Instruction>, walker: F) -> bool
where
    F: Fn(&mut Operand) -> bool + Copy,
{
    let mut result = false;
    match instr.deref_mut() {
        Instruction::Nop => {}
        Instruction::BinOp { lhs, rhs, .. } => {
            result = result || walker(lhs);
            result = result || walker(rhs);
        }
        Instruction::UnaryOp { operand, .. } => {
            result = result || walker(operand);
        }
        Instruction::Store { ptr, value } => {
            result = result || walker(ptr);
            result = result || walker(value);
        }
        Instruction::Load { ptr } => {
            result = result || walker(ptr);
        }
        Instruction::Call { callee, args, .. } => {
            result = result || walker(callee);
            for arg in args.iter_mut() {
                result = result || walker(arg);
            }
        }
        Instruction::TypeCast { value, .. } => {
            result = result || walker(value);
        }
        Instruction::GetElementPtr { ptr, offset, .. } => {
            result = result || walker(ptr);
            result = result || walker(offset);
        }
    }
    result
}

fn walk_exit<F>(exit: &mut BlockExit, walker: F) -> bool
where
    F: Fn(&mut Operand) -> bool + Copy,
{
    let mut result = false;
    match exit {
        BlockExit::Jump { arg } => {
            result = result || walk_jump_arg(arg, walker);
        }
        BlockExit::ConditionalJump {
            condition,
            arg_then,
            arg_else,
        } => {
            result = result || walker(condition);
            result = result || walk_jump_arg(arg_then.deref_mut(), walker);
            result = result || walk_jump_arg(arg_else.deref_mut(), walker);
        }
        BlockExit::Switch {
            value,
            default,
            cases,
        } => {
            result = result || walker(value);
            result = result || walk_jump_arg(default.deref_mut(), walker);
            for (_, arg) in cases.iter_mut() {
                result = result || walk_jump_arg(arg, walker);
            }
        }
        BlockExit::Return { value } => {
            result = result || walker(value);
        }
        BlockExit::Unreachable => {}
    }
    result
}

fn walk_jump_arg<F>(arg: &mut JumpArg, walker: F) -> bool
where
    F: Fn(&mut Operand) -> bool + Copy,
{
    let mut result = false;
    for op in arg.args.iter_mut() {
        result = result || walker(op);
    }
    result
}
