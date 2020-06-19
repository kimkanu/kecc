use crate::ir::*;
use crate::opt::opt_utils::*;
use crate::opt::FunctionPass;
use crate::*;
use itertools::izip;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::ops::Deref;
pub type SimplifyCfg = FunctionPass<
    Repeat<(
        SimplifyCfgConstProp,
        (SimplifyCfgReach, (SimplifyCfgMerge, SimplifyCfgEmpty)),
    )>,
>;

/// Simplifies block exits by propagating constants.
#[derive(Default)]
pub struct SimplifyCfgConstProp {}

/// Retains only those blocks that are reachable from the init.
#[derive(Default)]
pub struct SimplifyCfgReach {}

/// Merges two blocks if a block is pointed to only by another
#[derive(Default)]
pub struct SimplifyCfgMerge {}

/// Removes empty blocks
#[derive(Default)]
pub struct SimplifyCfgEmpty {}

impl Optimize<FunctionDefinition> for SimplifyCfgConstProp {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        code.blocks
            .iter_mut()
            .map(|(_, block)| {
                if let Some(exit) = self.simplify_block_exit(&block.exit) {
                    block.exit = exit;
                    true
                } else {
                    false
                }
            })
            .fold(false, |l, r| l || r)
    }
}

impl Optimize<FunctionDefinition> for SimplifyCfgReach {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let graph = make_cfg(code);

        let mut queue = vec![code.bid_init];
        let mut visited = HashSet::new();
        visited.insert(code.bid_init);

        while let Some(bid) = queue.pop() {
            if let Some(args) = graph.get(&bid) {
                for arg in args {
                    if visited.insert(arg.bid) {
                        queue.push(arg.bid);
                    }
                }
            }
        }

        let size_orig = code.blocks.len();

        let mut retained_blocks = BTreeMap::new();
        for (bid, v) in code.blocks.iter() {
            if visited.contains(bid) {
                retained_blocks.insert(*bid, v.clone());
            }
        }
        code.blocks = retained_blocks;

        code.blocks.len() < size_orig
    }
}

impl Optimize<FunctionDefinition> for SimplifyCfgMerge {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let graph = make_cfg(code);

        let mut indegrees = HashMap::<BlockId, usize>::new();
        for args in graph.values() {
            for arg in args {
                *indegrees.entry(arg.bid).or_insert(0) += 1;
            }
        }

        let mut result = false; // whether we removed a block
        let mut replaces = HashMap::new();
        let mut removed_bids = HashSet::new();

        for (bid_from, block_from) in
            unsafe { &mut *(&mut code.blocks as *mut BTreeMap<BlockId, Block>) }
        {
            if let BlockExit::Jump { arg } = &block_from.exit {
                // when the indegree is 1 and the edge going in is not a loop
                if *bid_from != arg.bid
                    && indegrees.get(&arg.bid) == Some(&1)
                    && !removed_bids.contains(bid_from)
                {
                    let bid_to = arg.bid;
                    let block_to = code.blocks.get_mut(&bid_to);
                    let block_to = if let Some(block_to) = block_to {
                        block_to
                    } else {
                        continue;
                    };
                    let block_to = block_to.clone();
                    let args_to = arg.args.clone();
                    removed_bids.insert(bid_to);

                    // gather info about phinodes replacement by arguments
                    for (i, (a, p)) in izip!(&args_to, block_to.phinodes.iter()).enumerate() {
                        assert_eq!(&a.dtype(), p.deref());
                        let from = RegisterId::arg(bid_to, i);
                        replaces.insert(from, a.clone());
                    }

                    // move instructions
                    let len = block_from.instructions.len();
                    for (i, instr) in block_to.instructions.into_iter().enumerate() {
                        let dtype = instr.dtype();
                        block_from.instructions.push(instr);
                        let from = RegisterId::temp(arg.bid, i);
                        // rename instr id
                        let to =
                            Operand::register(RegisterId::temp(*bid_from, len + i), dtype.clone());

                        replaces.insert(from, to);
                    }

                    // move the block exit
                    block_from.exit = block_to.exit;

                    // code.walk(|operand| {
                    //     match operand {
                    //         Operand::Register { rid, .. } => {
                    //             if let Some(repl) = replaces.get(rid) {
                    //                 *operand = repl.clone();
                    //             }
                    //         }
                    //         _ => {}
                    //     }
                    // });

                    for (_, block) in code.blocks.iter_mut() {
                        for named_instr in block.instructions.iter_mut() {
                            let named_instr_clone = named_instr.clone();
                            let instr = named_instr_clone.deref().clone();
                            let instr = replace_operands_in_instr(instr, |operand| {
                                replace_operand(operand, &replaces)
                            });

                            *named_instr = Named::new(named_instr_clone.name().cloned(), instr);
                        }

                        block.exit = replace_operands_in_exit(block.exit.clone(), |operand| {
                            replace_operand(operand, &replaces)
                        });
                    }

                    result = true;
                }
            }
        }

        // remove blocks whose bid is in removed_bids
        for bid in removed_bids.iter() {
            code.blocks.remove(bid);
        }

        result
    }
}

impl Optimize<FunctionDefinition> for SimplifyCfgEmpty {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let empty_blocks = code
            .blocks
            .iter()
            .filter(|(_, block)| block.phinodes.is_empty() && block.instructions.is_empty())
            .map(|(bid, block)| (*bid, block.clone()))
            .collect::<HashMap<_, _>>();

        code.blocks
            .iter_mut()
            .map(|(_, block)| self.simplify_block_exit(&mut block.exit, &empty_blocks))
            .fold(false, |l, r| l || r)
    }
}

impl SimplifyCfgConstProp {
    fn simplify_block_exit(&mut self, exit: &BlockExit) -> Option<BlockExit> {
        match exit {
            BlockExit::ConditionalJump {
                condition,
                arg_then,
                arg_else,
            } => {
                if arg_then == arg_else {
                    return Some(BlockExit::Jump {
                        arg: arg_then.as_ref().clone(),
                    });
                }

                if let Some(c) = condition.get_constant() {
                    match c {
                        // br false <then> <else> -> j <else>
                        Constant::Int { value: 0, .. } => {
                            return Some(BlockExit::Jump {
                                arg: arg_else.as_ref().clone(),
                            })
                        }

                        // br true <then> <else> -> j <then>
                        Constant::Int { value: 1, .. } => {
                            return Some(BlockExit::Jump {
                                arg: arg_then.as_ref().clone(),
                            })
                        }
                        // strange program
                        _ => {}
                    }
                }

                None
            }

            BlockExit::Switch {
                value,
                default,
                cases,
            } => {
                if cases.iter().all(|(_, bid)| default.as_ref() == bid) {
                    return Some(BlockExit::Jump {
                        arg: default.as_ref().clone(),
                    });
                }

                if let Some(v) = value.get_constant() {
                    return Some(BlockExit::Jump {
                        arg: if let Some((_, arg)) = cases.iter().find(|(c, _)| v == c) {
                            arg.clone()
                        } else {
                            default.as_ref().clone()
                        },
                    });
                }

                None
            }

            _ => None,
        }
    }
}

impl SimplifyCfgEmpty {
    fn simplify_jump_arg(&self, arg: &mut JumpArg, empty_blocks: &HashMap<BlockId, Block>) -> bool {
        let block = some_or!(empty_blocks.get(&arg.bid), return false);

        assert!(arg.args.is_empty());

        if let BlockExit::Jump { arg: a } = &block.exit {
            *arg = a.clone();
            true
        } else {
            false
        }
    }

    fn simplify_block_exit(
        &mut self,
        exit: &mut BlockExit,
        empty_blocks: &HashMap<BlockId, Block>,
    ) -> bool {
        match exit {
            BlockExit::Jump { arg } => {
                let block = some_or!(empty_blocks.get(&arg.bid), return false);
                *exit = block.exit.clone();
                true
            }
            BlockExit::ConditionalJump {
                arg_then, arg_else, ..
            } => {
                let changed_then = self.simplify_jump_arg(arg_then, empty_blocks);
                let changed_else = self.simplify_jump_arg(arg_else, empty_blocks);
                changed_then || changed_else
            }
            BlockExit::Switch { default, cases, .. } => {
                let changed_default = self.simplify_jump_arg(default, empty_blocks);
                let changed_cases = cases
                    .iter_mut()
                    .map(|case| self.simplify_jump_arg(&mut case.1, empty_blocks))
                    .fold(false, |l, r| l || r);
                changed_default || changed_cases
            }
            _ => false,
        }
    }
}

fn replace_operands_in_instr<F>(instr: Instruction, f: F) -> Instruction
where
    F: Fn(Operand) -> Operand,
{
    match instr {
        Instruction::Nop => Instruction::Nop,
        Instruction::BinOp {
            op,
            lhs,
            rhs,
            dtype,
        } => Instruction::BinOp {
            op,
            lhs: f(lhs),
            rhs: f(rhs),
            dtype,
        },
        Instruction::UnaryOp { op, operand, dtype } => Instruction::UnaryOp {
            op,
            operand: f(operand),
            dtype,
        },
        Instruction::Store { ptr, value } => Instruction::Store {
            ptr: f(ptr),
            value: f(value),
        },
        Instruction::Load { ptr } => Instruction::Load { ptr: f(ptr) },
        Instruction::Call {
            callee,
            args,
            return_type,
        } => Instruction::Call {
            callee: f(callee),
            args: args.iter().map(|arg| f(arg.clone())).collect::<Vec<_>>(),
            return_type,
        },
        Instruction::TypeCast {
            value,
            target_dtype,
        } => Instruction::TypeCast {
            value: f(value),
            target_dtype,
        },
        Instruction::GetElementPtr { ptr, offset, dtype } => Instruction::GetElementPtr {
            ptr: f(ptr),
            offset: f(offset),
            dtype,
        },
    }
}

fn replace_operands_in_exit<F>(exit: BlockExit, f: F) -> BlockExit
where
    F: Fn(Operand) -> Operand,
{
    match exit {
        BlockExit::Jump { arg } => BlockExit::Jump {
            arg: replace_operands_in_jump_arg(arg, &f),
        },
        BlockExit::ConditionalJump {
            condition,
            arg_then,
            arg_else,
        } => BlockExit::ConditionalJump {
            condition: f(condition),
            arg_then: Box::new(replace_operands_in_jump_arg(arg_then.deref().clone(), &f)),
            arg_else: Box::new(replace_operands_in_jump_arg(arg_else.deref().clone(), &f)),
        },
        BlockExit::Switch {
            value,
            default,
            cases,
        } => BlockExit::Switch {
            value: f(value),
            default: Box::new(replace_operands_in_jump_arg(default.deref().clone(), &f)),
            cases: cases
                .iter()
                .map(|(c, arg)| (c.clone(), replace_operands_in_jump_arg(arg.clone(), &f)))
                .collect::<Vec<_>>(),
        },
        BlockExit::Return { value } => BlockExit::Return { value: f(value) },
        BlockExit::Unreachable => BlockExit::Unreachable,
    }
}

fn replace_operands_in_jump_arg<F>(arg: JumpArg, f: &F) -> JumpArg
where
    F: Fn(Operand) -> Operand,
{
    JumpArg::new(
        arg.bid,
        arg.args.iter().map(|op| f(op.clone())).collect::<Vec<_>>(),
    )
}

fn replace_operand(operand: Operand, replaces: &HashMap<RegisterId, Operand>) -> Operand {
    match operand.clone() {
        Operand::Register { rid, .. } => replaces.get(&rid).cloned().unwrap_or(operand),
        _ => operand,
    }
}
