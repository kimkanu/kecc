use crate::ir::*;
use crate::opt::opt_utils::*;
use crate::opt::FunctionPass;
use crate::*;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::ops::Deref;
use std::ops::DerefMut;
pub type Mem2reg = FunctionPass<Mem2regInner>;

#[derive(Default)]
pub struct Mem2regInner {}

impl Optimize<FunctionDefinition> for Mem2regInner {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        // A local allocation is promotable only if it is used only as the pointer of store/load instructions.
        // Collects inpromotable local memory allocations and stores.
        let mut inpromotable = HashSet::new();

        // Stores to each promotable local allocation
        // stores: HashMap (aid) |=> (blocks where storing to local allocation with `aid` occurs)
        let mut stores = HashMap::<usize, Vec<BlockId>>::new();

        for (bid, block) in &code.blocks {
            for instr in &block.instructions {
                match instr.deref() {
                    Instruction::Nop | Instruction::Load { .. } => {}
                    Instruction::BinOp { lhs, rhs, .. } => {
                        mark_inpromotable(&mut inpromotable, &lhs);
                        mark_inpromotable(&mut inpromotable, &rhs);
                    }
                    Instruction::UnaryOp { operand, .. } => {
                        mark_inpromotable(&mut inpromotable, &operand);
                    }
                    Instruction::Store { ptr, value } => {
                        mark_inpromotable(&mut inpromotable, &value);

                        // deal local registers only
                        let (rid, _) = some_or!(ptr.get_register(), continue);
                        if let RegisterId::Local { aid } = rid {
                            stores.entry(*aid).or_insert_with(Vec::new).push(*bid);
                        }
                    }
                    Instruction::Call { callee, args, .. } => {
                        mark_inpromotable(&mut inpromotable, &callee);
                        for arg in args {
                            mark_inpromotable(&mut inpromotable, &arg);
                        }
                    }
                    Instruction::TypeCast { value, .. } => {
                        mark_inpromotable(&mut inpromotable, &value);
                    }
                    Instruction::GetElementPtr { ptr, offset, .. } => {
                        mark_inpromotable(&mut inpromotable, &ptr);
                        mark_inpromotable(&mut inpromotable, &offset);
                    }
                }
            }
        }

        // If no local allocations are promotable, bail out.
        if (0..code.allocations.len()).all(|i| inpromotable.contains(&i)) {
            return false;
        }

        let cfg = make_cfg(code);
        let reverse_cfg = reverse_cfg(&cfg); // B1 -> B2 in CFG => B2 -> B1 in reverse CFG
        let domtree = Domtree::new(code.bid_init, &cfg, &reverse_cfg);

        // First, we need to investigate the spots to insert the phinodes.
        // ---> \bigcup_{i \ge 1} DF^i (S(aid)), where S(aid) is the set of stores for LocalAlloca(aid)
        // aid: usize ===> S(aid): HashSet<BlockId>

        let joins: HashMap<usize, HashSet<BlockId>> = stores
            .iter()
            .filter(|(aid, _)| !inpromotable.contains(*aid))
            .map(|(aid, bids)| {
                (*aid, {
                    // bid: the list of block ids of which the corresponding block has a store instr for LocalAlloca(aid)
                    let mut stack = bids.clone();
                    let mut visited = HashSet::new();
                    while let Some(bid) = stack.pop() {
                        let bid_frontiers = some_or!(domtree.frontiers(bid), continue);
                        for bid_frontier in bid_frontiers {
                            if visited.insert(*bid_frontier) {
                                stack.push(*bid_frontier);
                            }
                        }
                    }
                    visited
                })
            })
            .collect();

        // replacement dictionary
        let mut replaces = HashMap::<RegisterId, OperandVar>::new();

        // actual spots to insert phinodes
        let mut phinode_positions: Vec<(usize, BlockId)> = vec![];

        // current values of a local alloca within a block
        let mut current_values = HashMap::<(usize, BlockId), OperandVar>::new();
        let mut end_values = HashMap::<(usize, BlockId), OperandVar>::new();

        let mut reverse_post_order = traverse_post_order(code.bid_init, &cfg);
        reverse_post_order.reverse();

        for bid in reverse_post_order.iter() {
            let block: &mut Block = code.blocks.get_mut(&bid).unwrap();

            for instr in block.instructions.iter_mut() {
                let instr: &mut Instruction = instr.deref_mut();

                if let Instruction::Store { ptr, value } = instr {
                    let (rid, _) = some_or!(ptr.get_register(), continue);
                    if let RegisterId::Local { aid } = rid {
                        if inpromotable.contains(aid) {
                            continue;
                        }
                        end_values.insert((*aid, *bid), OperandVar::Operand(value.clone()));
                    }
                }
            }
        }

        for bid in reverse_post_order.iter() {
            let block: &mut Block = code.blocks.get_mut(&bid).unwrap();

            for (iid, instr) in block.instructions.iter_mut().enumerate() {
                let instr: &mut Instruction = instr.deref_mut();

                match instr {
                    Instruction::Store { ptr, value } => {
                        let (rid, _) = some_or!(ptr.get_register(), continue);
                        if let RegisterId::Local { aid } = rid {
                            if inpromotable.contains(aid) {
                                continue;
                            }
                            current_values.insert((*aid, *bid), OperandVar::Operand(value.clone()));
                        }
                    }

                    Instruction::Load { ptr } => {
                        let (rid, _) = some_or!(ptr.get_register(), continue);

                        if let RegisterId::Local { aid } = rid {
                            if inpromotable.contains(aid) {
                                continue;
                            }
                            let var = get_mut_from_current_values(
                                &mut current_values,
                                &end_values,
                                &domtree,
                                &joins,
                                &mut phinode_positions,
                                &reverse_cfg,
                                &(*aid, *bid),
                            )
                            .unwrap_or(OperandVar::Operand(
                                Operand::constant(Constant::undef(
                                    ptr.dtype().get_pointer_inner().unwrap().clone(),
                                )),
                            ));
                            replaces.insert(RegisterId::Temp { bid: *bid, iid }, var);
                        }
                    }

                    _ => {}
                }
            }
        }
        phinode_positions.sort();

        //                                <(aid, bid), phinode_index>
        let mut phinode_indices = HashMap::<(usize, BlockId), usize>::new();

        for (aid, bid) in phinode_positions.iter() {
            let block = code.blocks.get_mut(bid).unwrap();
            let phinode = code.allocations.get(*aid).unwrap().clone();
            let index = block.phinodes.len();
            block.phinodes.push(phinode);
            phinode_indices.insert((*aid, *bid), index);
        }

        for (aid, bid) in phinode_positions.iter() {
            let dtype = code.allocations.get(*aid).unwrap().deref().clone();

            let jumps = reverse_cfg.get(bid).unwrap();
            for (bid_from, _) in jumps {
                let block_from = code.blocks.get_mut(bid_from).unwrap();
                block_from.exit.walk_jump_args(|arg| {
                    if *bid == arg.bid {
                        // append to the jump arg
                        let value = get_from_current_values(
                            &current_values,
                            &domtree,
                            &joins,
                            &phinode_positions,
                            &reverse_cfg,
                            &(*aid, *bid_from),
                        )
                        .unwrap_or(OperandVar::Operand(Operand::constant(Constant::undef(
                            dtype.clone(),
                        ))));

                        let value = value.lookup(&dtype, &phinode_indices);

                        arg.args.push(value);
                    }
                })
            }
        }

        code.walk(|operand| {
            let (rid, dtype) = some_or!(operand.get_register(), return false);
            let operand_var = some_or!(replaces.get(rid), return false);
            *operand = operand_var.lookup(dtype, &phinode_indices);
            true
        });

        for block in code.blocks.values_mut() {
            for instr in block.instructions.iter_mut() {
                match instr.deref().deref() {
                    Instruction::Store { ptr, .. } => {
                        let (rid, _) = some_or!(ptr.get_register(), continue);
                        if let RegisterId::Local { aid } = rid {
                            if !inpromotable.contains(aid) {
                                *instr.deref_mut() = Instruction::Nop;
                            }
                        }
                    }
                    Instruction::Load { ptr } => {
                        let (rid, _) = some_or!(ptr.get_register(), continue);
                        if let RegisterId::Local { aid } = rid {
                            if !inpromotable.contains(aid) {
                                *instr.deref_mut() = Instruction::Nop;
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        true
    }
}

fn get_mut_from_current_values(
    current_values: &mut HashMap<(usize, BlockId), OperandVar>,
    end_values: &HashMap<(usize, BlockId), OperandVar>,
    domtree: &Domtree,
    joins: &HashMap<usize, HashSet<BlockId>>,
    phinode_positions: &mut Vec<(usize, BlockId)>,
    reverse_cfg: &ReverseCFG,
    key: &(usize, BlockId),
) -> Option<OperandVar> {
    if let Some(value) = current_values.get(key) {
        Some(value.clone())
    } else if joins
        .get(&key.0)
        .map(|s| s.contains(&key.1))
        .unwrap_or(false)
    {
        phinode_positions.push(key.clone());
        let current_value = OperandVar::Phi(key.clone());
        current_values.insert(key.clone(), current_value.clone());

        for (bid_prev, _) in reverse_cfg.get(&key.1).unwrap().iter() {
            if let None = end_values.get(&(key.0, *bid_prev)) {
                let _ = get_mut_from_current_values(
                    current_values,
                    end_values,
                    domtree,
                    joins,
                    phinode_positions,
                    reverse_cfg,
                    &(key.0, *bid_prev),
                );
            }
        }

        Some(current_value)
    } else {
        if let Some(bid_idom) = domtree.idom(key.1) {
            get_mut_from_current_values(
                current_values,
                end_values,
                domtree,
                joins,
                phinode_positions,
                reverse_cfg,
                &(key.0, bid_idom),
            )
        } else {
            None
        }
    }
}

fn get_from_current_values(
    current_values: &HashMap<(usize, BlockId), OperandVar>,
    domtree: &Domtree,
    joins: &HashMap<usize, HashSet<BlockId>>,
    phinode_positions: &Vec<(usize, BlockId)>,
    reverse_cfg: &ReverseCFG,
    key: &(usize, BlockId),
) -> Option<OperandVar> {
    if let Some(value) = current_values.get(key) {
        Some(value.clone())
    } else {
        if let Some(bid_idom) = domtree.idom(key.1) {
            get_from_current_values(
                current_values,
                domtree,
                joins,
                phinode_positions,
                reverse_cfg,
                &(key.0, bid_idom),
            )
        } else {
            None
        }
    }
}

fn mark_inpromotable(inpromotable: &mut HashSet<usize>, operand: &Operand) -> () {
    match operand.clone() {
        Operand::Register { rid, .. } => match rid {
            RegisterId::Local { aid } => {
                inpromotable.insert(aid);
            }
            _ => {}
        },
        _ => {}
    }
}
