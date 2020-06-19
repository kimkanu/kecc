use crate::ir::*;
use crate::opt::opt_utils::*;
use crate::opt::FunctionPass;
use crate::*;
use lang_c::ast;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::ops::Deref;
use std::ops::DerefMut;

pub type Gvn = FunctionPass<GvnInner>;

#[derive(Default)]
pub struct GvnInner {}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub enum Num {
    Num(usize),
}
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum ConstantNum {
    Constant(Constant),
    Num(Num),
}
impl ConstantNum {
    fn from_operand(
        operand: &Operand,
        register_table: &mut HashMap<RegisterId, ConstantNum>,
    ) -> Self {
        match &operand {
            &Operand::Constant(constant) => Self::Constant(constant.clone()),
            &Operand::Register { rid, .. } => {
                let len = register_table.len();
                if let Some(obtained) = register_table.get(&rid) {
                    obtained.clone()
                } else {
                    let num = Num::Num(len);
                    register_table.insert(rid.clone(), ConstantNum::Num(num));
                    ConstantNum::Num(num)
                }
            }
        }
    }
}

// optimizable expressions without any side effects
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum Expr {
    BinOp {
        op: ast::BinaryOperator,
        lhs: ConstantNum,
        rhs: ConstantNum,
        dtype: Dtype,
    },
    UnaryOp {
        op: ast::UnaryOperator,
        operand: ConstantNum,
        dtype: Dtype,
    },
    TypeCast {
        value: ConstantNum,
        target_dtype: Dtype,
    },
    GetElementPtr {
        ptr: ConstantNum,
        offset: ConstantNum,
        dtype: Box<Dtype>,
    },
}

fn get_from_leader_table(
    key: &(BlockId, usize, Num),
    leader_table: &HashMap<(BlockId, usize, Num), Operand>,
    domtree: &Domtree,
    code: &FunctionDefinition,
) -> Option<Operand> {
    if let Some(operand) = leader_table.get(key) {
        Some(operand.clone())
    } else {
        if key.1 != 0 {
            get_from_leader_table(
                &(key.0, key.1 - 1, key.2.clone()),
                leader_table,
                domtree,
                code,
            )
        } else if let Some(bid_idom) = domtree.idom(key.0) {
            get_from_leader_table(
                &(
                    bid_idom,
                    code.blocks.get(&bid_idom).unwrap().instructions.len(),
                    key.2.clone(),
                ),
                leader_table,
                domtree,
                code,
            )
        } else {
            None
        }
    }
}

impl Optimize<ir::FunctionDefinition> for GvnInner {
    fn optimize(&mut self, code: &mut ir::FunctionDefinition) -> bool {
        let mut register_table = HashMap::<RegisterId, ConstantNum>::new();
        let mut expr_table = HashMap::<Expr, Num>::new();
        // leader_table: (aid, num) => operand
        //   in the line of %bid:aid,
        //   the occurrence of num could be changed into operand
        let mut leader_table = HashMap::<(BlockId, usize, Num), Operand>::new();
        let mut leader_table_traversed = HashSet::<BlockId>::new();

        let cfg = make_cfg(code);
        let reverse_cfg = reverse_cfg(&cfg);
        let domtree = Domtree::new(code.bid_init, &cfg, &reverse_cfg);

        let mut reverse_post_order = traverse_post_order(code.bid_init, &cfg);
        reverse_post_order.reverse();

        let mut replaces = HashMap::<RegisterId, Operand>::new();
        let mut phinode_indices = HashMap::<BlockId, Vec<Named<Dtype>>>::new();
        let mut jump_args_indices = HashMap::<(BlockId, BlockId, usize), Operand>::new();

        for bid in reverse_post_order.iter() {
            let block = code.blocks.get(bid).unwrap();

            // insert arguments in the register table
            for (pid, _) in block.phinodes.iter().enumerate() {
                let empty = Vec::<(BlockId, JumpArg)>::new();
                let registers: Vec<_> = reverse_cfg
                    .get(bid)
                    .unwrap_or(&empty)
                    .iter()
                    .map(|(_, arg)| arg.args.get(pid).unwrap().get_register())
                    .collect();
                if registers.len() == 0 {
                    register_table.insert(
                        RegisterId::arg(*bid, pid),
                        ConstantNum::Num(Num::Num(register_table.len())),
                    );
                    continue;
                }
                if registers.iter().any(|&x| x.is_none()) {
                    register_table.insert(
                        RegisterId::arg(*bid, pid),
                        ConstantNum::Num(Num::Num(register_table.len())),
                    );
                    continue;
                }
                let registers: Vec<_> = registers.iter().map(|&x| x.unwrap()).collect();
                let nums: Vec<_> = registers
                    .iter()
                    .map(|&(rid, _)| register_table.get(rid))
                    .collect();
                if nums.iter().any(|&x| x.is_none()) {
                    register_table.insert(
                        RegisterId::arg(*bid, pid),
                        ConstantNum::Num(Num::Num(register_table.len())),
                    );
                    continue;
                }
                let nums: Vec<_> = nums.iter().map(|x| x.clone().unwrap().clone()).collect();
                let num = nums.get(1).unwrap().clone();
                if nums.iter().any(|x| *x != num) {
                    register_table.insert(
                        RegisterId::arg(*bid, pid),
                        ConstantNum::Num(Num::Num(register_table.len())),
                    );
                    continue;
                }
                register_table.insert(RegisterId::arg(*bid, pid), num);
            }

            let predecessors = reverse_cfg
                .get(bid)
                .map(|x| x.clone())
                .unwrap_or(Vec::new());

            // traverse the phinodes
            for (pid, phinode) in block.phinodes.iter().enumerate() {
                // For a phinode %i@pc, suppose %i is assigned with a number Ⓝ.
                let num = register_table
                    .get(&RegisterId::arg(*bid, pid))
                    .unwrap()
                    .clone();
                let num = match num {
                    ConstantNum::Constant(constant) => {
                        replaces.insert(RegisterId::arg(*bid, pid), Operand::constant(constant));
                        continue;
                    }
                    ConstantNum::Num(num) => num,
                };
                // If LT@pc(Ⓝ) exists, then replaces %i with LT@pc(Ⓝ).
                let leader_value =
                    get_from_leader_table(&(*bid, 0, num), &leader_table, &domtree, code);
                if let Some(operand) = leader_value {
                    replaces.insert(RegisterId::arg(*bid, pid), operand);
                    continue;
                }

                if predecessors.len() > 0 {
                    // If [LT@B_final(Ⓝ) exists for all predecessor B of %i’s block],
                    let bids: Vec<_> = predecessors.iter().map(|(bid_pred, _)| *bid_pred).collect();
                    // - predecessor B should have been traversed
                    if bids
                        .iter()
                        .any(|bid_pred| !leader_table_traversed.contains(bid_pred))
                    {
                        let operand =
                            Operand::register(RegisterId::arg(*bid, pid), phinode.deref().clone());
                        leader_table.insert((*bid, 0, num), operand.clone());
                        continue;
                    }
                    // println!("{} {} bids: all traversed", *bid, pid);
                    let mut pred_leader_values = Vec::<(BlockId, Option<Operand>)>::new();
                    for bid_pred in bids.iter() {
                        let pred_block = code.blocks.get(bid_pred).unwrap();
                        pred_block.clone().exit.walk_jump_args(|arg| {
                            if *bid == arg.bid {
                                pred_leader_values
                                    .push((*bid_pred, arg.args.get(pid).map(|s| s.clone())));
                            }
                        });
                    }
                    // println!(
                    //     "{} {} pred_leader_values {:?}",
                    //     *bid,
                    //     pid,
                    //     pred_leader_values.clone()
                    // );
                    let pred_leader_values: Vec<_> = pred_leader_values
                        .iter()
                        .map(|(bid_pred, value)| {
                            let const_num = ConstantNum::from_operand(
                                &value.clone().unwrap(),
                                &mut register_table,
                            );
                            match const_num {
                                ConstantNum::Constant(constant) => {
                                    Some(Operand::Constant(constant))
                                }
                                ConstantNum::Num(num) => {
                                    let final_aid =
                                        code.blocks.get(bid_pred).unwrap().instructions.len();
                                    get_from_leader_table(
                                        &(*bid_pred, final_aid, num),
                                        &leader_table,
                                        &domtree,
                                        code,
                                    )
                                }
                            }
                        })
                        .collect();
                    // println!(
                    //     "=> {} {} pred_leader_values {:?}",
                    //     *bid,
                    //     pid,
                    //     pred_leader_values.clone()
                    // );

                    // - every value should exist
                    if pred_leader_values.iter().any(|value| value.is_none()) {
                        let operand =
                            Operand::register(RegisterId::arg(*bid, pid), phinode.deref().clone());
                        leader_table.insert((*bid, 0, num), operand.clone());
                        continue;
                    }
                    let pred_leader_values: Vec<_> = pred_leader_values
                        .iter()
                        .map(|s| s.clone().unwrap())
                        .collect();

                    // if LT(phi_arg) are all the same,
                    // then replace the phinode register by that
                    let common_leader_value = pred_leader_values.get(0).unwrap().clone();
                    if pred_leader_values
                        .iter()
                        .any(|value| *value != common_leader_value)
                    {
                        let operand =
                            Operand::register(RegisterId::arg(*bid, pid), phinode.deref().clone());
                        leader_table.insert((*bid, 0, num), operand.clone());
                        continue;
                    }
                    let common_leader_value_as_const_num =
                        ConstantNum::from_operand(&common_leader_value, &mut register_table);

                    register_table
                        .insert(RegisterId::arg(*bid, pid), common_leader_value_as_const_num);
                    leader_table.insert((*bid, 0, num), common_leader_value.clone());
                    replaces.insert(RegisterId::arg(*bid, pid), common_leader_value);
                } else {
                    // Otherwise, let LT@pc(Ⓝ) = %i.
                    let operand =
                        Operand::register(RegisterId::arg(*bid, pid), phinode.deref().clone());
                    leader_table.insert((*bid, 0, num), operand.clone());
                }
            }

            // traverse the instructions: assign nums to exprs
            for (iid, instr) in block.instructions.iter().enumerate() {
                let instr = instr.deref().clone();
                let expr: Option<Expr> = match instr.clone() {
                    Instruction::BinOp {
                        op,
                        lhs,
                        rhs,
                        dtype,
                    } => {
                        let lhs = ConstantNum::from_operand(&lhs, &mut register_table);
                        let rhs = ConstantNum::from_operand(&rhs, &mut register_table);

                        Some(Expr::BinOp {
                            op,
                            lhs,
                            rhs,
                            dtype,
                        })
                    }
                    Instruction::UnaryOp { op, operand, dtype } => {
                        let operand = ConstantNum::from_operand(&operand, &mut register_table);

                        Some(Expr::UnaryOp { op, operand, dtype })
                    }
                    Instruction::TypeCast {
                        value,
                        target_dtype,
                    } => {
                        let value = ConstantNum::from_operand(&value, &mut register_table);
                        Some(Expr::TypeCast {
                            value,
                            target_dtype,
                        })
                    }
                    Instruction::GetElementPtr { ptr, offset, dtype } => {
                        let ptr = ConstantNum::from_operand(&ptr, &mut register_table);
                        let offset = ConstantNum::from_operand(&offset, &mut register_table);

                        Some(Expr::GetElementPtr { ptr, offset, dtype })
                    }
                    Instruction::Call { callee, args, .. } => {
                        let _ = ConstantNum::from_operand(&callee, &mut register_table);
                        for arg in args {
                            let _ = ConstantNum::from_operand(&arg, &mut register_table);
                        }
                        None
                    }
                    Instruction::Load { ptr } => {
                        let _ = ConstantNum::from_operand(&ptr, &mut register_table);
                        None
                    }
                    Instruction::Store { ptr, value } => {
                        let _ = ConstantNum::from_operand(&ptr, &mut register_table);
                        let _ = ConstantNum::from_operand(&value, &mut register_table);
                        None
                    }
                    _ => None,
                };

                let expr = if let Some(expr) = expr {
                    expr
                } else {
                    let len = register_table.len();
                    register_table
                        .insert(RegisterId::temp(*bid, iid), ConstantNum::Num(Num::Num(len)));
                    continue;
                };

                let num = expr_table.get(&expr);
                if let Some(num) = num {
                    register_table.insert(RegisterId::temp(*bid, iid), ConstantNum::Num(*num));
                }
                expr_table.entry(expr.clone()).or_insert_with(|| {
                    let len = register_table.len();
                    register_table
                        .insert(RegisterId::temp(*bid, iid), ConstantNum::Num(Num::Num(len)));
                    Num::Num(len)
                });
            }

            // traverse the instructions
            for (iid, instr) in block.instructions.iter().enumerate() {
                let instr = instr.deref().clone();
                // For an instruction %i@pc, suppose %i is assigned with a number Ⓝ.
                let num = register_table
                    .get(&RegisterId::temp(*bid, iid))
                    .unwrap()
                    .clone();
                // println!("bid {}, iid {}, num {:?}", *bid, iid, num);
                let num = match num {
                    ConstantNum::Constant(constant) => {
                        replaces.insert(RegisterId::temp(*bid, iid), Operand::constant(constant));
                        continue;
                    }
                    ConstantNum::Num(num) => num,
                };
                // If LT@pc(Ⓝ) exists, then replaces %i with LT@pc(Ⓝ).
                let leader_value =
                    get_from_leader_table(&(*bid, iid, num), &leader_table, &domtree, code);
                if let Some(operand) = leader_value {
                    if *operand.get_register().unwrap().0 != RegisterId::temp(*bid, iid) {
                        replaces.insert(RegisterId::temp(*bid, iid), operand);
                    }
                    continue;
                }

                let predecessors = reverse_cfg
                    .get(bid)
                    .map(|x| x.clone())
                    .unwrap_or(Vec::new());
                if predecessors.len() > 0 {
                    // If [LT@B_final(Ⓝ) exists for all predecessor B of %i’s block],
                    let bids: Vec<_> = predecessors.iter().map(|(bid_pred, _)| *bid_pred).collect();
                    // - predecessor B should have been traversed
                    if bids
                        .iter()
                        .any(|bid_pred| !leader_table_traversed.contains(bid_pred))
                    {
                        let operand = Operand::register(RegisterId::temp(*bid, iid), instr.dtype());
                        leader_table.insert((*bid, iid, num), operand.clone());
                        continue;
                    }
                    let pred_leader_values: HashMap<_, _> = bids
                        .iter()
                        .map(|bid_pred| {
                            let final_aid = code.blocks.get(bid_pred).unwrap().instructions.len();
                            (
                                *bid_pred,
                                get_from_leader_table(
                                    &(*bid_pred, final_aid, num),
                                    &leader_table,
                                    &domtree,
                                    code,
                                ),
                            )
                        })
                        .collect();
                    // - every value should exist
                    if pred_leader_values.iter().any(|(_, value)| value.is_none()) {
                        let operand = Operand::register(RegisterId::temp(*bid, iid), instr.dtype());
                        leader_table.insert((*bid, iid, num), operand.clone());
                        continue;
                    }
                    // then creates a new phinode, say %p=ϕ({LT@B_final(Ⓝ) | B ∈ pred(%i)});
                    let phinode = Named::new(None, instr.dtype());
                    let pid = block.phinodes.len();
                    phinode_indices
                        .entry(*bid)
                        .or_insert_with(Vec::new)
                        .push(phinode);
                    for bid_pred in bids.iter() {
                        let leader_value =
                            pred_leader_values.get(&bid_pred).unwrap().clone().unwrap();
                        jump_args_indices.insert((*bid_pred, *bid, pid), leader_value);
                    }
                    // let LT@pc(Ⓝ) = %p; and replaces %i with %p.
                    let phinode_operand =
                        Operand::register(RegisterId::arg(*bid, pid), instr.dtype());
                    leader_table.insert((*bid, iid, num), phinode_operand.clone());
                    replaces.insert(RegisterId::temp(*bid, iid), phinode_operand);
                } else {
                    // Otherwise, let LT@pc(Ⓝ) = %i.
                    let operand = Operand::register(RegisterId::temp(*bid, iid), instr.dtype());
                    leader_table.insert((*bid, iid, num), operand.clone());
                }
            }

            leader_table_traversed.insert(*bid);
        }

        // println!("replaces {:#?}", replaces.clone());

        // insert phinodes
        for (bid, phinodes) in phinode_indices.iter() {
            code.blocks
                .get_mut(bid)
                .unwrap()
                .phinodes
                .extend(phinodes.clone());
        }
        for ((bid_from, bid_to, jid), operand) in jump_args_indices.iter() {
            code.blocks
                .get_mut(bid_from)
                .unwrap()
                .exit
                .walk_jump_args(|arg| {
                    if *bid_to == arg.bid {
                        arg.args.insert(*jid, operand.clone());
                    }
                })
        }

        code.walk(|operand| {
            let register = operand.get_register();
            some_or!(register, return false);
            let register = register.unwrap();
            if let Some(replacement) = replaces.get(register.0) {
                *operand = replacement.clone();
                true
            } else {
                false
            }
        })
    }
}
