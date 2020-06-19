use crate::ir::*;
use crate::opt::FunctionPass;
use crate::*;
use std::collections::{HashMap, HashSet};
use std::ops::Deref;
use std::ops::DerefMut;

pub type Deadcode = FunctionPass<Repeat<DeadcodeInner>>;

#[derive(Default)]
pub struct DeadcodeInner {}

impl Optimize<FunctionDefinition> for DeadcodeInner {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        // println!("code {:#?}", code.clone());
        let mut uses: HashSet<RegisterId> = HashSet::new();
        let mut replaces = HashMap::<RegisterId, Operand>::new();

        for (bid, block) in code.blocks.iter_mut() {
            for (iid, instr) in block.instructions.iter().enumerate() {
                let instr = instr.deref().clone();
                match instr.clone() {
                    Instruction::Nop => {
                        replaces.insert(
                            RegisterId::temp(*bid, iid),
                            Operand::constant(Constant::unit()),
                        );
                    }
                    Instruction::BinOp { lhs, rhs, .. } => {
                        mark_used(&lhs, &mut uses);
                        mark_used(&rhs, &mut uses);
                    }
                    Instruction::UnaryOp { operand, .. } => {
                        mark_used(&operand, &mut uses);
                    }
                    Instruction::Store { ptr, value } => {
                        mark_used(&ptr, &mut uses);
                        mark_used(&value, &mut uses);
                        uses.insert(RegisterId::temp(*bid, iid));
                    }
                    Instruction::Load { ptr } => {
                        mark_used(&ptr, &mut uses);
                    }
                    Instruction::Call { callee, args, .. } => {
                        mark_used(&callee, &mut uses);
                        for arg in args.iter() {
                            mark_used(&arg, &mut uses);
                        }
                        uses.insert(RegisterId::temp(*bid, iid));
                    }

                    Instruction::TypeCast { value, .. } => {
                        mark_used(&value, &mut uses);
                    }
                    Instruction::GetElementPtr { ptr, offset, .. } => {
                        mark_used(&ptr, &mut uses);
                        mark_used(&offset, &mut uses);
                    }
                }
            }
            match block.exit.clone() {
                BlockExit::Jump { arg } => {
                    for operand in arg.args.iter() {
                        mark_used(operand, &mut uses);
                    }
                }
                BlockExit::ConditionalJump {
                    condition,
                    arg_then,
                    arg_else,
                } => {
                    mark_used(&condition, &mut uses);
                    for operand in arg_then.args.iter() {
                        mark_used(operand, &mut uses);
                    }
                    for operand in arg_else.args.iter() {
                        mark_used(operand, &mut uses);
                    }
                }
                BlockExit::Switch {
                    value,
                    default,
                    cases,
                } => {
                    mark_used(&value, &mut uses);
                    for operand in default.args.iter() {
                        mark_used(operand, &mut uses);
                    }
                    for case in cases.iter() {
                        for operand in case.1.args.iter() {
                            mark_used(operand, &mut uses);
                        }
                    }
                }
                BlockExit::Return { value } => {
                    mark_used(&value, &mut uses);
                }
                _ => {}
            }
        }

        let mut changed = false;
        // removal of unused instructions
        for (bid, block) in code.blocks.iter_mut() {
            let mut len = block.instructions.len();
            let mut iid = 0;
            let mut removes = 0;
            loop {
                if iid >= len {
                    break;
                }
                if !uses.contains(&RegisterId::temp(*bid, iid + removes)) {
                    block.instructions.remove(iid);
                    len -= 1;
                    removes += 1;
                    changed = true;
                } else {
                    if removes != 0 {
                        replaces.insert(
                            RegisterId::temp(*bid, iid + removes),
                            Operand::register(
                                RegisterId::temp(*bid, iid),
                                block.instructions[iid].dtype(),
                            ),
                        );
                    }
                    iid += 1;
                }
            }
        }

        // removal of unused local allocations
        let mut len = code.allocations.len();
        let mut aid = 0;
        let mut removes = 0;
        loop {
            if aid >= len {
                break;
            }
            let alloca_dtype = code.allocations[aid].deref().clone();
            if !uses.contains(&RegisterId::local(aid + removes)) {
                // println!("remove alloca: %l{}", aid + removes);
                code.allocations.remove(aid);
                len -= 1;
                removes += 1;
                changed = true;
            } else {
                if removes != 0 {
                    replaces.insert(
                        RegisterId::local(aid + removes),
                        Operand::register(RegisterId::local(aid), Dtype::pointer(alloca_dtype)),
                    );
                }
                aid += 1;
            }
        }

        for (_bid, block) in code.blocks.iter_mut() {
            for instr in block.instructions.iter_mut() {
                match instr.deref_mut() {
                    Instruction::Nop => {}
                    Instruction::BinOp { lhs, rhs, .. } => {
                        if let Some(rid) = lhs.get_register() {
                            if let Some(replacement) = replaces.get(rid.0) {
                                *lhs = replacement.clone();
                                changed = true;
                            }
                        }
                        if let Some(rid) = rhs.get_register() {
                            if let Some(replacement) = replaces.get(rid.0) {
                                *rhs = replacement.clone();
                                changed = true;
                            }
                        }
                    }
                    Instruction::UnaryOp { operand, .. } => {
                        if let Some(rid) = operand.get_register() {
                            if let Some(replacement) = replaces.get(rid.0) {
                                *operand = replacement.clone();
                                changed = true;
                            }
                        }
                    }
                    Instruction::Store { ptr, value } => {
                        if let Some(rid) = ptr.get_register() {
                            if let Some(replacement) = replaces.get(rid.0) {
                                *ptr = replacement.clone();
                                changed = true;
                            }
                        }
                        if let Some(rid) = value.get_register() {
                            if let Some(replacement) = replaces.get(rid.0) {
                                *value = replacement.clone();
                                changed = true;
                            }
                        }
                    }
                    Instruction::Load { ptr } => {
                        if let Some(rid) = ptr.get_register() {
                            if let Some(replacement) = replaces.get(rid.0) {
                                *ptr = replacement.clone();
                                changed = true;
                            }
                        }
                    }
                    Instruction::Call { callee, args, .. } => {
                        if let Some(rid) = callee.get_register() {
                            if let Some(replacement) = replaces.get(rid.0) {
                                *callee = replacement.clone();
                                changed = true;
                            }
                        }
                        for arg in args.iter_mut() {
                            if let Some(rid) = arg.get_register() {
                                if let Some(replacement) = replaces.get(rid.0) {
                                    *arg = replacement.clone();
                                    changed = true;
                                }
                            }
                        }
                    }
                    Instruction::TypeCast { value, .. } => {
                        if let Some(rid) = value.get_register() {
                            if let Some(replacement) = replaces.get(rid.0) {
                                *value = replacement.clone();
                                changed = true;
                            }
                        }
                    }
                    Instruction::GetElementPtr { ptr, offset, .. } => {
                        if let Some(rid) = ptr.get_register() {
                            if let Some(replacement) = replaces.get(rid.0) {
                                *ptr = replacement.clone();
                                changed = true;
                            }
                        }
                        if let Some(rid) = offset.get_register() {
                            if let Some(replacement) = replaces.get(rid.0) {
                                *offset = replacement.clone();
                                changed = true;
                            }
                        }
                    }
                }
            }

            match &mut block.exit {
                BlockExit::Jump { arg } => {
                    for op in arg.args.iter_mut() {
                        if let Some(rid) = op.get_register() {
                            if let Some(replacement) = replaces.get(rid.0) {
                                *op = replacement.clone();
                                changed = true;
                            }
                        }
                    }
                }
                BlockExit::ConditionalJump {
                    condition,
                    arg_then,
                    arg_else,
                } => {
                    if let Some(rid) = condition.get_register() {
                        if let Some(replacement) = replaces.get(rid.0) {
                            *condition = replacement.clone();
                            changed = true;
                        }
                    }
                    for op in arg_then.args.iter_mut() {
                        if let Some(rid) = op.get_register() {
                            if let Some(replacement) = replaces.get(rid.0) {
                                *op = replacement.clone();
                                changed = true;
                            }
                        }
                    }
                    for op in arg_else.args.iter_mut() {
                        if let Some(rid) = op.get_register() {
                            if let Some(replacement) = replaces.get(rid.0) {
                                *op = replacement.clone();
                                changed = true;
                            }
                        }
                    }
                }
                BlockExit::Switch {
                    value,
                    default,
                    cases,
                } => {
                    if let Some(rid) = value.get_register() {
                        if let Some(replacement) = replaces.get(rid.0) {
                            *value = replacement.clone();
                            changed = true;
                        }
                    }
                    for op in default.args.iter_mut() {
                        if let Some(rid) = op.get_register() {
                            if let Some(replacement) = replaces.get(rid.0) {
                                *op = replacement.clone();
                                changed = true;
                            }
                        }
                    }
                    for case in cases.iter_mut() {
                        for op in case.1.args.iter_mut() {
                            if let Some(rid) = op.get_register() {
                                if let Some(replacement) = replaces.get(rid.0) {
                                    *op = replacement.clone();
                                    changed = true;
                                }
                            }
                        }
                    }
                }
                BlockExit::Return { value } => {
                    if let Some(rid) = value.get_register() {
                        if let Some(replacement) = replaces.get(rid.0) {
                            *value = replacement.clone();
                            changed = true;
                        }
                    }
                }
                _ => {}
            }
        }

        changed
    }
}

fn mark_used(operand: &Operand, uses: &mut HashSet<RegisterId>) -> bool {
    match operand.clone() {
        Operand::Constant { .. } => true,
        Operand::Register { rid, .. } => match rid {
            RegisterId::Temp { .. } => uses.insert(rid),
            RegisterId::Local { .. } => uses.insert(rid),
            _ => true,
        },
    }
}
