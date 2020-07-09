use crate::asm;
use crate::ir;
use crate::ir::HasDtype;
use crate::Translate;
use crate::*;
use core::convert::TryFrom;
use lang_c::ast;
use std::collections::{HashMap, HashSet};
use std::ops::Deref;

#[derive(Default)]
pub struct Asmgen {}

pub struct Helper {}
impl Helper {
    fn to_eights(n: usize) -> usize {
        ((n + 7) / 8) * 8
    }
    fn u64_negative(i: u64) -> u64 {
        if i == 0 {
            0
        } else {
            u64::MAX - i + 1
        }
    }
    fn dtype_to_width(dtype: &ir::Dtype) -> usize {
        match dtype.clone() {
            ir::Dtype::Unit { .. } => 0,
            _ => {
                let data_size = asm::DataSize::try_from(dtype.clone())
                    .expect("`data_size` must be derived from `dtype`");
                match data_size {
                    asm::DataSize::Byte => 1,
                    asm::DataSize::Half => 2,
                    asm::DataSize::Word | asm::DataSize::SinglePrecision => 4,
                    asm::DataSize::Double | asm::DataSize::DoublePrecision => 8,
                }
            }
        }
    }
    fn const_to_u64(constant: &ast::Constant) -> Result<u64, ()> {
        let constant = ir::Constant::try_from(constant)?;
        match constant {
            ir::Constant::Int { value, .. } => Ok(value as u64),
            ir::Constant::Float { value, .. } => Ok(value.into_inner().floor() as u64),
            _ => panic!("unsupported initializer"),
        }
    }
    fn const_to_f64(constant: &ast::Constant) -> Result<f64, ()> {
        let constant = ir::Constant::try_from(constant)?;
        match constant {
            ir::Constant::Int { value, .. } => Ok(value as f64),
            ir::Constant::Float { value, .. } => Ok(value.into_inner() as f64),
            _ => panic!("unsupported initializer"),
        }
    }
    fn ir_const_to_u64_bytes(constant: &ir::Constant) -> u64 {
        match constant {
            ir::Constant::Int { value, .. } => *value as u64,
            ir::Constant::Float { value, .. } => u64::from_be_bytes(value.to_be_bytes()),
            _ => panic!("constant value of other than int and float"),
        }
    }
    fn an_to_fan(an: &asm::Register) -> asm::Register {
        match an {
            asm::Register::Arg(asm::RegisterType::Integer, id) => {
                asm::Register::arg(asm::RegisterType::FloatingPoint, *id)
            }
            _ => panic!(),
        }
    }
    fn fan_to_an(fan: &asm::Register) -> asm::Register {
        match fan {
            asm::Register::Arg(asm::RegisterType::FloatingPoint, id) => {
                asm::Register::arg(asm::RegisterType::Integer, *id)
            }
            _ => panic!(),
        }
    }
}

#[derive(Debug)]
pub struct IntervalTree {
    content: (usize, usize), // (a, b) corresponds to the interval [a, b[
    left: Option<Box<IntervalTree>>,
    right: Option<Box<IntervalTree>>,
}
impl IntervalTree {
    fn new_leaf(content: (usize, usize)) -> Self {
        IntervalTree {
            content,
            left: None,
            right: None,
        }
    }

    fn new(intervals: Vec<(usize, usize)>) -> Option<Self> {
        // assuming that the given intervals are disjoint
        let (head, tail) = intervals.split_at(1);
        let content = if let Some(elem) = head.first() {
            elem.clone()
        } else {
            return None;
        };
        let mut tree = Self::new_leaf(content);
        for interval in tail {
            tree.insert(*interval);
        }
        Some(tree)
    }

    // TODO: self-balancing (like AVL) to make it optimized
    fn insert(&mut self, new_interval: (usize, usize)) -> bool {
        // if interval.left_end is in self.content => overlapping; return false
        let new_left_end = new_interval.0;
        let new_right_end = new_interval.1;

        let curr_left_end = self.content.0;
        let curr_right_end = self.content.1;

        // overlapping case
        if new_left_end >= curr_left_end && new_left_end < curr_right_end {
            return false;
        }

        if new_left_end >= curr_right_end {
            // if the node has no right child
            if new_left_end == curr_right_end {
                self.content = (curr_left_end, new_right_end);
                true
            } else if self.right.is_none() {
                let right_child = Self::new_leaf(new_interval);
                self.right = Some(Box::new(right_child));
                true
            } else {
                self.right.as_mut().unwrap().insert(new_interval)
            }
        } else {
            if new_right_end == curr_left_end {
                self.content = (new_left_end, curr_right_end);
                true
            } else if self.left.is_none() {
                let left_child = Self::new_leaf(new_interval);
                self.left = Some(Box::new(left_child));
                true
            } else {
                self.left.as_mut().unwrap().insert(new_interval)
            }
        }
    }
}

// <- (+)                                                         (-) ->
// [   ra   |   s0   | ret | phinodes | local allocas | temp registers ]
#[derive(Debug)]
pub struct Stack {
    //                               (-start pt, width)
    allocations: HashMap<ir::RegisterId, (usize, usize)>,
    alloca_tree: Option<IntervalTree>,
    size: usize,
    ret: usize,
}
impl Stack {
    fn new() -> Self {
        Self {
            allocations: HashMap::new(),
            alloca_tree: None,
            size: 16,
            ret: 16,
        }
    }

    fn set_return(&mut self, return_width: usize) {
        self.ret += return_width;
    }

    fn insert_allocation(&mut self, aid: ir::RegisterId, width: usize) -> usize {
        let mut sp = self.ret;
        if let Some(alloca_tree) = &mut self.alloca_tree {
            loop {
                let res = alloca_tree.insert((sp, sp + width));
                if res {
                    break;
                }
                sp += width;
            }
        } else {
            self.alloca_tree = IntervalTree::new(vec![(sp, sp + width)]);
        }
        self.allocations.insert(aid, (sp + width, width));
        let last_to_eights = Helper::to_eights(sp + width);
        if self.size < last_to_eights {
            self.size = last_to_eights
        }
        sp + width
    }
}

enum AsmgenError {
    AsmgenError(String),
}
impl AsmgenError {
    fn new<S>(message: S) -> Self
    where
        S: Into<String>,
    {
        Self::AsmgenError(message.into())
    }
}

impl Translate<ir::TranslationUnit> for Asmgen {
    type Target = asm::Asm;
    type Error = ();

    fn translate(&mut self, source: &ir::TranslationUnit) -> Result<Self::Target, Self::Error> {
        let mut variables = Vec::<asm::Section<asm::Variable>>::new();
        let mut functions = Vec::<asm::Section<asm::Function>>::new();

        for (name, decl) in source.decls.iter() {
            match decl {
                ir::Declaration::Variable { dtype, initializer } => {
                    if let Some(variable) =
                        self.translate_variable_declaration(name, dtype, initializer)?
                    {
                        variables.push(variable);
                    }
                }
                ir::Declaration::Function {
                    signature,
                    definition,
                } => {
                    let definition = some_or!(definition, continue);

                    let mut blocks = Vec::<asm::Block>::new();
                    let mut instructions = Vec::new();

                    // 1. stack pointer allocation
                    let mut stack = Stack::new();
                    stack.set_return(Helper::dtype_to_width(&signature.ret));

                    //    (a) phinode allocations
                    for (bid, block) in definition.blocks.iter() {
                        for (pid, phinode) in block.phinodes.iter().enumerate() {
                            let dtype = phinode.deref();
                            let rid = ir::RegisterId::arg(*bid, pid);
                            stack.insert_allocation(rid, Helper::dtype_to_width(dtype));
                        }
                    }

                    //    (b) local allocations
                    let allocations = &definition.allocations;
                    for (aid, allocation) in allocations.iter().enumerate() {
                        let dtype = allocation.deref();
                        let rid = ir::RegisterId::local(aid);
                        stack.insert_allocation(rid, Helper::dtype_to_width(dtype));
                    }

                    //    (c) temporary registers
                    for (bid, block) in definition.blocks.iter() {
                        for (iid, instr) in block.instructions.iter().enumerate() {
                            let dtype = instr.deref().dtype();
                            let rid = ir::RegisterId::temp(*bid, iid);
                            match dtype {
                                ir::Dtype::Int { width, .. } => {
                                    stack.insert_allocation(rid, Helper::to_eights(width) / 8);
                                }
                                ir::Dtype::Float { width, .. } => {
                                    stack.insert_allocation(rid, width / 8);
                                }
                                ir::Dtype::Pointer { .. } => {
                                    stack.insert_allocation(rid, ir::Dtype::SIZE_OF_POINTER);
                                }
                                ir::Dtype::Array { .. } => todo!("temporary registers allocation"),
                                ir::Dtype::Struct { .. } => todo!("temporary registers allocation"),
                                ir::Dtype::Unit { .. } => {}
                                _ => {}
                            }
                        }
                    }

                    let stack_size = stack.size as u64;

                    // decrement the stack pointer `sp`
                    instructions.push(asm::Instruction::IType {
                        instr: asm::IType::ADDI,
                        rd: asm::Register::Sp,
                        rs1: asm::Register::Sp,
                        imm: asm::Immediate::Value(Helper::u64_negative(stack_size)),
                    });

                    // Backup the return address `ra` and frame pointer `s0`
                    instructions.push(asm::Instruction::SType {
                        instr: asm::SType::SD,
                        rs1: asm::Register::Sp,
                        rs2: asm::Register::Ra,
                        imm: asm::Immediate::Value(stack_size - 8),
                    });
                    instructions.push(asm::Instruction::SType {
                        instr: asm::SType::SD,
                        rs1: asm::Register::Sp,
                        rs2: asm::Register::S0,
                        imm: asm::Immediate::Value(stack_size - 16),
                    });
                    instructions.push(asm::Instruction::IType {
                        instr: asm::IType::ADDI,
                        rd: asm::Register::S0,
                        rs1: asm::Register::Sp,
                        imm: asm::Immediate::Value(stack_size),
                    });

                    // default return value
                    instructions.push(asm::Instruction::Pseudo(asm::Pseudo::Mv {
                        rd: asm::Register::A0,
                        rs: asm::Register::Zero,
                    }));
                    instructions.push(asm::Instruction::SType {
                        instr: asm::SType::SD,
                        rs1: asm::Register::S0,
                        rs2: asm::Register::A0,
                        imm: asm::Immediate::Value(Helper::u64_negative(stack.ret as u64)),
                    });

                    let block_init = definition.blocks.get(&definition.bid_init).unwrap();
                    self.translate_block(
                        definition.bid_init,
                        block_init,
                        &signature.ret,
                        name,
                        &mut functions,
                        &mut variables,
                        &mut instructions,
                        &mut stack,
                    )
                    .map_err(|e| match e {
                        AsmgenError::AsmgenError(s) => panic!(s),
                    })?;

                    // push main block
                    blocks.push(asm::Block::new(
                        Some(asm::Label(name.clone())),
                        instructions,
                    ));

                    for (bid, block) in definition.blocks.iter() {
                        if bid == &definition.bid_init {
                            continue;
                        }

                        let mut instructions = Vec::new();
                        self.translate_block(
                            *bid,
                            block,
                            &signature.ret,
                            name,
                            &mut functions,
                            &mut variables,
                            &mut instructions,
                            &mut stack,
                        )
                        .map_err(|e| match e {
                            AsmgenError::AsmgenError(s) => panic!(s),
                        })?;
                        blocks.push(asm::Block::new(
                            Some(asm::Label(format!(".{}_{}", name.clone(), bid))),
                            instructions,
                        ));
                    }

                    let func = asm::Function { blocks };
                    let section = asm::Section {
                        header: Vec::new(),
                        body: func,
                    };

                    functions.push(section);
                }
            }
        }

        let unit = asm::TranslationUnit {
            functions,
            variables,
        };

        Ok(asm::Asm { unit })
    }
}

impl Asmgen {
    /// Translate a global variable declaration
    fn translate_variable_declaration(
        &mut self,
        name: &String,
        dtype: &ir::Dtype,
        initializer: &Option<ast::Initializer>,
    ) -> Result<Option<asm::Section<asm::Variable>>, ()> {
        // global variables
        let directives = match dtype {
            // ignore unit global variables
            ir::Dtype::Unit { .. } => return Ok(None),
            ir::Dtype::Int { width, .. } => {
                // initializer to u64
                // we only deal with the constant initializers (for hw7)
                let value: u64 = match initializer {
                    None => 0,
                    Some(ast::Initializer::Expression(expr)) => {
                        let expr = expr.as_ref().clone().node;
                        match expr {
                            ast::Expression::Constant(constant) => {
                                Helper::const_to_u64(&constant.as_ref().node)?
                            }
                            ast::Expression::UnaryOperator(unary_expr) => {
                                let unary_expr = &unary_expr.as_ref().node;
                                let operand = &unary_expr.operand.as_ref().node;
                                if let (
                                    ast::UnaryOperator::Minus,
                                    ast::Expression::Constant(constant),
                                ) = (&unary_expr.operator.node, operand)
                                {
                                    Helper::u64_negative(Helper::const_to_u64(
                                        &constant.as_ref().node,
                                    )?)
                                } else {
                                    panic!("unsupported initializer")
                                }
                            }
                            _ => panic!("unsupported initializer"),
                        }
                    }
                    _ => panic!("Initialize a non-array variable by a list"),
                };

                let directive = match width / ir::Dtype::BITS_OF_BYTE {
                    ir::Dtype::SIZE_OF_CHAR => asm::Directive::Byte(value as u8),
                    ir::Dtype::SIZE_OF_SHORT => asm::Directive::Half(value as u16),
                    ir::Dtype::SIZE_OF_INT => asm::Directive::Word(value as u32),
                    ir::Dtype::SIZE_OF_LONG => asm::Directive::Quad(value),
                    _ => panic!("not an integer"),
                };
                vec![directive]
            }
            ir::Dtype::Float { width, .. } => {
                // initializer to f64
                // we only deal with the constant initializers (for hw7)
                let value: f64 = match initializer {
                    None => 0.,
                    Some(ast::Initializer::Expression(expr)) => {
                        let expr = expr.as_ref().clone().node;
                        match expr {
                            ast::Expression::Constant(constant) => {
                                Helper::const_to_f64(&constant.as_ref().node)?
                            }
                            ast::Expression::UnaryOperator(unary_expr) => {
                                let unary_expr = &unary_expr.as_ref().node;
                                let operand = &unary_expr.operand.as_ref().node;
                                if let (
                                    ast::UnaryOperator::Minus,
                                    ast::Expression::Constant(constant),
                                ) = (&unary_expr.operator.node, operand)
                                {
                                    -Helper::const_to_f64(&constant.as_ref().node)?
                                } else {
                                    panic!("unsupported initializer")
                                }
                            }
                            _ => panic!("unsupported initializer"),
                        }
                    }
                    _ => panic!("Initialize a non-array variable by a list"),
                };

                let directive = match width / ir::Dtype::BITS_OF_BYTE {
                    ir::Dtype::SIZE_OF_FLOAT => {
                        asm::Directive::Word(u32::from_be_bytes((value as f32).to_be_bytes()))
                    }
                    ir::Dtype::SIZE_OF_DOUBLE => {
                        asm::Directive::Quad(u64::from_be_bytes(value.to_be_bytes()))
                    }
                    _ => panic!("not a float"),
                };
                vec![directive]
            }
            _ => todo!("should support variable declaration other than int and float"),
        };

        let label = asm::Label(name.clone());
        let var = asm::Variable { label, directives };
        let section = asm::Section {
            header: Vec::new(),
            body: var,
        };

        Ok(Some(section))
    }

    fn translate_block(
        &mut self,
        bid: ir::BlockId,
        block: &ir::Block,
        ret: &ir::Dtype,
        function_name: &String,
        functions: &mut Vec<asm::Section<asm::Function>>,
        variables: &mut Vec<asm::Section<asm::Variable>>,
        instructions: &mut Vec<asm::Instruction>,
        stack: &mut Stack,
    ) -> Result<(), AsmgenError> {
        // TODO: phinodes

        // instructions
        for (iid, named_instr) in block.instructions.iter().enumerate() {
            instructions.extend(self.translate_instruction(
                &named_instr,
                iid,
                bid,
                block,
                ret,
                function_name,
                functions,
                variables,
                stack,
            )?);
        }

        // block exit
        match &block.exit {
            ir::BlockExit::Return { value } => {
                let stack_size = stack.size as u64;
                instructions.extend(Self::translate_operand_to_register(
                    value,
                    asm::Register::A0,
                    stack,
                )?);
                instructions.push(asm::Instruction::IType {
                    instr: asm::IType::LD,
                    rd: asm::Register::Sp,
                    rs1: asm::Register::S0,
                    imm: asm::Immediate::Value(stack_size - 16),
                });
                instructions.push(asm::Instruction::IType {
                    instr: asm::IType::LD,
                    rd: asm::Register::Sp,
                    rs1: asm::Register::Ra,
                    imm: asm::Immediate::Value(stack_size - 8),
                });
                instructions.push(asm::Instruction::IType {
                    instr: asm::IType::ADDI,
                    rd: asm::Register::Sp,
                    rs1: asm::Register::Sp,
                    imm: asm::Immediate::Value(stack_size),
                });
                instructions.push(asm::Instruction::Pseudo(asm::Pseudo::Ret));
            }

            ir::BlockExit::ConditionalJump {
                condition,
                arg_then,
                arg_else,
            } => {
                let (instrs, regs) = Self::translate_operands_to_register(vec![condition], stack)?;
                instructions.extend(instrs);
                let reg = regs[0];
                instructions.push(asm::Instruction::BType {
                    instr: asm::BType::Bne,
                    rs1: reg,
                    rs2: asm::Register::Zero,
                    imm: asm::Label(format!(
                        ".{}_{}",
                        function_name.clone(),
                        arg_then.deref().bid
                    )),
                });
                instructions.push(asm::Instruction::Pseudo(asm::Pseudo::J {
                    offset: asm::Label(format!(
                        ".{}_{}",
                        function_name.clone(),
                        arg_else.deref().bid
                    )),
                }));
            }
            _ => todo!("translate block exit"),
        }

        Ok(())
    }
}

impl Asmgen {
    fn translate_instruction(
        &mut self,
        named_instr: &ir::Named<ir::Instruction>,
        iid: usize,
        bid: ir::BlockId,
        block: &ir::Block,
        ret: &ir::Dtype,
        function_name: &String,
        functions: &mut Vec<asm::Section<asm::Function>>,
        variables: &mut Vec<asm::Section<asm::Variable>>,
        stack: &mut Stack,
    ) -> Result<Vec<asm::Instruction>, AsmgenError> {
        let mut instructions = Vec::<asm::Instruction>::new();

        let instr = named_instr.deref().clone();
        let instr_rid = ir::RegisterId::temp(bid, iid);
        match &instr {
            ir::Instruction::Load { ptr } => match ptr {
                ir::Operand::Register { rid, dtype } => {
                    // match rid {
                    //     ir::RegisterId::Arg {}
                    // }
                }
                ir::Operand::Constant(constant) => match constant {
                    ir::Constant::GlobalVariable { name, dtype } => {
                        instructions.push(asm::Instruction::UType {
                            instr: asm::UType::Lui,
                            rd: asm::Register::A0,
                            imm: asm::Immediate::relocation(
                                asm::RelocationFunction::HI20,
                                asm::Label(name.clone()),
                            ),
                        });
                        instructions.push(asm::Instruction::IType {
                            instr: asm::IType::load(dtype.clone()),
                            rd: asm::Register::A0,
                            rs1: asm::Register::A0,
                            imm: asm::Immediate::relocation(
                                asm::RelocationFunction::HI20,
                                asm::Label(name.clone()),
                            ),
                        });
                    }
                    _ => panic!("load from a constant"),
                },
            },

            ir::Instruction::BinOp {
                op,
                lhs,
                rhs,
                dtype,
            } => {
                //
                let (instrs, reg) = self.translate_instruction_binary_op(
                    op,
                    lhs,
                    rhs,
                    iid,
                    bid,
                    block,
                    function_name,
                    functions,
                    variables,
                    stack,
                )?;
                instructions.extend(instrs);
                instructions.push(asm::Instruction::SType {
                    instr: asm::SType::store(dtype.clone()),
                    rs1: asm::Register::S0,
                    rs2: reg,
                    imm: asm::Immediate::Value(Helper::u64_negative(
                        stack.allocations.get(&instr_rid).unwrap().0 as u64,
                    )),
                });
            }

            ir::Instruction::UnaryOp { op, operand, dtype } => {
                //
                let (instrs, reg) = self.translate_instruction_unary_op(
                    op,
                    operand,
                    iid,
                    bid,
                    block,
                    function_name,
                    functions,
                    variables,
                    stack,
                )?;
                instructions.extend(instrs);
                instructions.push(asm::Instruction::SType {
                    instr: asm::SType::store(dtype.clone()),
                    rs1: asm::Register::S0,
                    rs2: reg,
                    imm: asm::Immediate::Value(Helper::u64_negative(
                        stack.allocations.get(&instr_rid).unwrap().0 as u64,
                    )),
                });
            }

            ir::Instruction::TypeCast {
                value,
                target_dtype,
            } => {
                //
                let (instrs, reg) = self.translate_instruction_typecast(
                    value,
                    target_dtype,
                    iid,
                    bid,
                    block,
                    function_name,
                    functions,
                    variables,
                    stack,
                )?;
                instructions.extend(instrs);
                instructions.push(asm::Instruction::SType {
                    instr: asm::SType::store(target_dtype.clone()),
                    rs1: asm::Register::S0,
                    rs2: reg,
                    imm: asm::Immediate::Value(Helper::u64_negative(
                        stack.allocations.get(&instr_rid).unwrap().0 as u64,
                    )),
                });
            }

            _ => todo!("translate instruction"),
        }

        let dtype = instr.dtype();
        match &dtype {
            &ir::Dtype::Unit { .. } => {}
            _ => {
                instructions.push(asm::Instruction::SType {
                    instr: asm::SType::store(instr.dtype()),
                    rs1: asm::Register::S0,
                    rs2: asm::Register::A0,
                    imm: asm::Immediate::Value(Helper::u64_negative(
                        stack.allocations.get(&instr_rid).unwrap().0 as u64,
                    )),
                });
            }
        }

        Ok(instructions)
    }

    fn translate_instruction_unary_op(
        &mut self,
        op: &ast::UnaryOperator,
        operand: &ir::Operand,
        iid: usize,
        bid: ir::BlockId,
        block: &ir::Block,
        function_name: &String,
        functions: &mut Vec<asm::Section<asm::Function>>,
        variables: &mut Vec<asm::Section<asm::Variable>>,
        stack: &mut Stack,
    ) -> Result<(Vec<asm::Instruction>, asm::Register), AsmgenError> {
        // move the value of operand into a register
        let (operand_instructions, operand_registers) =
            Self::translate_operands_to_register(vec![operand], stack)?;
        let register = operand_registers[0];

        let mut arithmetic_instructions: Vec<asm::Instruction> = Vec::new();

        match operand.dtype() {
            ir::Dtype::Int { .. } => match op {
                ast::UnaryOperator::Plus => {}
                ast::UnaryOperator::Minus => {}
                ast::UnaryOperator::Negate => {}
                _ => return Err(AsmgenError::new("invalid ir")),
            },
            ir::Dtype::Float { .. } => match op {
                ast::UnaryOperator::Plus => {}
                ast::UnaryOperator::Minus => {}
                _ => return Err(AsmgenError::new("invalid ir")),
            },
            _ => return Err(AsmgenError::new("invalid operand dtype")),
        }

        let instructions = vec![operand_instructions, arithmetic_instructions].concat();

        Ok((instructions, register))
    }

    fn translate_instruction_binary_op(
        &mut self,
        op: &ast::BinaryOperator,
        lhs: &ir::Operand,
        rhs: &ir::Operand,
        iid: usize,
        bid: ir::BlockId,
        block: &ir::Block,
        function_name: &String,
        functions: &mut Vec<asm::Section<asm::Function>>,
        variables: &mut Vec<asm::Section<asm::Variable>>,
        stack: &mut Stack,
    ) -> Result<(Vec<asm::Instruction>, asm::Register), AsmgenError> {
        // move the value of operand into a register
        let (operand_instructions, operand_registers) =
            Self::translate_operands_to_register(vec![lhs, rhs], stack)?;
        let register = operand_registers[0];
        let rhs_register = operand_registers[1];

        let mut arithmetic_instructions: Vec<asm::Instruction> = Vec::new();

        match lhs.dtype() {
            ir::Dtype::Float { .. } => {
                arithmetic_instructions.push(asm::Instruction::RType {
                    instr: asm::RType::fadd(lhs.dtype()),
                    rd: register,
                    rs1: register,
                    rs2: Some(rhs_register),
                });
            }
            _ => todo!("binary op"),
        }

        let instructions = vec![operand_instructions, arithmetic_instructions].concat();

        Ok((instructions, register))
    }

    fn translate_instruction_typecast(
        &mut self,
        operand: &ir::Operand,
        target_dtype: &ir::Dtype,
        iid: usize,
        bid: ir::BlockId,
        block: &ir::Block,
        function_name: &String,
        functions: &mut Vec<asm::Section<asm::Function>>,
        variables: &mut Vec<asm::Section<asm::Variable>>,
        stack: &mut Stack,
    ) -> Result<(Vec<asm::Instruction>, asm::Register), AsmgenError> {
        // move the value of operand into a register
        let (operand_instructions, operand_registers) =
            Self::translate_operands_to_register(vec![operand], stack)?;
        let register = operand_registers[0];

        let mut typecast_instructions: Vec<asm::Instruction> = Vec::new();

        match (operand.dtype(), target_dtype) {
            (ir::Dtype::Int { .. }, ir::Dtype::Float { .. }) => {
                typecast_instructions.push(asm::Instruction::RType {
                    instr: asm::RType::fcvt_int_to_float(operand.dtype(), target_dtype.clone()),
                    rd: Helper::an_to_fan(&register),
                    rs1: register,
                    rs2: None,
                });
            }
            (ir::Dtype::Float { .. }, ir::Dtype::Int { .. }) => {
                typecast_instructions.push(asm::Instruction::RType {
                    instr: asm::RType::fcvt_float_to_int(operand.dtype(), target_dtype.clone()),
                    rd: Helper::fan_to_an(&register),
                    rs1: register,
                    rs2: None,
                });
            }
            _ => todo!("typecast"),
        }

        let instructions = vec![operand_instructions, typecast_instructions].concat();

        Ok((instructions, register))
    }
}

impl Asmgen {
    fn translate_operands_to_register(
        operands: Vec<&ir::Operand>,
        stack: &mut Stack,
    ) -> Result<(Vec<asm::Instruction>, Vec<asm::Register>), AsmgenError> {
        if operands.is_empty() {
            return Ok((vec![], vec![]));
        }
        if operands.len() >= 3 {
            return Err(AsmgenError::new("# of operands should be <= 3"));
        }

        // TODO: allocate registers efficiently
        // workaround: manual allocation of registers
        let registers: Vec<_> = operands
            .iter()
            .enumerate()
            .map(|(i, operand)| match operand.dtype() {
                ir::Dtype::Float { .. } => asm::Register::arg(asm::RegisterType::FloatingPoint, i),
                _ => asm::Register::arg(asm::RegisterType::Integer, i),
            })
            .collect();

        let instructions = operands
            .iter()
            .enumerate()
            .map(|(i, operand)| Self::translate_operand_to_register(operand, registers[i], stack))
            .collect::<Result<Vec<_>, _>>()?
            .concat();

        Ok((instructions, registers))
    }

    fn translate_operand_to_register(
        operand: &ir::Operand,
        rd: asm::Register,
        stack: &mut Stack,
    ) -> Result<Vec<asm::Instruction>, AsmgenError> {
        let mut instructions: Vec<asm::Instruction> = Vec::new();

        // TODO: if not necessary, do not insert instructions
        // TODO: if necessary, store the data in the memory

        match operand {
            ir::Operand::Constant(constant) => match constant {
                ir::Constant::Int { value, .. } => {
                    instructions.push(asm::Instruction::Pseudo(asm::Pseudo::Li {
                        rd,
                        imm: *value as u64,
                    }));
                }
                ir::Constant::Float { value, .. } => {
                    instructions.push(asm::Instruction::Pseudo(asm::Pseudo::Li {
                        rd,
                        imm: u64::from_be_bytes(value.to_be_bytes()),
                    }));
                }
                _ => {
                    println!("{:?}", constant);
                    todo!("")
                }
            },
            ir::Operand::Register { rid, dtype } => {
                instructions.push(asm::Instruction::IType {
                    instr: asm::IType::load(dtype.clone()),
                    rd,
                    rs1: asm::Register::S0,
                    imm: asm::Immediate::Value(Helper::u64_negative(
                        stack.allocations.get(&rid).unwrap().0 as u64,
                    )),
                });
            }
        }

        Ok(instructions)
    }
}
