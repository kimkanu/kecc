use core::fmt;
use core::mem;
use std::collections::{BTreeMap, HashMap};
use std::convert::TryFrom;
use std::ops::Deref;
use std::result::Result;

use failure::Fail;
use lang_c::ast::*;
use lang_c::span::Node;

use crate::ir::{Dtype, DtypeError, HasDtype, Named};
use crate::write_base::WriteString;
use crate::*;

use itertools::izip;

/**
 * Datatypes for debug use
 */

#[derive(Debug, PartialEq)]
pub struct IrgenError {
    /// source code
    pub code: String,
    /// error message
    pub message: IrgenErrorMessage,
}

impl IrgenError {
    pub fn new(code: String, message: IrgenErrorMessage) -> Self {
        Self { code, message }
    }
}

#[derive(Debug, PartialEq, Fail)]
pub enum IrgenErrorMessage {
    #[fail(display = "{}", message)]
    Misc { message: String },

    #[fail(display = "unreachable")]
    Unreachable,

    #[fail(
        display = "called object `{:?}` is not a function or a function pointer",
        callee
    )]
    NeedFunctionOrFunctionPointer { callee: ir::Operand },

    #[fail(display = "redefinition of `{}`", name)]
    Redefinition { name: String },

    #[fail(display = "initialization of `{}`", name)]
    FunctionInitialization { name: String },

    #[fail(
        display = "`{}` conflicts prototype's dtype, `{}`",
        dtype, prototype_dtype
    )]
    ConflictingDtype {
        dtype: Dtype,
        prototype_dtype: Dtype,
    },

    #[fail(display = "Invalid dtype: `{}`", dtype_error)]
    InvalidDtype { dtype_error: DtypeError },

    #[fail(display = "l-value required as {}", message)]
    RequireLvalue { message: String },
}

impl IrgenErrorMessage {
    pub fn conflicting_dtype(dtype: Dtype, prototype_dtype: Dtype) -> Self {
        Self::ConflictingDtype {
            dtype,
            prototype_dtype,
        }
    }

    pub fn invalid_dtype(dtype_error: DtypeError) -> Self {
        Self::InvalidDtype { dtype_error }
    }

    pub fn redefinition(name: String) -> Self {
        Self::Redefinition { name }
    }

    pub fn function_initialization(name: String) -> Self {
        Self::FunctionInitialization { name }
    }

    pub fn misc<T>(message: T) -> Self
    where
        T: AsRef<str>,
    {
        Self::Misc {
            message: message.as_ref().to_owned(),
        }
    }
}

impl fmt::Display for IrgenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Error code: {}, message: {}", self.code, self.message)
    }
}

/**
 * Datatypes
 */

/// a pair of `BlockId` and the instructions
pub struct Context {
    bid: ir::BlockId,
    instructions: Vec<Named<ir::Instruction>>,
}

impl Context {
    pub fn new(bid: ir::BlockId) -> Self {
        Self {
            bid,
            instructions: Vec::new(),
        }
    }

    pub fn insert_instruction(
        &mut self,
        new_instruction: ir::Instruction,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        self.instructions
            .push(Named::new(None, new_instruction.clone()));

        match new_instruction {
            ir::Instruction::Load { ptr } => {
                let dtype = if let Dtype::Pointer { inner, .. } = ptr.dtype() {
                    inner.deref().clone()
                } else {
                    return Err(IrgenErrorMessage::invalid_dtype(DtypeError::Misc {
                        message: "need pointer type".to_string(),
                    }));
                };
                Ok(ir::Operand::register(
                    ir::RegisterId::temp(self.bid, self.instructions.len() - 1),
                    dtype,
                ))
            }
            ir::Instruction::Store { ptr, .. } => Ok(ptr),
            ir::Instruction::Nop => Ok(ir::Operand::register(
                ir::RegisterId::temp(self.bid, self.instructions.len() - 1),
                Dtype::unit(),
            )),
            ir::Instruction::UnaryOp { dtype, .. } => Ok(ir::Operand::register(
                ir::RegisterId::temp(self.bid, self.instructions.len() - 1),
                dtype,
            )),
            ir::Instruction::BinOp { dtype, .. } => Ok(ir::Operand::register(
                ir::RegisterId::temp(self.bid, self.instructions.len() - 1),
                dtype,
            )),
            ir::Instruction::Call { return_type, .. } => Ok(ir::Operand::register(
                ir::RegisterId::temp(self.bid, self.instructions.len() - 1),
                return_type,
            )),
            ir::Instruction::TypeCast { target_dtype, .. } => {
                // todo: check for the compatibility
                Ok(ir::Operand::register(
                    ir::RegisterId::temp(self.bid, self.instructions.len() - 1),
                    target_dtype,
                ))
            }
            ir::Instruction::GetElementPtr { dtype, .. } => Ok(ir::Operand::register(
                ir::RegisterId::temp(self.bid, self.instructions.len() - 1),
                dtype.deref().clone(),
            )),
        }
    }
}

#[derive(Default)]
pub struct Irgen {
    /// global variable decls and function definitions
    decls: BTreeMap<String, ir::Declaration>,
    /// struct name --> `Option<Dtype::Struct>`
    structs: HashMap<String, Option<Dtype>>,
    /// typedef name --> `Dtype`
    typedefs: HashMap<String, Dtype>,
}

/// translate function
impl Translate<TranslationUnit> for Irgen {
    type Target = ir::TranslationUnit;
    type Error = IrgenError;

    fn translate(&mut self, _unit: &TranslationUnit) -> Result<Self::Target, Self::Error> {
        for ext_decl in &_unit.0 {
            match ext_decl.node {
                ExternalDeclaration::Declaration(ref var) => {
                    self.add_declaration(&var.node)?;
                }
                ExternalDeclaration::StaticAssert(_) => {
                    panic!("ExternalDeclaration::StaticAssert");
                }
                ExternalDeclaration::FunctionDefinition(ref func) => {
                    self.add_function_definition(&func.node)?;
                }
            }
        }

        let decls = mem::replace(&mut self.decls, BTreeMap::new());
        let structs = mem::replace(&mut self.structs, HashMap::new());

        Ok(Self::Target { decls, structs })
    }
}

impl Irgen {
    fn add_declaration(&mut self, source: &Declaration) -> Result<(), IrgenError> {
        let code = source.write_string();

        // get the base dtype from its specifiers and if it is a typedef
        let specifiers = &source.specifiers;
        let (base_dtype, is_typedef) = Dtype::try_from_ast_declaration_specifiers(specifiers)
            .map_err(|e| IrgenError::new(code.clone(), IrgenErrorMessage::invalid_dtype(e)))?;

        let mut tempid: usize = 0;

        // loop over declarators
        let declarators = &source.declarators;
        for init_decl in declarators {
            let declarator = &init_decl.node.declarator.node;
            let initializer = (&init_decl.node.initializer).as_ref();

            // `dtype = base_dtype + declarator + resolving structs and typedefs`
            let dtype = base_dtype
                .clone()
                .with_ast_declarator(declarator)
                .and_then(|dtype| {
                    dtype
                        .deref()
                        .clone()
                        .resolve_typedefs(&self.typedefs, &self.structs)
                })
                .and_then(|dtype| dtype.resolve_structs(&mut self.structs, &mut tempid))
                .map_err(|e| IrgenError::new(code.clone(), IrgenErrorMessage::invalid_dtype(e)))?;

            let declarator_name = Helper::declarator_name(declarator);

            // for a typedef, check if it is redefined,
            // and if so, check if it is the same with the original dtype
            if is_typedef {
                let prev_dtype = self
                    .typedefs
                    .entry(declarator_name.clone())
                    .or_insert(dtype.clone());

                if prev_dtype != &dtype {
                    let e = IrgenError::new(
                        code.clone(),
                        IrgenErrorMessage::conflicting_dtype(dtype, prev_dtype.clone()),
                    );
                    return Err(e);
                }

                continue;
            }

            // make an ir::Declaration for a variable declaration
            let mut decl = ir::Declaration::try_from(dtype.clone())
                .map_err(|e| IrgenError::new(code.clone(), IrgenErrorMessage::invalid_dtype(e)))?;

            if let Some(initializer) = initializer {
                let value = initializer.node.clone();
                match &mut decl {
                    ir::Declaration::Variable { initializer, .. } => {
                        if initializer.is_some() {
                            return Err(IrgenError::new(
                                code.clone(),
                                IrgenErrorMessage::redefinition(declarator_name),
                            ));
                        }
                        *initializer = Some(value);
                    }
                    ir::Declaration::Function { .. } => {
                        return Err(IrgenError::new(
                            code.clone(),
                            IrgenErrorMessage::function_initialization(declarator_name),
                        ));
                    }
                }
            }

            self.add_decl(&declarator_name, decl)?;
        }

        Ok(())
    }

    fn add_function_definition(&mut self, source: &FunctionDefinition) -> Result<(), IrgenError> {
        let specifiers = &source.specifiers;
        let declarator = &source.declarator.node;
        let name = Helper::declarator_name(declarator);
        let params_name = Helper::declarator_params_name(declarator);

        let code = format!(
            "specifiers: {:?},\ndeclarator: {:?}",
            specifiers.write_string(),
            declarator.write_string()
        );

        let (base_dtype, is_typedef) = Dtype::try_from_ast_declaration_specifiers(specifiers)
            .map_err(|e| IrgenError::new(code.clone(), IrgenErrorMessage::invalid_dtype(e)))?;

        if is_typedef {
            return Err(IrgenError {
                code: code.clone(),
                message: IrgenErrorMessage::misc("typedef to a function defition"),
            });
        }

        let mut tempid = 0;

        let dtype = base_dtype
            .with_ast_declarator(declarator)
            .and_then(|dtype| {
                dtype
                    .deref()
                    .clone()
                    .resolve_typedefs(&self.typedefs, &self.structs)
            })
            .and_then(|dtype| dtype.resolve_structs(&mut self.structs, &mut tempid))
            .map_err(|e| IrgenError::new(code.clone(), IrgenErrorMessage::invalid_dtype(e)))?;
        let signature = ir::FunctionSignature::new(dtype.clone());

        let decl = ir::Declaration::try_from(dtype)
            .map_err(|e| IrgenError::new(code.clone(), IrgenErrorMessage::invalid_dtype(e)))?;
        self.add_decl(&name, decl)?;

        let global_scope: HashMap<_, _> = self
            .decls
            .iter()
            .map(|(name, decl)| {
                let dtype = decl.dtype();
                let pointer = ir::Constant::global_variable(name.clone(), dtype);
                let operand = ir::Operand::constant(pointer);
                (name.clone(), operand)
            })
            .collect();

        let mut irgen = IrgenFunc {
            return_type: signature.ret.clone(),
            allocations: Vec::new(),
            blocks: BTreeMap::new(),
            bid_counter: 0,
            tempid_counter: 0,
            typedefs: self.typedefs.clone(),
            structs: self.structs.clone(),
            symbol_table: vec![global_scope],
        };
        let bid_init = irgen.alloc_bid();
        let mut context = Context::new(bid_init);

        // for a function definition, we have to enter a new scope
        irgen.enter_scope();

        // int foo(int x) { .. } -> int @foo(%x: int) { alloca xa: int; store %x xa; .. }
        irgen
            .translate_parameter_decl(&signature, bid_init, &params_name, &mut context)
            .map_err(|message| IrgenError::new(code.clone(), message))?;

        irgen.translate_statement(&source.statement.node, &mut context, None, None)?;

        // end block
        let ret = signature.ret.set_const(false);
        let value = if ret == Dtype::unit() {
            ir::Operand::constant(ir::Constant::unit())
        } else if ret == Dtype::INT {
            // int main() returns 0 even if the return value is undefined
            if name == "main" {
                ir::Operand::constant(ir::Constant::int(0, ret))
            } else {
                ir::Operand::constant(ir::Constant::undef(ret))
            }
        } else {
            ir::Operand::constant(ir::Constant::undef(ret))
        };

        irgen.commit_block(context, ir::BlockExit::Return { value });
        irgen.exit_scope();

        let func_def = ir::FunctionDefinition {
            allocations: irgen.allocations,
            blocks: irgen.blocks,
            bid_init,
        };

        let decl = if let Some(decl) = self.decls.get_mut(&name) {
            decl
        } else {
            return Err(IrgenError::new(code.clone(), IrgenErrorMessage::misc("hi")));
        };

        if let ir::Declaration::Function { definition, .. } = decl {
            if definition.is_some() {
                return Err(IrgenError::new(
                    code.clone(),
                    IrgenErrorMessage::misc(format!("`{}` is defined multiple times", name)),
                ));
            }

            *definition = Some(func_def);
        } else {
            return Err(IrgenError::new(
                code.clone(),
                IrgenErrorMessage::misc(format!("`{}` should be a FunctionDefinition", name)),
            ));
        }

        Ok(())
    }

    fn add_decl(&mut self, name: &str, decl: ir::Declaration) -> Result<(), IrgenError> {
        let old_decl = some_or!(
            self.decls.insert(name.to_string(), decl.clone()),
            return Ok(())
        );

        if !old_decl.is_compatible(&decl) {
            return Err(IrgenError {
                code: name.to_string(),
                message: IrgenErrorMessage::ConflictingDtype {
                    dtype: old_decl.dtype(),
                    prototype_dtype: decl.dtype(),
                },
            });
        }

        Ok(())
    }
}

pub struct Helper {}

/// declarator names
impl Helper {
    fn declarator_name(decl: &Declarator) -> String {
        match &decl.kind.node {
            DeclaratorKind::Abstract => "".to_string(),
            DeclaratorKind::Identifier(identifier) => identifier.node.name.clone(),
            DeclaratorKind::Declarator(declarator) => {
                Self::declarator_name(&declarator.deref().node)
            }
        }
    }
    fn declarator_params_name(decl: &Declarator) -> Vec<String> {
        decl.derived
            .iter()
            .find_map(|decl| match &decl.node {
                DerivedDeclarator::Function(function) => {
                    let params = &function.node.parameters;
                    let parameter_decl_to_name = |param: &Node<ParameterDeclaration>| {
                        param
                            .node
                            .declarator
                            .as_ref()
                            .map_or("".to_string(), |decl| Self::declarator_name(&decl.node))
                    };
                    Some(
                        params
                            .iter()
                            .map(parameter_decl_to_name)
                            .filter(|x| !x.is_empty())
                            .collect::<Vec<_>>(),
                    )
                }
                DerivedDeclarator::KRFunction(identifiers) => {
                    assert!(identifiers.is_empty());
                    Some(Vec::new())
                }
                _ => None,
            })
            .expect("no derived is a DerivedDeclarator::Function")
    }
}

/// Type Casting
impl Helper {
    fn merge_dtype(lhs: Dtype, rhs: Dtype) -> Result<Dtype, IrgenErrorMessage> {
        if &lhs == &rhs {
            return Ok(lhs);
        }

        if !Self::is_number_dtype(&lhs) || !Self::is_number_dtype(&rhs) {
            return Err(IrgenErrorMessage::conflicting_dtype(lhs, rhs));
        }

        // If one of the operands is double, the other becomes double.
        if &lhs == &Dtype::DOUBLE || &rhs == &Dtype::DOUBLE {
            return Ok(Dtype::DOUBLE);
        }

        // If one of the operands is float, the other becomes float.
        if &lhs == &Dtype::FLOAT || &rhs == &Dtype::FLOAT {
            return Ok(Dtype::FLOAT);
        }

        let lhs = Self::integer_promotion(lhs);
        let rhs = Self::integer_promotion(rhs);

        // If both have the same type, no more conversion is needed.
        if &lhs == &rhs {
            return Ok(lhs);
        }

        match (&lhs, &rhs) {
            (
                &Dtype::Int {
                    width: lhs_width,
                    is_signed: lhs_is_signed,
                    ..
                },
                &Dtype::Int {
                    width: rhs_width,
                    is_signed: rhs_is_signed,
                    ..
                },
            ) => {
                // If both have the same is_signed, the operand with shorter width is converted to the longer width.
                if lhs_is_signed == rhs_is_signed {
                    return Ok(Dtype::Int {
                        width: if lhs_width > rhs_width {
                            lhs_width
                        } else {
                            rhs_width
                        },
                        is_signed: lhs_is_signed,
                        is_const: false,
                    });
                }

                // If the width of the unsigned operand is longer than or equal to the width of the signed operand, then the signed operand is converted to the type of the unsigned operand.
                if lhs_is_signed == false && lhs_width >= rhs_width {
                    return Ok(lhs);
                }
                if rhs_is_signed == false && lhs_width <= rhs_width {
                    return Ok(rhs);
                }

                // If the width of the signed operand is longer than the width of the unsigned operand, then the unsigned operand is converted to the type of the signed operand.
                if lhs_is_signed == true {
                    return Ok(lhs);
                }
                if rhs_is_signed == true {
                    return Ok(rhs);
                }

                Err(IrgenErrorMessage::conflicting_dtype(lhs, rhs))
            }
            _ => Err(IrgenErrorMessage::conflicting_dtype(lhs, rhs)),
        }
    }

    fn integer_promotion(dtype: Dtype) -> Dtype {
        if let Dtype::Int {
            width, is_signed, ..
        } = dtype
        {
            if width < Dtype::SIZE_OF_INT * Dtype::BITS_OF_BYTE {
                Dtype::INT
            } else {
                Dtype::Int {
                    width,
                    is_signed,
                    is_const: false,
                }
            }
        } else {
            dtype
        }
    }

    fn is_number_dtype(dtype: &Dtype) -> bool {
        match dtype {
            &Dtype::Int { .. } => true,
            &Dtype::Float { .. } => true,
            _ => false,
        }
    }
}

/// An irgen for a function
pub struct IrgenFunc {
    return_type: Dtype,
    allocations: Vec<Named<Dtype>>,
    blocks: BTreeMap<ir::BlockId, ir::Block>,
    bid_counter: usize,
    /// the counter for temporary registers
    tempid_counter: usize,
    typedefs: HashMap<String, Dtype>,
    structs: HashMap<String, Option<Dtype>>,
    symbol_table: Vec<HashMap<String, ir::Operand>>,
}

/// Scope Entering/Exiting
impl IrgenFunc {
    fn enter_scope(&mut self) {
        self.symbol_table.push(HashMap::new());
    }

    fn exit_scope(&mut self) {
        self.symbol_table.pop().unwrap();
    }
}

/// Local Variable Allocation/Insertion/Search
impl IrgenFunc {
    fn insert_alloc(&mut self, alloc: ir::Named<Dtype>) -> usize {
        self.allocations.push(alloc);
        self.allocations.len() - 1 // index of the last element
    }

    fn insert_symbol_table_entry(
        &mut self,
        var: String,
        ptr: ir::Operand,
    ) -> Result<(), IrgenErrorMessage> {
        if let Some(top_layer) = self.symbol_table.last_mut() {
            top_layer.entry(var).or_insert_with(|| ptr.clone());
            Ok(())
        } else {
            return Err(IrgenErrorMessage::Misc {
                message: "empty symbol table".to_string(),
            });
        }
    }

    fn translate_alloc(
        &mut self,
        var: String,
        dtype: Dtype,
        value: Option<ir::Operand>,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        // insert a new local allocation
        // int x ---> %x: *int
        // id is the index of the allocation
        // self.allocations[id] == Named(x, int)
        let id = self.insert_alloc(ir::Named::new(Some(var.clone()), dtype.clone()));

        // create the pointer (%x: *int) pointing the allocation
        // x + 37 ---> %t1 = load %x; %t2 = add %t1 37; ..
        let pointer_type = Dtype::pointer(dtype.clone());
        let rid = ir::RegisterId::local(id);
        let ptr = ir::Operand::register(rid, pointer_type);
        self.insert_symbol_table_entry(var, ptr.clone())?;

        // deal the initializer
        if let Some(value) = value {
            let value = self.translate_typecast(value, dtype, context)?;

            return context.insert_instruction(ir::Instruction::Store { ptr, value });
        }
        Ok(ptr)
    }

    fn lookup_symbol_table(&mut self, name: &String) -> Result<ir::Operand, IrgenErrorMessage> {
        for layer in self.symbol_table.iter().rev() {
            if let Some(ptr) = layer.get(name) {
                return Ok(ptr.clone());
            }
        }

        Err(IrgenErrorMessage::Misc {
            message: format!("missing variable: {}", name),
        })
    }
}

/// Block Allocation/Insertion
impl IrgenFunc {
    fn alloc_bid(&mut self) -> ir::BlockId {
        let bid = self.bid_counter;
        self.bid_counter += 1;
        ir::BlockId(bid)
    }

    fn commit_block(&mut self, context: Context, exit: ir::BlockExit) {
        let block = ir::Block {
            phinodes: Vec::new(),
            instructions: context.instructions,
            exit,
        };
        if self.blocks.insert(context.bid, block).is_some() {
            panic!("the bid `{}` is defined multiple time", context.bid);
        }
    }
}

/// Register Allocation
impl IrgenFunc {
    fn alloc_tempid(&mut self) -> String {
        self.tempid_counter += 1;
        format!("t{}", self.tempid_counter - 1)
    }
}

/// Expression Translation: Value
impl IrgenFunc {
    fn translate_expr_rvalue(
        &mut self,
        expr: &Expression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match expr {
            Expression::Identifier(identifier) => {
                let ptr = self.lookup_symbol_table(&identifier.node.name)?;

                let ptr_dtype = ptr.dtype();
                let ptr_inner_dtype = ptr_dtype.get_pointer_inner().ok_or_else(|| {
                    panic!("`Operand` from the `symbol_table` should be a pointer type")
                })?;

                // if the pointer points a function or an array, return the pointer itself
                if ptr_inner_dtype.get_function_inner().is_some() {
                    return Ok(ptr);
                }

                // if an array is used as an rvalue, it should be transformed into a pointer
                if let Some(array_inner) = ptr_inner_dtype.get_array_inner() {
                    return self.convert_array_to_pointer(ptr, array_inner.clone(), context);
                }

                // otherwise, we should load the value from the pointer pointing the variable
                context.insert_instruction(ir::Instruction::Load { ptr })
            }

            Expression::Constant(constant) => {
                let constant = ir::Constant::try_from(&constant.node)
                    .expect("`constant` should be interpreted to an `ir::Constant` value");

                Ok(ir::Operand::constant(constant))
            }

            Expression::StringLiteral(_) => panic!("Expression::StringLiteral"),

            Expression::GenericSelection(_) => panic!("Expression::GenericSelection"),

            Expression::Member(member) => {
                match member.node.operator.node {
                    MemberOperator::Direct => {
                        //
                        let expression = &member.node.expression.node;
                        let field_name = &member.node.identifier.node.name;
                        let val_expr = self.translate_expr_lvalue(expression, context)?;

                        let ptr_dtype = val_expr.dtype();
                        let struct_dtype = ptr_dtype
                            .get_pointer_inner()
                            .expect("should be a pointer to struct");

                        let struct_name = struct_dtype
                            .get_struct_name()
                            .expect("should be a pointer to struct")
                            .as_ref()
                            .expect("name should exist");

                        let (struct_field, offset) =
                            self.find_struct_field(struct_name, field_name, 0)?;
                        let ptr = context.insert_instruction(ir::Instruction::GetElementPtr {
                            ptr: val_expr,
                            offset: ir::Operand::constant(ir::Constant::int(
                                offset as u128,
                                ir::Dtype::LONG,
                            )),
                            dtype: Box::new(Dtype::pointer(struct_field.clone())),
                        })?;

                        match struct_field {
                            Dtype::Array { inner, .. } => {
                                context.insert_instruction(ir::Instruction::GetElementPtr {
                                    ptr,
                                    offset: ir::Operand::constant(ir::Constant::int(
                                        0,
                                        Dtype::LONG,
                                    )),
                                    dtype: Box::new(Dtype::pointer(inner.as_ref().clone())),
                                })
                            }
                            _ => context.insert_instruction(ir::Instruction::Load { ptr }),
                        }
                    }
                    _ => todo!("pointer member op"),
                }
            }

            Expression::Call(call) => self.translate_function_call(&call.node, context),

            Expression::SizeOf(type_name) => {
                let dtype = Dtype::try_from(&type_name.node)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;
                let (size_of, _) = dtype
                    .size_align_of(&self.structs)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

                Ok(ir::Operand::constant(ir::Constant::int(
                    size_of as u128,
                    Dtype::LONG,
                )))
            }
            Expression::AlignOf(type_name) => {
                let dtype = Dtype::try_from(&type_name.node)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;
                let (_, align_of) = dtype
                    .size_align_of(&self.structs)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

                Ok(ir::Operand::constant(ir::Constant::int(
                    align_of as u128,
                    Dtype::Int {
                        width: Dtype::SIZE_OF_LONG * Dtype::BITS_OF_BYTE,
                        is_signed: false,
                        is_const: false,
                    },
                )))
            }

            Expression::UnaryOperator(unary) => self.translate_unary_op(&unary.node, context),

            Expression::Cast(cast) => {
                let cast = &cast.node;
                let target_dtype = Dtype::try_from(&cast.type_name.node)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?
                    .resolve_typedefs(&self.typedefs, &self.structs)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

                let operand = self.translate_expr_rvalue(&cast.expression.node, context)?;
                self.translate_typecast(operand, target_dtype, context)
            }

            Expression::BinaryOperator(binary) => self.translate_binary_op(&binary.node, context),

            Expression::Conditional(conditional) => {
                self.translate_conditional(&conditional.node, context)
            }

            Expression::Comma(comma) => {
                let mut val = ir::Operand::constant(ir::Constant::int(0, Dtype::INT));
                for expr in comma.as_ref().iter() {
                    val = self.translate_expr_rvalue(&expr.node, context)?;
                }
                Ok(val)
            }

            _ => todo!("Expression rvalue"),
        }
    }

    fn find_struct_field(
        &self,
        struct_name: &String,
        field_name: &String,
        offset: usize,
    ) -> Result<(Dtype, usize), IrgenErrorMessage> {
        let struct_dtype = self
            .structs
            .get(struct_name)
            .expect("struct should exist")
            .as_ref()
            .expect("struct should exist");

        let struct_fields = struct_dtype
            .get_struct_fields()
            .expect("should be a struct type")
            .as_ref()
            .expect("fields should exist")
            .clone();

        let size_align_offsets = struct_dtype
            .get_struct_size_align_offsets()
            .expect("should be a struct type")
            .as_ref()
            .expect("size_align_offsets should exist")
            .clone();

        for (i, struct_field) in struct_fields.iter().enumerate() {
            match struct_field.name() {
                Some(f) => {
                    if f == field_name {
                        return Ok((
                            struct_field.deref().clone(),
                            offset + size_align_offsets.2[i],
                        ));
                    }
                }
                None => {
                    let nested = self.find_struct_field(
                        struct_field
                            .deref()
                            .get_struct_name()
                            .expect("expect struct")
                            .as_ref()
                            .expect("should have `name`"),
                        field_name,
                        offset + size_align_offsets.2[i],
                    );
                    if let Ok(res) = nested {
                        return Ok(res);
                    }
                }
            }
        }

        Err(IrgenErrorMessage::misc(""))
    }

    fn translate_expr_lvalue(
        &mut self,
        expr: &Expression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match expr {
            Expression::Identifier(identifier) => self.lookup_symbol_table(&identifier.node.name),
            Expression::Member(member) => todo!("lvalue of Expression::Member"),
            Expression::UnaryOperator(unary) => match &unary.node.operator.node {
                UnaryOperator::Indirection => {
                    let val = self.translate_expr_rvalue(&unary.node.operand.node, context)?;
                    Ok(val)
                }
                _ => Err(IrgenErrorMessage::Misc {
                    message: "lvalue of a unary operation other than the indirection".to_string(),
                }),
            },
            Expression::BinaryOperator(binary) => match &binary.node.operator.node {
                BinaryOperator::Index => {
                    self.translate_index_op(&binary.node.lhs.node, &binary.node.rhs.node, context)
                }
                _ => Err(IrgenErrorMessage::Misc {
                    message: "lvalue of a binary operation other than the index operation"
                        .to_string(),
                }),
            },
            _ => Err(IrgenErrorMessage::Misc {
                message: format!("inappropriate operand for lvalue: {:#?}", expr),
            }),
        }
    }

    fn translate_list_rvalue(
        &mut self,
        list: &Vec<Node<InitializerListItem>>,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let a = list
            .iter()
            .map(|a: &Node<InitializerListItem>| {
                self.translate_initializer(&a.node.initializer.as_ref().node, context)
            })
            .collect::<Vec<_>>();

        println!("{:#?}", list);
        println!("mapped {:#?}", a);
        todo!("translate_list_rvalue");
    }
}

/// Expression Translation: Function Call
impl IrgenFunc {
    fn translate_function_call(
        &mut self,
        call: &CallExpression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let callee = self.translate_expr_rvalue(&call.callee.node, context)?;
        let function_pointer_type = callee.dtype();
        let function_type = function_pointer_type.get_pointer_inner().ok_or_else(|| {
            IrgenErrorMessage::NeedFunctionOrFunctionPointer {
                callee: callee.clone(),
            }
        })?;
        let (return_type, parameters) = function_type.get_function_inner().ok_or_else(|| {
            IrgenErrorMessage::NeedFunctionOrFunctionPointer {
                callee: callee.clone(),
            }
        })?;

        let args = call
            .arguments
            .iter()
            .map(|a| self.translate_expr_rvalue(&a.node, context))
            .collect::<Result<Vec<_>, _>>()?;

        if args.len() != parameters.len() {
            return Err(IrgenErrorMessage::Misc {
                message: format!(
                    "too few or too many arguments to the function `{}`",
                    callee.write_string()
                ),
            });
        }

        // type casting arguments to make it match with the target parameter types
        let args = izip!(args, parameters)
            .map(|(a, p)| {
                // // array case
                // let a = if let Dtype::Pointer { inner, .. } = a.dtype() {
                //     if let Dtype::Array { inner, .. } = inner.deref() {
                //         context.insert_instruction(ir::Instruction::GetElementPtr {
                //             ptr: a,
                //             offset: ir::Operand::constant(ir::Constant::int(0, Dtype::INT)),
                //             dtype: Box::new(Dtype::pointer(inner.deref().clone())),
                //         })?
                //     } else {
                //         a
                //     }
                // } else {
                //     a
                // };
                self.translate_typecast(a, p.clone(), context)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let return_type = return_type.clone().set_const(false);

        context.insert_instruction(ir::Instruction::Call {
            callee,
            args,
            return_type,
        })
    }
}

/// Expression Translation: Type Casting
impl IrgenFunc {
    fn translate_typecast(
        &mut self,
        value: ir::Operand,
        target_dtype: Dtype,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        if value.dtype().set_const(false) == target_dtype.clone().set_const(false) {
            return Ok(value);
        }

        match value.clone() {
            ir::Operand::Constant(constant) => {
                // todo: check for the compatibility
                context.insert_instruction(ir::Instruction::TypeCast {
                    value,
                    target_dtype,
                })
            }
            ir::Operand::Register { rid, dtype } => {
                // todo: check for the compatibility
                context.insert_instruction(ir::Instruction::TypeCast {
                    value,
                    target_dtype,
                })
            }
        }
    }

    fn translate_typecast_to_bool(
        &mut self,
        value: ir::Operand,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match value.dtype() {
            Dtype::Unit { .. } => Err(IrgenErrorMessage::invalid_dtype(DtypeError::Misc {
                message: "unit to bool".to_string(),
            })),
            Dtype::Int { width, .. } => {
                // if it is already a bool variable,
                if width == 1 {
                    return Ok(value);
                }
                match value.clone() {
                    ir::Operand::Constant(constant) => {
                        if let ir::Constant::Int { value, .. } = constant {
                            Ok(ir::Operand::constant(ir::Constant::int(
                                if value == 0 { 0 } else { 1 },
                                Dtype::BOOL,
                            )))
                        } else {
                            Err(IrgenErrorMessage::conflicting_dtype(
                                constant.dtype(),
                                value.dtype(),
                            ))
                        }
                    }
                    ir::Operand::Register { dtype, .. } => {
                        context.insert_instruction(ir::Instruction::BinOp {
                            op: BinaryOperator::NotEquals,
                            lhs: value,
                            rhs: ir::Operand::constant(ir::Constant::int(0, dtype.clone())),
                            dtype: Dtype::BOOL,
                        })
                    }
                }
            }
            Dtype::Float { .. } => todo!("float"),
            Dtype::Pointer { .. } => {
                // todo
                Ok(ir::Operand::constant(ir::Constant::int(1, ir::Dtype::BOOL)))
            }
            Dtype::Array { .. } => {
                // always true
                Ok(ir::Operand::constant(ir::Constant::int(1, ir::Dtype::BOOL)))
            }
            Dtype::Struct { .. } => Err(IrgenErrorMessage::invalid_dtype(DtypeError::Misc {
                message: "value of struct is not contextually convertible to 'bool'".to_string(),
            })),
            Dtype::Function { .. } => {
                // always true
                Ok(ir::Operand::constant(ir::Constant::int(1, ir::Dtype::BOOL)))
            }
            Dtype::Typedef { .. } => Err(IrgenErrorMessage::invalid_dtype(DtypeError::Misc {
                message: "unrealized typedef".to_string(),
            })),
        }
    }

    fn convert_array_to_pointer(
        &mut self,
        ptr: ir::Operand,
        inner_dtype: Dtype,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        // ptr.dtype == *(inner_dtype[])
        // return: %reg:*inner_dtype = getelementptr `ptr` offset 0

        context.insert_instruction(ir::Instruction::GetElementPtr {
            ptr,
            offset: ir::Operand::constant(ir::Constant::int(0, Dtype::LONG)),
            dtype: Box::new(Dtype::pointer(inner_dtype)),
        })
    }
}

/// Expression Translation: Related to Condition Expressions
impl IrgenFunc {
    fn translate_condition(
        &mut self,
        condition: &Expression,
        mut context: Context,
        bid_then: ir::BlockId,
        bid_else: ir::BlockId,
    ) -> Result<(), IrgenErrorMessage> {
        let condition = self.translate_expr_rvalue(condition, &mut context)?;

        self.translate_condition_with_operand(condition, context, bid_then, bid_else)
    }
    fn translate_condition_with_operand(
        &mut self,
        condition: ir::Operand,
        mut context: Context,
        bid_then: ir::BlockId,
        bid_else: ir::BlockId,
    ) -> Result<(), IrgenErrorMessage> {
        let condition = self.translate_typecast_to_bool(condition, &mut context)?;
        self.commit_block(
            context,
            ir::BlockExit::ConditionalJump {
                condition,
                arg_then: Box::new(ir::JumpArg::new(bid_then, Vec::new())),
                arg_else: Box::new(ir::JumpArg::new(bid_else, Vec::new())),
            },
        );

        Ok(())
    }

    fn translate_opt_condition(
        &mut self,
        condition: &Option<Box<Node<Expression>>>,
        context: Context,
        bid_then: ir::BlockId,
        bid_else: ir::BlockId,
    ) -> Result<(), IrgenErrorMessage> {
        if let Some(condition) = condition {
            self.translate_condition(&condition.node, context, bid_then, bid_else)
        } else {
            self.commit_block(
                context,
                ir::BlockExit::Jump {
                    arg: ir::JumpArg::new(bid_then, Vec::new()),
                },
            );
            Ok(())
        }
    }
    fn translate_conditional(
        &mut self,
        conditional_expr: &ConditionalExpression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let bid_then = self.alloc_bid();
        let bid_else = self.alloc_bid();
        let bid_end = self.alloc_bid();

        self.translate_condition(
            &conditional_expr.condition.node,
            mem::replace(context, Context::new(bid_end)),
            bid_then,
            bid_else,
        )?;

        let mut context_then = Context::new(bid_then);
        let val_then =
            self.translate_expr_rvalue(&conditional_expr.then_expression.node, &mut context_then)?;
        let mut context_else = Context::new(bid_else);
        let val_else =
            self.translate_expr_rvalue(&conditional_expr.else_expression.node, &mut context_else)?;

        let merged_dtype = Helper::merge_dtype(val_then.dtype(), val_else.dtype())?;
        let val_then =
            self.translate_typecast(val_then, merged_dtype.clone(), &mut context_then)?;
        let val_else =
            self.translate_typecast(val_else, merged_dtype.clone(), &mut context_else)?;

        let var = self.alloc_tempid();
        let ptr = self.translate_alloc(var, merged_dtype, None, context)?;

        let _ = context_then.insert_instruction(ir::Instruction::Store {
            ptr: ptr.clone(),
            value: val_then,
        });
        self.commit_block(
            context_then,
            ir::BlockExit::Jump {
                arg: ir::JumpArg::new(bid_end, Vec::new()),
            },
        );
        let _ = context_else.insert_instruction(ir::Instruction::Store {
            ptr: ptr.clone(),
            value: val_else,
        });
        self.commit_block(
            context_else,
            ir::BlockExit::Jump {
                arg: ir::JumpArg::new(bid_end, Vec::new()),
            },
        );

        context.insert_instruction(ir::Instruction::Load { ptr })
    }
}

/// Expression Translation: Initializer and ForInitializer
impl IrgenFunc {
    fn translate_initializer(
        &mut self,
        initializer: &Initializer,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match initializer {
            Initializer::Expression(expr) => self.translate_expr_rvalue(&expr.node, context),
            Initializer::List(list) => self.translate_list_rvalue(list, context),
        }
    }
    fn translate_for_initializer(
        &mut self,
        initializer: &ForInitializer,
        context: &mut Context,
    ) -> Result<(), IrgenErrorMessage> {
        match initializer {
            ForInitializer::Empty => (),
            ForInitializer::Expression(expr) => {
                let _ = self.translate_expr_rvalue(&expr.node, context)?;
            }
            ForInitializer::Declaration(decl) => {
                self.translate_decl(&decl.node, context)?;
            }
            ForInitializer::StaticAssert(_) => panic!("ForInitializer::StaticAssert"),
        }

        Ok(())
    }
}

/// Expression Translation: Unary, Binary, and Index Operations
impl IrgenFunc {
    fn translate_unary_op(
        &mut self,
        unary: &UnaryOperatorExpression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match unary.operator.node {
            UnaryOperator::PostIncrement => {
                let lval = self.translate_expr_lvalue(&unary.operand.node, context)?;
                let prev_rval = self.translate_expr_rvalue(&unary.operand.node, context)?;
                let dtype = prev_rval.dtype();
                let dtype = if let Dtype::Int { .. } = dtype {
                    dtype
                } else {
                    Dtype::LONG
                };
                let new_rval = self.translate_binary_op_with_operands(
                    BinaryOperator::Plus,
                    prev_rval.clone(),
                    ir::Operand::constant(ir::Constant::int(1, dtype)),
                    context,
                )?;
                self.translate_assign(lval, new_rval, context)?;
                Ok(prev_rval)
            }
            UnaryOperator::PostDecrement => {
                let lval = self.translate_expr_lvalue(&unary.operand.node, context)?;
                let prev_rval = self.translate_expr_rvalue(&unary.operand.node, context)?;
                let dtype = prev_rval.dtype();
                let dtype = if let Dtype::Int { .. } = dtype {
                    dtype
                } else {
                    Dtype::LONG
                };
                let new_rval = self.translate_binary_op_with_operands(
                    BinaryOperator::Minus,
                    prev_rval.clone(),
                    ir::Operand::constant(ir::Constant::int(1, dtype)),
                    context,
                )?;
                self.translate_assign(lval, new_rval, context)?;
                Ok(prev_rval)
            }
            UnaryOperator::PreIncrement => {
                let lval = self.translate_expr_lvalue(&unary.operand.node, context)?;
                let prev_rval = self.translate_expr_rvalue(&unary.operand.node, context)?;
                let dtype = prev_rval.dtype();
                let new_rval = self.translate_binary_op_with_operands(
                    BinaryOperator::Plus,
                    prev_rval.clone(),
                    ir::Operand::constant(ir::Constant::int(1, dtype)),
                    context,
                )?;
                self.translate_assign(lval, new_rval, context)
            }
            UnaryOperator::PreDecrement => {
                let lval = self.translate_expr_lvalue(&unary.operand.node, context)?;
                let prev_rval = self.translate_expr_rvalue(&unary.operand.node, context)?;
                let dtype = prev_rval.dtype();
                let new_rval = self.translate_binary_op_with_operands(
                    BinaryOperator::Minus,
                    prev_rval.clone(),
                    ir::Operand::constant(ir::Constant::int(1, dtype)),
                    context,
                )?;
                self.translate_assign(lval, new_rval, context)
            }
            UnaryOperator::Minus => {
                let rval = self.translate_expr_rvalue(&unary.operand.node, context)?;
                let dtype = rval.dtype();
                context.insert_instruction(ir::Instruction::UnaryOp {
                    op: unary.operator.node.clone(),
                    operand: rval,
                    dtype,
                })
            }
            UnaryOperator::Negate => {
                let rval = self.translate_expr_rvalue(&unary.operand.node, context)?;
                let rval = self.translate_typecast_to_bool(rval, context)?;
                context.insert_instruction(ir::Instruction::UnaryOp {
                    op: unary.operator.node.clone(),
                    operand: rval,
                    dtype: Dtype::BOOL,
                })
            }
            UnaryOperator::Address => self.translate_expr_lvalue(&unary.operand.node, context),
            UnaryOperator::Indirection => {
                let ptr = self.translate_expr_rvalue(&unary.operand.node, context)?;
                ptr.dtype().set_const(false);
                context.insert_instruction(ir::Instruction::Load { ptr })
            }
            _ => todo!("translate_unary_op"),
        }
    }
    fn translate_binary_op(
        &mut self,
        binary: &BinaryOperatorExpression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match binary.operator.node {
            BinaryOperator::Index => {
                let val_lhs = self.translate_expr_rvalue(&binary.lhs.node, context)?;
                let val_rhs = self.translate_expr_rvalue(&binary.rhs.node, context)?;

                let dtype = val_lhs.dtype();
                let ptr_inner = dtype.get_pointer_inner().expect("should be a ptr").clone();

                let array_item_size = self.size_of(&ptr_inner)?;
                let offset = self.translate_binary_op_with_operands(
                    BinaryOperator::Multiply,
                    val_rhs,
                    ir::Operand::constant(ir::Constant::int(array_item_size as u128, Dtype::LONG)),
                    context,
                )?;
                let ptr = context.insert_instruction(ir::Instruction::GetElementPtr {
                    ptr: val_lhs.clone(),
                    offset,
                    dtype: Box::new(val_lhs.dtype()),
                })?;

                match ptr_inner {
                    Dtype::Array { inner, .. } => {
                        context.insert_instruction(ir::Instruction::GetElementPtr {
                            ptr,
                            offset: ir::Operand::constant(ir::Constant::int(0, Dtype::LONG)),
                            dtype: Box::new(Dtype::pointer(inner.as_ref().clone())),
                        })
                    }
                    _ => context.insert_instruction(ir::Instruction::Load { ptr }),
                }
            }
            BinaryOperator::Assign => {
                let val_lhs = self.translate_expr_lvalue(&binary.lhs.node, context)?;
                let val_rhs = self.translate_expr_rvalue(&binary.rhs.node, context)?;
                self.translate_assign(val_lhs, val_rhs, context)
            }
            BinaryOperator::AssignBitwiseAnd
            | BinaryOperator::AssignBitwiseOr
            | BinaryOperator::AssignBitwiseXor
            | BinaryOperator::AssignDivide
            | BinaryOperator::AssignMinus
            | BinaryOperator::AssignModulo
            | BinaryOperator::AssignMultiply
            | BinaryOperator::AssignPlus
            | BinaryOperator::AssignShiftLeft
            | BinaryOperator::AssignShiftRight => {
                let operator = match binary.operator.node {
                    BinaryOperator::AssignBitwiseAnd => BinaryOperator::BitwiseAnd,
                    BinaryOperator::AssignBitwiseOr => BinaryOperator::BitwiseOr,
                    BinaryOperator::AssignBitwiseXor => BinaryOperator::BitwiseXor,
                    BinaryOperator::AssignDivide => BinaryOperator::Divide,
                    BinaryOperator::AssignMinus => BinaryOperator::Minus,
                    BinaryOperator::AssignModulo => BinaryOperator::Modulo,
                    BinaryOperator::AssignMultiply => BinaryOperator::Multiply,
                    BinaryOperator::AssignPlus => BinaryOperator::Plus,
                    BinaryOperator::AssignShiftLeft => BinaryOperator::ShiftLeft,
                    BinaryOperator::AssignShiftRight => BinaryOperator::ShiftRight,
                    _ => return Err(IrgenErrorMessage::Unreachable),
                };
                let val_lhs = self.translate_expr_rvalue(&binary.lhs.node, context)?;
                let val_rhs = self.translate_expr_rvalue(&binary.rhs.node, context)?;
                let result =
                    self.translate_binary_op_with_operands(operator, val_lhs, val_rhs, context)?;
                let val_lhs = self.translate_expr_lvalue(&binary.lhs.node, context)?;
                self.translate_assign(val_lhs, result, context)
            }
            BinaryOperator::LogicalAnd => {
                self.translate_logical_and(&binary.lhs.node, &binary.rhs.node, context)
            }
            BinaryOperator::LogicalOr => {
                self.translate_logical_or(&binary.lhs.node, &binary.rhs.node, context)
            }
            _ => {
                let val_lhs = self.translate_expr_rvalue(&binary.lhs.node, context)?;
                let val_rhs = self.translate_expr_rvalue(&binary.rhs.node, context)?;

                self.translate_binary_op_with_operands(
                    binary.operator.node.clone(),
                    val_lhs,
                    val_rhs,
                    context,
                )
            }
        }
    }

    fn translate_binary_op_with_operands(
        &mut self,
        op: BinaryOperator,
        val_lhs: ir::Operand,
        val_rhs: ir::Operand,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let lhs_dtype = val_lhs.dtype();
        let rhs_dtype = val_rhs.dtype();

        match (lhs_dtype.clone(), rhs_dtype.clone()) {
            (Dtype::Int { .. }, Dtype::Int { .. })
            | (Dtype::Float { .. }, Dtype::Int { .. })
            | (Dtype::Int { .. }, Dtype::Float { .. })
            | (Dtype::Float { .. }, Dtype::Float { .. }) => {
                let lhs_dtype = Helper::integer_promotion(lhs_dtype);
                let rhs_dtype = Helper::integer_promotion(rhs_dtype);

                let merged_dtype = Helper::merge_dtype(lhs_dtype, rhs_dtype)?;

                let is_bool = match op {
                    BinaryOperator::Less
                    | BinaryOperator::LessOrEqual
                    | BinaryOperator::LogicalAnd
                    | BinaryOperator::LogicalOr
                    | BinaryOperator::Greater
                    | BinaryOperator::GreaterOrEqual
                    | BinaryOperator::Equals
                    | BinaryOperator::NotEquals => true,
                    _ => false,
                };
                let val_lhs = self.translate_typecast(val_lhs, merged_dtype.clone(), context)?;
                let val_rhs = self.translate_typecast(val_rhs, merged_dtype.clone(), context)?;

                match &op {
                    &BinaryOperator::Multiply
                    | &BinaryOperator::Divide
                    | &BinaryOperator::Modulo
                    | &BinaryOperator::Plus
                    | &BinaryOperator::Minus
                    | &BinaryOperator::ShiftLeft
                    | &BinaryOperator::ShiftRight
                    | &BinaryOperator::Equals
                    | &BinaryOperator::NotEquals
                    | &BinaryOperator::Less
                    | &BinaryOperator::LessOrEqual
                    | &BinaryOperator::Greater
                    | &BinaryOperator::GreaterOrEqual
                    | &BinaryOperator::BitwiseAnd
                    | &BinaryOperator::BitwiseXor
                    | &BinaryOperator::BitwiseOr => {
                        context.insert_instruction(ir::Instruction::BinOp {
                            op,
                            lhs: val_lhs,
                            rhs: val_rhs,
                            dtype: if is_bool { Dtype::BOOL } else { merged_dtype },
                        })
                    }
                    _ => todo!(
                        "ast::BinaryOperator::WriteOp: write operation for {:?} is needed",
                        op
                    ),
                }
            }

            // pointer and an int for incrementing/decrementing
            (Dtype::Pointer { inner, .. }, Dtype::Int { .. }) => match op {
                BinaryOperator::Plus => {
                    let offset = self.translate_binary_op_with_operands(
                        BinaryOperator::Multiply,
                        val_rhs,
                        ir::Operand::constant(ir::Constant::int(
                            self.size_of(&inner)? as u128,
                            Dtype::LONG,
                        )),
                        context,
                    )?;
                    context.insert_instruction(ir::Instruction::GetElementPtr {
                        ptr: val_lhs,
                        offset,
                        dtype: Box::new(lhs_dtype),
                    })
                }
                BinaryOperator::Minus => todo!(""),
                _ => Err(IrgenErrorMessage::misc(
                    "strange pointer arithmetic with int",
                )),
            },
            (Dtype::Int { .. }, Dtype::Pointer { .. }) => {
                if op == BinaryOperator::Plus {
                    self.translate_binary_op_with_operands(op, val_rhs, val_lhs, context)
                } else {
                    Err(IrgenErrorMessage::misc(
                        "strange pointer arithmetic with int",
                    ))
                }
            }
            _ => Err(IrgenErrorMessage::misc("strange arithmetic")),
        }
    }

    fn translate_logical_and(
        &mut self,
        lhs: &Expression,
        rhs: &Expression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let bid_true = self.alloc_bid();
        let bid_false = self.alloc_bid();
        let bid_end = self.alloc_bid();

        let var = self.alloc_tempid();
        let ptr = self.translate_alloc(var, Dtype::BOOL, None, context)?;

        let lhs = self.translate_expr_rvalue(lhs, context)?;
        let lhs = self.translate_typecast_to_bool(lhs, context)?;

        self.translate_condition_with_operand(
            lhs,
            mem::replace(context, Context::new(bid_end)),
            bid_true,
            bid_false,
        )?;

        let mut context_true = Context::new(bid_true);
        let rhs = self.translate_expr_rvalue(rhs, &mut context_true)?;
        let rhs = self.translate_typecast_to_bool(rhs, &mut context_true)?;
        let _ = context_true.insert_instruction(ir::Instruction::Store {
            ptr: ptr.clone(),
            value: rhs,
        });
        self.commit_block(
            context_true,
            ir::BlockExit::Jump {
                arg: ir::JumpArg::new(bid_end, Vec::new()),
            },
        );

        let mut context_false = Context::new(bid_false);
        let _ = context_false.insert_instruction(ir::Instruction::Store {
            ptr: ptr.clone(),
            value: ir::Operand::constant(ir::Constant::int(0, Dtype::BOOL)),
        });
        self.commit_block(
            context_false,
            ir::BlockExit::Jump {
                arg: ir::JumpArg::new(bid_end, Vec::new()),
            },
        );

        context.insert_instruction(ir::Instruction::Load { ptr })
    }

    fn translate_logical_or(
        &mut self,
        lhs: &Expression,
        rhs: &Expression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let bid_true = self.alloc_bid();
        let bid_false = self.alloc_bid();
        let bid_end = self.alloc_bid();

        let var = self.alloc_tempid();
        let ptr = self.translate_alloc(var, Dtype::BOOL, None, context)?;

        let lhs = self.translate_expr_rvalue(lhs, context)?;
        let lhs = self.translate_typecast_to_bool(lhs, context)?;

        self.translate_condition_with_operand(
            lhs,
            mem::replace(context, Context::new(bid_end)),
            bid_true,
            bid_false,
        )?;

        let mut context_true = Context::new(bid_true);
        let _ = context_true.insert_instruction(ir::Instruction::Store {
            ptr: ptr.clone(),
            value: ir::Operand::constant(ir::Constant::int(1, Dtype::BOOL)),
        });
        self.commit_block(
            context_true,
            ir::BlockExit::Jump {
                arg: ir::JumpArg::new(bid_end, Vec::new()),
            },
        );

        let mut context_false = Context::new(bid_false);
        let rhs = self.translate_expr_rvalue(rhs, &mut context_false)?;
        let rhs = self.translate_typecast_to_bool(rhs, &mut context_false)?;
        let _ = context_false.insert_instruction(ir::Instruction::Store {
            ptr: ptr.clone(),
            value: rhs,
        });
        self.commit_block(
            context_false,
            ir::BlockExit::Jump {
                arg: ir::JumpArg::new(bid_end, Vec::new()),
            },
        );

        context.insert_instruction(ir::Instruction::Load { ptr })
    }

    fn translate_assign(
        &mut self,
        ptr: ir::Operand, // l-value
        value: ir::Operand,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let ptr_dtype = ptr.dtype();
        let dtype = ptr_dtype.get_pointer_inner().expect("PTR!").clone();
        let value = self.translate_typecast(value, dtype, context)?;
        let _ = context.insert_instruction(ir::Instruction::Store {
            ptr,
            value: value.clone(),
        });
        Ok(value)
    }

    fn size_of(&self, array_inner: &Dtype) -> Result<usize, IrgenErrorMessage> {
        match array_inner.clone() {
            Dtype::Int { width, .. } => Ok(width / Dtype::BITS_OF_BYTE),
            Dtype::Float { width, .. } => Ok(width / Dtype::BITS_OF_BYTE),
            Dtype::Pointer { .. } => Ok(Dtype::SIZE_OF_POINTER),
            Dtype::Array { size, inner } => Ok(size * self.size_of(&inner.as_ref().clone())?),
            Dtype::Struct { .. } => todo!("array of structs"),
            _ => Err(IrgenErrorMessage::invalid_dtype(DtypeError::Misc {
                message: "not a valid r-value".to_string(),
            })),
        }
    }

    // l-value of the index operator
    fn translate_index_op(
        &mut self,
        lhs: &Expression,
        rhs: &Expression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        // int a[5];             int b[5][5];
        // a[3];                 b[2][3];

        // r-value of a: *i32  | of b: *[5 x i32]
        let lhs = self.translate_expr_rvalue(lhs, context)?;
        let lhs_dtype = &lhs.dtype();

        //     i32       |    [5 x i32]
        let array_inner = match lhs_dtype {
            Dtype::Array { inner, .. } => inner.as_ref(),
            Dtype::Pointer { inner, .. } => inner.as_ref(),
            _ => {
                return Err(IrgenErrorMessage::invalid_dtype(DtypeError::Misc {
                    message: "lhs_dtype has an invalid dtype".to_string(),
                }))
            }
        };

        // multiply the index with `array item size` as i64
        let array_item_size = self.size_of(array_inner)?;

        let rhs = self.translate_expr_rvalue(rhs, context)?;
        let _ = rhs.dtype().get_int_width().expect("should be an integer");
        let offset = self.translate_binary_op_with_operands(
            BinaryOperator::Multiply,
            rhs,
            ir::Operand::constant(ir::Constant::int(array_item_size as u128, Dtype::LONG)),
            context,
        )?;

        context.insert_instruction(ir::Instruction::GetElementPtr {
            ptr: lhs.clone(),
            offset,
            dtype: Box::new(Dtype::pointer(array_inner.clone())),
        })
    }
}

/// Switch Statement Translation
impl IrgenFunc {
    fn translate_switch_body(
        &mut self,
        statement: &Statement,
        bid_end: ir::BlockId,
    ) -> Result<(Vec<(ir::Constant, ir::JumpArg)>, ir::BlockId), IrgenError> {
        let mut cases = Vec::new();
        let mut default = None;

        let items = if let Statement::Compound(items) = statement {
            items
        } else {
            panic!("malformed switch case: the statement should be a compound statement");
        };

        self.enter_scope();

        for item in items {
            match &item.node {
                BlockItem::Statement(statement) => self.translate_switch_body_inner(
                    &statement.node,
                    &mut cases,
                    &mut default,
                    bid_end,
                )?,
                _ => todo!("block item other than statement"),
            }
        }

        self.exit_scope();

        // if default is None, go to bid_end
        let default = default.unwrap_or(bid_end);

        Ok((cases, default))
    }

    fn translate_switch_body_inner(
        &mut self,
        statement: &Statement,
        cases: &mut Vec<(ir::Constant, ir::JumpArg)>,
        default: &mut Option<ir::BlockId>,
        bid_end: ir::BlockId,
    ) -> Result<(), IrgenError> {
        let label_statement = if let Statement::Labeled(label_statement) = statement {
            &label_statement.node
        } else {
            panic!("Statement other than Statement::Labeled inside the switch-case")
        };

        let bid_label = self.alloc_bid();
        let case =
            self.translate_switch_body_label_statement(label_statement, bid_label, bid_end)?;

        if let Some(case) = case {
            if !case.is_integer_constant() {
                return Err(IrgenError {
                    code: label_statement.label.write_string(),
                    message: IrgenErrorMessage::Misc {
                        message: "expression is not an integer constant expression".to_string(),
                    },
                });
            }

            if cases.iter().any(|(c, _)| &case == c) {
                return Err(IrgenError {
                    code: label_statement.label.write_string(),
                    message: IrgenErrorMessage::Misc {
                        message: "duplicated case value".to_string(),
                    },
                });
            }

            cases.push((case, ir::JumpArg::new(bid_label, Vec::new())));
        } else {
            // "default" is previously assigned
            if default.is_some() {
                return Err(IrgenError {
                    code: label_statement.label.write_string(),
                    message: IrgenErrorMessage::Misc {
                        message: "previously defined default".to_string(),
                    },
                });
            }

            *default = Some(bid_label);
        }

        Ok(())
    }

    fn translate_switch_body_label_statement(
        &mut self,
        label_statement: &LabeledStatement,
        bid: ir::BlockId,
        bid_end: ir::BlockId,
    ) -> Result<Option<ir::Constant>, IrgenError> {
        let case = match &label_statement.label.node {
            Label::Identifier(_) => panic!("Label::Identifier"),
            Label::Case(expr) => {
                let constant = ir::Constant::try_from(&expr.node).map_err(|_| IrgenError {
                    code: expr.write_string(),
                    message: IrgenErrorMessage::Misc {
                        message: "case label does not reduce to an integer constant".to_string(),
                    },
                })?;

                Some(constant)
            }
            Label::Default => None,
        };

        let items = if let Statement::Compound(items) = &label_statement.statement.node {
            items
        } else {
            panic!("not a Compound")
        };

        self.enter_scope();

        // last should be the `break;`
        let (last, items) = items.split_last().expect("Empty case statement");

        // interp except the last item
        let mut context = Context::new(bid);
        for item in items {
            match &item.node {
                BlockItem::Declaration(decl) => {
                    self.translate_decl(&decl.node, &mut context)
                        .map_err(|e| IrgenError {
                            code: decl.write_string(),
                            message: e,
                        })?;
                }
                BlockItem::Statement(statement) => {
                    self.translate_statement(&statement.node, &mut context, None, None)?;
                }
                BlockItem::StaticAssert(_) => panic!("StaticAssert"),
            }
        }

        let last_statement = if let BlockItem::Statement(last_statement) = &last.node {
            &last_statement.node
        } else {
            panic!("BlockItem should be Statement inside the label compound statement")
        };
        assert_eq!(
            last_statement,
            &Statement::Break,
            "last item should be the break"
        );
        // commit the block
        self.commit_block(
            context,
            ir::BlockExit::Jump {
                arg: ir::JumpArg::new(bid_end, Vec::new()),
            },
        );

        self.exit_scope();
        Ok(case)
    }
}

/// Declaration Translation
impl IrgenFunc {
    fn translate_decl(
        &mut self,
        decl: &Declaration,
        context: &mut Context,
    ) -> Result<(), IrgenErrorMessage> {
        let (base_dtype, is_typedef) = Dtype::try_from_ast_declaration_specifiers(&decl.specifiers)
            .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

        assert!(!is_typedef);

        for init_decl in &decl.declarators {
            let declarator = &init_decl.node.declarator.node;
            let dtype = base_dtype
                .clone()
                .with_ast_declarator(declarator)
                .and_then(|dtype| {
                    dtype
                        .deref()
                        .clone()
                        .resolve_typedefs(&self.typedefs, &self.structs)
                })
                .and_then(|dtype| {
                    dtype.resolve_structs(&mut self.structs, &mut self.tempid_counter)
                })
                .and_then(|dtype| dtype.resolve_typedefs(&self.typedefs, &self.structs))
                .map_err(|e| IrgenErrorMessage::invalid_dtype(e))?;

            let name = Helper::declarator_name(declarator);

            match &dtype {
                Dtype::Unit { .. } => panic!("decl by unit"),
                Dtype::Int { .. }
                | Dtype::Float { .. }
                | Dtype::Pointer { .. }
                | Dtype::Struct { .. } => {
                    let value = if let Some(initializer) = &init_decl.node.initializer {
                        Some(self.translate_initializer(&initializer.node, context)?)
                    } else {
                        None
                    };
                    let _ = self.translate_alloc(name, dtype.clone(), value, context)?;
                }
                Dtype::Array { inner, size } => {
                    let ptr = self.translate_alloc(name, dtype.clone(), None, context)?;
                    if let Some(initializer) = &init_decl.node.initializer {
                        // should be a list
                        if let Initializer::List(list) = &initializer.node {
                            let elem_ptr =
                                context.insert_instruction(ir::Instruction::GetElementPtr {
                                    ptr,
                                    offset: ir::Operand::constant(ir::Constant::int(
                                        0,
                                        Dtype::LONG,
                                    )),
                                    dtype: Box::new(Dtype::pointer(inner.as_ref().clone())),
                                })?;
                            for (i, item) in list.iter().enumerate() {
                                if i >= size.clone() {
                                    break;
                                }
                                let offset = self.translate_binary_op_with_operands(
                                    BinaryOperator::Multiply,
                                    ir::Operand::constant(ir::Constant::int(
                                        i as u128,
                                        Dtype::LONG,
                                    )),
                                    ir::Operand::constant(ir::Constant::int(
                                        self.size_of(inner.as_ref())? as u128,
                                        Dtype::LONG,
                                    )),
                                    context,
                                )?;
                                let lhs =
                                    context.insert_instruction(ir::Instruction::GetElementPtr {
                                        ptr: elem_ptr.clone(),
                                        offset,
                                        dtype: Box::new(Dtype::pointer(inner.as_ref().clone())),
                                    })?;
                                let rhs = self.translate_initializer(
                                    &item.node.initializer.as_ref().node,
                                    context,
                                )?;
                                let _ = context.insert_instruction(ir::Instruction::Store {
                                    ptr: lhs,
                                    value: rhs,
                                })?;
                            }
                        } else {
                            return Err(IrgenErrorMessage::invalid_dtype(DtypeError::Misc {
                                message: "initializer of an array is not a list".to_string(),
                            }));
                        }
                    }
                }
                _ => todo!("decl by a function, typedef"),
            }
        }

        Ok(())
    }

    fn translate_parameter_decl(
        &mut self,
        signature: &ir::FunctionSignature,
        bid_init: ir::BlockId,
        params_name: &Vec<String>,
        context: &mut Context,
    ) -> Result<(), IrgenErrorMessage> {
        if signature.params.len() != params_name.len() {
            panic!("insufficient or too many parameters");
        }
        for (i, (dtype, var)) in izip!(&signature.params, params_name).enumerate() {
            let value = Some(ir::Operand::register(
                ir::RegisterId::arg(bid_init, i),
                dtype.clone(),
            ));
            let _ = self.translate_alloc(var.clone(), dtype.clone(), value, context)?;
        }
        Ok(())
    }
}

/// Statement Translation
impl IrgenFunc {
    fn translate_statement(
        &mut self,
        statement: &Statement,
        context: &mut Context,
        bid_continue: Option<ir::BlockId>,
        bid_break: Option<ir::BlockId>,
    ) -> Result<(), IrgenError> {
        match statement {
            Statement::Compound(items) => {
                self.enter_scope();
                for item in items {
                    match &item.node {
                        BlockItem::Declaration(decl) => {
                            self.translate_decl(&decl.node, context)
                                .map_err(|e| IrgenError {
                                    code: decl.write_string(),
                                    message: IrgenErrorMessage::Misc {
                                        message: e.to_string(),
                                    },
                                })?;
                        }
                        BlockItem::Statement(statement) => {
                            self.translate_statement(
                                &statement.node,
                                context,
                                bid_continue,
                                bid_break,
                            )?;
                        }
                        _ => {
                            return Err(IrgenError::new(
                                statement.write_string(),
                                IrgenErrorMessage::misc("static_assert"),
                            ));
                        }
                    }
                }
                self.exit_scope();
                Ok(())
            }

            Statement::Expression(expr) => {
                if let Some(expr) = expr {
                    let _ = self
                        .translate_expr_rvalue(&expr.node, context)
                        .map_err(|e| IrgenError {
                            code: expr.write_string(),
                            message: e,
                        })?;
                }
                Ok(())
            }

            Statement::If(statement) => {
                let bid_then = self.alloc_bid();
                let bid_else = self.alloc_bid();
                let bid_end = self.alloc_bid();

                self.translate_condition(
                    &statement.node.condition.node,
                    mem::replace(context, Context::new(bid_end)),
                    bid_then,
                    bid_else,
                )
                .map_err(|e| IrgenError {
                    code: statement.write_string(),
                    message: IrgenErrorMessage::Misc {
                        message: e.to_string(),
                    },
                })?;

                let mut context_then = Context::new(bid_then);
                self.translate_statement(
                    &statement.node.then_statement.node,
                    &mut context_then,
                    bid_continue,
                    bid_break,
                )?;
                self.commit_block(
                    context_then,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_end, Vec::new()),
                    },
                );

                let mut context_else = Context::new(bid_else);
                if let Some(else_statement) = &statement.node.else_statement {
                    self.translate_statement(
                        &else_statement.node,
                        &mut context_else,
                        bid_continue,
                        bid_break,
                    )?;
                }
                self.commit_block(
                    context_else,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_end, Vec::new()),
                    },
                );

                Ok(())
            }

            Statement::Return(expr) => {
                let value = match expr {
                    Some(expr) => self
                        .translate_expr_rvalue(&expr.node, context)
                        .map_err(|e| IrgenError {
                            code: expr.write_string(),
                            message: IrgenErrorMessage::Misc {
                                message: e.to_string(),
                            },
                        })?,
                    None => ir::Operand::constant(ir::Constant::unit()),
                };

                let value = self
                    .translate_typecast(value, self.return_type.clone(), context)
                    .map_err(|e| IrgenError {
                        code: expr.write_string(),
                        message: e,
                    })?;

                let bid_end = self.alloc_bid();
                self.commit_block(
                    mem::replace(context, Context::new(bid_end)),
                    ir::BlockExit::Return { value },
                );

                Ok(())
            }

            Statement::For(for_statement) => {
                let for_statement = &for_statement.node;

                let bid_init = self.alloc_bid();
                self.commit_block(
                    mem::replace(context, Context::new(bid_init)),
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_init, Vec::new()),
                    },
                );

                self.enter_scope();
                self.translate_for_initializer(&for_statement.initializer.node, context)
                    .map_err(|e| IrgenError {
                        code: for_statement.initializer.write_string(),
                        message: e,
                    })?;

                let bid_cond = self.alloc_bid();
                self.commit_block(
                    mem::replace(context, Context::new(bid_cond)),
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_cond, Vec::new()),
                    },
                );

                let bid_body = self.alloc_bid();
                let bid_step = self.alloc_bid();
                let bid_end = self.alloc_bid();
                self.translate_opt_condition(
                    &for_statement.condition,
                    mem::replace(context, Context::new(bid_end)),
                    bid_body,
                    bid_end,
                )
                .map_err(|e| IrgenError {
                    code: for_statement.condition.write_string(),
                    message: e,
                })?;

                self.enter_scope();

                let mut context_body = Context::new(bid_body);
                self.translate_statement(
                    &for_statement.statement.node,
                    &mut context_body,
                    Some(bid_step), // continue -> go to increment statement
                    Some(bid_end),  // break -> go out of the loop
                )?;

                self.exit_scope();

                // end of the body -> go to the increment statement
                // commit the body block
                self.commit_block(
                    context_body,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_step, Vec::new()),
                    },
                );

                let mut context_step = Context::new(bid_step);
                if let Some(step_expr) = &for_statement.step {
                    let _ = self
                        .translate_expr_rvalue(&step_expr.node, &mut context_step)
                        .map_err(|e| IrgenError {
                            code: for_statement.step.write_string(),
                            message: e,
                        });
                }
                // commit the step block
                self.commit_block(
                    context_step,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_cond, Vec::new()),
                    },
                );

                self.exit_scope();
                Ok(())
            }

            Statement::While(while_statement) => {
                let while_statement = &while_statement.node;

                let bid_cond = self.alloc_bid();
                self.commit_block(
                    mem::replace(context, Context::new(bid_cond)),
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_cond, Vec::new()),
                    },
                );
                let bid_body = self.alloc_bid();
                let bid_end = self.alloc_bid();

                self.translate_condition(
                    &while_statement.expression.node,
                    mem::replace(context, Context::new(bid_end)),
                    bid_body,
                    bid_end,
                )
                .map_err(|e| IrgenError {
                    code: while_statement.expression.write_string(),
                    message: e,
                })?;

                self.enter_scope();
                let mut context_body = Context::new(bid_body);
                self.translate_statement(
                    &while_statement.statement.node,
                    &mut context_body,
                    Some(bid_cond),
                    Some(bid_end),
                )?;
                // end of the body -> condition block
                self.commit_block(
                    context_body,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_cond, Vec::new()),
                    },
                );

                self.exit_scope();

                Ok(())
            }

            Statement::DoWhile(do_while_statement) => {
                let do_while_statement = &do_while_statement.node;

                let bid_body = self.alloc_bid();
                self.commit_block(
                    mem::replace(context, Context::new(bid_body)),
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_body, Vec::new()),
                    },
                );

                self.enter_scope();

                let bid_cond = self.alloc_bid();
                let bid_end = self.alloc_bid();

                self.translate_statement(
                    &do_while_statement.statement.node,
                    context,
                    Some(bid_cond),
                    Some(bid_end),
                )?;
                self.exit_scope();
                // end of the body -> condition block
                self.commit_block(
                    mem::replace(context, Context::new(bid_cond)),
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_cond, Vec::new()),
                    },
                );

                self.translate_condition(
                    &do_while_statement.expression.node,
                    mem::replace(context, Context::new(bid_end)),
                    bid_body,
                    bid_end,
                )
                .map_err(|e| IrgenError {
                    code: do_while_statement.expression.write_string(),
                    message: e,
                })?;

                Ok(())
            }

            Statement::Switch(switch_statement) => {
                let value = self
                    .translate_expr_rvalue(&switch_statement.node.expression.node, context)
                    .map_err(|e| IrgenError {
                        code: switch_statement.node.expression.write_string(),
                        message: e,
                    })?;

                let bid_end = self.alloc_bid();
                let (cases, bid_default) =
                    self.translate_switch_body(&switch_statement.node.statement.node, bid_end)?;

                self.commit_block(
                    mem::replace(context, Context::new(bid_end)),
                    ir::BlockExit::Switch {
                        value,
                        default: Box::new(ir::JumpArg::new(bid_default, Vec::new())),
                        cases,
                    },
                );

                Ok(())
            }

            Statement::Continue => {
                let bid_continue = bid_continue.ok_or_else(|| IrgenError {
                    code: "continue;".to_string(),
                    message: IrgenErrorMessage::Misc {
                        message: "no blocks to continue".to_string(),
                    },
                })?;
                let new_context = mem::replace(context, Context::new(self.alloc_bid()));
                self.commit_block(
                    new_context,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_continue, Vec::new()),
                    },
                );
                Ok(())
            }
            Statement::Break => {
                let bid_break = bid_break.ok_or_else(|| IrgenError {
                    code: "break;".to_string(),
                    message: IrgenErrorMessage::Misc {
                        message: "no blocks to break".to_string(),
                    },
                })?;
                let new_context = mem::replace(context, Context::new(self.alloc_bid()));
                self.commit_block(
                    new_context,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_break, Vec::new()),
                    },
                );
                Ok(())
            }
            Statement::Labeled(labeled_statement) => Err(IrgenError {
                code: labeled_statement.node.label.write_string(),
                message: IrgenErrorMessage::Misc {
                    message: "label statement not within a switch".to_string(),
                },
            }),
            _ => todo!("other statements"),
        }
    }
}
