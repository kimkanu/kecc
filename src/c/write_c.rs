use lang_c::ast::*;
use lang_c::span::Node;

use core::ops::Deref;
use std::io::{Result, Write};

use crate::write_base::*;

pub trait WriteStringIndent {
    fn write_string_indent(&self, _indent: usize) -> String;
}

impl<T: WriteLine> WriteLine for Node<T> {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        self.node.write_line(indent, write)
    }
}
impl<T: WriteStringIndent> WriteStringIndent for Node<T> {
    fn write_string_indent(&self, indent: usize) -> String {
        self.node.write_string_indent(indent)
    }
}
impl<T: WriteString> WriteString for Node<T> {
    fn write_string(&self) -> String {
        self.node.write_string()
    }
}

impl<T: WriteString> WriteString for Box<T> {
    fn write_string(&self) -> String {
        self.deref().write_string()
    }
}
impl<T: WriteStringIndent> WriteStringIndent for Box<T> {
    fn write_string_indent(&self, indent: usize) -> String {
        self.deref().write_string_indent(indent)
    }
}

impl<T: WriteString> WriteString for &T {
    fn write_string(&self) -> String {
        (*self).write_string()
    }
}
impl<T: WriteStringIndent> WriteStringIndent for &T {
    fn write_string_indent(&self, indent: usize) -> String {
        (*self).write_string_indent(indent)
    }
}

impl<T: WriteString> WriteString for Option<T> {
    fn write_string(&self) -> String {
        if let Some(this) = self {
            this.write_string()
        } else {
            "".to_string()
        }
    }
}
impl<T: WriteStringIndent> WriteStringIndent for Option<T> {
    fn write_string_indent(&self, indent: usize) -> String {
        if let Some(this) = self {
            this.write_string_indent(indent)
        } else {
            "".to_string()
        }
    }
}

impl<T: WriteString> WriteString for Vec<T> {
    fn write_string(&self) -> String {
        self.iter()
            .map(WriteString::write_string)
            .collect::<Vec<_>>()
            .join(" ")
    }
}
impl<T: WriteStringIndent> WriteStringIndent for Vec<T> {
    fn write_string_indent(&self, indent: usize) -> String {
        self.iter()
            .map(|s| s.write_string_indent(indent))
            .collect::<Vec<_>>()
            .join(" ")
    }
}

impl WriteLine for TranslationUnit {
    fn write_line(&self, _indent: usize, _write: &mut dyn Write) -> Result<()> {
        for ext_decl in &self.0 {
            ext_decl.write_line(_indent, _write)?;
            writeln!(_write)?;
        }
        Ok(())
    }
}

impl WriteLine for ExternalDeclaration {
    fn write_line(&self, _indent: usize, _write: &mut dyn Write) -> Result<()> {
        match self {
            Self::Declaration(decl) => decl.write_line(_indent, _write),
            Self::StaticAssert(_) => panic!(),
            Self::FunctionDefinition(fdef) => fdef.write_line(_indent, _write),
        }
    }
}

impl WriteLine for Declaration {
    fn write_line(&self, _indent: usize, _write: &mut dyn Write) -> Result<()> {
        write_indent(_indent, _write)?;
        writeln!(_write, "{}", self.write_string_indent(_indent))?;
        Ok(())
    }
}

impl WriteLine for FunctionDefinition {
    fn write_line(&self, _indent: usize, _write: &mut dyn Write) -> Result<()> {
        write_indent(_indent, _write)?;
        write!(_write, "{}", self.write_string_indent(_indent))?;
        Ok(())
    }
}

impl WriteStringIndent for FunctionDefinition {
    fn write_string_indent(&self, _indent: usize) -> String {
        format!(
            "{} {}{} {}",
            self.specifiers.write_string_indent(_indent),
            self.declarator.write_string_indent(_indent),
            self.declarations
                .iter()
                .map(|s| s.write_string_indent(_indent))
                .collect::<Vec<_>>()
                .join(", "),
            self.statement.write_string_indent(_indent),
        )
    }
}

impl WriteString for Identifier {
    fn write_string(&self) -> String {
        self.name.clone()
    }
}

impl WriteStringIndent for Declaration {
    fn write_string_indent(&self, _indent: usize) -> String {
        format!(
            "{} {};",
            self.specifiers.write_string_indent(_indent),
            self.declarators
                .iter()
                .map(|s| s.write_string_indent(_indent))
                .collect::<Vec<_>>()
                .join(", "),
        )
    }
}

impl WriteStringIndent for DeclarationSpecifier {
    fn write_string_indent(&self, _indent: usize) -> String {
        match self {
            Self::StorageClass(storage_class_specifier) => storage_class_specifier.write_string(),
            Self::TypeSpecifier(type_specifier) => type_specifier.write_string_indent(_indent),
            Self::TypeQualifier(type_qualifier) => type_qualifier.write_string(),
            Self::Function(_) => panic!("DeclarationSpecifier::Function"),
            Self::Alignment(_) => panic!("DeclarationSpecifier::Alignment"),
            Self::Extension(_) => panic!("DeclarationSpecifier::Extension"),
        }
    }
}

impl WriteString for StorageClassSpecifier {
    fn write_string(&self) -> String {
        match self {
            Self::Typedef => "typedef".to_string(),
            _ => panic!("StorageClassifier other than Typedef"),
        }
    }
}

impl WriteStringIndent for TypeSpecifier {
    fn write_string_indent(&self, _indent: usize) -> String {
        match self {
            Self::Void => "void".to_string(),
            Self::Char => "char".to_string(),
            Self::Short => "short".to_string(),
            Self::Int => "int".to_string(),
            Self::Long => "long".to_string(),
            Self::Float => "float".to_string(),
            Self::Double => "double".to_string(),
            Self::Signed => "signed".to_string(),
            Self::Unsigned => "unsigned".to_string(),
            Self::Bool => "_Bool".to_string(),
            Self::Complex => panic!("TypeSpecifier::Complex"),
            Self::Atomic(_) => panic!("TypeSpecifier::Atomic"),
            Self::Struct(struct_type) => struct_type.write_string_indent(_indent),
            Self::Enum(_) => panic!("TypeSpecifier::Enum"),
            Self::TypedefName(typedef_name) => typedef_name.write_string(),
            Self::TypeOf(_) => panic!("TypeSpecifier::TypeOf"),
            Self::TS18661Float(_) => panic!("TypeSpecifier::TS18661Float"),
        }
    }
}

impl WriteStringIndent for StructType {
    fn write_string_indent(&self, _indent: usize) -> String {
        match &self.declarations {
            Some(declarations) => format!(
                "{} {} {{ {} }}",
                self.kind.write_string(),
                self.identifier.write_string(),
                declarations.write_string_indent(_indent),
            ),
            None => format!(
                "{} {}",
                self.kind.write_string(),
                self.identifier.write_string(),
            ),
        }
    }
}

impl WriteStringIndent for StructDeclaration {
    fn write_string_indent(&self, _indent: usize) -> String {
        match self {
            Self::Field(field) => field.write_string_indent(_indent),
            Self::StaticAssert(_) => panic!("StructDeclaration::StaticAssert"),
        }
    }
}

impl WriteStringIndent for StructField {
    fn write_string_indent(&self, _indent: usize) -> String {
        format!(
            "{} {};",
            self.specifiers.write_string_indent(_indent),
            self.declarators.write_string_indent(_indent),
        )
    }
}

impl WriteStringIndent for StructDeclarator {
    fn write_string_indent(&self, _indent: usize) -> String {
        assert_eq!(true, self.bit_width.is_none());
        self.declarator.write_string_indent(_indent)
    }
}

impl WriteString for StructKind {
    fn write_string(&self) -> String {
        match self {
            Self::Struct => "struct".to_string(),
            Self::Union => panic!("StructKind::Union"),
        }
    }
}

impl WriteStringIndent for AlignmentSpecifier {
    fn write_string_indent(&self, _indent: usize) -> String {
        match self {
            Self::Type(typename) => format!("_Alignas({})", typename.write_string_indent(_indent)),
            Self::Constant(_) => panic!(AlignmentSpecifier::Constant),
        }
    }
}

impl WriteStringIndent for InitDeclarator {
    fn write_string_indent(&self, _indent: usize) -> String {
        match &self.initializer {
            Some(initializer) => format!(
                "{} = {}",
                self.declarator.write_string_indent(_indent),
                initializer.write_string_indent(_indent),
            ),
            None => self.declarator.write_string_indent(_indent),
        }
    }
}

impl WriteStringIndent for Initializer {
    fn write_string_indent(&self, _indent: usize) -> String {
        match self {
            Self::Expression(expr) => expr.write_string_indent(_indent),
            Self::List(_) => panic!("Initializer::List"),
        }
    }
}

impl WriteStringIndent for Declarator {
    fn write_string_indent(&self, _indent: usize) -> String {
        assert_eq!(true, self.extensions.is_empty());

        let pointers = self
            .derived
            .iter()
            .filter(|decl| {
                if let DerivedDeclarator::Pointer(_) = decl.node {
                    true
                } else {
                    false
                }
            })
            .collect::<Vec<_>>();
        let nonpointers = self
            .derived
            .iter()
            .filter(|decl| {
                if let DerivedDeclarator::Pointer(_) = decl.node {
                    false
                } else {
                    true
                }
            })
            .collect::<Vec<_>>();

        format!(
            "{}{}{}{}",
            pointers.write_string_indent(_indent),
            if pointers.is_empty() { "" } else { " " },
            self.kind.write_string_indent(_indent),
            nonpointers.write_string_indent(_indent),
        )
    }
}

impl WriteStringIndent for DerivedDeclarator {
    fn write_string_indent(&self, _indent: usize) -> String {
        match self {
            Self::Pointer(pointer_qualifiers) => format!("* {}", pointer_qualifiers.write_string()),
            Self::Array(array_decl) => array_decl.write_string_indent(_indent),
            Self::Function(func_decl) => func_decl.write_string_indent(_indent),
            // Support when K&R function has no parameter
            Self::KRFunction(kr_func_decl) => {
                assert_eq!(true, kr_func_decl.is_empty());
                format!("({})", kr_func_decl.write_string(),)
            }
        }
    }
}

impl WriteString for PointerQualifier {
    fn write_string(&self) -> String {
        match self {
            Self::TypeQualifier(type_qualifier) => type_qualifier.write_string(),
            Self::Extension(_) => panic!("PointerQualifier::Extension"),
        }
    }
}

impl WriteStringIndent for ArrayDeclarator {
    fn write_string_indent(&self, _indent: usize) -> String {
        format!(
            "[{}{}{}]",
            self.qualifiers.write_string(),
            if self.qualifiers.is_empty() { "" } else { " " },
            self.size.write_string_indent(_indent),
        )
    }
}

impl WriteString for TypeQualifier {
    fn write_string(&self) -> String {
        match self {
            Self::Const => "const".to_string(),
            _ => panic!("TypeQualifier::_"),
        }
    }
}

impl WriteStringIndent for ArraySize {
    fn write_string_indent(&self, _indent: usize) -> String {
        match self {
            Self::VariableExpression(expr) => expr.write_string_indent(_indent),
            _ => panic!("ArraySize::_"),
        }
    }
}

impl WriteStringIndent for FunctionDeclarator {
    fn write_string_indent(&self, _indent: usize) -> String {
        assert_eq!(self.ellipsis, Ellipsis::None);
        format!(
            "({})",
            self.parameters
                .iter()
                .map(|s| s.write_string_indent(_indent))
                .collect::<Vec<_>>()
                .join(", "),
        )
    }
}

impl WriteStringIndent for ParameterDeclaration {
    fn write_string_indent(&self, _indent: usize) -> String {
        assert_eq!(true, self.extensions.is_empty());
        format!(
            "{} {}",
            self.specifiers.write_string_indent(_indent),
            self.declarator.write_string_indent(_indent),
        )
    }
}

impl WriteStringIndent for DeclaratorKind {
    fn write_string_indent(&self, _indent: usize) -> String {
        match self {
            Self::Abstract => "".to_string(),
            Self::Identifier(identifier) => identifier.write_string(),
            Self::Declarator(decl) => format!("({})", decl.write_string_indent(_indent),),
        }
    }
}

impl WriteStringIndent for BlockItem {
    fn write_string_indent(&self, _indent: usize) -> String {
        match self {
            Self::Declaration(decl) => decl.write_string_indent(_indent),
            Self::StaticAssert(_) => panic!("BlockItem::StaticAssert"),
            Self::Statement(stmt) => stmt.write_string_indent(_indent),
        }
    }
}

impl WriteStringIndent for ForInitializer {
    fn write_string_indent(&self, _indent: usize) -> String {
        match self {
            Self::Empty => ";".to_string(),
            Self::Expression(expr) => format!("{};", expr.write_string_indent(_indent)),
            Self::Declaration(decl) => decl.write_string_indent(_indent),
            Self::StaticAssert(_) => panic!("ForInitializer::StaticAssert"),
        }
    }
}

impl WriteStringIndent for Statement {
    fn write_string_indent(&self, _indent: usize) -> String {
        match self {
            Self::Labeled(labeled_statement) => format!(
                "{}: {}",
                labeled_statement.node.label.write_string_indent(_indent),
                labeled_statement
                    .node
                    .statement
                    .write_string_indent(_indent),
            ),
            Self::Compound(items) => format!(
                "{{\n{}\n{}}}",
                items
                    .iter()
                    .map(|item| format!(
                        "{}{}",
                        "  ".repeat(_indent + 1),
                        item.write_string_indent(_indent + 1)
                    ))
                    .collect::<Vec<_>>()
                    .join("\n"),
                "  ".repeat(_indent),
            ),
            Self::Expression(expr) => format!("{};", expr.write_string_indent(_indent)),
            Self::If(stmt) => stmt.write_string_indent(_indent),
            Self::Switch(stmt) => stmt.write_string_indent(_indent),
            Self::While(stmt) => stmt.write_string_indent(_indent),
            Self::DoWhile(stmt) => stmt.write_string_indent(_indent),
            Self::For(stmt) => stmt.write_string_indent(_indent),
            Self::Goto(_) => panic!("Statement::Goto"),
            Self::Continue => "continue;".to_string(),
            Self::Break => "break;".to_string(),
            Self::Return(expr) => format!("return {};", expr.write_string_indent(_indent)),
            Self::Asm(_) => panic!("Statement::Asm"),
        }
    }
}

impl WriteStringIndent for IfStatement {
    fn write_string_indent(&self, _indent: usize) -> String {
        match &self.else_statement {
            Some(else_statement) => format!(
                "if ({}) {} else {}{}",
                self.condition.write_string_indent(_indent),
                self.then_statement.write_string_indent(_indent),
                else_statement.write_string_indent(_indent),
                "  ".repeat(_indent),
            ),
            None => format!(
                "if ({}) {}{}",
                self.condition.write_string_indent(_indent),
                self.then_statement.write_string_indent(_indent),
                "  ".repeat(_indent),
            ),
        }
    }
}

impl WriteStringIndent for WhileStatement {
    fn write_string_indent(&self, _indent: usize) -> String {
        format!(
            "while ({}) {}{}",
            self.expression.write_string_indent(_indent),
            self.statement.write_string_indent(_indent),
            "  ".repeat(_indent),
        )
    }
}

impl WriteStringIndent for DoWhileStatement {
    fn write_string_indent(&self, _indent: usize) -> String {
        format!(
            "do {} while ({});{}",
            self.statement.write_string_indent(_indent),
            self.expression.write_string_indent(_indent),
            "  ".repeat(_indent),
        )
    }
}

impl WriteStringIndent for ForStatement {
    fn write_string_indent(&self, _indent: usize) -> String {
        format!(
            "for ({} {}; {}) {}{}",
            self.initializer.write_string_indent(_indent),
            self.condition.write_string_indent(_indent),
            self.step.write_string_indent(_indent),
            self.statement.write_string_indent(_indent),
            "  ".repeat(_indent),
        )
    }
}

impl WriteStringIndent for SwitchStatement {
    fn write_string_indent(&self, _indent: usize) -> String {
        format!(
            "switch ({}) {}{}",
            self.expression.write_string_indent(_indent),
            self.statement.write_string_indent(_indent),
            "  ".repeat(_indent),
        )
    }
}

impl WriteStringIndent for Expression {
    fn write_string_indent(&self, _indent: usize) -> String {
        match self {
            Self::Identifier(identifier) => identifier.write_string(),
            Self::Constant(constant) => constant.write_string(),
            Self::StringLiteral(_) => panic!("Expression::StringLiteral"),
            Self::GenericSelection(_) => panic!("Expression::GenericSelection"),
            Self::Member(member) => member.write_string_indent(_indent),
            Self::Call(call) => call.write_string_indent(_indent),
            Self::CompoundLiteral(_) => panic!("Expression::CompoundLiteral"),
            Self::SizeOf(typename) => format!("sizeof({})", typename.write_string_indent(_indent)),
            Self::AlignOf(typename) => format!("_Alignof({})", typename.write_string_indent(_indent)),
            Self::UnaryOperator(unary) => unary.write_string_indent(_indent),
            Self::Cast(cast) => cast.write_string_indent(_indent),
            Self::BinaryOperator(binary) => binary.write_string_indent(_indent),
            Self::Conditional(conditional) => conditional.write_string_indent(_indent),
            Self::Comma(exprs) => format!(
                "({})",
                exprs
                    .iter()
                    .map(|s| s.write_string_indent(_indent))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::OffsetOf(_) => panic!("Expression::OffsetOf"),
            Self::VaArg(_) => panic!("Expression::VaArg"),
            Self::Statement(_) => panic!("Expression::Statement"),
        }
    }
}

impl WriteStringIndent for Label {
    fn write_string_indent(&self, _indent: usize) -> String {
        match self {
            Self::Identifier(_) => panic!("Label::Identifier"),
            Self::Case(expr) => format!("case {}", expr.write_string_indent(_indent)),
            Self::Default => "default".to_string(),
        }
    }
}

impl WriteStringIndent for MemberExpression {
    fn write_string_indent(&self, _indent: usize) -> String {
        format!(
            "({}{}{})",
            self.expression.write_string_indent(_indent),
            match self.operator.node {
                MemberOperator::Direct => ".",
                MemberOperator::Indirect => "->",
            },
            self.identifier.write_string(),
        )
    }
}

impl WriteStringIndent for CallExpression {
    fn write_string_indent(&self, _indent: usize) -> String {
        format!(
            "{}({})",
            self.callee.write_string_indent(_indent),
            self.arguments
                .iter()
                .map(|s| s.write_string_indent(_indent))
                .collect::<Vec<_>>()
                .join(", "),
        )
    }
}

impl WriteStringIndent for TypeName {
    fn write_string_indent(&self, _indent: usize) -> String {
        format!(
            "{} {}",
            self.specifiers.write_string_indent(_indent),
            self.declarator.write_string_indent(_indent),
        )
    }
}

impl WriteStringIndent for SpecifierQualifier {
    fn write_string_indent(&self, _indent: usize) -> String {
        match self {
            Self::TypeSpecifier(type_specifier) => type_specifier.write_string_indent(_indent),
            Self::TypeQualifier(type_qualifier) => type_qualifier.write_string(),
        }
    }
}

impl WriteStringIndent for UnaryOperatorExpression {
    fn write_string_indent(&self, _indent: usize) -> String {
        match self.operator.node {
            UnaryOperator::PostIncrement | UnaryOperator::PostDecrement => format!(
                "({}{})",
                self.operand.write_string_indent(_indent),
                self.operator.write_string(),
            ),
            _ => format!(
                "({}{})",
                self.operator.write_string(),
                self.operand.write_string_indent(_indent),
            ),
        }
    }
}

impl WriteString for UnaryOperator {
    fn write_string(&self) -> String {
        match self {
            Self::PostIncrement | Self::PreIncrement => "++".to_string(),
            Self::PostDecrement | Self::PreDecrement => "--".to_string(),
            Self::Address => "&".to_string(),
            Self::Indirection => "*".to_string(),
            Self::Plus => "+".to_string(),
            Self::Minus => "-".to_string(),
            Self::Complement => "~".to_string(),
            Self::Negate => "!".to_string(),
            Self::SizeOf => "sizeof ".to_string(),
        }
    }
}

impl WriteStringIndent for CastExpression {
    fn write_string_indent(&self, _indent: usize) -> String {
        format!(
            "({}) {}",
            self.type_name.write_string_indent(_indent),
            self.expression.write_string_indent(_indent),
        )
    }
}

impl WriteStringIndent for BinaryOperatorExpression {
    fn write_string_indent(&self, _indent: usize) -> String {
        match self.operator.node {
            BinaryOperator::Index => format!(
                "{}[{}]",
                self.lhs.write_string_indent(_indent),
                self.rhs.write_string_indent(_indent),
            ),
            _ => format!(
                "({} {} {})",
                self.lhs.write_string_indent(_indent),
                self.operator.write_string(),
                self.rhs.write_string_indent(_indent),
            ),
        }
    }
}

impl WriteString for Constant {
    fn write_string(&self) -> String {
        match self {
            Self::Integer(integer) => integer.write_string(),
            Self::Float(float) => float.write_string(),
            Self::Character(c) => c.to_string(),
        }
    }
}

impl WriteString for Integer {
    fn write_string(&self) -> String {
        assert_eq!(false, self.suffix.imaginary);
        format!(
            "{}{}{}",
            match self.base {
                IntegerBase::Decimal => "",
                IntegerBase::Octal => "0",
                IntegerBase::Hexadecimal => "0x",
            },
            self.number.to_string(),
            self.suffix.write_string(),
        )
    }
}

impl WriteString for IntegerSuffix {
    fn write_string(&self) -> String {
        format!(
            "{}{}{}",
            match self.size {
                IntegerSize::Int => "",
                IntegerSize::Long => "l",
                IntegerSize::LongLong => "ll",
            },
            if self.unsigned { "u" } else { "" },
            if self.imaginary { "i" } else { "" },
        )
    }
}

impl WriteString for Float {
    fn write_string(&self) -> String {
        format!(
            "{}{}{}",
            match self.base {
                FloatBase::Decimal => "",
                FloatBase::Hexadecimal => "0x",
            },
            self.number.to_string(),
            self.suffix.write_string(),
        )
    }
}

impl WriteString for FloatSuffix {
    fn write_string(&self) -> String {
        assert_eq!(false, self.imaginary);
        format!(
            "{}",
            match self.format {
                FloatFormat::Float => "f",
                FloatFormat::Double => "",
                FloatFormat::LongDouble => "l",
                FloatFormat::TS18661Format(_) => panic!("TS18861"),
            }
        )
    }
}

impl WriteString for BinaryOperator {
    fn write_string(&self) -> String {
        match self {
            Self::Index => panic!("Will not happen"),
            Self::Multiply => "*".to_string(),
            Self::Divide => "/".to_string(),
            Self::Modulo => "%".to_string(),
            Self::Plus => "+".to_string(),
            Self::Minus => "-".to_string(),
            Self::ShiftLeft => "<<".to_string(),
            Self::ShiftRight => ">>".to_string(),
            Self::Less => "<".to_string(),
            Self::Greater => ">".to_string(),
            Self::LessOrEqual => "<=".to_string(),
            Self::GreaterOrEqual => ">=".to_string(),
            Self::Equals => "==".to_string(),
            Self::NotEquals => "!=".to_string(),
            Self::BitwiseAnd => "&".to_string(),
            Self::BitwiseXor => "^".to_string(),
            Self::BitwiseOr => "|".to_string(),
            Self::LogicalAnd => "&&".to_string(),
            Self::LogicalOr => "||".to_string(),
            Self::Assign => "=".to_string(),
            Self::AssignMultiply => "*=".to_string(),
            Self::AssignDivide => "/=".to_string(),
            Self::AssignModulo => "%=".to_string(),
            Self::AssignPlus => "+=".to_string(),
            Self::AssignMinus => "-=".to_string(),
            Self::AssignShiftLeft => "<<=".to_string(),
            Self::AssignShiftRight => ">>=".to_string(),
            Self::AssignBitwiseAnd => "&=".to_string(),
            Self::AssignBitwiseXor => "^=".to_string(),
            Self::AssignBitwiseOr => "|=".to_string(),
        }
    }
}

impl WriteStringIndent for ConditionalExpression {
    fn write_string_indent(&self, _indent: usize) -> String {
        format!(
            "({} ? {} : {})",
            self.condition.write_string_indent(_indent),
            self.then_expression.write_string_indent(_indent),
            self.else_expression.write_string_indent(_indent),
        )
    }
}
