use lang_c::ast::*;
use lang_c::span::Node;

use core::ops::Deref;
use std::io::{Result, Write};

use crate::write_base::*;

impl<T: WriteLine> WriteLine for Node<T> {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        self.node.write_line(indent, write)
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

impl<T: WriteString> WriteString for &T {
    fn write_string(&self) -> String {
        (*self).write_string()
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
        writeln!(_write, "{}", self.write_string())?;
        Ok(())
    }
}

impl WriteLine for FunctionDefinition {
    fn write_line(&self, _indent: usize, _write: &mut dyn Write) -> Result<()> {
        write_indent(_indent, _write)?;
        write!(_write, "{}", self.write_string())?;
        Ok(())
    }
}

impl WriteString for FunctionDefinition {
    fn write_string(&self) -> String {
        format!(
            "{} {}{} {}",
            self.specifiers
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(" "),
            self.declarator.write_string(),
            self.declarations
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(", "),
            self.statement.write_string(),
        )
    }
}

impl WriteString for Statement {
    fn write_string(&self) -> String {
        match self {
            Self::Labeled(labeled_statement) => format!(
                "{}: {}",
                labeled_statement.node.label.write_string(),
                labeled_statement.node.statement.write_string(),
            ),
            Self::Compound(items) => format!(
                "{{ {} }}",
                items
                    .iter()
                    .map(WriteString::write_string)
                    .collect::<Vec<_>>()
                    .join(" "),
            ),
            Self::Expression(expr) => format!("{};", expr.write_string()),
            Self::If(stmt) => stmt.write_string(),
            Self::Switch(stmt) => stmt.write_string(),
            Self::While(stmt) => stmt.write_string(),
            Self::DoWhile(stmt) => stmt.write_string(),
            Self::For(stmt) => stmt.write_string(),
            Self::Goto(_) => panic!("Statement::Goto"),
            Self::Continue => "continue;".to_string(),
            Self::Break => "break;".to_string(),
            Self::Return(expr) => format!("return {};", expr.write_string()),
            Self::Asm(_) => panic!("Statement::Asm"),
        }
    }
}

impl WriteString for Label {
    fn write_string(&self) -> String {
        match self {
            Self::Identifier(_) => panic!("Label::Identifier"),
            Self::Case(expr) => format!("case {}", expr.write_string()),
            Self::Default => "default".to_string(),
        }
    }
}

impl WriteString for BlockItem {
    fn write_string(&self) -> String {
        match self {
            Self::Declaration(decl) => decl.write_string(),
            Self::StaticAssert(_) => panic!("BlockItem::StaticAssert"),
            Self::Statement(stmt) => stmt.write_string(),
        }
    }
}

impl WriteString for IfStatement {
    fn write_string(&self) -> String {
        match &self.else_statement {
            Some(else_statement) => format!(
                "if ({}) {} else {}",
                self.condition.write_string(),
                self.then_statement.write_string(),
                else_statement.write_string(),
            ),
            None => format!(
                "if ({}) {}",
                self.condition.write_string(),
                self.then_statement.write_string(),
            ),
        }
    }
}

impl WriteString for SwitchStatement {
    fn write_string(&self) -> String {
        format!(
            "switch ({}) {}",
            self.expression.write_string(),
            self.statement.write_string(),
        )
    }
}

impl WriteString for WhileStatement {
    fn write_string(&self) -> String {
        format!(
            "while ({}) {}",
            self.expression.write_string(),
            self.statement.write_string(),
        )
    }
}

impl WriteString for DoWhileStatement {
    fn write_string(&self) -> String {
        format!(
            "do {} while ({});",
            self.statement.write_string(),
            self.expression.write_string(),
        )
    }
}

impl WriteString for ForStatement {
    fn write_string(&self) -> String {
        format!(
            "for ({} {}; {}) {}",
            self.initializer.write_string(),
            self.condition.write_string(),
            self.step.write_string(),
            self.statement.write_string(),
        )
    }
}

impl WriteString for ForInitializer {
    fn write_string(&self) -> String {
        match self {
            Self::Empty => ";".to_string(),
            Self::Expression(expr) => format!("{};", expr.write_string()),
            Self::Declaration(decl) => decl.write_string(),
            Self::StaticAssert(_) => panic!("ForInitializer::StaticAssert"),
        }
    }
}

impl WriteString for Declaration {
    fn write_string(&self) -> String {
        format!(
            "{} {};",
            self.specifiers
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(" "),
            self.declarators
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(", "),
        )
    }
}

impl WriteString for InitDeclarator {
    fn write_string(&self) -> String {
        match &self.initializer {
            Some(initializer) => format!(
                "{} = {}",
                self.declarator.write_string(),
                initializer.write_string(),
            ),
            None => self.declarator.write_string(),
        }
    }
}

impl WriteString for Initializer {
    fn write_string(&self) -> String {
        match self {
            Self::Expression(expr) => expr.write_string(),
            Self::List(items) => format!(
                "{{{}}}",
                items
                    .iter()
                    .map(WriteString::write_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

impl WriteString for InitializerListItem {
    fn write_string(&self) -> String {
        assert!(self.designation.is_empty());
        self.initializer.write_string()
    }
}

impl WriteString for Expression {
    fn write_string(&self) -> String {
        match self {
            Self::Identifier(identifier) => identifier.write_string(),
            Self::Constant(constant) => constant.write_string(),
            Self::StringLiteral(_) => panic!("Expression::StringLiteral"),
            Self::GenericSelection(_) => panic!("Expression::GenericSelection"),
            Self::Member(member) => member.write_string(),
            Self::Call(call) => call.write_string(),
            Self::CompoundLiteral(_) => panic!("Expression::CompoundLiteral"),
            Self::SizeOf(typename) => format!("sizeof({})", typename.write_string()),
            Self::AlignOf(typename) => format!("_Alignof({})", typename.write_string()),
            Self::UnaryOperator(unary) => unary.write_string(),
            Self::Cast(cast) => cast.write_string(),
            Self::BinaryOperator(binary) => binary.write_string(),
            Self::Conditional(conditional) => conditional.write_string(),
            Self::Comma(exprs) => format!(
                "({})",
                exprs
                    .iter()
                    .map(WriteString::write_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::OffsetOf(_) => panic!("Expression::OffsetOf"),
            Self::VaArg(_) => panic!("Expression::VaArg"),
            Self::Statement(_) => panic!("Expression::Statement"),
        }
    }
}

impl WriteString for Identifier {
    fn write_string(&self) -> String {
        self.name.clone()
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
        match self.format {
            FloatFormat::Float => "f".to_string(),
            FloatFormat::Double => "".to_string(),
            FloatFormat::LongDouble => "l".to_string(),
            FloatFormat::TS18661Format(_) => panic!("TS18861"),
        }
    }
}

impl WriteString for MemberExpression {
    fn write_string(&self) -> String {
        format!(
            "({} {} {})",
            self.expression.write_string(),
            match self.operator.node {
                MemberOperator::Direct => ".",
                MemberOperator::Indirect => "->",
            },
            self.identifier.write_string(),
        )
    }
}

impl WriteString for CallExpression {
    fn write_string(&self) -> String {
        format!(
            "{}({})",
            self.callee.write_string(),
            self.arguments
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(", "),
        )
    }
}

impl WriteString for TypeName {
    fn write_string(&self) -> String {
        format!(
            "{} {}",
            self.specifiers
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(" "),
            self.declarator.write_string(),
        )
    }
}

impl WriteString for SpecifierQualifier {
    fn write_string(&self) -> String {
        match self {
            Self::TypeSpecifier(type_specifier) => type_specifier.write_string(),
            Self::TypeQualifier(type_qualifier) => type_qualifier.write_string(),
        }
    }
}

impl WriteString for TypeSpecifier {
    fn write_string(&self) -> String {
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
            Self::Struct(struct_type) => struct_type.write_string(),
            Self::Enum(_) => panic!("TypeSpecifier::Enum"),
            Self::TypedefName(typedef_name) => typedef_name.write_string(),
            Self::TypeOf(_) => panic!("TypeSpecifier::TypeOf"),
            Self::TS18661Float(_) => panic!("TypeSpecifier::TS18661Float"),
        }
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

impl WriteString for StructType {
    fn write_string(&self) -> String {
        match &self.declarations {
            Some(declarations) => format!(
                "{} {} {{ {} }}",
                self.kind.write_string(),
                self.identifier.write_string(),
                declarations
                    .iter()
                    .map(WriteString::write_string)
                    .collect::<Vec<_>>()
                    .join(" "),
            ),
            None => format!(
                "{} {}",
                self.kind.write_string(),
                self.identifier.write_string(),
            ),
        }
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

impl WriteString for StructDeclaration {
    fn write_string(&self) -> String {
        match self {
            Self::Field(field) => field.write_string(),
            Self::StaticAssert(_) => panic!("StructDeclaration::StaticAssert"),
        }
    }
}

impl WriteString for StructField {
    fn write_string(&self) -> String {
        format!(
            "{} {};",
            self.specifiers
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(" "),
            self.declarators
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(" ")
        )
    }
}

impl WriteString for StructDeclarator {
    fn write_string(&self) -> String {
        assert_eq!(true, self.bit_width.is_none());
        self.declarator.write_string()
    }
}

impl WriteString for Declarator {
    fn write_string(&self) -> String {
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
            pointers
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(" "),
            if pointers.is_empty() { "" } else { " " },
            self.kind.write_string(),
            nonpointers
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(" "),
        )
    }
}

impl WriteString for DerivedDeclarator {
    fn write_string(&self) -> String {
        match self {
            Self::Pointer(pointer_qualifiers) => format!(
                "*{}",
                pointer_qualifiers
                    .iter()
                    .map(WriteString::write_string)
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            Self::Array(array_decl) => array_decl.write_string(),
            Self::Function(func_decl) => func_decl.write_string(),
            // Support when K&R function has no parameter
            Self::KRFunction(kr_func_decl) => {
                assert_eq!(true, kr_func_decl.is_empty());
                "()".to_string()
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

impl WriteString for ArrayDeclarator {
    fn write_string(&self) -> String {
        format!(
            "[{}{}{}]",
            self.qualifiers
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(" "),
            if self.qualifiers.is_empty() { "" } else { " " },
            self.size.write_string(),
        )
    }
}

impl WriteString for ArraySize {
    fn write_string(&self) -> String {
        match self {
            Self::VariableExpression(expr) => expr.write_string(),
            _ => panic!("ArraySize::_"),
        }
    }
}

impl WriteString for FunctionDeclarator {
    fn write_string(&self) -> String {
        assert_eq!(self.ellipsis, Ellipsis::None);
        format!(
            "({})",
            self.parameters
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(", "),
        )
    }
}

impl WriteString for ParameterDeclaration {
    fn write_string(&self) -> String {
        assert_eq!(true, self.extensions.is_empty());
        format!(
            "{} {}",
            self.specifiers
                .iter()
                .map(WriteString::write_string)
                .collect::<Vec<_>>()
                .join(" "),
            self.declarator.write_string(),
        )
    }
}

impl WriteString for DeclarationSpecifier {
    fn write_string(&self) -> String {
        match self {
            Self::StorageClass(storage_class_specifier) => storage_class_specifier.write_string(),
            Self::TypeSpecifier(type_specifier) => type_specifier.write_string(),
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

impl WriteString for DeclaratorKind {
    fn write_string(&self) -> String {
        match self {
            Self::Abstract => "".to_string(),
            Self::Identifier(identifier) => identifier.write_string(),
            Self::Declarator(decl) => format!("({})", decl.write_string()),
        }
    }
}

impl WriteString for UnaryOperatorExpression {
    fn write_string(&self) -> String {
        match self.operator.node {
            UnaryOperator::PostIncrement | UnaryOperator::PostDecrement => format!(
                "({}{})",
                self.operand.write_string(),
                self.operator.write_string(),
            ),
            _ => format!(
                "({}{})",
                self.operator.write_string(),
                self.operand.write_string(),
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

impl WriteString for CastExpression {
    fn write_string(&self) -> String {
        format!(
            "({}) {}",
            self.type_name.write_string(),
            self.expression.write_string(),
        )
    }
}

impl WriteString for BinaryOperatorExpression {
    fn write_string(&self) -> String {
        match self.operator.node {
            BinaryOperator::Index => {
                format!("{}[{}]", self.lhs.write_string(), self.rhs.write_string(),)
            }
            _ => format!(
                "({} {} {})",
                self.lhs.write_string(),
                self.operator.write_string(),
                self.rhs.write_string(),
            ),
        }
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

impl WriteString for ConditionalExpression {
    fn write_string(&self) -> String {
        format!(
            "({} ? {} : {})",
            self.condition.write_string(),
            self.then_expression.write_string(),
            self.else_expression.write_string(),
        )
    }
}
