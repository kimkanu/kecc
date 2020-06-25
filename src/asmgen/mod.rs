use crate::asm;
use crate::ir;
use crate::Translate;

#[derive(Default)]
pub struct Asmgen {}

impl Translate<ir::TranslationUnit> for Asmgen {
    type Target = asm::Asm;
    type Error = ();

    fn translate(&mut self, source: &ir::TranslationUnit) -> Result<Self::Target, Self::Error> {
        let mut functions = Vec::<asm::Section<asm::Function>>::new();
        let mut variables = Vec::<asm::Section<asm::Variable>>::new();

        for (name, decl) in source.decls.iter() {
            match decl {
                ir::Declaration::Variable { dtype, initializer } => {}
                ir::Declaration::Function {
                    signature,
                    definition,
                } => {
                    let mut blocks = Vec::<asm::Block>::new();

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
