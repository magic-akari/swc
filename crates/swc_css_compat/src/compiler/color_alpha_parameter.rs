use swc_atoms::atom;
use swc_css_ast::{AbsoluteColorBase, ComponentValue, FunctionName};

use crate::compiler::Compiler;

impl Compiler {
    pub(crate) fn process_color_alpha_parameter(&mut self, n: &mut AbsoluteColorBase) {
        if let AbsoluteColorBase::Function(function) = n {
            if let Some(ComponentValue::AlphaValue(_) | ComponentValue::Function(_)) =
                function.value.last()
            {
                let name = match &mut function.name {
                    FunctionName::Ident(name) => name,
                    _ => {
                        return;
                    }
                };

                if name.value.eq_ignore_ascii_case("rgb") {
                    name.value = atom!("rgba");
                    name.raw = None;
                } else if name.value.eq_ignore_ascii_case("hsl") {
                    name.value = atom!("hsla");
                    name.raw = None;
                }
            } else {
                let name = match &mut function.name {
                    FunctionName::Ident(name) => name,
                    _ => {
                        return;
                    }
                };

                if name.value.eq_ignore_ascii_case("rgba") {
                    name.value = atom!("rgb");
                    name.raw = None;
                } else if name.value.eq_ignore_ascii_case("hsla") {
                    name.value = atom!("hsl");
                    name.raw = None;
                }
            }
        }
    }
}
