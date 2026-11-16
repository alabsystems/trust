//! Diagnostic equality check for a published Trust-IR binary/text pair.
//!
//! Usage: targo --unverified run -p trust-cg-bridge --example trust_ir_pair_check \
//!     --features trust-ir-pair-check -- <module.trust-ir.bin> <module.trust-ir.txt>
//!
//! Equality of two parsed IR structures does not authenticate their producer,
//! validate the IR, or establish G7 executable/codegen authority.

#![forbid(unsafe_code)]

use std::process::ExitCode;
use std::{env, fs};

use trust_ir::{binary, parser};

fn check_pair(binary_bytes: &[u8], text_bytes: &[u8]) -> Result<(), String> {
    let binary = binary::deserialize_module(binary_bytes)
        .map_err(|error| format!("binary decode refused: {error}"))?;
    let text =
        std::str::from_utf8(text_bytes).map_err(|error| format!("text is not UTF-8: {error}"))?;
    let parsed_text =
        parser::parse_module(text).map_err(|error| format!("text parse refused: {error}"))?;

    // Compare the stored structures. Canonicalizing the binary first could
    // renumber SSA values and clear source provenance without authorization.
    if binary != parsed_text {
        return Err("decoded binary and text modules differ".to_string());
    }
    Ok(())
}

fn main() -> ExitCode {
    let mut args = env::args_os().skip(1);
    let (Some(binary_path), Some(text_path), None) = (args.next(), args.next(), args.next()) else {
        eprintln!("usage: trust_ir_pair_check <module.trust-ir.bin> <module.trust-ir.txt>");
        return ExitCode::from(2);
    };
    let binary = match fs::read(&binary_path) {
        Ok(bytes) => bytes,
        Err(error) => {
            eprintln!("binary read refused: {error}");
            return ExitCode::from(2);
        }
    };
    let text = match fs::read(&text_path) {
        Ok(bytes) => bytes,
        Err(error) => {
            eprintln!("text read refused: {error}");
            return ExitCode::from(2);
        }
    };
    match check_pair(&binary, &text) {
        Ok(()) => {
            println!("structural match (diagnostic only; not G7 authority)");
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("trust_ir_pair_check: {error}");
            ExitCode::from(1)
        }
    }
}

#[cfg(test)]
mod tests {
    use trust_ir::constant::Constant;
    use trust_ir::inst::Inst;
    use trust_ir::node::InstrNode;
    use trust_ir::ty::{FuncTy, Ty};
    use trust_ir::value::{BlockId, FuncId, ValueId};
    use trust_ir::{Block, Function, Global, Linkage, Module, Visibility};

    use super::check_pair;

    fn module_with_value(value: i128) -> Module {
        let mut module = Module::new("pair");
        module.globals.push(Global {
            name: "answer".into(),
            ty: Ty::I32,
            mutable: false,
            initializer: Some(Constant::Int(value)),
            linkage: Linkage::External,
            tls: None,
            align: None,
            section: None,
            visibility: Visibility::Default,
            retained: false,
        });
        module
    }

    #[test]
    fn matching_pair_passes() {
        let module = module_with_value(1);
        let binary = trust_ir::binary::serialize_module(&module);
        let text = trust_ir::format::text_checked(&module).unwrap();
        assert_eq!(trust_ir::binary::deserialize_module(&binary).unwrap(), module);
        assert_eq!(trust_ir::parser::parse_module(&text).unwrap(), module);
        assert_eq!(check_pair(&binary, text.as_bytes()), Ok(()));
    }

    #[test]
    fn byte_valid_but_different_value_is_refused() {
        let binary_module = module_with_value(1);
        let text_module = module_with_value(2);
        let binary = trust_ir::binary::serialize_module(&binary_module);
        let text = trust_ir::format::text_checked(&text_module).unwrap();
        assert_eq!(trust_ir::binary::deserialize_module(&binary).unwrap(), binary_module);
        assert_eq!(trust_ir::parser::parse_module(&text).unwrap(), text_module);
        assert!(check_pair(&binary, text.as_bytes()).unwrap_err().contains("differ"));
    }

    #[test]
    fn canonicalization_cannot_hide_stored_id_change() {
        let mut module = Module::new("pair");
        let sig = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let mut function = Function::new(FuncId::new(0), "answer", sig, BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(1) })
                .with_result(ValueId::new(7)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(7)] }));
        function.blocks.push(block);
        module.functions.push(function);

        let binary = trust_ir::binary::serialize_module(&module);
        let canonical = trust_ir::format::canonical_checked(&module).unwrap();
        assert_ne!(trust_ir::parser::parse_module(&canonical).unwrap(), module);
        assert!(check_pair(&binary, canonical.as_bytes()).unwrap_err().contains("differ"));
    }

    #[test]
    fn malformed_input_is_refused() {
        let module = module_with_value(1);
        let mut binary = trust_ir::binary::serialize_module(&module);
        let text = trust_ir::format::text_checked(&module).unwrap();
        binary.push(0);
        assert!(check_pair(&binary, text.as_bytes()).unwrap_err().contains("binary decode"));
        binary.pop();
        assert!(check_pair(&binary, b"\xff").unwrap_err().contains("UTF-8"));
        assert!(
            check_pair(&binary, b"module \"pair\"\nunknown directive")
                .unwrap_err()
                .contains("text parse")
        );
    }
}
