// trust-wasm-bridge/binary.rs - the real binary-.wasm front door
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The binary-`.wasm` lowering front door for already-closed trust-ir modules,
//! distinct from the fail-closed WAT-text helpers in `lib.rs`.
//!
//! This is not a rustc link step: it does not consume dependency objects,
//! statics, native libraries, exported-symbol policy, or linker arguments.
//! Consequently `rustc_codegen_trust_cg` does not use it to link Rust crates;
//! linked `wasm32` output remains fail-closed until relocatable Wasm objects and
//! rustc's normal linker boundary are wired.
//!
//! ```text
//! VerifiableFunction(s)
//!   → trust_ir_bridge::lower_to_trust_ir_functions   (VF → trust-ir Module)
//!   → trust_cg_codegen::wasm::compile_module          (trust-ir → .wasm)
//!   → Vec<u8>  (a binary WebAssembly module)
//! ```
//!
//! For closed inputs this realizes the `trust-types → trust-ir → trust-cg →
//! .wasm` lowering contract. It does not by itself establish that an arbitrary
//! Rust crate was faithfully closed into those inputs.

use std::fmt;

use trust_cg_codegen::wasm::{self, WasmLowerError};
use trust_ir::Module as TrustIrModule;
use trust_ir_bridge::lower_to_trust_ir_functions;
use trust_types::VerifiableFunction;

/// Failure compiling to a binary wasm module through the front door.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WasmCompileError {
    /// `VerifiableFunction` → trust-ir lowering failed (trust-ir-bridge).
    /// Carries the bridge error's rendered message.
    TrustIrLowering(String),
    /// trust-ir → wasm lowering failed (trust-cg backend).
    WasmLowering(WasmLowerError),
}

impl fmt::Display for WasmCompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WasmCompileError::TrustIrLowering(m) => {
                write!(f, "VerifiableFunction → trust-ir lowering failed: {m}")
            }
            WasmCompileError::WasmLowering(e) => write!(f, "trust-ir → wasm lowering failed: {e}"),
        }
    }
}

impl std::error::Error for WasmCompileError {}

/// Compile a trust-ir module to a binary `.wasm` module via the trust-cg wasm
/// backend.
pub fn compile_trust_ir_module_to_wasm(
    module: &TrustIrModule,
) -> Result<Vec<u8>, WasmCompileError> {
    wasm::compile_module(module).map_err(WasmCompileError::WasmLowering)
}

/// Compile trust-types `VerifiableFunction`s to a binary `.wasm` module through
/// the production lowering path (VerifiableFunction → trust-ir → wasm).
///
/// This function performs lowering and returns the emitted bytes; it does not
/// establish a proof over those exact bytes. Callers that require proof-grade
/// output must separately bind and check the emitted artifact. `module_name`
/// names the emitted trust-ir module. Each function is exported under its name.
pub fn compile_functions_to_wasm(
    module_name: &str,
    functions: &[VerifiableFunction],
) -> Result<Vec<u8>, WasmCompileError> {
    let module = lower_to_trust_ir_functions(module_name, functions)
        .map_err(|e| WasmCompileError::TrustIrLowering(e.to_string()))?;
    compile_trust_ir_module_to_wasm(&module)
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{BinOp, Ty};
    use trust_ir_build::ModuleBuilder;

    /// A trust-ir module with `add(a, b) = a + b` over i32.
    fn add_module() -> TrustIrModule {
        let mut mb = ModuleBuilder::new("m");
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("add", ft);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I32);
        let b = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let r = fb.binop(BinOp::Add, Ty::I32, a, b);
        fb.ret(vec![r]);
        fb.build();
        mb.build()
    }

    #[test]
    fn module_front_door_emits_valid_wasm_header() {
        let bytes = compile_trust_ir_module_to_wasm(&add_module()).unwrap();
        assert!(bytes.len() > 8, "module too short");
        assert_eq!(
            &bytes[..8],
            &[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00],
            "wasm magic + version"
        );
    }
}
