//! trust_ir_codegen: feature-gated OBSERVATIONAL CODEGEN PROBE (Step 2).
//!
//! This module realizes "trust-ir first" *observationally* on the real
//! functions the backend compiles. It is a pure composition of the two
//! already-proven seams:
//!
//! 1. `trust_ir_emission::emit_trust_ir_module` (the Step-1 adapter,
//!    `&[VerifiableFunction]` -> `trust_ir::Module`), and
//! 2. `trust_cg_bridge::lower_module_to_lir`
//!    (`trust_ir::Module` -> LIR `Function`, fail-closed `ModuleLirError`).
//!
//! For each function in the emitted Module it runs the Module->LIR converter
//! and LOGS whether the converter handled it (`Ok`, with the produced LIR
//! instruction count) or fell closed (`Err(ModuleLirError)`, with the
//! unsupported-shape variant). It tallies handled vs fail-closed for the CGU.
//!
//! # Drop-in safety / observational contract
//!
//! Everything here is reachable only behind the off-by-default
//! `trust-ir-codegen` cargo feature (which implies `trust-ir-emission`). It
//! NEVER feeds the converter's LIR back into emission and NEVER refuses on a
//! converter failure: the shipped production path (VF -> LIR -> object,
//! `trust_cg_bridge::codegen_backend`) is completely untouched. With the
//! feature OFF this module is not compiled into the backend dylib at all, so
//! codegen is byte-for-byte unchanged.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_ir::Module;

/// Drive the proven `trust_ir::Module` -> LIR converter over every function in
/// `module`, log per-function Ok/Err, and return `(handled, fail_closed)`.
///
/// Purely observational: the produced LIR is measured (instruction count) and
/// then dropped. The function never errors out — a converter `Err` is the
/// expected, informative outcome for any shape outside the converter's current
/// real-code coverage, and is logged, not propagated.
pub(crate) fn probe_module_to_lir(cgu_name: &str, module: &Module) -> (usize, usize) {
    let mut handled = 0usize;
    let mut fail_closed = 0usize;

    for function in &module.functions {
        match trust_cg_bridge::lower_module_to_lir(module, function.id) {
            Ok(lir) => {
                handled += 1;
                let lir_instrs: usize = lir.blocks.values().map(|b| b.instructions.len()).sum();
                tracing::info!(
                    cgu = %cgu_name,
                    function = %function.name,
                    lir_instructions = lir_instrs,
                    "[trust_cg] trust-ir->LIR converter HANDLED function"
                );
            }
            Err(e) => {
                fail_closed += 1;
                tracing::info!(
                    cgu = %cgu_name,
                    function = %function.name,
                    variant = module_lir_error_variant(&e),
                    detail = %e,
                    "[trust_cg] trust-ir->LIR converter FAIL-CLOSED on function"
                );
            }
        }
    }

    tracing::info!(
        cgu = %cgu_name,
        functions = module.functions.len(),
        handled,
        fail_closed,
        "[trust_cg] trust-ir->LIR converter coverage (observational; production path unaffected)"
    );

    (handled, fail_closed)
}

/// Stable discriminant name for a `ModuleLirError`, for structured logs /
/// coverage aggregation. Mirrors the variant identifiers so a log scan can
/// bucket fail-closed reasons without parsing the human message.
fn module_lir_error_variant(e: &trust_cg_bridge::ModuleLirError) -> &'static str {
    use trust_cg_bridge::ModuleLirError as E;
    match e {
        E::MissingFunction(_) => "MissingFunction",
        E::MissingFuncType { .. } => "MissingFuncType",
        E::NoBlocks { .. } => "NoBlocks",
        E::MissingBlock { .. } => "MissingBlock",
        E::EdgeArgArity { .. } => "EdgeArgArity",
        E::UnsupportedSwitchCase { .. } => "UnsupportedSwitchCase",
        E::MalformedControlFlow { .. } => "MalformedControlFlow",
        E::BlockParamArity { .. } => "BlockParamArity",
        E::UnsupportedType { .. } => "UnsupportedType",
        E::UnsupportedInst { .. } => "UnsupportedInst",
        E::UnsupportedBinOp { .. } => "UnsupportedBinOp",
        E::UnsupportedConstant { .. } => "UnsupportedConstant",
        E::UndefinedValue { .. } => "UndefinedValue",
        E::MalformedReturn { .. } => "MalformedReturn",
        E::UnsupportedSignature { .. } => "UnsupportedSignature",
        E::NonLocalPointer { .. } => "NonLocalPointer",
        E::UnsupportedMemory { .. } => "UnsupportedMemory",
        E::UninlinableCall { .. } => "UninlinableCall",
        // `ModuleLirError` is `#[non_exhaustive]`; a future variant logs as
        // "Other" rather than failing to compile here.
        _ => "Other",
    }
}
