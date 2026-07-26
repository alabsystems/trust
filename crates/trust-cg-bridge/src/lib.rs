//! trust-cg-bridge: Bridge between trust-types VerifiableFunction and trust_cg LIR
//!
//! Converts trust-types IR (VerifiableFunction, BasicBlock, Statement, Terminator)
//! into trust_cg LIR (Function, BasicBlock, Instruction) for verified code generation.
//!
//! Scope: scalars, aggregates (tuples/ADTs/arrays), function calls, memory
//! operations (load/store/stack slots), casts, drops, and discriminants.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// Trust: FxHashMap for internal maps; std HashMap only where required by trust_cg-lower API
#![allow(clippy::module_name_repetitions)]

// Trust: #828 — validation of lowered LIR for structural consistency.
pub mod validation;

// Trust: M-POS — the reusable PROVEN-OUTPUT GATE. Promotes the auto-spec
// interpreter + symbolic-exec prover + ay discharge out of the
// `tests/proven_output_autospec.rs` test file into a library API
// (`verify_output_preserved` / `OutputVerdict`) a targo/codegen integration
// calls to REFUSE emitting a function whose output is not proven-correct.
// Wiring into the rustc_codegen_trust_cg dylib + bootstrap is a follow-on.
#[cfg(feature = "ay-proofs")]
pub mod verify_output;
// Trust: B4 — the O(1) structured-instantiation [PROVED] path (additive fast
// path for the proven-output gate; gated on `kernel-recheck`).
#[cfg(feature = "kernel-recheck")]
pub mod verify_output_instantiate;

// Trust: #829 — CodegenBackend scaffold for trust_cg integration.
pub mod codegen_backend;

// Trust: #1032 — safe binary-derived TrustIr to trust_cg LIR conversion contract.
pub mod binary_conversion;

// Trust: the "trust-ir first" codegen seam — trust_ir::Module -> LIR, feeding
// the EXISTING verified LIR -> object emitter. Additive, fail-closed scalar
// slice (Const/BinOp/ICmp/Return over integer scalars).
pub mod module_to_lir;

// Trust: #948 — split monolithic lib.rs into focused modules.
mod lift;
mod lower;
pub(crate) mod mapping;

#[cfg(test)]
mod tests;

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors during trust-types to trust_cg LIR conversion.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum BridgeError {
    #[error("unsupported type: {0}")]
    UnsupportedType(String),

    #[error("unsupported operation: {0}")]
    UnsupportedOp(String),

    #[error("missing block: bb{0}")]
    MissingBlock(usize),

    #[error("missing local: _{0}")]
    MissingLocal(usize),

    #[error("empty function body: no basic blocks")]
    EmptyBody,

    #[error("invalid MIR: {0}")]
    InvalidMir(String),
}

// ---------------------------------------------------------------------------
// Public API re-exports
// ---------------------------------------------------------------------------

pub use binary_conversion::{
    BinaryTrustCgCheckedCertificateEvidence, BinaryTrustCgConversion, BinaryTrustCgConversionError,
    BinaryTrustCgProofBindingInput, BinaryTrustCgProofConsumerEvidence, BinaryTrustCgProofConsumerRecord,
    BinaryTrustCgProofConsumerStatus, BinaryTrustCgProofReplayEvidence, BinaryTrustCgSymbolicFormula,
    BinaryTrustCgSymbolicFormulaEvidence, BinaryTrustCgTargetProofBinding,
    BinaryTrustCgUnsupportedLedgerEvidence, BinaryTrustCgValidationBlocker,
    BinaryTrustCgValidationStatus, CanonicalTrustCgConversion, lower_binary_decompiled_function_to_lir,
    lower_binary_trust_ir_to_lir, lower_canonical_trust_ir_to_lir,
};
pub use lift::lift_from_lir;
pub use lower::{
    LoweringOptions, PanicRuntimeSymbols, lower_body_to_lir, lower_body_to_lir_with_options,
    lower_to_lir, lower_to_lir_with_options,
};
pub use mapping::{map_binop, map_float_binop, map_type, map_unop};
pub use module_to_lir::{
    ModuleLirError, lower_module_to_lir, lower_trust_ir_function_to_lir,
    lower_trust_ir_function_to_lir_real_calls,
};
