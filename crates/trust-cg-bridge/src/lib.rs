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

// Shared integration fixtures must call this unit build, not a stale rlib.
#[cfg(test)]
extern crate self as trust_cg_bridge;

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
// Trust: F1 — the SAME proven-output gate with its SPECIFICATION SIDE derived
// from the producer's `trust_ir::Function` instead of from a MIR-shaped
// `VerifiableFunction`. This is what lets `-Ztrust-cg-frontend=trust-ir` be
// GATED rather than emitted unverified.
/// Complete, bounded Compiler CER input data; no decoding or replay admission authority.
#[cfg(feature = "ay-proofs")]
pub mod compiler_input_capture;

#[cfg(feature = "ay-proofs")]
pub mod archive_object;
/// Bounded, diagnostic retention and source-bound replay of actual object evidence.
#[cfg(feature = "ay-proofs")]
pub mod object_replay;
/// Compact retained original CIC packets; decoding does not grant proof authority.
#[cfg(feature = "ay-proofs")]
pub mod original_conjunction_certificate;
#[cfg(feature = "ay-proofs")]
pub mod verify_output_trust_ir;
/// Conditional exact-original register observations; never compiler admission.
#[cfg(feature = "ay-proofs")]
pub mod direct_ir_observation;
// Trust (increment 5, step 5.2): the CALL-EVENT REFINEMENT gate core over the
// object trust-cg's `Compiler::compile` ships — the AArch64 Mach-O/ELF readers
// (obligation O1, no solver, so not feature-gated) and the per-function
// call-event refinement with its certificates and closure report (O0-O5).
// Nothing in the compiler path calls it yet (F1 wiring is step 5.4).
#[cfg(feature = "ay-proofs")]
pub mod call_event;
// Shared model frontier for relocatable-object execution; no placed-image authority.
#[cfg(feature = "ay-proofs")]
pub(crate) mod pc_object_model;
// PTR.3b term builders only; not a CER verdict or shipping authority.
#[cfg(feature = "ay-proofs")]
pub mod cer_memory;
// PTR.3b decoded memory observations; pending until actual CER coverage integration.
#[cfg(feature = "ay-proofs")]
pub mod cer_memory_machine;
pub mod compiled_object;
/// Runtime scalar register-bank classification; no source witness or proof placement.
pub mod source_scalar_abi;
#[cfg(feature = "ay-proofs")]
pub mod compiler_frame_inputs;
/// Conditional actual pair-step evidence; does not participate in shipping.
#[cfg(feature = "frame-step-reference")]
pub mod frame_step_evidence;
// Trust (increment 5, step 5.4.1): F1's SHIPPING CONSUMER for the compiler lane
// — `Compiler::compile` under the D31 license, the call-event gate on its own
// 16 MiB thread, and the object handed out only when `CerReport::ships` allows
// it. No rustc lane calls it until step 5.4.2.
#[cfg(feature = "ay-proofs")]
pub mod f1_compile;
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

// Trust (R-5 groundwork): trust-cg's `Compiler::compile` reached from the
// superproject. MEASUREMENT / TEST API ONLY — no rustc lane calls it, and its
// census test fails if one starts to (see the module doc).
pub mod compiler_consumer;

// Trust: function-entry register bindings for binary-lifted bodies — the
// per-block write-freedom certificate and the byte-assembled load recognizer
// behind the real Opcode::Load lowering.
pub mod entry_binding;

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
    BinaryTrustCgProofBindingInput, BinaryTrustCgProofConsumerEvidence,
    BinaryTrustCgProofConsumerRecord, BinaryTrustCgProofConsumerStatus,
    BinaryTrustCgProofReplayEvidence, BinaryTrustCgSymbolicFormula,
    BinaryTrustCgSymbolicFormulaEvidence, BinaryTrustCgTargetProofBinding,
    BinaryTrustCgUnsupportedLedgerEvidence, BinaryTrustCgValidationBlocker,
    BinaryTrustCgValidationStatus, CanonicalTrustCgConversion,
    lower_binary_decompiled_function_to_lir,
    lower_binary_decompiled_function_to_lir_with_entry_bindings, lower_binary_trust_ir_to_lir,
    lower_binary_trust_ir_to_lir_with_entry_bindings, lower_canonical_trust_ir_to_lir,
};
pub use entry_binding::{
    BinaryEntryBindings, BinaryEntryParam, BindingArch, ConsumedSymbolicLowering,
};
pub use lift::lift_from_lir;
/// trust-cg's canonical storage type for a flat byte/relocation data image. Re-exported for
/// the rustc plugin's compiler lane, which types a `core::panic::Location` record with it
/// (PKG-CP), so a record is spelled exactly as trust-cg's own importers spell one.
pub use trust_cg_lower::global_image;
pub use lower::{
    LoweringOptions, PanicRuntimeSymbols, lower_body_to_lir, lower_body_to_lir_with_options,
    lower_to_lir, lower_to_lir_with_options,
};
pub use mapping::{map_binop, map_float_binop, map_type, map_unop};
pub use module_to_lir::{
    AbiArgExtension, AbiParamExtensions, AbiPassModeCrossCheck, ModuleLirError,
    UnfaithfulAssertSite, function_has_unfaithful_assert, lower_module_to_lir,
    lower_module_to_lir_maybe_cross_checked, lower_module_to_lir_with_abi_cross_check,
    lower_trust_ir_function_to_lir, lower_trust_ir_function_to_lir_real_calls,
    lower_trust_ir_function_to_lir_real_calls_with_abi_cross_check,
    lower_trust_ir_function_to_lir_with_abi_cross_check, unfaithful_assert_site,
};
