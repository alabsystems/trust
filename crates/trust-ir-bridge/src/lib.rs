//! trust-ir-bridge: MIR-compatibility bridge into typed Trust-IR.
//!
//! Converts the legacy MIR-derived `trust_types::VerifiableFunction` view into
//! Trust-IR for compatibility backends, differential oracles, and migration.
//! Source frontends must produce Trust-IR directly: Rust uses
//! `trust-thir-lower`; Lean/Clean uses `clean-compiler::emit_trust_ir`. This
//! crate is not an alternative source frontend, and a module produced here is
//! not the shared Rust/Clean source module. Ratified migration rule P9 retains
//! current MIR proving routes until the direct/router routes are
//! capability-equivalent; this crate makes that compatibility boundary explicit.
//!
//! This is a pure translation layer -- no analysis, no optimization. Maps Trust
//! MIR concepts to TrustIr equivalents. Where there's no 1:1 mapping, the gap is
//! documented and the closest approximation is used.
//!
//! ## Design decisions
//!
//! - **TrustIr uses SSA values (ValueId), Trust uses place-based locals.** Each
//!   trust-types local gets a TrustIr ValueId. Place projections (field, index, deref)
//!   are lowered to TrustIr `ExtractField`, `ExtractElement`, or `Load` instructions.
//!
//! - **TrustIr preserves integer signedness.** Rust signed and unsigned integer
//!   types map to distinct TrustIr `I*` and `U*` types, while operations still
//!   carry signedness where semantics require it.
//!
//! - **TrustIr uses Overflow instructions for checked ops.** trust-types
//!   `CheckedBinaryOp` maps to `Inst::Overflow` which produces (value, bool).
//!
//! - **Contracts/specs are lowered to TrustIr ProofAnnotations and ProofObligations.**
//!   Requires -> Precondition, Ensures -> Postcondition.
//!
//! - **Binary symbolic formulas remain distinguishable from `Undef`.** TrustIr has
//!   no first-class `Formula` instruction today, so `Operand::Symbolic` lowers
//!   to a typed `trust_symbolic.formula` dialect op carrying round-trippable
//!   formula JSON plus SMT-LIB/sort/debug attributes. Downstream passes can
//!   reject or interpret that op explicitly instead of accidentally treating the
//!   value as an unconstrained `Undef`.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![forbid(unsafe_code)]
#![allow(clippy::module_name_repetitions)]

mod cache_key;
// trust-ir-spine VERDICT FLIP: make trust-ir the verdict source of record for
// L0 safety obligations, verdict-identically (see `flip.rs`).
mod flip;
mod layout_evidence;
mod lower;
mod native_request;
mod parity;
mod provenance;
pub mod trust_wp_claim;
// Phase-2 prototype: trust-ir-native VC generation, shadow mode. See
// `vcgen_proto.rs` and `docs/TRUST_IR_SPINE.md` Phase 2.
mod vcgen_proto;
// Phase-2 prototype: trust-ir-native L1 CONTRACT VC generation (pre/post,
// invariants, refinements). Walks `module.proof_obligations` rather than the
// function instruction nodes the L0 `vcgen_proto` walks. See
// `contract_vcgen_proto.rs` and `docs/TRUST_IR_SPINE.md` Phase 2 (L1).
mod contract_vcgen_proto;

pub use cache_key::module_stable_content_hash;
pub use flip::{
    flip_contract_verdicts_to_spine, flip_contract_verdicts_with_module,
    flip_safety_verdicts_to_spine, flip_safety_verdicts_with_module,
    generate_native_or_flip_safety_vcs, FlipDecision, FlipReport, NativeGenOutcome,
};
pub use layout_evidence::{
    TRUST_IR_LAYOUT_EVIDENCE_BLOCKER_FEATURE, TRUST_IR_LAYOUT_EVIDENCE_BLOCKER_STAGE,
    TRUST_IR_LAYOUT_EVIDENCE_COMMIT, TrustIrLayoutSensitiveCastBlocker,
    collect_layout_sensitive_cast_blockers, ensure_layout_sensitive_cast_evidence,
};
pub use lower::{
    BinOpMapping, BridgeError, NativeBoolPredSummary, SYMBOLIC_AGGREGATE_ATTR_FIELD_COUNT,
    SYMBOLIC_AGGREGATE_ATTR_KIND, SYMBOLIC_AGGREGATE_OP, SYMBOLIC_FORMULA_ATTR_CONTEXT,
    SYMBOLIC_FORMULA_ATTR_DEBUG, SYMBOLIC_FORMULA_ATTR_JSON, SYMBOLIC_FORMULA_ATTR_SCHEMA,
    SYMBOLIC_FORMULA_ATTR_SMTLIB, SYMBOLIC_FORMULA_ATTR_SORT, SYMBOLIC_FORMULA_DIALECT,
    SYMBOLIC_FORMULA_OP, SYMBOLIC_MEMORY_STATE_OP, TRUST_OBLIGATION_SOURCE_SCHEMA,
    generate_native_safety_vcs, lower_functions_to_trust_ir, lower_to_trust_ir,
    lower_to_trust_ir_function, lower_to_trust_ir_functions,
    lower_to_trust_ir_functions_with_abi_total_context,
    lower_to_trust_ir_functions_with_assumed_total_context,
    lower_to_trust_ir_functions_with_context, lower_to_trust_ir_functions_with_expected_absent,
    map_binop, map_type, map_unop, NativeCalleeSummaryContext, NativeCalleeSummaryGuard,
    verifiable_function_lowers_in_module_context,
};
#[cfg(feature = "compiler-context")]
pub use lower::lower_to_trust_ir_functions_with_compiler_context;
// Explicit names for production call sites that still require the MIR migration
// adapter. The historical short names remain for API compatibility, but new
// compiler code should make this boundary visible in its spelling.
pub use lower::{
    lower_to_trust_ir as lower_mir_compat_to_trust_ir,
    lower_to_trust_ir_functions as lower_mir_compat_functions_to_trust_ir,
    lower_to_trust_ir_functions_with_context as lower_mir_compat_functions_to_trust_ir_with_context,
};
pub use native_request::{
    NativeVerificationBundleBuildError, TRUST_NATIVE_REQUEST_TRANSFORM_VERSION,
    native_verification_bundle_from_module,
};
pub use parity::{
    ObligationKindSummary, lowered_obligation_summary, obligation_count, obligation_kind_summary,
};
// Phase-2 prototype: trust-ir-native VC generation (shadow mode).
pub use vcgen_proto::{
    safety_obligations_from_trust_ir_module, safety_vcs_from_trust_ir, TrustIrSafetyObligation,
    TrustIrSafetyVc,
};
// Phase-2 prototype: trust-ir-native L1 contract VC generation (shadow mode).
pub use contract_vcgen_proto::{contract_vcs_from_trust_ir, TrustIrContractVc};
pub use provenance::{
    BINARY_PROVENANCE_ATTR_ARTIFACT_SHA256, BINARY_PROVENANCE_ATTR_BINARY_PATH,
    BINARY_PROVENANCE_ATTR_BLOCK_ID, BINARY_PROVENANCE_ATTR_ENCODING,
    BINARY_PROVENANCE_ATTR_FUNCTION_ENTRY, BINARY_PROVENANCE_ATTR_FUNCTION_NAME,
    BINARY_PROVENANCE_ATTR_INSTRUCTION_ADDRESS, BINARY_PROVENANCE_ATTR_INSTRUCTION_BYTES,
    BINARY_PROVENANCE_ATTR_INSTRUCTION_SIZE, BINARY_PROVENANCE_ATTR_PROVENANCE_STATUS,
    BINARY_PROVENANCE_ATTR_RECORD_DIGEST, BINARY_PROVENANCE_ATTR_SCHEMA,
    BINARY_PROVENANCE_ATTR_SELECTED_IMAGE_FILE_OFFSET,
    BINARY_PROVENANCE_ATTR_SELECTED_IMAGE_FILE_SIZE, BINARY_PROVENANCE_ATTR_SELECTED_IMAGE_SHA256,
    BINARY_PROVENANCE_ATTR_SOURCE, BINARY_PROVENANCE_ATTR_SOURCE_COL_END,
    BINARY_PROVENANCE_ATTR_SOURCE_COL_START, BINARY_PROVENANCE_ATTR_SOURCE_FILE,
    BINARY_PROVENANCE_ATTR_SOURCE_LINE_END, BINARY_PROVENANCE_ATTR_SOURCE_LINE_START,
    BINARY_PROVENANCE_ATTR_SOURCE_STATUS, BINARY_PROVENANCE_ATTR_STATEMENT_INDEX,
    BINARY_PROVENANCE_ATTR_TARGET_SEMANTICS_CONSUMED, BINARY_PROVENANCE_DIALECT,
    BINARY_PROVENANCE_OP, BINARY_PROVENANCE_SCHEMA, BINARY_PROVENANCE_STATUS_AMBIGUOUS,
    BINARY_PROVENANCE_STATUS_CHECKED_EXACT, BINARY_PROVENANCE_STATUS_UNAVAILABLE,
    CanonicalBinaryProvenanceAcceptance, CanonicalBinaryProvenanceRecord,
    CanonicalBinaryProvenanceRejection, CanonicalBinaryProvenanceReport,
    attach_decompilation_binary_provenance, canonical_binary_provenance_target_blockers,
    collect_canonical_binary_provenance, lower_decompilation_artifact_to_trust_ir,
};
pub use trust_ir::{
    TrustVcNativeRequest, TrustVcRequestOptions, TrustVcVerificationMode,
    NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION, NativeAdapterInput, NativeAssertionId,
    NativeBundleProducer, NativeDiagnosticsPolicy, NativeObligationCause, NativeObligationSource,
    NativeRequestId, NativeRequestProvenance, NativeToolIdentity, NativeVerificationBundle,
    NativeVerificationBundleError, NativeVerificationRequest, ProofDigest, TrustWpNativeRequest,
    TrustWpRequestOptions, TrustWpVerificationMode, TrustMcChcOptions, TrustMcNativeRequest,
    TrustMcRequestOptions, TrustMcVerificationMode,
};

#[cfg(test)]
mod tests;

// Per-phase flat-tax measurement (lower vs vcgen) over the committed fixtures;
// grounds the warm-rebuild artifact-cache economics. Prints under
// TRUST_FLAT_TAX_MEASURE=1.
#[cfg(test)]
mod flat_tax_measure;

// Trust: curated soundness+completeness oracle for the bridge call-summary decision
// (rung-1 precision frontier + false-proof regression guard).
#[cfg(test)]
mod call_summary_oracle;
