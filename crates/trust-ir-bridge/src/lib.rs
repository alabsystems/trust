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

// Trust (job L1 / A-LIN): artifact-lineage attestation — the digest chain that
// makes the per-body module the flip consumes, the assembled crate artifact a
// proof pins, and the MIR re-derived at the flip provably the SAME OBJECT.
pub mod artifact_lineage;
// trust-ir-spine VERDICT FLIP: make trust-ir the verdict source of record for
// L0 safety obligations, verdict-identically (see `flip.rs`).
mod flip;
mod layout_evidence;
/// The bridge's def-counting seam — nothing else may scan `body.blocks` for a
/// local's definitions (see the module doc).
mod local_defs;

/// The bridge's single-value question, exposed for the shared-definition regression.
#[doc(hidden)]
pub fn local_defs_holds_one_value_for_test(
    func: &trust_types::VerifiableFunction,
    local: usize,
) -> bool {
    local_defs::holds_one_value(func, local)
}

/// The bridge's resolver, exposed for the same regression.
#[doc(hidden)]
pub fn local_defs_unique_value_def_is_some_for_test(
    func: &trust_types::VerifiableFunction,
    local: usize,
) -> bool {
    local_defs::unique_value_def(func, local).is_some()
}

/// Exact answers, so the regression checks the chosen definition as well as
/// admission. Both consumers use the shared reducer while retaining their own
/// traversal and escape classification.
#[doc(hidden)]
pub fn local_defs_exact_for_test(
    func: &trust_types::VerifiableFunction,
    local: usize,
) -> (trust_types::ValueCount, Option<&trust_types::Rvalue>, Option<&trust_types::Terminator>) {
    let summary = local_defs::summarize(func, local);
    let call = summary
        .unique_value_call_index(&func.body)
        .map(|block| &func.body.blocks[block].terminator);
    (summary.value_count(), summary.unique_value_def().map(|(_, value)| value), call)
}
mod lower;
// Trust (C1, 2026-11-06): source reference sites recorded before type erasure.
mod source_reference_sites;
#[doc(hidden)]
pub use lower::{local_stability_for_test, native_math_stability_for_test};
mod physical_body_walk;
#[cfg(test)]
mod physical_enum_tests;
#[cfg(test)]
mod physical_struct_construction_tests;
mod physical_types;
#[cfg(test)]
mod physical_types_tests;
// Obligation-birth cutover SCORECARD (Stage C/D entry instrument): per-class
// aggregation of the flip's NativeGenOutcome into a measured artifact. The
// corpus walk lives in examples/ (it needs the trust-vcgen dev-dependency).
pub mod native_gen_scorecard;
mod native_request;
mod native_shadow_request;
mod parity;
mod provenance;
// STEP 6 (docs/design/DIRECT-LANE-PROOF-AUTHORITY.md, increment 1): the
// direct-lane typed L0 safety-formula mint — single source of truth,
// delegating to lower.rs's own reconstruct_* builders — plus its byte-or-
// decline parity oracle (#[cfg(test)]).
pub mod safety_formulas;
// STEP 6 increment 2: the production-dump schema/writer/fail-closed parser
// shared by the installer seam (trust-thir-lower) and the grader below, and
// the hoisted grading core both the model oracle and grade_real_records use.
pub mod direct_formula_dump;
pub mod direct_record_grading;
pub mod direct_set_parity;
pub mod trust_wp_claim;
// Phase-2 prototype: trust-ir-native VC generation, shadow mode. See
// `vcgen_proto.rs` and `docs/TRUST_IR_SPINE.md` Phase 2.
mod vcgen_proto;
// Phase-2 prototype: trust-ir-native L1 CONTRACT VC generation (pre/post,
// invariants, refinements). Walks `module.proof_obligations` rather than the
// function instruction nodes the L0 `vcgen_proto` walks. See
// `contract_vcgen_proto.rs` and `docs/TRUST_IR_SPINE.md` Phase 2 (L1).
mod contract_vcgen_proto;

// trust-ir v50 uniform arrays: the ONE spelling rule for `[x; N]` and a uniform array's
// sub-array, shared with the THIR producer so the differential pairs one spelling.
pub mod uniform_array;

pub use artifact_lineage::{
    BodyLineage, BuildIdentity, CalleeIdentity, CalleeRemap, CrateLineage, LineageError,
    RemapCertificate, callee_ledger_digest, verify_covered_by_artifact, verify_flip_lineage,
};
// Phase-2 prototype: trust-ir-native L1 contract VC generation (shadow mode).
pub use contract_vcgen_proto::{TrustIrContractVc, contract_vcs_from_trust_ir};
pub use flip::{
    FlipDecision, FlipReport, NativeGenOutcome, ObligationKey, ObligationSetDiff,
    flip_contract_verdicts_to_spine, flip_contract_verdicts_with_module,
    flip_safety_verdicts_to_spine, flip_safety_verdicts_with_module,
    generate_native_or_flip_safety_vcs, generate_native_or_flip_safety_vcs_with_discharged,
    generate_native_or_flip_safety_vcs_with_module,
    generate_native_or_flip_safety_vcs_with_reachability, l0_obligation_set_diff,
    l0_obligation_set_diff_with_discharged,
};
pub use layout_evidence::{
    TRUST_IR_LAYOUT_EVIDENCE_BLOCKER_FEATURE, TRUST_IR_LAYOUT_EVIDENCE_BLOCKER_STAGE,
    TRUST_IR_LAYOUT_EVIDENCE_COMMIT, TrustIrLayoutSensitiveCastBlocker,
    collect_layout_sensitive_cast_blockers, ensure_layout_sensitive_cast_evidence,
};
pub use lower::{
    BinOpMapping, BridgeError, CallReachWithdrawals, CompilerAllocGrowPins,
    CoroutineResumeContractModuleEvidence, CoroutineUpvarFramesGuard, DROP_REACH_UNDECIDED,
    InstanceHypothesisSites, ModuleContextProbe, NativeBoolPredSummary, NativeCalleeSummaryContext,
    NativeCalleeSummaryGuard, OwnedSequenceAccess, SYMBOLIC_AGGREGATE_ATTR_FIELD_COUNT,
    SYMBOLIC_AGGREGATE_ATTR_KIND, SYMBOLIC_AGGREGATE_OP, SYMBOLIC_FORMULA_ATTR_CONTEXT,
    SYMBOLIC_FORMULA_ATTR_DEBUG, SYMBOLIC_FORMULA_ATTR_JSON, SYMBOLIC_FORMULA_ATTR_SCHEMA,
    SYMBOLIC_FORMULA_ATTR_SMTLIB, SYMBOLIC_FORMULA_ATTR_SORT, SYMBOLIC_FORMULA_DIALECT,
    SYMBOLIC_FORMULA_OP, SYMBOLIC_MEMORY_STATE_OP, SurvivorProbe, SurvivorProbeStats,
    SurvivorRound, TRUST_OBLIGATION_SOURCE_SCHEMA, callee_is_recognized_total_no_panic,
    callee_is_slice_sort_comparator_family, closure_body_is_total_ord_key_comparator,
    closure_driving_consumer_call, coroutine_resume_contract_module_evidence,
    fmt_format_call_is_total, generate_native_safety_vcs, generate_native_safety_vcs_with_module,
    generate_native_safety_vcs_with_reachability, is_diverging_panic_site_obligation_description,
    is_panicking_primitive_int_div_method, is_vec_index_removal_method_path,
    lower_functions_to_trust_ir, lower_to_trust_ir, lower_to_trust_ir_function,
    lower_to_trust_ir_functions, lower_to_trust_ir_functions_with_abi_total_context,
    lower_to_trust_ir_functions_with_assumed_total_context,
    lower_to_trust_ir_functions_with_context, lower_to_trust_ir_functions_with_expected_absent,
    map_binop, map_type, map_unop, pin_enum_tag_lane, verifiable_function_lowers_in_module_context,
};
// Trust (bundled-member derived preconditions — the bundled-Assert remedy):
// the entry-prefix div/rem/bounds requires derivation and its fail-closed
// admission classification for would-be-bundled members, plus the exact
// recognizer that tells the extractor's always-true integer type-range
// invariant apart from a DECLARED member contract (the gate's "contract-less
// only" arm must refuse the second and only the second).
pub use lower::{
    BundledConstructorCallSite,
    BundledConstructorSafetySite,
    BundledMemberAssertAdmission,
    // Trust (2026-09-29): the typed class of a `Refused` admission, which the
    // compiler's bundled std-member disposition reads instead of the reason text.
    MemberAssertRefusalClass,
    bundled_constructor_call_sites,
    bundled_constructor_formal_names,
    bundled_constructor_local_safety_sites,
    bundled_constructor_rebind_requirement,
    bundled_member_assert_admission,
    // Trust (BoundsCheck lane): the CALL-SITE half of the derived-charge
    // discipline — the derived `<formal>__slice_len` spelling is substituted
    // conditionally, not unconditionally, so the gate must check each regenerated
    // caller-side row for a surviving member name rather than assume totality.
    derived_member_length_var_survives,
    member_entry_prefix_assert_requires,
    member_precondition_is_integer_param_type_range,
};
#[cfg(feature = "compiler-context")]
pub use lower::{
    lower_compiler_relaxed_xadd_u64_body, lower_to_trust_ir_functions_with_compiler_context,
    lower_to_trust_ir_functions_with_instance_hypothesis_context,
};
// Explicit names for production call sites that still require the MIR migration
// adapter. The historical short names remain for API compatibility, but new
// compiler code should make this boundary visible in its spelling.
pub use lower::{
    lower_to_trust_ir as lower_mir_compat_to_trust_ir,
    lower_to_trust_ir_functions as lower_mir_compat_functions_to_trust_ir,
    lower_to_trust_ir_functions_with_context as lower_mir_compat_functions_to_trust_ir_with_context,
};
pub use native_request::{
    NativeBundleOwner, NativeVerificationBundleBuildError, TRUST_NATIVE_REQUEST_TRANSFORM_VERSION,
    native_verification_bundle_from_module, native_verification_bundle_from_module_owners,
    trust_mc_chc_request_options,
};
#[cfg(any(test, feature = "direct-contract-shadow"))]
mod direct_contract_shadow;
#[cfg(any(test, feature = "direct-contract-shadow"))]
pub use direct_contract_shadow::{
    DirectContractShadowQuestion, direct_contract_shadow_verification_bundle,
};
pub use native_shadow_request::{
    DIRECT_SHADOW_ADMITTED_SOURCE_ID, DIRECT_SHADOW_NON_APPLYING_CHECKS,
    DIRECT_SHADOW_PUBLIC_ID_PREFIX, DIRECT_SHADOW_WIRE_DISCLOSURE, DirectOwnerIneligibility,
    DirectShadowBundle, DirectShadowBundleBuildError, DirectShadowLineageDisclosure,
    TRUST_DIRECT_SHADOW_TRANSFORM_VERSION, direct_shadow_verification_bundle_from_module,
};
pub use parity::{
    ObligationKindSummary, lowered_obligation_summary, obligation_count, obligation_kind_summary,
};
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
pub use source_reference_sites::{
    LoweredSourceReferenceSites, ReconciledSourceReferenceLoad, ReconciledSourceReferenceParameter,
    ReconciledSourceReferenceSites, ReconciledSourceReferenceValue,
};
pub use trust_ir::{
    NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION, NativeAdapterInput, NativeAssertionId,
    NativeBundleProducer, NativeDiagnosticsPolicy, NativeObligationCause, NativeObligationSource,
    NativeRequestId, NativeRequestProvenance, NativeToolIdentity, NativeVerificationBundle,
    NativeVerificationBundleError, NativeVerificationRequest, ProofDigest,
    SourceGenerationAuthority, SourceGenerationAuthorityMintError, TrustMcChcOptions,
    TrustMcNativeRequest, TrustMcRequestOptions, TrustMcVerificationMode, TrustVcNativeRequest,
    TrustVcRequestOptions, TrustVcVerificationMode, TrustWpNativeRequest, TrustWpRequestOptions,
    TrustWpVerificationMode,
};
// Phase-2 prototype: trust-ir-native VC generation (shadow mode).
pub use vcgen_proto::{
    TrustIrSafetyObligation, TrustIrSafetyVc, safety_obligations_from_trust_ir_module,
    safety_vcs_from_trust_ir,
};

#[cfg(test)]
mod tests;

// DIVERGE-ANCHOR-1 / DIVERGE-ENTRY-1: the diverging-site arm takes its encoding only
// for a callee whose `callee_key` carries the extractor's `diverging_entry` stamp (a
// real sysroot crate, not a trait item, the generic-free definition path). Also hosts
// the key helpers the older diverging-site fixtures use.
#[cfg(test)]
mod diverging_site_anchor_tests;

// CLOSURE-ABSENT-CALLEE (fix6): a `Fn*::call*` shim whose closure body is not in
// the bundle lowers as a fail-closed absent callee with its capture effects havocked.
#[cfg(test)]
mod absent_closure_body_tests;

// BMC-LANE-1: the one-field newtype cast and the empty array, each one complete
// constructor that the reference interpreter runs.
#[cfg(test)]
mod complete_constructor_cast_tests;

// R146-SPELLING-1: the integer cast into `Option<NonZero<..>>` is one stamped
// havoc under every spelling the extractor writes, on both lanes.
#[cfg(test)]
mod r146_option_nonzero_cast_tests;

// Trust: curated soundness+completeness oracle for the bridge call-summary decision
// (rung-1 precision frontier + false-proof regression guard).
#[cfg(test)]
mod call_summary_oracle;

// Trust: STEP-4 coverage ratchet (docs/design/2026-08-19-verified-sysroot-scoping.md
// §5 step 4 — "a coverage ratchet so the number can only go up"): pins the
// verified core::num function count N and its discharged-L0-obligation count
// against the committed floor + snapshot pair under fixtures/std-coverage/.
// Test-only measurement plumbing; grants no verification authority.
#[cfg(test)]
mod std_core_num_coverage_ratchet;
