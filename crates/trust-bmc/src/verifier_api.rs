//! Adapter from trust_mc into the public `trust-verifier-api` engine surface.
//!
//! This module is deliberately fail-closed. The public API deals in
//! `TrustContractBundle` obligations. A positive proof additionally requires a
//! freshly validated native TrustIr bundle and the live, non-serializable opaque
//! authority returned for that exact module; structured typed input and native
//! metadata alone remain reconstructible candidates. The adapter builds typed
//! `ChcVc` inputs from structured contract data, runs the native typed CHC/PDR
//! solver, rejects generic and serialized proof data as diagnostic-only, and keeps
//! missing, bounded, diagnostic, or unsupported cases fail-closed.

use std::collections::BTreeMap;
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
use std::collections::BTreeSet;
#[cfg(feature = "trust-mc-native-solver")]
use std::sync::Arc;
#[cfg(any(feature = "trust-mc-native-solver", feature = "trust-mc-native-trust-ir-bundle"))]
use std::time::Instant;

use ay_bindings::{Expr, Sort};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
#[cfg(feature = "trust-mc-native-solver")]
pub use trust_mc_driver::{
    NativeTypedChcPdrNormalizedInput as TrustMcNativeTypedChcPdrNormalizedInput,
    NativeTypedChcPdrProofTransport as TrustMcNativeTypedChcPdrProofTransport,
    NativeTypedProofArtifactRef as TrustMcNativeTypedProofArtifactRef,
    NativeTypedProofStatus as TrustMcNativeTypedProofStatus,
    NativeTypedProofStrength as TrustMcNativeTypedProofStrength,
};
use trust_types::stable_sha256_hex;
#[cfg(feature = "trust-mc-native-solver")]
use trust_verifier_api::Counterexample as ApiCounterexample;
use trust_verifier_api::{
    ArtifactHash, AssuranceLevel, BundleSubject, ContractKind, ContractPredicate, EngineCapability,
    EngineKind, EngineManifest, EvidenceArtifact, EvidenceArtifactKind,
    EvidenceArtifactMaterialization, EvidenceArtifactReference, EvidencePublicationMetadata,
    EvidenceStatus, MetadataEntry, ObligationEvidence, ObligationKind, ProofStrength,
    ReasoningKind, SupportLevel, TrustContract, TrustContractBundle, TrustObligation,
    ValidatedVerificationRequest, VerificationEngine,
};

use crate::{TrustMcConfig, TrustMcProofMode};

/// Trust: true once the optional per-function wall-clock deadline has
/// elapsed. A `None` deadline (budget disabled) never trips.
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
fn trust_mc_budget_deadline_exceeded(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|deadline| Instant::now() >= deadline)
}

#[cfg(feature = "trust-mc-native-solver")]
fn fresh_exact_direct_completion_is_timely(
    deadline: Option<Instant>,
    completed_at: Instant,
) -> bool {
    deadline.is_none_or(|deadline| completed_at <= deadline)
}

const ENGINE_NAME: &str = "trust-mc";
const MISSING_TYPED_INPUT_REASON: &str = "typed-input-required: trust-verifier-api obligations \
must carry trust-mc.typed-chc-obligation.v1 data for the direct typed trust_mc CHC/PDR path; \
serialized FullVerificationVerdict metadata is diagnostic-only and is not proof evidence";
const DIRECT_TYPED_CHC_INPUT_REASON: &str = "direct typed trust_mc CHC/PDR input required as \
ContractPredicate::MathIr, ContractPredicate::CanonicalJson, or schema-matched \
ContractPredicate::TrustIr with schema \
trust-mc.typed-chc-obligation.v1 and native Trust/TrustIr proof metadata";
const REQUIRED_CHC_PDR_EVIDENCE_SHAPE: &str = "trust-mc proof-grade admission requires a live \
opaque native-bundle authority whose diagnostic candidate has shape \
FullVerificationVerdict::Proved { evidence: \
FullProofEvidence::ChcPdr(ChcPdrProofEvidence { kind: ChcPdrProofKind::ChcValidity | \
ChcPdrProofKind::PdrInvariant, metadata: FullProofEvidenceMetadata { normalized_input_hash: \
Some(SHA-256), transcript_hashes: non-empty, replay_log_hashes: non-empty, \
checked_report_hashes: non-empty, ... }, artifacts: digest-backed input, transcript, replay, \
and checked-report artifacts, and native typed CHC/TrustIr metadata, ... }) }; the serialized \
shape alone is diagnostic-only and never sufficient for Proved";
const UNSUPPORTED_PROOF_STRENGTH_REASON: &str = "adapter returns Unsupported with no \
proof_strength when direct typed trust_mc CHC/PDR input is absent or the native typed solver does not \
prove the obligation";
#[cfg(feature = "trust-mc-native-solver")]
const ACCEPTED_NATIVE_TYPED_TRANSPORT_REASON: &str = "native trust_mc typed CHC/PDR proof accepted \
from a live opaque native-bundle authority, with exact typed-CHC/request binding and digest-backed \
artifacts; the serialized transport remains diagnostic-only";
const TRUST_MC_FULL_VERIFICATION_VERDICT_METADATA_SCHEMA_VERSION: &str =
    "trust-mc.full-verification-verdict-metadata.v1";
const TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION: &str = "trust-mc.typed-chc-obligation.v1";
const TRUST_MC_TYPED_CHC_BINDING_SCHEMA_VERSION: &str = "trust-mc.typed-chc-binding.v1";
// Trust: the compiler tags whole-function panic-freedom obligations with this
// metadata key. They carry a router-placeholder direct typed-CHC input (no
// per-VC predicate) and must be discharged by the path-sensitive transport
// CHC/PDR solve over the native bundle, not the direct typed lane.
const TRUST_MC_PANIC_FREEDOM_OBLIGATION_METADATA_KEY: &str =
    "trust-trust-mc.panic-freedom-obligation.v1";
// Trust (R1 corpus): the compiler's typed-CHC lowering stamps its per-obligation
// unsupported ROOT CAUSE under this key (`annotate_trust_mc_typed_chc_lowering_status`);
// the adapter surfaces it as the leading unsupported diagnostic.
const TRUST_MC_TYPED_CHC_UNSUPPORTED_REASON_METADATA_KEY: &str =
    "trust-trust-mc.typed-chc-obligation.unsupported_reason";
// Trust: the compiler's POSITIVE per-obligation record of whether its typed-CHC
// lowering actually produced a `TrustMcTypedChcConstraint` for this row
// (`annotate_trust_mc_typed_chc_lowering_status`). `supported` is the witness
// that the row owns a per-VC violation predicate; `unsupported` is the compiler
// stating that it has none. Deliberately NOT in
// `TRUST_IR_NATIVE_TRANSPORT_METADATA_KEYS`, so it is inside the obligation's
// canonical public semantic digest and travels under the same authentication as
// the rest of the row rather than as detachable transport annotation.
const TRUST_MC_TYPED_CHC_LOWERING_STATUS_METADATA_KEY: &str =
    "trust-trust-mc.typed-chc-obligation.lowering_status";
#[cfg(feature = "trust-mc-native-solver")]
const TRUST_MC_TYPED_CHC_LOWERING_STATUS_UNSUPPORTED: &str = "unsupported";
const TRUST_MC_TYPED_CHC_SYNTHETIC_CONTRACT_METADATA_KEY: &str =
    "trust-trust-mc.typed-chc-obligation.synthetic_contract.v1";

/// Why a solved trust_mc Horn rule set is entitled to speak about one public
/// obligation.
///
/// A CHC/PDR "safe" verdict means exactly one thing: the query relation is not
/// derivable from the rule set. That is a statement ABOUT THE RULE SET. It
/// becomes a statement about a public obligation only when the obligation's own
/// violation condition is inside those rules — otherwise "I found no
/// counterexample" is being read as "I proved it", which is the same sentence
/// with the opposite meaning. Every admission of trust_mc CHC evidence must
/// therefore name which of these two witnesses it holds; there is no third.
#[cfg(feature = "trust-mc-native-solver")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TrustMcChcCreditWitness {
    /// The rule set IS the whole-function structural reachability query, and the
    /// obligation IS that whole-function property (the compiler's per-function
    /// default admission, or its counted panic-freedom aggregate). Here "no rule
    /// derives `error`" is not silence — it is the proof, because the query and
    /// the obligation are the same proposition. This is the one and only case in
    /// which a `TriviallySafe` route may be credited.
    WholeFunctionStructuralQuery,
    /// The rule set derives the query target from THIS obligation's own
    /// compiler-emitted per-VC violation predicate, so refuting derivability of
    /// the query refutes the violation.
    PerObligationViolationPredicate,
}

/// The positive-witness gate: decide, for one public obligation and the route
/// the driver selected for its solve, which [`TrustMcChcCreditWitness`] holds.
///
/// `route` is `None` on surfaces that never mint proof evidence; they still run
/// the obligation-side half so a row that could not be credited anywhere is
/// reported with the same reason everywhere.
///
/// The failure direction is the point. Historically each discovered false-PROVE
/// class was closed by a bespoke post-hoc structural refutation keyed on the
/// class that happened to be found — an allowlist that says nothing about the
/// next one. This is the complement: nothing is credited unless a witness is
/// affirmatively produced, so an unanticipated obligation family fails closed
/// on arrival instead of waiting to be discovered.
#[cfg(feature = "trust-mc-native-solver")]
fn trust_mc_chc_credit_witness(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    route: Option<trust_mc_driver::TypedChcPdrRoute>,
) -> Result<TrustMcChcCreditWitness, String> {
    // Exemption, stated as a case rather than smuggled in as an exception: these
    // two rows legitimately have no per-VC predicate because the obligation is
    // the whole function. Their identity is pinned to the compiler's exact
    // synthesized shape (id, kind, source, metadata inventory, producer context),
    // so an ordinary formula-less obligation cannot join the class by adding a
    // marker.
    if obligation.is_default_admission()
        || obligation_is_whole_function_panic_freedom(bundle, obligation)
    {
        return Ok(TrustMcChcCreditWitness::WholeFunctionStructuralQuery);
    }

    // The compiler answered this question at lowering time and recorded the
    // answer on the row. "unsupported" is it saying, in its own words, that this
    // obligation contributed no constraint.
    if metadata_value(&obligation.metadata, TRUST_MC_TYPED_CHC_LOWERING_STATUS_METADATA_KEY)
        .is_some_and(|status| status == TRUST_MC_TYPED_CHC_LOWERING_STATUS_UNSUPPORTED)
    {
        return Err(format!(
            "obligation `{}` contributed no typed CHC constraint (compiler-recorded lowering status `{TRUST_MC_TYPED_CHC_LOWERING_STATUS_UNSUPPORTED}`) and is not the whole-function structural query; a CHC that does not encode this violation cannot prove it",
            obligation.obligation_id
        ));
    }

    // Route-side half. `TriviallySafe` means the driver found no Horn rule at all
    // deriving the query target, so the solved rule set is literally silent about
    // every obligation but the whole-function one. A genuine per-VC input cannot
    // land here: `validate_non_vacuous_mir_rule_binding` requires a query-headed
    // rule with a MIR-derived premise before the input is accepted at all. So
    // this rejects only rule sets that lost the predicate between admission and
    // solve — exactly the case that must not read as a proof.
    if route == Some(trust_mc_driver::TypedChcPdrRoute::TriviallySafe) {
        return Err(format!(
            "obligation `{}` is not the whole-function structural query, but its solve took the trivially-safe route: no Horn rule derives the query target, so the rule set contains no encoding of this obligation's violation",
            obligation.obligation_id
        ));
    }

    Ok(TrustMcChcCreditWitness::PerObligationViolationPredicate)
}

/// True only for the compiler's exact counted whole-function panic aggregate.
///
/// This is a shape gate, not authority by itself. The native-bundle caller also
/// validates the public/native claim digest, source, proof unit, compiler facts,
/// replay assertion, and derived CHC marker before consulting this predicate.
/// Requiring the exact compiler context here prevents an ordinary formula-less
/// assertion from laundering a whole-function transport proof merely by adding
/// the historical diagnostic marker.
fn obligation_is_whole_function_panic_freedom(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> bool {
    let trust_verifier_api::BundleSubject::Function { crate_name, path } = &bundle.subject else {
        return false;
    };
    let expected_id = format!(
        "vc:{}:assertion:panic-freedom:0",
        trust_types::canonical_artifact_id_component(path)
    );
    if obligation.metadata.iter().any(|entry| {
        !matches!(
            entry.key.as_str(),
            trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY
                | TRUST_MC_PANIC_FREEDOM_OBLIGATION_METADATA_KEY
                | "trust.vc.kind"
                | TRUST_SOURCE_DIGEST_METADATA_KEY
                | TRUST_VC_DIGEST_METADATA_KEY
                | TRUST_MC_TYPED_CHC_LOWERING_STATUS_METADATA_KEY
                | TRUST_MC_TYPED_CHC_UNSUPPORTED_REASON_METADATA_KEY
                | TRUST_MC_TYPED_CHC_SYNTHETIC_CONTRACT_METADATA_KEY
                | TRUST_MC_TYPED_CHC_SOURCE_DIGEST_METADATA_KEY
                | TRUST_MC_TYPED_CHC_VC_DIGEST_METADATA_KEY
                | TRUST_MC_TYPED_CHC_SYNTHETIC_DIGEST_METADATA_KEY
                | TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY
                | "trust.trust_ir.native.transport_status"
                | "trust.trust_ir.native.unsupported_reason"
                | TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY
                | TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY
                | TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY
                | "trust.trust_ir.native.proof_unit.v1"
                | "trust.trust_ir.native.assertion_id"
                | "trust.trust_ir.native.trust_ir_module_digest"
                | "trust.trust_ir.native.request_digest"
                | "trust.trust_ir.native.compiler_facts_digest"
                | "trust.trust_ir.native.obligation_source_digest"
                | "trust.trust_ir.native.replay_engine"
                | "trust.trust_ir.native.replay_invocation"
                | "trust.trust_ir.native.replay_transcript_digest"
                | "trust.trust_ir.native.artifact_fingerprint"
        )
    }) || obligation.obligation_id != expected_id
        || obligation.kind != ObligationKind::Assertion
        || obligation.contract_id.is_some()
        || obligation.proof_item_id.is_some()
        || obligation.required_strength.is_some()
        || !obligation.summary_facts.is_empty()
        || metadata_value(&obligation.metadata, TRUST_MC_PANIC_FREEDOM_OBLIGATION_METADATA_KEY)
            != Some("enabled")
        || metadata_value(&obligation.metadata, "trust.vc.kind") != Some("panic_freedom")
        || !metadata_value(&obligation.metadata, TRUST_SOURCE_DIGEST_METADATA_KEY)
            .is_some_and(is_lowercase_sha256_hex)
        || !metadata_value(&obligation.metadata, TRUST_VC_DIGEST_METADATA_KEY)
            .is_some_and(is_lowercase_sha256_hex)
        || metadata_value(&obligation.metadata, TRUST_VC_FORMULA_SCHEMA_METADATA_KEY).is_some()
        || metadata_value(&obligation.metadata, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY).is_some()
    {
        return false;
    }

    let Some(encoded) =
        metadata_value(&obligation.metadata, trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY)
    else {
        return false;
    };
    let Ok(context) =
        trust_types::json_depth::from_str_deep::<trust_verifier_api::ObligationContext>(encoded)
    else {
        return false;
    };
    context.has_current_schema()
        && matches!(&context.producer, trust_verifier_api::ObligationProducer::CompilerMirExtract)
        && context.function.as_ref().is_some_and(|function| {
            function.crate_name == crate_name.as_str() && function.path == path.as_str()
        })
        && matches!(
            &context.origin,
            trust_verifier_api::ObligationOrigin::VerificationCondition {
                vc_kind,
                vc_index: 0,
                formula_schema: None,
            } if vc_kind == "panic_freedom"
        )
}
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
const TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION: &str =
    "trust-mc-native-admission-contract-v1";
pub const TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY: &str =
    "trust-mc.typed-chc-obligation.binding.v1";
pub const TRUST_MC_TYPED_CHC_SOURCE_DIGEST_METADATA_KEY: &str =
    "trust-mc.typed-chc-obligation.source_digest.sha256";
pub const TRUST_MC_TYPED_CHC_VC_DIGEST_METADATA_KEY: &str =
    "trust-mc.typed-chc-obligation.vc_digest.sha256";
pub const TRUST_MC_TYPED_CHC_SYNTHETIC_DIGEST_METADATA_KEY: &str =
    "trust-mc.typed-chc-obligation.synthetic_digest.sha256";
const TRUST_SOURCE_DIGEST_METADATA_KEY: &str = "trust.mir-extract.source.digest.sha256";
const TRUST_VC_DIGEST_METADATA_KEY: &str = "trust.vc.digest.sha256";
const TRUST_VC_FORMULA_SCHEMA_METADATA_KEY: &str = "trust.vc.formula.schema";
const TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY: &str = "trust.vc.formula.payload";
const TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY: &str =
    "trust.trust_ir.native.proof_obligation_id";
const TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY: &str = "trust.trust_ir.native.request_id";
const TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY: &str =
    "trust.trust_ir.native.verifier_suite";
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
const TRUST_VC_FORMULA_SMTLIB_METADATA_KEY: &str = "trust.vc.formula.smtlib2";
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
const TRUST_VC_FORMULA_SORT_METADATA_KEY: &str = "trust.vc.formula.sort";
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
const TRUST_IR_OBLIGATION_SOURCE_FORMULA_SCHEMA: &str = "trust.trust_ir.obligation-source.v1";
const TRUST_VC_HARDENED_NAMESPACE: &str = "trust.vc.hardened";
const TRUST_VC_HARDENED_WILDCARD: &str = "*";

/// E4/E5 are trust-mc reachability obligations only when the compiler supplied
/// the exact typed violation formula. A bare `LoopInvariant` or `Termination`
/// claim remains trust-wp-owned; metadata key presence alone is insufficient.
fn is_typed_body_aware_e4_e5_obligation(obligation: &TrustObligation) -> bool {
    matches!(obligation.kind, ObligationKind::LoopInvariant | ObligationKind::Termination)
        && typed_spec_predicate_envelope(obligation).is_some()
}

/// The fresh-exact receipt lane's admission: E4/E5, plus a body-aware
/// POSTCONDITION row whose NEGATED CLAUSE references the return slot.
///
/// The discriminator is a deliberate scoping decision: a postcondition whose
/// clause never mentions the post-state does not constrain the body — it is
/// a ∀-params statement that belongs to the tautology/kernel lanes
/// (trust-wp fully proves that class today), and the E9
/// citation-undischarged tripwires pin exactly such clauses (`x >= x`) as
/// NOT dischargeable without a kernel citation. Admitting them here would
/// flip a load-bearing sealed-authority pin.
///
/// The body-aware payload spells `result` as the canonical return-slot
/// variable `_0` (`spec_parse::map_var_name` rewrites it before any payload
/// is minted; a `{"node":"result"}` node never reaches
/// `trust.vc.formula.payload`), and GLOBAL `_0` presence does NOT
/// discriminate — every body-aware VC pins `_0` to its return definition as
/// a positive conjunct (the tautology row carries `_0 = x` beside
/// `¬(x >= x)`). What separates the two is WHERE the return slot appears:
/// the violation formula's negation subtree IS the negated ensures clause,
/// so a clause that constrains the post-state puts `_0` under the `Not`,
/// verified against the real dumped payloads of both fixture classes.
/// Every structural requirement of the E4/E5 envelope (current-schema typed
/// `TrustSpecPredicate` payload, `Bool` root, `CompilerMirExtract` VC
/// origin) applies unchanged; the consumption path reuses the SAME
/// sealed-authority validation chain (canonical public-digest
/// reconciliation, affine receipt, bundle seal).
fn is_typed_body_aware_exact_direct_obligation(obligation: &TrustObligation) -> bool {
    if is_typed_body_aware_e4_e5_obligation(obligation) {
        return true;
    }
    if !matches!(obligation.kind, ObligationKind::Postcondition) {
        return false;
    }
    typed_spec_predicate_envelope(obligation).is_some_and(|predicate| {
        typed_spec_negated_clause_references_return_slot(&predicate.root, false)
            || typed_spec_expr_references_result(&predicate.root)
    })
}

/// Whether any `Not` subtree of the typed violation formula references the
/// canonical return-slot variable (`_0`, or a versioned `_0#<token>` /
/// projected `_0.<field>` spelling). `under_not` tracks whether the walk is
/// already inside a negation.
fn typed_spec_negated_clause_references_return_slot(
    expr: &trust_verifier_api::TrustSpecExpr,
    under_not: bool,
) -> bool {
    use trust_verifier_api::TrustSpecExprKind as Kind;
    let is_return_slot = |name: &str| {
        let base = name.split('#').next().unwrap_or(name);
        base == "_0" || base.starts_with("_0.")
    };
    match &expr.kind {
        Kind::Variable { name } => under_not && is_return_slot(name),
        Kind::Result => under_not,
        Kind::BoolLiteral { .. } | Kind::IntLiteral { .. } | Kind::BitVecLiteral { .. } => false,
        Kind::Unary { op, expr } => {
            let inside = under_not || matches!(op, trust_verifier_api::TrustSpecUnaryOp::Not);
            typed_spec_negated_clause_references_return_slot(expr, inside)
        }
        Kind::Old { expr }
        | Kind::BvUnary { expr, .. }
        | Kind::BvFromInt { expr, .. }
        | Kind::IntFromBv { expr, .. } => {
            typed_spec_negated_clause_references_return_slot(expr, under_not)
        }
        Kind::Binary { lhs, rhs, .. } | Kind::BvBinary { lhs, rhs, .. } => {
            typed_spec_negated_clause_references_return_slot(lhs, under_not)
                || typed_spec_negated_clause_references_return_slot(rhs, under_not)
        }
        Kind::Field { base, .. } => {
            typed_spec_negated_clause_references_return_slot(base, under_not)
        }
        Kind::Index { base, index } => {
            typed_spec_negated_clause_references_return_slot(base, under_not)
                || typed_spec_negated_clause_references_return_slot(index, under_not)
        }
        Kind::Quantifier { body, .. } => {
            typed_spec_negated_clause_references_return_slot(body, under_not)
        }
        Kind::IsVariant { scrutinee, .. } | Kind::VariantField { scrutinee, .. } => {
            typed_spec_negated_clause_references_return_slot(scrutinee, under_not)
        }
        // Future vocabulary fails CLOSED out of the fresh lane.
        _ => false,
    }
}

/// The validated typed-formula envelope shared by the exact-direct lanes:
/// current-schema `TrustSpecPredicate` payload with a `Bool` root and a
/// current `CompilerMirExtract` VerificationCondition origin.
fn typed_spec_predicate_envelope(
    obligation: &TrustObligation,
) -> Option<trust_verifier_api::TrustSpecPredicate> {
    let schema = metadata_value(&obligation.metadata, TRUST_VC_FORMULA_SCHEMA_METADATA_KEY)?;
    if schema != trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION {
        return None;
    }
    let payload = metadata_value(&obligation.metadata, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)?;
    let predicate =
        trust_types::json_depth::from_str_deep::<trust_verifier_api::TrustSpecPredicate>(payload)
            .ok()?;
    (predicate.has_current_schema()
        && predicate.root_sort == trust_verifier_api::TrustSpecSort::Bool
        && predicate.root.sort == trust_verifier_api::TrustSpecSort::Bool
        && predicate.validate().is_ok()
        && has_current_compiler_vc_origin(obligation))
    .then_some(predicate)
}

/// Whether a typed spec expression tree contains a post-state `Result` node.
fn typed_spec_expr_references_result(expr: &trust_verifier_api::TrustSpecExpr) -> bool {
    use trust_verifier_api::TrustSpecExprKind as Kind;
    match &expr.kind {
        Kind::Result => true,
        Kind::BoolLiteral { .. }
        | Kind::IntLiteral { .. }
        | Kind::Variable { .. }
        | Kind::BitVecLiteral { .. } => false,
        Kind::Unary { expr, .. }
        | Kind::Old { expr }
        | Kind::BvUnary { expr, .. }
        | Kind::BvFromInt { expr, .. }
        | Kind::IntFromBv { expr, .. } => typed_spec_expr_references_result(expr),
        Kind::Binary { lhs, rhs, .. } | Kind::BvBinary { lhs, rhs, .. } => {
            typed_spec_expr_references_result(lhs) || typed_spec_expr_references_result(rhs)
        }
        Kind::Field { base, .. } => typed_spec_expr_references_result(base),
        Kind::Index { base, index } => {
            typed_spec_expr_references_result(base) || typed_spec_expr_references_result(index)
        }
        Kind::Quantifier { body, .. } => typed_spec_expr_references_result(body),
        Kind::IsVariant { scrutinee, .. } | Kind::VariantField { scrutinee, .. } => {
            typed_spec_expr_references_result(scrutinee)
        }
        // Future vocabulary fails CLOSED out of the fresh lane: an
        // unrecognized node cannot demonstrate a post-state reference.
        _ => false,
    }
}

fn has_current_compiler_vc_origin(obligation: &TrustObligation) -> bool {
    let Some(encoded) =
        metadata_value(&obligation.metadata, trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY)
    else {
        return false;
    };
    let Ok(context) =
        trust_types::json_depth::from_str_deep::<trust_verifier_api::ObligationContext>(encoded)
    else {
        return false;
    };
    context.has_current_schema()
        && matches!(&context.producer, trust_verifier_api::ObligationProducer::CompilerMirExtract)
        && matches!(
            &context.origin,
            trust_verifier_api::ObligationOrigin::VerificationCondition {
                formula_schema: Some(schema),
                ..
            } if schema == trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION
        )
}

fn is_trust_mc_owned_obligation(obligation: &TrustObligation) -> bool {
    is_trust_mc_owned_obligation_kind(&obligation.kind)
        || is_typed_body_aware_e4_e5_obligation(obligation)
}

/// Metadata key for serialized trust-mc-core `FullVerificationVerdict` diagnostics.
pub const TRUST_MC_FULL_VERIFICATION_VERDICT_METADATA_KEY: &str =
    "trust-mc.full-verification-verdict.v1";
/// Schema for structured typed CHC/PDR verifier input consumed by the direct trust_mc path.
pub const TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA: &str = TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION;
/// Schema for public typed CHC/PDR binding metadata required by proof-grade native trust_mc evidence.
pub const TRUST_MC_TYPED_CHC_BINDING_SCHEMA: &str = TRUST_MC_TYPED_CHC_BINDING_SCHEMA_VERSION;

/// Opaque identity for one immutable, validated bundle snapshot.
///
/// The token is intentionally cloneable so every receipt minted by one native
/// batch can share it. Callers cannot construct a token or inspect its bundle,
/// and a byte-identical bundle sealed independently has a different identity.
/// It is not serializable and therefore cannot be reconstructed from public
/// [`ObligationEvidence`].
#[cfg(feature = "trust-mc-native-solver")]
#[derive(Debug, Clone)]
pub struct FreshExactDirectChcPdrBundleSeal {
    bundle: Arc<TrustContractBundle>,
}

#[cfg(feature = "trust-mc-native-solver")]
impl FreshExactDirectChcPdrBundleSeal {
    fn from_validated_bundle(bundle: &TrustContractBundle) -> Self {
        Self { bundle: Arc::new(bundle.clone()) }
    }

    /// Reconcile a current complete bundle with the immutable bundle that
    /// produced a live receipt batch. Call this once at the outer batch
    /// authority boundary; individual receipt replay then remains local.
    #[must_use]
    pub fn matches_bundle(&self, bundle: &TrustContractBundle) -> bool {
        bundle.validate().is_ok() && self.bundle.as_ref() == bundle
    }

    fn shares_identity(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.bundle, &other.bundle)
    }
}

#[cfg(feature = "trust-mc-native-solver")]
/// Owned live receipt for one compiler-authenticated exact-direct CHC/PDR
/// replay.
///
/// This type is intentionally neither `Clone` nor serializable. It retains the
/// affine trust-mc verification response whose private seal can still be
/// recomputed, plus the independently derived pre-solve normalization and the
/// canonical public semantic digest that bound the exact source claim to that
/// CHC. Public [`ObligationEvidence`] is only a projection of this receipt and
/// can never reconstruct it.
#[derive(Debug)]
pub struct FreshExactDirectChcPdrReceipt {
    bundle_seal: FreshExactDirectChcPdrBundleSeal,
    bundle_id: String,
    bundle_subject: BundleSubject,
    public_obligation_id: String,
    public_obligation: TrustObligation,
    public_semantic_digest: String,
    input_artifact_hash: ArtifactHash,
    dispatch_deadline: Option<Instant>,
    completed_at: Instant,
    expected_normalized_input: TrustMcNativeTypedChcPdrNormalizedInput,
    verification: trust_mc_driver::TypedChcPdrFullVerification,
}

/// One exact-direct public result and its optional live proof sidecar.
///
/// The evidence remains ordinary serializable verifier-api data. Only the
/// non-clone receipt can carry authority into a compiler-owned finalization
/// boundary; inconclusive/refuted/timed-out solves return `receipt: None`.
#[cfg(feature = "trust-mc-native-solver")]
#[derive(Debug)]
pub struct FreshExactDirectChcPdrDispatch {
    pub evidence: ObligationEvidence,
    pub receipt: Option<FreshExactDirectChcPdrReceipt>,
}

/// Public native-bundle evidence plus live exact-direct receipt sidecars.
///
/// Whole-function transport rows never appear in `fresh_exact_direct_receipts`:
/// without an exact public-row membership receipt they carry only their existing
/// bundle authority. The map is keyed by the exact public obligation id and can
/// contain only compiler-authenticated standalone E4/E5 rows.
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
#[derive(Debug)]
pub struct NativeTrustIrBundleEvidenceWithFreshReceipts {
    pub evidence: Vec<ObligationEvidence>,
    pub fresh_exact_direct_receipts: BTreeMap<String, FreshExactDirectChcPdrReceipt>,
}

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
impl From<Vec<ObligationEvidence>> for NativeTrustIrBundleEvidenceWithFreshReceipts {
    fn from(evidence: Vec<ObligationEvidence>) -> Self {
        Self { evidence, fresh_exact_direct_receipts: BTreeMap::new() }
    }
}

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
fn finalize_native_bundle_evidence_with_fresh_receipts(
    evidence: Vec<ObligationEvidence>,
    mut fresh_exact_direct_receipts: BTreeMap<String, FreshExactDirectChcPdrReceipt>,
) -> NativeTrustIrBundleEvidenceWithFreshReceipts {
    // A sidecar may survive only when the final public projection still has
    // exactly one row for that identity and that row remains Proved. This
    // catches any later demotion/replacement in the bundle control flow and
    // prevents a stale live capability from being paired with different public
    // evidence.
    // Index the complete public projection once. Re-scanning all evidence for
    // every receipt is quadratic at the bundle inventory limit and lets a
    // large but otherwise valid batch turn the final affine-authority boundary
    // into a denial of service.
    let mut public_row_summaries = BTreeMap::<&str, (usize, bool)>::new();
    for row in &evidence {
        let summary = public_row_summaries.entry(row.obligation_id.as_str()).or_insert((0, false));
        summary.0 += 1;
        summary.1 = row.status == EvidenceStatus::Proved;
    }
    fresh_exact_direct_receipts.retain(|obligation_id, receipt| {
        if receipt.public_obligation_id() != obligation_id {
            return false;
        }
        public_row_summaries
            .get(obligation_id.as_str())
            .is_some_and(|(count, proved)| *count == 1 && *proved)
    });
    NativeTrustIrBundleEvidenceWithFreshReceipts { evidence, fresh_exact_direct_receipts }
}

#[cfg(feature = "trust-mc-native-solver")]
impl FreshExactDirectChcPdrReceipt {
    /// Return the exact public obligation id bound by this receipt.
    #[must_use]
    pub fn public_obligation_id(&self) -> &str {
        &self.public_obligation_id
    }

    /// Return the exact direct-engine input artifact hash captured before solve.
    #[must_use]
    pub fn input_artifact_hash(&self) -> &ArtifactHash {
        &self.input_artifact_hash
    }

    /// Return the dispatch deadline frozen into this receipt, when one applied.
    #[must_use]
    pub fn dispatch_deadline(&self) -> Option<Instant> {
        self.dispatch_deadline
    }

    /// Opaque exact-bundle identity shared by receipts from one native batch.
    /// The token is cloneable but cannot be constructed by callers.
    #[must_use]
    pub fn bundle_seal(&self) -> FreshExactDirectChcPdrBundleSeal {
        self.bundle_seal.clone()
    }

    /// True only when this receipt and `seal` originated from the same exact
    /// validated bundle snapshot.
    #[must_use]
    pub fn shares_bundle_seal(&self, seal: &FreshExactDirectChcPdrBundleSeal) -> bool {
        self.bundle_seal.shares_identity(seal)
    }

    /// Recompute every live CHC-level and public source binding and return the
    /// resulting publication-grade proof strength.
    ///
    /// Callers must invoke this on the live owned receipt at the final authority
    /// boundary. A serialized transport, public `Proved` status, copied digest,
    /// or reconstructed receipt-shaped record cannot call this method because
    /// none retains trust-mc's private affine seal.
    pub fn still_authorizes(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
    ) -> Result<ProofStrength, String> {
        if bundle.bundle_id != self.bundle_id
            || obligation.obligation_id != self.public_obligation_id
        {
            return Err(
                "fresh exact-direct receipt does not identify this bundle/obligation".to_string()
            );
        }
        if bundle.subject != self.bundle_subject || obligation != &self.public_obligation {
            return Err(
                "fresh exact-direct receipt exact subject/obligation record no longer matches"
                    .to_string(),
            );
        }
        if !fresh_exact_direct_completion_is_timely(self.dispatch_deadline, self.completed_at) {
            return Err(
                "fresh exact-direct receipt completed after its dispatch deadline".to_string()
            );
        }
        if !is_typed_body_aware_exact_direct_obligation(obligation) {
            return Err(
                "fresh exact-direct receipt requires a current compiler-authenticated body-aware typed formula (E4/E5 or result-referencing postcondition)"
                    .to_string(),
            );
        }
        bundle.validate_requested_obligations(std::slice::from_ref(obligation))?;
        let current_digest = bundle.canonical_obligation_semantic_digest_sha256(obligation)?;
        if current_digest != self.public_semantic_digest {
            return Err(
                "fresh exact-direct receipt public semantic digest no longer matches".to_string()
            );
        }
        // Re-run the config-independent exact direct-input reconciliation so
        // post-dispatch changes to the canonical contract, authenticated native
        // marker, request metadata, or source/formula projection cannot survive
        // merely because transport annotations are excluded from the canonical
        // public digest domain.
        let rebinding_adapter = TrustMcVerifierApiAdapter::default();
        let current_input = rebinding_adapter
            .typed_chc_pdr_obligation_for(bundle, obligation)?
            .ok_or_else(|| {
                "fresh exact-direct receipt no longer has one reconciled direct input".to_string()
            })?;
        if current_input.input_artifact.hash != self.input_artifact_hash {
            return Err("fresh exact-direct receipt engine-input artifact hash no longer matches"
                .to_string());
        }
        let current_normalized =
            trust_mc_driver::normalized_typed_chc_pdr_input(&current_input.trust_mc_obligation)
                .map_err(native_typed_chc_pdr_error_reason)?;
        if current_normalized != self.expected_normalized_input {
            return Err(
                "fresh exact-direct receipt normalized typed request no longer matches".to_string()
            );
        }
        self.still_authorizes_under_exact_bundle_seal(&self.bundle_seal, obligation)
    }

    /// Revalidate the receipt-local proof after an outer authority boundary has
    /// already byte-validated and sealed the complete bundle exactly once.
    ///
    /// This avoids repeating full bundle validation, canonical indexing, and
    /// typed-input reconstruction for every receipt in one affine batch. It is
    /// sound only when the caller retains the exact sealed bundle; therefore
    /// this method still checks its bundle identity/subject and the complete
    /// obligation row before replaying every private CHC/PDR proof binding.
    #[doc(hidden)]
    pub fn still_authorizes_under_exact_bundle_seal(
        &self,
        bundle_seal: &FreshExactDirectChcPdrBundleSeal,
        obligation: &TrustObligation,
    ) -> Result<ProofStrength, String> {
        if !self.bundle_seal.shares_identity(bundle_seal) {
            return Err(
                "fresh exact-direct receipt does not share the supplied opaque bundle seal"
                    .to_string(),
            );
        }
        let sealed_bundle = bundle_seal.bundle.as_ref();
        if sealed_bundle.bundle_id != self.bundle_id
            || sealed_bundle.subject != self.bundle_subject
            || obligation.obligation_id != self.public_obligation_id
            || obligation != &self.public_obligation
        {
            return Err(
                "fresh exact-direct receipt does not match the exact sealed bundle row".to_string()
            );
        }
        if !fresh_exact_direct_completion_is_timely(self.dispatch_deadline, self.completed_at) {
            return Err(
                "fresh exact-direct receipt completed after its dispatch deadline".to_string()
            );
        }
        if !is_typed_body_aware_exact_direct_obligation(obligation) {
            return Err(
                "fresh exact-direct receipt requires a current compiler-authenticated body-aware typed formula (E4/E5 or result-referencing postcondition)"
                    .to_string(),
            );
        }
        validate_native_full_verification_normalized_input(
            &self.verification,
            &self.expected_normalized_input,
        )?;
        let authority = self.verification.authorized_native_proof().map_err(|error| {
            format!(
                "fresh exact-direct receipt lost opaque trust-mc authority: {}",
                native_typed_chc_pdr_error_reason(error)
            )
        })?;
        let transport = authority.transport_record();
        validate_native_typed_transport_common(
            sealed_bundle,
            obligation,
            &transport,
            Some(&self.expected_normalized_input),
        )
        .map_err(|reasons| {
            format!(
                "fresh exact-direct receipt failed public/source binding: {}",
                reasons.join("; ")
            )
        })?;
        native_typed_proof_strength(transport.proof_strength).ok_or_else(|| {
            format!(
                "fresh exact-direct receipt has unsupported proof strength {:?}",
                transport.proof_strength
            )
        })
    }
}

/// Public verifier-api adapter for trust_mc.
///
/// The adapter owns trust-mc's CHC/PDR reachability lanes. It prefers structured
/// typed CHC input from `trust-verifier-api` contract data and keeps bounded,
/// serialized, or unsupported evidence from being upgraded into full proofs.
#[derive(Debug, Clone)]
pub struct TrustMcVerifierApiAdapter {
    manifest: EngineManifest,
    config: TrustMcConfig,
}

impl TrustMcVerifierApiAdapter {
    /// Create an adapter with an explicit trust_mc configuration.
    #[must_use]
    pub fn new(config: TrustMcConfig) -> Self {
        Self { manifest: trust_mc_manifest(), config }
    }

    /// Return the trust_mc configuration used by this adapter.
    #[must_use]
    pub fn config(&self) -> &TrustMcConfig {
        &self.config
    }

    fn unsupported_evidence(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
    ) -> ObligationEvidence {
        let mut evidence =
            self.evidence_with_status(bundle, obligation, EvidenceStatus::Unsupported);
        evidence.diagnostics = self.unsupported_diagnostics(obligation);
        evidence
    }

    /// Trust: evidence for an obligation skipped because the per-function
    /// wall-clock budget was exhausted before it could be solved. Status is
    /// `Timeout`, which `FunctionVerdict::from_summary` maps to `TimedOut`
    /// *before* it ever considers `Proved` — so a budget-skipped obligation can
    /// never make a function `Proved`. This is the sound degradation path; the
    /// only alternative is solving unbounded (the trust-strengthen self-compile
    /// stall this fix removes).
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn budget_timeout_evidence(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
    ) -> ObligationEvidence {
        let mut evidence = self.evidence_with_status(bundle, obligation, EvidenceStatus::Timeout);
        evidence.diagnostics.push(
            "tracked per-function wall-clock budget (-Ztrust-verify-function-budget-ms) exceeded \
             before this trust-mc obligation was solved; degraded to Timeout (sound: never Proved)"
                .to_string(),
        );
        evidence
    }

    fn evidence_with_status(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        status: EvidenceStatus,
    ) -> ObligationEvidence {
        ObligationEvidence {
            evidence_id: format!(
                "{}:{}:{}",
                self.manifest.name, bundle.bundle_id, obligation.obligation_id
            ),
            obligation_id: obligation.obligation_id.clone(),
            engine: self.manifest.clone(),
            status,
            proof_strength: None,
            artifacts: Vec::new(),
            counterexample: None,
            publication: EvidencePublicationMetadata {
                publication_plan_hash: bundle.publication.dpub_plan_hash.clone(),
                trust_engines_lock_hash: bundle.publication.trust_engines_lock_hash.clone(),
                ..EvidencePublicationMetadata::default()
            },
            diagnostics: Vec::new(),
        }
    }

    /// Convert native full-verifier evidence into public verifier evidence.
    ///
    /// This public serialized-evidence bridge is diagnostic-only for CHC/PDR
    /// proofs: it has no exact pre-solve typed request from which to derive the
    /// native normalized-input identity. Only private in-process lanes that
    /// validate that request independently may promote the subordinate proof
    /// metadata to `Proved`.
    #[must_use]
    pub fn evidence_from_native_full_verifier_evidence(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        evidence: TrustMcNativeFullVerifierEvidence,
    ) -> ObligationEvidence {
        if !is_trust_mc_owned_obligation(obligation) {
            let mut unsupported = self.unsupported_evidence(bundle, obligation);
            unsupported.diagnostics.push(format!(
                "native trust_mc full-verifier evidence rejected for unowned {:?} obligation",
                obligation.kind
            ));
            return unsupported;
        }

        match evidence {
            TrustMcNativeFullVerifierEvidence::ChcPdrProof(proof) => {
                self.evidence_from_chc_pdr_proof(bundle, obligation, *proof)
            }
            #[cfg(feature = "trust-mc-native-solver")]
            TrustMcNativeFullVerifierEvidence::TypedChcPdrProofTransport(transport) => self
                .evidence_from_native_typed_chc_pdr_proof_transport(bundle, obligation, transport),
            TrustMcNativeFullVerifierEvidence::DiagnosticOnly(diagnostic) => {
                self.evidence_from_diagnostic_only(bundle, obligation, diagnostic)
            }
        }
    }

    /// Reject an unauthenticated raw typed CHC/PDR transport as proof evidence.
    ///
    /// A transport is serializable and therefore cannot by itself prove that it
    /// came from trust-mc's proof-grade constructor. It is validated here for
    /// precise diagnostics, but only the private in-process path fed directly by
    /// `NativeTrustIrChcPdrRunner` may upgrade it to `Proved`.
    #[cfg(feature = "trust-mc-native-solver")]
    #[must_use]
    pub fn evidence_from_native_typed_chc_pdr_proof_transport(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        transport: TrustMcNativeTypedChcPdrProofTransport,
    ) -> ObligationEvidence {
        if !is_trust_mc_owned_obligation(obligation) {
            let mut unsupported = self.unsupported_evidence(bundle, obligation);
            unsupported.diagnostics.push(format!(
                "native trust_mc typed CHC/PDR proof transport rejected for unowned {:?} obligation",
                obligation.kind
            ));
            return unsupported;
        }

        let mut evidence = self.unsupported_evidence(bundle, obligation);
        match validate_native_typed_transport(bundle, obligation, &transport) {
            Ok(()) => evidence.diagnostics.push(
                "raw native typed CHC/PDR transport is diagnostic-only; proof admission requires the in-process trust-mc proof-grade runner"
                    .to_string(),
            ),
            Err(reasons) => {
                evidence.diagnostics.push(format!(
                    "native trust_mc typed CHC/PDR proof transport rejected: {}",
                    reasons.join("; ")
                ));
            }
        }
        evidence
    }

    #[cfg(feature = "trust-mc-native-solver")]
    fn evidence_from_authorized_native_typed_chc_pdr_proof(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        authority: &trust_mc_driver::AuthorizedNativeTypedChcPdrProof<'_>,
        expected: &TrustMcNativeTypedChcPdrNormalizedInput,
    ) -> ObligationEvidence {
        // The opaque borrow is the capability. Its transport snapshot is only
        // the exact bound payload we independently validate and publish; no raw
        // or deserialized transport can call this private path.
        let diagnostic_transport = authority.transport_record();
        if !is_trust_mc_owned_obligation(obligation) {
            return self.evidence_from_native_typed_chc_pdr_proof_transport(
                bundle,
                obligation,
                diagnostic_transport,
            );
        }
        match validated_authorized_native_typed_transport_artifacts(
            bundle, obligation, authority, expected,
        ) {
            Ok((transport, artifacts)) => {
                let Some(proof_strength) = native_typed_proof_strength(transport.proof_strength)
                else {
                    let mut evidence = self.unsupported_evidence(bundle, obligation);
                    evidence.diagnostics.push(format!(
                        "native trust_mc typed CHC/PDR proof transport rejected: unsupported proof strength {:?}",
                        transport.proof_strength
                    ));
                    return evidence;
                };
                ObligationEvidence {
                    evidence_id: format!(
                        "{}:{}:{}",
                        self.manifest.name, bundle.bundle_id, obligation.obligation_id
                    ),
                    obligation_id: obligation.obligation_id.clone(),
                    engine: self.manifest.clone(),
                    status: EvidenceStatus::Proved,
                    proof_strength: Some(proof_strength),
                    artifacts,
                    counterexample: None,
                    publication: EvidencePublicationMetadata {
                        publication_plan_hash: bundle.publication.dpub_plan_hash.clone(),
                        trust_engines_lock_hash: bundle.publication.trust_engines_lock_hash.clone(),
                        ..EvidencePublicationMetadata::default()
                    },
                    diagnostics: native_typed_transport_diagnostics(&transport),
                }
            }
            Err(reasons) => {
                let mut evidence = self.unsupported_evidence(bundle, obligation);
                evidence.diagnostics.push(format!(
                    "opaque-authorized native trust_mc typed CHC/PDR proof failed consumer binding: {}",
                    reasons.join("; ")
                ));
                evidence
            }
        }
    }

    /// Solve a typed TrustIr native verification bundle and convert trust_mc CHC/PDR proofs.
    ///
    /// This is the Trust native-bundle entry point for callers that already have
    /// a `trust_ir::NativeVerificationBundle` from `trust-ir-bridge`. It selects
    /// typed trust_mc CHC/PDR requests from the bundle, runs the native proof-grade
    /// typed solver, and retains the live opaque producer authority through the
    /// private consumer admission path. Exported transport records are never
    /// capabilities.
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    #[must_use]
    pub fn evidence_from_native_trust_ir_bundle(
        &self,
        bundle: &TrustContractBundle,
        obligations: &[TrustObligation],
        native_bundle: &trust_ir::NativeVerificationBundle,
    ) -> Vec<ObligationEvidence> {
        self.evidence_from_native_trust_ir_bundle_with_deadline(
            bundle,
            obligations,
            native_bundle,
            None,
        )
    }

    /// Trust: deadline-aware variant of
    /// [`Self::evidence_from_native_trust_ir_bundle`]. When `deadline` is `Some`
    /// and elapses, obligations not yet solved are degraded to `Timeout`
    /// (sound: never `Proved`, via `from_summary`) so a function with a large
    /// trust-mc obligation set cannot stall the build unbounded. A `None`
    /// deadline preserves the original unbounded behaviour exactly.
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    pub fn evidence_from_native_trust_ir_bundle_with_deadline(
        &self,
        bundle: &TrustContractBundle,
        obligations: &[TrustObligation],
        native_bundle: &trust_ir::NativeVerificationBundle,
        deadline: Option<Instant>,
    ) -> Vec<ObligationEvidence> {
        self.evidence_from_native_trust_ir_bundle_with_deadline_and_fresh_receipts(
            bundle,
            obligations,
            native_bundle,
            deadline,
        )
        .evidence
    }

    /// Run the native-bundle path while retaining live exact-direct E4/E5
    /// receipt sidecars from the same per-row solves that produced the public
    /// evidence.
    ///
    /// This preserves the complete public/native claim-binding gate below; a
    /// router or compiler must not recreate that gate around the source-only
    /// direct method. The ordinary deadline-aware method delegates here and
    /// discards the sidecars for compatibility.
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    pub fn evidence_from_native_trust_ir_bundle_with_deadline_and_fresh_receipts(
        &self,
        bundle: &TrustContractBundle,
        obligations: &[TrustObligation],
        native_bundle: &trust_ir::NativeVerificationBundle,
        deadline: Option<Instant>,
    ) -> NativeTrustIrBundleEvidenceWithFreshReceipts {
        // Trust: ownership is a property of the authenticated public VC, not
        // of a caller-supplied native bundle or direct contract. Record every
        // unowned row before inspecting either input so an invalid native
        // inventory cannot mask (or bypass) the E4/E5 authority rejection.
        let mut direct_by_id = obligations
            .iter()
            .filter(|obligation| !is_trust_mc_owned_obligation(obligation))
            .map(|obligation| {
                let mut evidence = self.unsupported_evidence(bundle, obligation);
                evidence.diagnostics.push(format!(
                    "native trust_mc TrustIr bundle input rejected before direct solving for unowned {:?} obligation",
                    obligation.kind
                ));
                (obligation.obligation_id.clone(), evidence)
            })
            .collect::<BTreeMap<_, _>>();
        if obligations.iter().all(|obligation| !is_trust_mc_owned_obligation(obligation)) {
            return obligations
                .iter()
                .map(|obligation| {
                    direct_by_id
                        .remove(&obligation.obligation_id)
                        .unwrap_or_else(|| self.unsupported_evidence(bundle, obligation))
                })
                .collect::<Vec<_>>()
                .into();
        }

        if !matches!(self.config.proof_mode, TrustMcProofMode::Chc | TrustMcProofMode::PdrIc3) {
            return obligations
                .iter()
                .map(|obligation| {
                    if let Some(evidence) = direct_by_id.remove(&obligation.obligation_id) {
                        return evidence;
                    }
                    let mut evidence = self.unsupported_evidence(bundle, obligation);
                    evidence.diagnostics.push(format!(
                        "native trust_mc TrustIr CHC/PDR bundle input is present, but configured proof mode {:?} is not CHC/PDR",
                        self.config.proof_mode
                    ));
                    evidence
                })
                .collect::<Vec<_>>()
                .into();
        }

        if let Err(reason) = validate_trust_mc_native_admission_contract(native_bundle) {
            return obligations
                .iter()
                .map(|obligation| {
                    if let Some(evidence) = direct_by_id.remove(&obligation.obligation_id) {
                        return evidence;
                    }
                    let mut evidence = self.unsupported_evidence(bundle, obligation);
                    evidence.diagnostics.push(reason.clone());
                    evidence
                })
                .collect::<Vec<_>>()
                .into();
        }

        // Trust: validate the requested public inventory once and build one
        // immutable ownership/index view over the native bundle. Besides
        // keeping every later row check on the same snapshot, this avoids
        // re-validating/re-digesting the whole public bundle and rescanning all
        // native requests, proof units, compiler facts, and replay atoms for
        // every obligation (quadratic at inventory scale).
        let public_claim_binding_context =
            match NativeTrustIrPublicClaimBindingContext::build(bundle, obligations, native_bundle)
            {
                Ok(context) => context,
                Err(reason) => {
                    return obligations
                        .iter()
                        .map(|obligation| {
                            if let Some(evidence) = direct_by_id.remove(&obligation.obligation_id) {
                                return evidence;
                            }
                            let mut evidence = self.unsupported_evidence(bundle, obligation);
                            evidence.diagnostics.insert(
                            0,
                            format!(
                                "native trust_mc public/TrustIr claim inventory rejected: {reason}"
                            ),
                        );
                            evidence
                        })
                        .collect::<Vec<_>>()
                        .into();
                }
            };
        let fresh_exact_bundle_seal =
            FreshExactDirectChcPdrBundleSeal::from_validated_bundle(bundle);

        let translated = match self
            .native_trust_ir_chc_pdr_translated_obligations(native_bundle, deadline)
        {
            Ok(translated) => translated,
            Err(reason) => {
                return obligations
                    .iter()
                    .map(|obligation| {
                        if let Some(evidence) = direct_by_id.remove(&obligation.obligation_id) {
                            return evidence;
                        }
                        let mut evidence = self.unsupported_evidence(bundle, obligation);
                        evidence.diagnostics.push(format!(
                            "native trust_mc TrustIr CHC/PDR bundle did not translate to typed obligations: {reason}"
                        ));
                        evidence
                    })
                    .collect::<Vec<_>>()
                    .into();
            }
        };

        let mut translated_by_obligation = BTreeMap::new();
        let mut translated_counts = BTreeMap::<String, usize>::new();
        for translated in translated {
            let lookup_key =
                native_trust_mc_obligation_lookup_key(&translated.obligation.obligation_id);
            *translated_counts.entry(lookup_key.clone()).or_default() += 1;
            translated_by_obligation.entry(lookup_key).or_insert(translated);
        }

        // Trust: solve each obligation by its OWN cheapest sound path. Any
        // direct (compiler-emitted MathIr) encoding is the exact standalone
        // proof unit for that public obligation, so its result is terminal even
        // when it is Unknown / Timeout / Unsupported. The path-sensitive
        // transport proves properties of a translated executable function; it
        // must never replace an inconclusive result for a predicate that is not
        // itself injected into that function. Only `Ok(None)` obligations (for
        // example the whole-function panic-freedom marker, which carries no
        // per-VC predicate) may be DEFERRED to the transport solve.
        // This is per-obligation, not all-or-nothing: a function that mixes a
        // directly-provable arithmetic obligation with a transport-only
        // panic-freedom obligation keeps the arithmetic proof on the direct path
        // (and its direct-path artifacts) instead of dragging the whole bundle to
        // the transport. Sound: transport can only return Proved if its own
        // encoding proves the obligation.
        let mut deferred_ids: BTreeSet<String> = BTreeSet::new();
        let mut fresh_exact_direct_receipts = BTreeMap::new();
        for obligation in obligations {
            // Trust: this public low-level entrypoint may be called without the
            // router's `supports` filter.  Apply the same payload-aware
            // ownership gate before inspecting a supplied direct contract: a
            // bare E4/E5 kind is not trust-mc-owned, and an otherwise valid
            // typed CHC contract must not be able to manufacture ownership.
            if direct_by_id.contains_key(&obligation.obligation_id) {
                continue;
            }

            // Trust: neither the direct typed lane nor the whole-module
            // transport lane may speak for an ID-only public alias. Reconcile
            // the exact requested public record with the atomic public identity
            // embedded in this request's module proof unit before considering a
            // timeout or either solver verdict. The embedded SHA-256 covers the
            // canonical public claim; the remaining checks prove that the
            // module, compiler-fact sidecar, replay assertion, and derived CHC
            // marker all refer to that same request/proof/function/source.
            if let Err(reason) = validate_native_trust_ir_public_claim_binding(
                bundle,
                obligation,
                native_bundle,
                &public_claim_binding_context,
            ) {
                let mut evidence = self.unsupported_evidence(bundle, obligation);
                evidence.diagnostics.insert(
                    0,
                    format!("native trust_mc public/TrustIr claim binding rejected: {reason}"),
                );
                direct_by_id.insert(obligation.obligation_id.clone(), evidence);
                continue;
            }
            // Trust: stop solving once the per-function budget is spent;
            // the remaining direct-path obligations degrade to Timeout.
            if trust_mc_budget_deadline_exceeded(deadline) {
                direct_by_id.insert(
                    obligation.obligation_id.clone(),
                    self.budget_timeout_evidence(bundle, obligation),
                );
                continue;
            }
            let expected_native_id = native_trust_ir_expected_trust_mc_obligation_id(obligation)
                .unwrap_or_else(|| obligation.obligation_id.clone());
            let expected_lookup_key = native_trust_mc_obligation_lookup_key(&expected_native_id);
            if translated_counts.get(&expected_lookup_key).is_some_and(|count| *count > 1) {
                let mut evidence = self.unsupported_evidence(bundle, obligation);
                evidence.diagnostics.push(format!(
                    "native trust_mc TrustIr CHC/PDR bundle returned duplicate translated obligations for `{expected_native_id}`"
                ));
                direct_by_id.insert(obligation.obligation_id.clone(), evidence);
                continue;
            }
            let Some(translated) = translated_by_obligation.get(&expected_lookup_key) else {
                let mut evidence = self.unsupported_evidence(bundle, obligation);
                evidence.diagnostics.push(format!(
                    "native trust_mc TrustIr CHC/PDR bundle returned no translated obligation for `{expected_native_id}`"
                ));
                direct_by_id.insert(obligation.obligation_id.clone(), evidence);
                continue;
            };

            let exact_e4_e5_formula_lane = is_typed_body_aware_e4_e5_obligation(obligation);
            // Additive postcondition fresh lane: a result-referencing
            // body-aware Postcondition row ATTEMPTS the receipt-bearing fresh
            // dispatch, and takes its evidence ONLY when the live receipt was
            // actually delivered. On any shortfall — missing canonical
            // public digest, no exact direct input, non-Proved solve, or
            // dispatch error — the row falls through to the ordinary
            // reject-only arm, byte-compatible with the unwidened build (the
            // E4/E5 terminal Unsupported arms below are deliberately NOT
            // reachable from this lane: those encode the E4/E5-specific
            // refusal to substitute transport proofs, while a payload-bearing
            // postcondition row keeps today's semantic-claim handling).
            let exact_postcondition_fresh_lane = !exact_e4_e5_formula_lane
                && is_typed_body_aware_exact_direct_obligation(obligation);
            let direct_outcome = if exact_postcondition_fresh_lane {
                let fresh_dispatch = public_claim_binding_context
                    .canonical_public_digests
                    .get(obligation.obligation_id.as_str())
                    .map(|public_semantic_digest| {
                        self.exact_direct_chc_pdr_evidence_with_prevalidated_bundle_seal(
                            bundle,
                            obligation,
                            public_semantic_digest.to_string(),
                            fresh_exact_bundle_seal.clone(),
                            Some(&public_claim_binding_context.contracts),
                            deadline,
                        )
                    });
                match fresh_dispatch {
                    Some(Ok(Some(FreshExactDirectChcPdrDispatch {
                        evidence,
                        receipt: Some(receipt),
                    }))) => {
                        if fresh_exact_direct_receipts
                            .insert(obligation.obligation_id.clone(), receipt)
                            .is_some()
                        {
                            fresh_exact_direct_receipts.remove(&obligation.obligation_id);
                            let mut rejected = self.unsupported_evidence(bundle, obligation);
                            rejected.diagnostics.push(
                                "duplicate live exact-direct receipt for one public obligation; refusing ambiguous authority"
                                    .to_string(),
                            );
                            Ok(Some(rejected))
                        } else {
                            Ok(Some(evidence))
                        }
                    }
                    _ => self.direct_typed_chc_pdr_evidence_for(bundle, obligation),
                }
            } else if exact_e4_e5_formula_lane {
                let Some(public_semantic_digest) = public_claim_binding_context
                    .canonical_public_digests
                    .get(obligation.obligation_id.as_str())
                else {
                    direct_by_id.insert(
                        obligation.obligation_id.clone(),
                        self.unsupported_evidence(bundle, obligation),
                    );
                    continue;
                };
                self.exact_direct_chc_pdr_evidence_with_prevalidated_bundle_seal(
                    bundle,
                    obligation,
                    public_semantic_digest.to_string(),
                    fresh_exact_bundle_seal.clone(),
                    Some(&public_claim_binding_context.contracts),
                    deadline,
                )
                .map(|dispatch| {
                    dispatch.map(|dispatch| {
                        let FreshExactDirectChcPdrDispatch { evidence, receipt } = dispatch;
                        let Some(receipt) = receipt else {
                            return evidence;
                        };
                        if fresh_exact_direct_receipts
                            .insert(obligation.obligation_id.clone(), receipt)
                            .is_some()
                        {
                            fresh_exact_direct_receipts.remove(&obligation.obligation_id);
                            let mut rejected = self.unsupported_evidence(bundle, obligation);
                            rejected.diagnostics.push(
                                "duplicate live exact-direct receipt for one public obligation; refusing ambiguous authority"
                                    .to_string(),
                            );
                            return rejected;
                        }
                        evidence
                    })
                })
            } else {
                self.direct_typed_chc_pdr_evidence_for(bundle, obligation)
            };
            if std::env::var("TRUST_NATIVE_DEBUG").is_ok() {
                let tag = match &direct_outcome {
                    Ok(Some(e)) => {
                        format!("direct status={:?} strength={:?}", e.status, e.proof_strength)
                    }
                    Ok(None) => "direct=None".to_string(),
                    Err(reason) => format!("direct Err -> {reason}"),
                };
                eprintln!(
                    "[NATIVE_TRUSTMC_DIRECT] obl={} kind={:?} expected_native_id={} -> {tag}",
                    obligation.obligation_id, obligation.kind, expected_native_id
                );
            }
            // A compiler-authenticated direct predicate is the complete proof
            // unit for this obligation. The native TrustIr transport proves
            // properties of the executable function body, not that standalone
            // predicate, so it cannot soundly replace an inconclusive direct
            // solve. In particular, a panic-free body can make the transport
            // prove even when a precondition, postcondition, invariant, protocol
            // predicate, or E4/E5 replay formula has a satisfiable bad state.
            let has_complete_public_formula =
                obligation_metadata_value(obligation, TRUST_VC_FORMULA_SCHEMA_METADATA_KEY)
                    .is_some()
                    && obligation_metadata_value(obligation, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
                        .is_some();
            let semantic_claim_requires_exact_direct_input = has_complete_public_formula
                || matches!(&obligation.kind, ObligationKind::Invariant | ObligationKind::Protocol)
                || matches!(
                    &obligation.kind,
                    ObligationKind::Custom { namespace, .. }
                        if namespace == TRUST_VC_HARDENED_NAMESPACE
                );
            // The claim-binding check above authenticates this exact public row
            // against the native module, compiler facts, and replay assertion.
            // Only the compiler's canonical formula-less whole-function panic
            // aggregate may then use the N:1 transport proof unit. Every other
            // row must have an exact standalone direct input.
            let can_defer_to_whole_function_transport =
                obligation_is_whole_function_panic_freedom(bundle, obligation);
            match direct_outcome {
                Ok(Some(mut evidence)) => {
                    if !matches!(evidence.status, EvidenceStatus::Proved | EvidenceStatus::Failed) {
                        evidence.diagnostics.push(if exact_e4_e5_formula_lane {
                            "compiler-authenticated E4/E5 typed formula was not proved by its exact direct CHC query; refusing to replace that result with a whole-function native TrustIr transport proof"
                                .to_string()
                        } else {
                            "exact direct typed CHC formula was not proved by its standalone query; refusing to replace that result with a whole-function native TrustIr transport proof whose translated proof unit does not contain that formula"
                                .to_string()
                        });
                    }
                    evidence
                        .diagnostics
                        .push(native_trust_ir_direct_typed_context_diagnostic(translated));
                    direct_by_id.insert(obligation.obligation_id.clone(), evidence);
                }
                Ok(None) if exact_e4_e5_formula_lane => {
                    let mut evidence = self.unsupported_evidence(bundle, obligation);
                    evidence.diagnostics.push(
                        "compiler-authenticated E4/E5 typed formula has no exact direct CHC input; refusing to substitute a whole-function native TrustIr transport proof"
                            .to_string(),
                    );
                    direct_by_id.insert(obligation.obligation_id.clone(), evidence);
                }
                Ok(None) if semantic_claim_requires_exact_direct_input => {
                    let mut evidence = self.unsupported_evidence(bundle, obligation);
                    evidence.diagnostics.push(
                        "public obligation carries a standalone formula or semantic claim but has no exact direct CHC input; refusing to substitute a whole-function native TrustIr transport proof whose translated proof unit does not contain that claim"
                            .to_string(),
                    );
                    direct_by_id.insert(obligation.obligation_id.clone(), evidence);
                }
                Ok(None) if can_defer_to_whole_function_transport => {
                    deferred_ids.insert(obligation.obligation_id.clone());
                }
                Ok(None) => {
                    let mut evidence = self.unsupported_evidence(bundle, obligation);
                    evidence.diagnostics.push(
                        "formula-less public obligation is not the exact compiler-authenticated whole-function panic-freedom aggregate; refusing to substitute an N:1 native TrustIr transport proof"
                            .to_string(),
                    );
                    direct_by_id.insert(obligation.obligation_id.clone(), evidence);
                }
                Err(reason) => {
                    let mut evidence = self.unsupported_evidence(bundle, obligation);
                    evidence.diagnostics.push(format!(
                        "native trust_mc TrustIr CHC/PDR direct typed input rejected: {reason}"
                    ));
                    direct_by_id.insert(obligation.obligation_id.clone(), evidence);
                }
            }
        }
        if deferred_ids.is_empty() {
            let evidence = obligations
                .iter()
                .map(|obligation| {
                    direct_by_id
                        .remove(&obligation.obligation_id)
                        .unwrap_or_else(|| self.unsupported_evidence(bundle, obligation))
                })
                .collect();
            return finalize_native_bundle_evidence_with_fresh_receipts(
                evidence,
                fresh_exact_direct_receipts,
            );
        }

        // Trust: the path-sensitive transport re-translation below is the
        // expensive in-process CHC/PDR solve. If the per-function budget is
        // already spent, do not start it; degrade the DEFERRED obligations to
        // Timeout (sound: never Proved) while keeping the direct verdicts.
        if trust_mc_budget_deadline_exceeded(deadline) {
            let evidence = obligations
                .iter()
                .map(|obligation| {
                    direct_by_id
                        .remove(&obligation.obligation_id)
                        .unwrap_or_else(|| self.budget_timeout_evidence(bundle, obligation))
                })
                .collect();
            return finalize_native_bundle_evidence_with_fresh_receipts(
                evidence,
                fresh_exact_direct_receipts,
            );
        }

        let (transports, transport_not_proved) = match self
            .native_trust_ir_chc_pdr_proof_transports(native_bundle, deadline)
        {
            Ok(transports) => transports,
            Err(reason) => {
                let evidence = obligations
                    .iter()
                    .map(|obligation| {
                        if let Some(evidence) =
                            direct_by_id.remove(&obligation.obligation_id)
                        {
                            return evidence;
                        }
                        let mut evidence = self.unsupported_evidence(bundle, obligation);
                        evidence.diagnostics.push(format!(
                            "native trust_mc TrustIr CHC/PDR bundle runner did not produce proof-grade evidence: {reason}"
                        ));
                        evidence
                    })
                    .collect();
                return finalize_native_bundle_evidence_with_fresh_receipts(
                    evidence,
                    fresh_exact_direct_receipts,
                );
            }
        };

        let mut transports_by_obligation = BTreeMap::new();
        let mut transport_counts = BTreeMap::<String, usize>::new();
        for transport in transports {
            let lookup_key =
                native_trust_mc_obligation_lookup_key(&transport.diagnostic_transport().native_id);
            *transport_counts.entry(lookup_key.clone()).or_default() += 1;
            transports_by_obligation.entry(lookup_key).or_insert(transport);
        }

        let evidence = obligations
            .iter()
            .map(|obligation| {
                // A directly-proved (or directly-refuted) obligation keeps its
                // direct verdict and direct-path artifacts; only deferred
                // obligations consume the transport.
                if let Some(evidence) = direct_by_id.remove(&obligation.obligation_id) {
                    if std::env::var("TRUST_NATIVE_DEBUG").is_ok() {
                        eprintln!(
                            "[NATIVE_TRUSTMC_RESULT] obl={} kind={:?} FINAL(direct) status={:?} strength={:?}",
                            obligation.obligation_id, obligation.kind, evidence.status, evidence.proof_strength
                        );
                    }
                    return evidence;
                }
                // Trust: the transport solve can exhaust the budget partway
                // through this obligation set; degrade the remainder to Timeout.
                if trust_mc_budget_deadline_exceeded(deadline) {
                    return self.budget_timeout_evidence(bundle, obligation);
                }
                let expected_native_id = native_trust_ir_expected_trust_mc_obligation_id(obligation)
                    .unwrap_or_else(|| obligation.obligation_id.clone());
                let expected_lookup_key =
                    native_trust_mc_obligation_lookup_key(&expected_native_id);
                if transport_counts.get(&expected_lookup_key).is_some_and(|count| *count > 1)
                {
                    let mut evidence = self.unsupported_evidence(bundle, obligation);
                    evidence.diagnostics.push(format!(
                        "native trust_mc TrustIr CHC/PDR bundle returned duplicate proof transports for obligation `{expected_native_id}`"
                    ));
                    return evidence;
                }

                let Some(transport) = transports_by_obligation.remove(&expected_lookup_key)
                else {
                    let mut evidence = self.unsupported_evidence(bundle, obligation);
                    if let Some(reason) = transport_not_proved.get(&expected_lookup_key) {
                        // Trust (T3): the transport solve DID run this row and
                        // did not prove it — surface the row's OWN outcome as
                        // the FIRST diagnostic (the compiler prints only the
                        // first three evidence diagnostics), so the gate log
                        // names the real cause (ay-chc unknown, refutation,
                        // admission rejection) instead of only the generic
                        // "missing `trust.vc.formula.schema`" direct-lane wall.
                        // Status stays Unsupported: a not-proved transport row
                        // carries no proof evidence and no counterexample
                        // artifact, so it neither proves nor refutes here.
                        evidence.diagnostics.insert(
                            0,
                            format!(
                                "native trust_mc TrustIr CHC/PDR transport solved obligation `{expected_native_id}` without a proof: {reason}"
                            ),
                        );
                    } else {
                        evidence.diagnostics.push(format!(
                            "native trust_mc TrustIr CHC/PDR bundle returned no proof transport for obligation `{expected_native_id}`"
                        ));
                    }
                    if std::env::var("TRUST_NATIVE_DEBUG").is_ok() {
                        eprintln!(
                            "[NATIVE_TRUSTMC] obl={} kind={:?} expected_native_id={} -> NO TRANSPORT (not_proved_reason={:?}, available keys: {:?})",
                            obligation.obligation_id, obligation.kind, expected_native_id,
                            transport_not_proved.get(&expected_lookup_key),
                            transports_by_obligation.keys().collect::<Vec<_>>()
                        );
                    }
                    return evidence;
                };

                let native_trust_ir_context_diagnostic = transport.native_trust_ir_context_diagnostic();
                let expected_normalized_input = transport.expected_normalized_input.clone();
                let authority = match transport.evidence.verification.authorized_native_proof() {
                    Ok(authority) => authority,
                    Err(error) => {
                        let mut evidence = self.unsupported_evidence(bundle, obligation);
                        evidence.diagnostics.push(format!(
                            "native trust_mc TrustIr CHC/PDR opaque authority no longer validates: {}",
                            native_typed_chc_pdr_error_reason(error)
                        ));
                        return evidence;
                    }
                };
                let mut evidence = self.evidence_from_authorized_native_typed_chc_pdr_proof(
                    bundle,
                    obligation,
                    &authority,
                    &expected_normalized_input,
                );
                evidence.diagnostics.push(native_trust_ir_context_diagnostic);
                if std::env::var("TRUST_NATIVE_DEBUG").is_ok() {
                    eprintln!(
                        "[NATIVE_TRUSTMC] obl={} kind={:?} FINAL status={:?} strength={:?} diag=[{}]",
                        obligation.obligation_id, obligation.kind, evidence.status,
                        evidence.proof_strength, evidence.diagnostics.join(" | ")
                    );
                }
                evidence
            })
            .collect();
        finalize_native_bundle_evidence_with_fresh_receipts(evidence, fresh_exact_direct_receipts)
    }

    /// Per-obligation ay CHC/PDR solve budget: the configured `timeout_ms`, but
    /// NEVER more than the wall-clock remaining until the per-function
    /// `deadline`. Without this clamp the per-solve budget is the flat
    /// `config.timeout_ms` (default 30s) regardless of how little of the
    /// per-function budget is left, so ONE obligation whose solve diverges (the
    /// ny-cert `certz::{qpair,lincon}_json`/`lincon_lean` serde grind:
    /// re-bitblasting a nested-serde structure) can burn its whole budget while
    /// the between-obligation `trust_mc_budget_deadline_exceeded` check never
    /// gets a turn. Clamping the per-solve budget to the remaining function
    /// deadline makes ay's `is_cancelled`/`solve_deadline` fire within the
    /// function budget instead of grinding to the wall-clock watchdog SIGKILL.
    /// Fail-closed: this only ever SHORTENS the solve budget → earlier Unknown,
    /// never a proof. `1` (not `0`) floor so a not-yet-exceeded deadline never
    /// passes a zero (instant-cancel) budget.
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_solve_timeout_ms(&self, deadline: Option<Instant>) -> u64 {
        let configured = self.config.timeout_ms;
        match deadline {
            Some(d) => {
                let remaining =
                    u64::try_from(d.saturating_duration_since(Instant::now()).as_millis())
                        .unwrap_or(u64::MAX)
                        .max(1);
                // `timeout_ms == 0` is the "unbounded" convention; still cap it
                // to the function deadline. Otherwise take the tighter of the two.
                if configured == 0 { remaining } else { configured.min(remaining) }
            }
            None => configured,
        }
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_chc_pdr_proof_transports(
        &self,
        native_bundle: &trust_ir::NativeVerificationBundle,
        deadline: Option<Instant>,
    ) -> Result<(Vec<NativeTrustIrChcPdrAuthorizedProof>, BTreeMap<String, String>), String> {
        validate_trust_mc_native_admission_contract(native_bundle)?;
        let runner = trust_mc_driver::NativeTrustIrChcPdrRunner::with_solve_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(chc_pdr_engine_from_config(self.config.proof_mode))
                .with_timeout(std::time::Duration::from_millis(
                    self.native_solve_timeout_ms(deadline),
                ))
                .with_proof_certificate(self.config.produce_proofs),
        );
        let bundle_evidence = runner
            .solve_bundle_native_proof_grade(native_bundle)
            .map_err(native_typed_chc_pdr_error_reason)?;
        // Requests whose solve ran but did not produce proof-grade evidence are
        // returned as typed, evidence-free rows. Preserve their exact per-row
        // reason so a failed request cannot be hidden behind a generic missing
        // transport message, while rejecting duplicate/overlapping identities
        // as structural corruption.
        let proved_ids = bundle_evidence
            .obligations
            .iter()
            .map(|row| {
                native_trust_mc_obligation_lookup_key(&row.translated.obligation.obligation_id)
            })
            .collect::<BTreeSet<_>>();
        let mut not_proved = BTreeMap::new();
        for row in bundle_evidence.not_proved {
            let obligation_id = row.translated.obligation.obligation_id;
            let lookup_key = native_trust_mc_obligation_lookup_key(&obligation_id);
            if proved_ids.contains(&lookup_key) {
                return Err(format!(
                    "native trust_mc bundle returned obligation `{obligation_id}` as both proved and not-proved"
                ));
            }
            if row.reason.is_empty()
                || row.reason.trim() != row.reason
                || row.reason.len() > 16 * 1024
                || row.reason.chars().any(char::is_control)
            {
                return Err(format!(
                    "native trust_mc bundle returned a non-canonical not-proved reason for `{obligation_id}`"
                ));
            }
            if not_proved.insert(lookup_key, row.reason).is_some() {
                return Err(format!(
                    "native trust_mc bundle returned duplicate not-proved rows for `{obligation_id}`"
                ));
            }
        }
        Ok((
            bundle_evidence
                .obligations
                .into_iter()
                .map(NativeTrustIrChcPdrAuthorizedProof::try_from_bundle_evidence)
                .collect::<Result<Vec<_>, _>>()?,
            not_proved,
        ))
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_chc_pdr_translated_obligations(
        &self,
        native_bundle: &trust_ir::NativeVerificationBundle,
        deadline: Option<Instant>,
    ) -> Result<Vec<trust_mc_trust_bmc::NativeTrustMcChcPdrObligation>, String> {
        let runner = trust_mc_driver::NativeTrustIrChcPdrRunner::with_solve_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(chc_pdr_engine_from_config(self.config.proof_mode))
                .with_timeout(std::time::Duration::from_millis(
                    self.native_solve_timeout_ms(deadline),
                ))
                .with_proof_certificate(self.config.produce_proofs),
        );
        runner.translate_obligations(native_bundle).map_err(native_typed_chc_pdr_error_reason)
    }

    fn evidence_from_chc_pdr_proof(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        proof: TrustMcChcPdrProofEvidence,
    ) -> ObligationEvidence {
        // Public CHC/PDR evidence is fully reconstructible. The only positive
        // native path retains `AuthorizedNativeTypedChcPdrProof`; a boolean
        // claiming pre-solve validation must never act as a capability.
        let rejection_reasons = missing_proof_grade_metadata(bundle, obligation, &proof);
        debug_assert!(
            !rejection_reasons.is_empty(),
            "raw CHC/PDR evidence must never satisfy the opaque-authority gate"
        );
        let mut evidence = self.unsupported_evidence(bundle, obligation);
        evidence.diagnostics.push(format!(
            "native trust_mc CHC/PDR evidence rejected: {}",
            rejection_reasons.join("; ")
        ));
        evidence
    }

    fn evidence_from_diagnostic_only(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        diagnostic: TrustMcDiagnosticOnlyEvidence,
    ) -> ObligationEvidence {
        let mut evidence = self.unsupported_evidence(bundle, obligation);
        evidence.artifacts = diagnostic_artifacts(&diagnostic);
        evidence.diagnostics.push(format!(
            "native trust_mc diagnostic-only evidence is not a full proof: {}: {}",
            diagnostic.problem_kind, diagnostic.summary
        ));
        if diagnostic.problem_kind == TrustMcFullVerificationProblemKind::Bmc {
            evidence.diagnostics.push(format!(
                "bounded BMC diagnostic evidence is rejected for full verification at configured depth {}",
                self.config.bmc_depth
            ));
        }
        evidence
    }

    fn unsupported_diagnostics(&self, obligation: &TrustObligation) -> Vec<String> {
        if !is_trust_mc_owned_obligation(obligation) {
            return vec![format!(
                "trust-mc verifier-api adapter does not own {:?} obligations",
                obligation.kind
            )];
        }

        let mut diagnostics = Vec::new();
        // Trust (R1 corpus, root-cause surfacing): when the compiler already
        // recorded WHY this obligation has no typed CHC input (the typed-CHC
        // lowering's per-obligation unsupported reason — e.g. an unsupported
        // formula node, a malformed/over-deep payload), lead with that ROOT
        // cause. Without it every fallthrough row stamps only the generic
        // "direct typed trust_mc CHC/PDR input required" wall, which the first
        // corpus sweep measured as the single largest unknown cluster (574
        // rows) — cascade noise that hides the actual construct to fix.
        if let Some(root_reason) =
            metadata_value(&obligation.metadata, TRUST_MC_TYPED_CHC_UNSUPPORTED_REASON_METADATA_KEY)
        {
            diagnostics.push(format!("typed CHC input unavailable (root cause): {root_reason}"));
        }
        diagnostics.push(DIRECT_TYPED_CHC_INPUT_REASON.to_string());
        match self.config.proof_mode {
            TrustMcProofMode::Bmc => diagnostics.push(format!(
                "bounded BMC at depth {} is diagnostic-only for full verification: trust_mc rejects \
FullVerificationProblemKind::Bmc / FullVerificationError::UnsupportedProblem, and this adapter \
omits proof_strength",
                self.config.bmc_depth
            )),
            TrustMcProofMode::FiniteAcyclicBmc => diagnostics.push(
                "finite acyclic BMC is BMC-shaped evidence, not ChcPdrProofEvidence; this adapter requires native CHC/PDR full-verification evidence before assigning proof_strength"
                    .to_string(),
            ),
            TrustMcProofMode::Chc | TrustMcProofMode::PdrIc3 => {
                if let Some(expectation) = self.accepted_chc_pdr_evidence_expectation() {
                    diagnostics.push(expectation.diagnostic());
                }
            }
        }
        diagnostics.push(UNSUPPORTED_PROOF_STRENGTH_REASON.to_string());
        diagnostics.push(MISSING_TYPED_INPUT_REASON.to_string());
        diagnostics.push(REQUIRED_CHC_PDR_EVIDENCE_SHAPE.to_string());
        diagnostics
    }

    fn accepted_chc_pdr_evidence_expectation(&self) -> Option<ChcPdrEvidenceExpectation> {
        match self.config.proof_mode {
            TrustMcProofMode::Chc => Some(ChcPdrEvidenceExpectation {
                proof_kind: "ChcPdrProofKind::ChcValidity",
                proof_strength: ProofStrength {
                    reasoning: ReasoningKind::Chc,
                    assurance: AssuranceLevel::SmtBacked,
                },
            }),
            TrustMcProofMode::PdrIc3 => Some(ChcPdrEvidenceExpectation {
                proof_kind: "ChcPdrProofKind::PdrInvariant",
                proof_strength: ProofStrength {
                    reasoning: ReasoningKind::Pdr,
                    assurance: AssuranceLevel::SmtBacked,
                },
            }),
            TrustMcProofMode::Bmc | TrustMcProofMode::FiniteAcyclicBmc => None,
        }
    }

    fn verify_obligation(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
    ) -> ObligationEvidence {
        if !is_trust_mc_owned_obligation(obligation) {
            return self.unsupported_evidence(bundle, obligation);
        }

        match self.direct_typed_chc_pdr_evidence_for(bundle, obligation) {
            Ok(Some(evidence)) => return evidence,
            Ok(None) => {}
            Err(reason) => {
                let mut evidence = self.unsupported_evidence(bundle, obligation);
                evidence.diagnostics.push(reason);
                return evidence;
            }
        }

        match self.native_full_verifier_evidence_for(bundle, obligation) {
            Ok(Some(evidence)) => {
                let mut evidence =
                    self.evidence_from_native_full_verifier_evidence(bundle, obligation, evidence);
                let serialized_artifact_count = evidence.artifacts.len();
                evidence.artifacts.clear();
                if serialized_artifact_count > 0 {
                    evidence.diagnostics.push(format!(
                        "serialized trust_mc FullVerificationVerdict artifact descriptors suppressed: {serialized_artifact_count} descriptor(s) are audit metadata only, not proof evidence"
                    ));
                }
                evidence.diagnostics.push(
                    "serialized trust_mc FullVerificationVerdict metadata is diagnostic-only; \
direct typed CHC/PDR solving is required before this adapter emits proof evidence"
                        .to_string(),
                );
                if evidence.status == EvidenceStatus::Proved {
                    evidence.status = EvidenceStatus::Unsupported;
                    evidence.proof_strength = None;
                }
                evidence
            }
            Ok(None) => self.unsupported_evidence(bundle, obligation),
            Err(reason) => {
                let mut evidence = self.unsupported_evidence(bundle, obligation);
                evidence.diagnostics.push(reason);
                evidence
            }
        }
    }

    fn direct_typed_chc_pdr_evidence_for(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
    ) -> Result<Option<ObligationEvidence>, String> {
        let Some(input) = self.typed_chc_pdr_obligation_for(bundle, obligation)? else {
            return Ok(None);
        };

        if !matches!(self.config.proof_mode, TrustMcProofMode::Chc | TrustMcProofMode::PdrIc3) {
            return Err(format!(
                "direct typed trust_mc CHC/PDR input is present, but configured proof mode {:?} is not CHC/PDR",
                self.config.proof_mode
            ));
        }

        Ok(Some(self.evidence_from_typed_chc_pdr_obligation(bundle, obligation, input)))
    }

    /// Solve one compiler-authenticated E4/E5 formula and return its public
    /// evidence alongside an optional live exact-direct replay receipt.
    ///
    /// This is the non-serializable handoff for a compiler that must carry proof
    /// authority beyond ordinary verifier-api dispatch. Evidence and receipt
    /// are derived from the same solve; callers should use this adapter-specific
    /// entry point instead of invoking ordinary dispatch and then solving again.
    /// `Ok(None)` means the row lacks an exact direct input. An inconclusive,
    /// refuted, or deadline-expired solve returns evidence with `receipt: None`.
    #[cfg(feature = "trust-mc-native-solver")]
    pub fn exact_direct_chc_pdr_evidence_with_fresh_receipt(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        deadline: Option<Instant>,
    ) -> Result<Option<FreshExactDirectChcPdrDispatch>, String> {
        if !is_typed_body_aware_exact_direct_obligation(obligation) {
            return Ok(None);
        }
        bundle.validate_requested_obligations(std::slice::from_ref(obligation))?;
        let public_semantic_digest =
            bundle.canonical_obligation_semantic_digest_sha256(obligation)?;
        let bundle_seal = FreshExactDirectChcPdrBundleSeal::from_validated_bundle(bundle);
        self.exact_direct_chc_pdr_evidence_with_prevalidated_bundle_seal(
            bundle,
            obligation,
            public_semantic_digest,
            bundle_seal,
            None,
            deadline,
        )
    }

    #[cfg(feature = "trust-mc-native-solver")]
    fn exact_direct_chc_pdr_evidence_with_prevalidated_bundle_seal(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        public_semantic_digest: String,
        bundle_seal: FreshExactDirectChcPdrBundleSeal,
        contract_indices: Option<&BTreeMap<String, Vec<usize>>>,
        deadline: Option<Instant>,
    ) -> Result<Option<FreshExactDirectChcPdrDispatch>, String> {
        if !is_typed_body_aware_exact_direct_obligation(obligation) {
            return Ok(None);
        }
        if !matches!(self.config.proof_mode, TrustMcProofMode::Chc | TrustMcProofMode::PdrIc3) {
            return Err(format!(
                "fresh exact-direct receipt requires CHC/PDR proof mode, got {:?}",
                self.config.proof_mode
            ));
        }
        let Some(input) = self.typed_chc_pdr_obligation_for_with_contract_index(
            bundle,
            obligation,
            contract_indices,
        )?
        else {
            return Ok(None);
        };
        Ok(Some(self.evidence_and_fresh_exact_direct_receipt_from_typed_chc_pdr_obligation(
            bundle,
            obligation,
            input,
            public_semantic_digest,
            bundle_seal,
            deadline,
            // Both dispatch entries deliver the receipt to the compiler's
            // authority installer, so the replay authority may be consumed.
            true,
        )))
    }

    fn typed_chc_pdr_obligation_for(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
    ) -> Result<Option<DirectTypedChcPdrInput>, String> {
        self.typed_chc_pdr_obligation_for_with_contract_index(bundle, obligation, None)
    }

    fn typed_chc_pdr_obligation_for_with_contract_index(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        contract_indices: Option<&BTreeMap<String, Vec<usize>>>,
    ) -> Result<Option<DirectTypedChcPdrInput>, String> {
        // Compiler-native CHC input is a derived transport contract. It must
        // not replace the canonical public `contract_id` after the TrustIr
        // module has committed the public claim. Validate that diagnostic
        // projection through its unique native marker, but select direct proof
        // input only through the ordinary public semantic contract link.
        let native_contract_id = native_trust_ir_synthetic_trust_mc_contract_id(obligation)?;
        let native_contract = if let Some(native_contract_id) = native_contract_id {
            let contract = if let Some(contract_indices) = contract_indices {
                let matching =
                    contract_indices.get(native_contract_id).map_or(&[][..], Vec::as_slice);
                let [index] = matching else {
                    return Err(format!(
                        "obligation `{}` names diagnostic native trust-mc synthetic contract `{native_contract_id}`, but the bundle contains {} matching contracts; expected exactly one",
                        obligation.obligation_id,
                        matching.len()
                    ));
                };
                bundle.contracts.get(*index).ok_or_else(|| {
                    "prevalidated native trust-mc contract index is out of bounds".to_string()
                })?
            } else {
                native_trust_ir_synthetic_trust_mc_contract(bundle, obligation, native_contract_id)?
            };
            validate_native_trust_ir_synthetic_trust_mc_contract_value(
                contract,
                obligation,
                native_contract_id,
            )?;
            Some(contract)
        } else {
            None
        };

        let Some(contract_id) = obligation.contract_id.as_deref() else {
            return Ok(None);
        };
        if native_contract_id == Some(contract_id) {
            // Post-build native transport contracts are diagnostic projections,
            // not canonical public semantics. They can never authorize the
            // direct proof lane. A proof-capable typed CHC contract must have
            // been linked through the public obligation before native identity
            // minting; otherwise the whole-module transport remains the only
            // proof-capable route.
            return Ok(None);
        }

        let matching_contracts: Vec<&TrustContract> = if let Some(contract_indices) =
            contract_indices
        {
            contract_indices
                .get(contract_id)
                .into_iter()
                .flatten()
                .filter_map(|index| bundle.contracts.get(*index))
                .collect()
        } else {
            bundle.contracts.iter().filter(|contract| contract.contract_id == contract_id).collect()
        };
        if matching_contracts.is_empty() {
            return Err(format!(
                "obligation {} references contract `{contract_id}`, but the bundle has no matching contract",
                obligation.obligation_id
            ));
        }

        let mut typed_inputs = Vec::new();
        for contract in matching_contracts {
            if let Some(input) = trust_mc_typed_chc_input_from_contract(contract)? {
                typed_inputs.push((contract, input));
            }
        }

        match typed_inputs.as_slice() {
            [] => Ok(None),
            [(contract, input)] => {
                let has_contract_binding = contract
                    .metadata
                    .iter()
                    .any(|entry| entry.key == TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY);
                let (input, input_digest) = if has_contract_binding
                    || input.native_metadata.is_some()
                {
                    // Legacy proof-capable typed contracts carry their own
                    // native material and complete binding. If either half is
                    // present, remain on the established admission path so a
                    // missing/malformed other half fails exactly as before.
                    (
                        input.clone(),
                        validate_trust_mc_typed_chc_binding(contract, obligation, input)?,
                    )
                } else {
                    // Compiler pre-build pivot: public semantics are committed
                    // in a canonical contract before the native request exists,
                    // so that contract intentionally cannot carry request-local
                    // metadata or binding records. The separately marked native
                    // contract supplies only authenticated provenance. It may
                    // authorize the canonical input only after every semantic
                    // field is proven identical.
                    validate_compiler_canonical_trust_mc_typed_chc_contract(
                        contract, obligation, input,
                    )?;
                    let native_contract = native_contract.ok_or_else(|| {
                        format!(
                            "compiler canonical typed trust_mc contract `{}` for public obligation `{}` requires one authenticated native synthetic-contract marker",
                            contract.contract_id, obligation.obligation_id
                        )
                    })?;
                    let native_input = trust_mc_typed_chc_input_from_contract(native_contract)?
                        .ok_or_else(|| {
                            format!(
                                "authenticated native trust_mc marker contract `{}` has no typed CHC/PDR input",
                                native_contract.contract_id
                            )
                        })?;
                    validate_trust_mc_typed_chc_binding(
                        native_contract,
                        obligation,
                        &native_input,
                    )?;
                    validate_compiler_canonical_trust_mc_semantic_projection(
                        contract,
                        native_contract,
                    )?;
                    let native_obligation_id = native_input.obligation_id.clone().ok_or_else(|| {
                        format!(
                            "authenticated native trust_mc marker contract `{}` is missing its native obligation id",
                            native_contract.contract_id
                        )
                    })?;
                    let native_metadata = native_input.native_metadata.clone().ok_or_else(|| {
                        format!(
                            "authenticated native trust_mc marker contract `{}` is missing native typed CHC obligation metadata",
                            native_contract.contract_id
                        )
                    })?;
                    let mut reconciled = input.clone();
                    reconciled.obligation_id = Some(native_obligation_id);
                    reconciled.native_metadata = Some(native_metadata);
                    (reconciled, trust_mc_typed_chc_contract_input_digest(contract)?)
                };
                // Trust: a whole-function panic-freedom obligation AND the
                // per-function trust-mc default-admission obligation each carry a
                // router-placeholder direct input (no per-VC predicate — the
                // default-admission's is the compiler's `bool_literal(false)`
                // placeholder). Defer them to the path-sensitive transport
                // CHC/PDR solve — strictly more complete — instead of solving the
                // placeholder in the direct lane. This is the SOUNDNESS-critical
                // half of the default-function fix: directly solving the
                // `false` placeholder is a refutation of a VACUOUS encoding, not
                // of the program, and for a certified-havoc-free function that
                // refutation would surface as a FALSE `Failed` (see the
                // refutation soundness gate in
                // `evidence_from_typed_chc_pdr_full_verification`). The compiler
                // instead routes these obligations to a SOUND structural whole-CFG
                // reachability CHC (`trust_mc_default_function_chc_from_trust_ir`:
                // `error` is derived only from bare/unguarded panic blocks, never
                // from a guarded `Inst::Assert` or direct call — each guarded panic
                // keeps its own per-site obligation), which the transport solve
                // discharges. The binding above is still validated, so the
                // transport proof binds to this public obligation. (Generic
                // placeholders that are neither marker remain rejected downstream.)
                if input.origin == TrustMcTypedChcOrigin::RouterPlaceholder
                    && (obligation_is_whole_function_panic_freedom(bundle, obligation)
                        || obligation.is_default_admission())
                {
                    return Ok(None);
                }
                let input_artifact = trust_mc_typed_chc_engine_input_artifact(
                    bundle,
                    obligation,
                    contract_id,
                    &input_digest,
                );
                let trust_mc_obligation = input.to_trust_mc_obligation(bundle, obligation)?;
                Ok(Some(DirectTypedChcPdrInput { trust_mc_obligation, input_artifact }))
            }
            _ => Err(format!(
                "contract `{contract_id}` has multiple typed trust_mc CHC/PDR inputs; refusing to guess"
            )),
        }
    }

    #[cfg(not(feature = "trust-mc-native-solver"))]
    fn evidence_from_typed_chc_pdr_obligation(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        input: DirectTypedChcPdrInput,
    ) -> ObligationEvidence {
        let stats = input.trust_mc_obligation.stats();
        let mut evidence = self.unsupported_evidence(bundle, obligation);
        evidence.artifacts.push(input.input_artifact);
        evidence.diagnostics.push(format!(
            "constructed typed trust_mc ChcVc from trust-verifier-api data, but native typed CHC/PDR solving is disabled; enable trust-bmc/trust-mc-native-solver to run it: obligation={}, function={}, kind={:?}, relations={}, clauses={}",
            input.trust_mc_obligation.obligation_id,
            input.trust_mc_obligation.function_name,
            input.trust_mc_obligation.kind,
            stats.relation_count,
            stats.clause_count
        ));
        evidence
    }

    #[cfg(feature = "trust-mc-native-solver")]
    fn evidence_from_typed_chc_pdr_obligation(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        input: DirectTypedChcPdrInput,
    ) -> ObligationEvidence {
        let public_semantic_digest =
            match bundle.canonical_obligation_semantic_digest_sha256(obligation) {
                Ok(digest) => digest,
                Err(reason) => {
                    let mut evidence = self.unsupported_evidence(bundle, obligation);
                    evidence.artifacts.push(input.input_artifact);
                    evidence.diagnostics.push(format!(
                        "direct typed trust_mc CHC/PDR canonical public binding failed: {reason}"
                    ));
                    return evidence;
                }
            };
        self.evidence_and_fresh_exact_direct_receipt_from_typed_chc_pdr_obligation(
            bundle,
            obligation,
            input,
            public_semantic_digest,
            FreshExactDirectChcPdrBundleSeal::from_validated_bundle(bundle),
            None,
            // Receipt-discarding wrapper: `.evidence` below drops any receipt,
            // so the replay authority must never be consumed on this path — a
            // definitive Proved whose receipt cannot be delivered is exactly
            // the label-suppression failure mode (the row would be excluded
            // from the ay bridge, no S1 authority could mint, and the public
            // Proved label would be demoted at transport).
            false,
        )
        .evidence
    }

    #[cfg(feature = "trust-mc-native-solver")]
    fn evidence_and_fresh_exact_direct_receipt_from_typed_chc_pdr_obligation(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        input: DirectTypedChcPdrInput,
        public_semantic_digest: String,
        bundle_seal: FreshExactDirectChcPdrBundleSeal,
        deadline: Option<Instant>,
        // Whether this caller can DELIVER a live receipt to the compiler's
        // authority installer. Only then may the fresh-replay authority be
        // consumed and definitive Proved evidence minted; every other caller
        // keeps the reject-only candidate path so the row stays
        // non-definitive and the ordinary bridge/S1 lane applies.
        consume_exact_direct_authority: bool,
    ) -> FreshExactDirectChcPdrDispatch {
        let stats = input.trust_mc_obligation.stats();
        let obligation_id = input.trust_mc_obligation.obligation_id.clone();
        let function_name = input.trust_mc_obligation.function_name.clone();
        let kind = input.trust_mc_obligation.kind;
        let input_artifact_hash = input.input_artifact.hash.clone();
        let diagnostics = vec![format!(
            "constructed typed trust_mc ChcVc from trust-verifier-api data: obligation={}, function={}, kind={:?}, relations={}, clauses={}",
            obligation_id, function_name, kind, stats.relation_count, stats.clause_count
        )];

        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            let mut evidence =
                self.evidence_with_status(bundle, obligation, EvidenceStatus::Timeout);
            evidence.artifacts.push(input.input_artifact);
            evidence.diagnostics.extend(diagnostics);
            evidence.diagnostics.push(
                "fresh exact-direct CHC/PDR dispatch deadline elapsed before solve; no live receipt minted"
                    .to_string(),
            );
            return FreshExactDirectChcPdrDispatch { evidence, receipt: None };
        }

        // Retain the exact typed request before the runner consumes it.  The
        // shared driver normalizer derives the solver-input identity from this
        // request, independently of every returned cache/proof/transport field.
        let normalized_input_source = input.trust_mc_obligation.clone();
        let expected_normalized_input =
            match trust_mc_driver::normalized_typed_chc_pdr_input(&normalized_input_source) {
                Ok(expected) => expected,
                Err(error) => {
                    let mut evidence = self.unsupported_evidence(bundle, obligation);
                    evidence.artifacts.push(input.input_artifact);
                    evidence.diagnostics.extend(diagnostics);
                    evidence.diagnostics.push(format!(
                    "native trust_mc typed CHC/PDR pre-solve request could not be normalized: {}",
                    native_typed_chc_pdr_error_reason(error)
                ));
                    return FreshExactDirectChcPdrDispatch { evidence, receipt: None };
                }
            };

        // Clamp the driver's own watchdog to the remaining caller budget. The
        // driver records timeout values in whole milliseconds, so round the
        // remaining duration up rather than accidentally turning a positive
        // sub-millisecond budget into an unbounded zero-millisecond request.
        let configured_timeout = std::time::Duration::from_millis(self.config.timeout_ms);
        let effective_timeout = if let Some(deadline) = deadline {
            let Some(remaining) = deadline.checked_duration_since(Instant::now()) else {
                let mut evidence =
                    self.evidence_with_status(bundle, obligation, EvidenceStatus::Timeout);
                evidence.artifacts.push(input.input_artifact);
                evidence.diagnostics.extend(diagnostics);
                evidence.diagnostics.push(
                    "fresh exact-direct CHC/PDR dispatch deadline elapsed before solver start; no live receipt minted"
                        .to_string(),
                );
                return FreshExactDirectChcPdrDispatch { evidence, receipt: None };
            };
            let rounded_millis = remaining
                .as_millis()
                .saturating_add(u128::from(remaining.subsec_nanos() % 1_000_000 != 0));
            let rounded_remaining =
                std::time::Duration::from_millis(rounded_millis.min(u128::from(u64::MAX)) as u64);
            configured_timeout.min(rounded_remaining)
        } else {
            configured_timeout
        };
        let runner = trust_mc_driver::NativeTypedChcPdrRunner::with_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(chc_pdr_engine_from_config(self.config.proof_mode))
                .with_timeout(effective_timeout)
                .with_proof_certificate(self.config.produce_proofs),
        );
        // The explicit fresh-replay API proves only the submitted CHC. Invoke
        // it solely for callers that can DELIVER the resulting live receipt
        // (the threaded `consume_exact_direct_authority` — the two dispatch
        // entries, whose admission predicate covers the compiler-authenticated
        // E4/E5 and result-referencing postcondition lanes). Every other
        // caller retains the generic reject-only API; it cannot turn a
        // source-unbound CHC candidate into public evidence.
        let solved = if consume_exact_direct_authority {
            runner.solve_full_verification_with_fresh_exact_replay(input.trust_mc_obligation)
        } else {
            runner.solve_full_verification(input.trust_mc_obligation)
        };
        match solved {
            Ok(solved) => {
                let completed_at = Instant::now();
                if !fresh_exact_direct_completion_is_timely(deadline, completed_at) {
                    let mut evidence =
                        self.evidence_with_status(bundle, obligation, EvidenceStatus::Timeout);
                    evidence.artifacts.push(input.input_artifact);
                    evidence.diagnostics.extend(diagnostics);
                    evidence.diagnostics.push(
                        "fresh exact-direct CHC/PDR solve completed after its dispatch deadline; proof and live receipt discarded"
                            .to_string(),
                    );
                    return FreshExactDirectChcPdrDispatch { evidence, receipt: None };
                }

                let mut fallthrough_diagnostics = diagnostics;
                if consume_exact_direct_authority
                    && let Ok(authority) = solved.authorized_native_proof()
                {
                    let mut authority_diagnostics = fallthrough_diagnostics.clone();
                    authority_diagnostics
                        .extend(typed_chc_pdr_full_verification_diagnostics(&solved));
                    let evidence = self.evidence_from_authorized_native_typed_chc_pdr_proof(
                        bundle,
                        obligation,
                        &authority,
                        &expected_normalized_input,
                    );
                    // Definitive Proved evidence iff a deliverable receipt: the
                    // authorized replacement is returned ONLY when consumer
                    // binding fully succeeded AND the receipt mints. Any
                    // shortfall (e.g. the failed-consumer-binding Unsupported
                    // arm) falls through to the reject-only candidate below —
                    // byte-compatible with the unconsumed path except for one
                    // appended diagnostic — so the row stays non-definitive and
                    // the ordinary bridge/S1 authority lane applies. A
                    // definitive Proved without its receipt is exactly the
                    // label-suppression failure mode and is unrepresentable
                    // through this branch.
                    if evidence.status == EvidenceStatus::Proved {
                        let evidence = evidence_with_direct_typed_chc_context(
                            evidence,
                            input.input_artifact,
                            authority_diagnostics,
                        );
                        drop(authority);
                        let receipt = Some(FreshExactDirectChcPdrReceipt {
                            bundle_seal,
                            bundle_id: bundle.bundle_id.clone(),
                            bundle_subject: bundle.subject.clone(),
                            public_obligation_id: obligation.obligation_id.clone(),
                            public_obligation: obligation.clone(),
                            public_semantic_digest,
                            input_artifact_hash,
                            dispatch_deadline: deadline,
                            completed_at,
                            expected_normalized_input,
                            verification: solved,
                        });
                        return FreshExactDirectChcPdrDispatch { evidence, receipt };
                    }
                    drop(authority);
                    fallthrough_diagnostics.push(format!(
                        "fresh exact-direct authority consumption did not yield deliverable Proved evidence (status {:?}); keeping the reject-only candidate",
                        evidence.status
                    ));
                }

                let evidence = self.evidence_from_typed_chc_pdr_full_verification(
                    bundle,
                    obligation,
                    input.input_artifact,
                    fallthrough_diagnostics,
                    solved,
                    expected_normalized_input,
                    false,
                );
                FreshExactDirectChcPdrDispatch { evidence, receipt: None }
            }
            Err(error) => {
                let status = native_typed_chc_pdr_error_status(&error);
                let mut evidence = if status == EvidenceStatus::Unsupported {
                    self.unsupported_evidence(bundle, obligation)
                } else {
                    self.evidence_with_status(bundle, obligation, status)
                };
                evidence.artifacts.push(input.input_artifact);
                evidence.diagnostics.extend(diagnostics);
                evidence.diagnostics.push(format!(
                    "native trust_mc typed CHC/PDR solver did not complete proof-grade obligation: {}",
                    native_typed_chc_pdr_error_reason(error)
                ));
                FreshExactDirectChcPdrDispatch { evidence, receipt: None }
            }
        }
    }

    #[cfg(feature = "trust-mc-native-solver")]
    fn evidence_from_typed_chc_pdr_full_verification(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        input_artifact: EvidenceArtifact,
        mut diagnostics: Vec<String>,
        solved: trust_mc_driver::TypedChcPdrFullVerification,
        expected_normalized_input: TrustMcNativeTypedChcPdrNormalizedInput,
        allow_exact_direct_authority: bool,
    ) -> ObligationEvidence {
        diagnostics.extend(typed_chc_pdr_full_verification_diagnostics(&solved));

        // Authority is deliberately orthogonal to the public candidate status:
        // both CHC-validity and PDR candidates remain `Unknown` until this live,
        // affine capability is consumed. The boolean is recomputed from the
        // authenticated public E4/E5 record, never read from solver output.
        if allow_exact_direct_authority {
            match solved.authorized_native_proof() {
                Ok(authority) => {
                    let evidence = self.evidence_from_authorized_native_typed_chc_pdr_proof(
                        bundle,
                        obligation,
                        &authority,
                        &expected_normalized_input,
                    );
                    return evidence_with_direct_typed_chc_context(
                        evidence,
                        input_artifact,
                        diagnostics,
                    );
                }
                Err(error) => diagnostics.push(format!(
                    "compiler-authenticated exact E4/E5 typed CHC candidate did not retain fresh opaque replay authority: {}",
                    native_typed_chc_pdr_error_reason(error)
                )),
            }
        }

        match &solved.outcome.status {
            trust_mc_core::ChcPdrSolveStatus::Proved { .. } => self
                .evidence_from_proved_typed_chc_pdr_full_verification(
                    bundle,
                    obligation,
                    input_artifact,
                    diagnostics,
                    solved,
                    expected_normalized_input,
                ),
            // SOUNDNESS GATE (refutation direction, fail-closed): a solver-level
            // `Refuted` is a refutation of the ENCODED VC, not necessarily of the
            // program. The typed-CHC encoding over-approximates wherever vcgen
            // havocs a value it cannot model (unmodeled call results, deref-store
            // invalidation, `&mut` argument havoc, opaque frames, ...): a havoc'd
            // local is a free variable the solver may set to any value, so the
            // solver can derive `error` along a path the program can never take
            // (e.g. `v < 0.0` with `bits = v.to_bits()` havoc'd lets the solver
            // pick `v < 0` AND `bits = 0`, "refuting" a provably-unreachable
            // `bits - 1` underflow). Mapping such a refutation to
            // `EvidenceStatus::Failed` is a FALSE refutation — fail-open.
            //
            // A consumer-side structural scan of the ChcVc cannot supply the
            // missing certificate soundly: a havoc'd local and a genuine
            // unconstrained input are both free variables — indistinguishable
            // without producer knowledge. So a bare `Refuted { witness: None }`
            // is demoted to `Unknown`, exactly as the historical fieldless
            // `Refuted` always was. No middle ground that guesses.
            //
            // IMPLEMENTED admissibility path (this was the documented extension
            // path #2, now live): `Refuted { witness: Some(_) }` carries a
            // `trust_mc_core::ChcPdrRefutationWitness` — a per-obligation
            // concreteness certificate plus a machine-checked counterexample,
            // bound to the exact obligation identity, encoded-formula digest,
            // and semantic-configuration digest. A bare producer-threaded
            // transport flag remains inadmissible (it can be forged, replayed,
            // or detached from the formula it claims to certify), so the gate
            // trusts NONE of the witness's digests as such: it recomputes the
            // encoded-formula digest from its OWN pre-solve
            // `normalized_typed_chc_pdr_input` over its OWN retained request,
            // recomputes the semantic-configuration digest from its OWN engine
            // configuration and route, checks the obligation identity against
            // the public obligation, requires the typed exact-encoding
            // concreteness attestation with all-zero counts (zero translation
            // drops, zero havocs INCLUDING "sound" havoc — sound
            // over-approximation is sound for proofs but makes refutations
            // spurious — and zero Undef-diagnostic havocs), and accepts only
            // recognized machine-checked counterexample verification kinds
            // (ay-chc replay-verified trace / direct-SMT witness model). ALL
            // checks pass -> `Failed` with the counterexample surfaced; ANY
            // failure or an absent witness -> the historical `Unknown`
            // demotion. Residual scope note: the witness's concreteness
            // attestation covers the trust-mc encoding stage (the submitted
            // ChcVc -> solver problem lowering, exact-or-reject with real
            // accounting); the ChcVc-production stage stays fail-closed at its
            // own producer boundary (unsupported shapes never emit a
            // MIR-derived typed CHC input) and is bound here by the
            // authenticated contract/binding validation that admitted the
            // typed input.
            trust_mc_core::ChcPdrSolveStatus::Refuted { witness } => {
                let witness_validation = match witness.as_deref() {
                    None => Err(None),
                    Some(witness) => validate_bound_typed_chc_pdr_refutation_witness(
                        bundle,
                        witness,
                        obligation,
                        &solved,
                        &expected_normalized_input,
                        chc_pdr_engine_from_config(self.config.proof_mode),
                    )
                    .map_err(Some),
                };
                match witness_validation {
                    Ok(verification_summary) => self.typed_chc_pdr_solver_outcome_evidence(
                        bundle,
                        obligation,
                        EvidenceStatus::Failed,
                        input_artifact,
                        diagnostics,
                        non_proof_artifacts_from_trust_mc_core_verdict(&solved.verdict),
                        format!(
                            "native trust_mc typed CHC/PDR solver refuted the encoded VC and its refutation witness validated: obligation identity, consumer-recomputed encoded-formula digest, consumer-recomputed semantic-configuration digest, and the exact-encoding concreteness attestation (zero translation drops / havocs / Undef-diagnostic havocs) all checked; counterexample verification: {verification_summary}"
                        ),
                    ),
                    Err(witness_rejection) => {
                        let summary = match witness_rejection {
                            None => "native trust_mc typed CHC/PDR solver refuted the encoded VC; refutation demoted to unknown: the solver returns no witness model and the encoding's concreteness (havoc-freedom) cannot be certified, so the refutation may reflect over-approximated (havoc'd) semantics rather than a reachable program failure; counterexample evidence is not a proof".to_string(),
                            Some(reason) => format!(
                                "native trust_mc typed CHC/PDR solver refuted the encoded VC; refutation demoted to unknown: a refutation witness was attached but failed validation ({reason}), so the refutation may reflect over-approximated (havoc'd) semantics or a detached/forged certificate rather than a reachable program failure; counterexample evidence is not a proof"
                            ),
                        };
                        self.typed_chc_pdr_solver_outcome_evidence(
                            bundle,
                            obligation,
                            EvidenceStatus::Unknown,
                            input_artifact,
                            diagnostics,
                            non_proof_artifacts_from_trust_mc_core_verdict(&solved.verdict),
                            summary,
                        )
                    }
                }
            }
            trust_mc_core::ChcPdrSolveStatus::Unknown { reason } => {
                let status = unknown_typed_chc_pdr_status(reason);
                self.typed_chc_pdr_solver_outcome_evidence(
                    bundle,
                    obligation,
                    status,
                    input_artifact,
                    diagnostics,
                    non_proof_artifacts_from_trust_mc_core_verdict(&solved.verdict),
                    format!(
                        "native trust_mc typed CHC/PDR solver returned {} for obligation: {reason}",
                        evidence_status_label(status)
                    ),
                )
            }
            _ => self.typed_chc_pdr_solver_outcome_evidence(
                bundle,
                obligation,
                EvidenceStatus::Unknown,
                input_artifact,
                diagnostics,
                non_proof_artifacts_from_trust_mc_core_verdict(&solved.verdict),
                "native trust_mc typed CHC/PDR solver returned an unrecognized status".to_string(),
            ),
        }
    }

    #[cfg(feature = "trust-mc-native-solver")]
    fn evidence_from_proved_typed_chc_pdr_full_verification(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        input_artifact: EvidenceArtifact,
        diagnostics: Vec<String>,
        solved: trust_mc_driver::TypedChcPdrFullVerification,
        expected_normalized_input: TrustMcNativeTypedChcPdrNormalizedInput,
    ) -> ObligationEvidence {
        if let Err(reason) =
            validate_native_full_verification_normalized_input(&solved, &expected_normalized_input)
        {
            let mut evidence = self.unsupported_evidence(bundle, obligation);
            evidence.artifacts.push(input_artifact);
            evidence.diagnostics.extend(diagnostics);
            evidence.diagnostics.push(format!(
                "native trust_mc typed CHC/PDR full-verification normalized input rejected: {reason}"
            ));
            return evidence;
        }
        let transport = match solved.native_proof_transport_record() {
            Ok(transport) => transport,
            Err(error) => {
                let mut evidence = self.unsupported_evidence(bundle, obligation);
                evidence.artifacts.push(input_artifact);
                evidence.diagnostics.extend(diagnostics);
                evidence.diagnostics.push(format!(
                    "native trust_mc typed CHC/PDR proof transport was not exported: {}",
                    native_typed_chc_pdr_error_reason(error)
                ));
                return evidence;
            }
        };
        let mut evidence = self.evidence_from_native_full_verifier_evidence(
            bundle,
            obligation,
            native_evidence_from_trust_mc_core_verdict(solved.verdict),
        );
        match validate_native_typed_transport_with_expected_normalized_input(
            bundle,
            obligation,
            &transport,
            Some(&expected_normalized_input),
        ) {
            Ok(()) => {
                evidence = match evidence_with_native_typed_transport_context(
                    evidence, obligation, &transport,
                ) {
                    Ok(evidence) => evidence,
                    Err(reason) => {
                        let mut rejected = self.unsupported_evidence(bundle, obligation);
                        rejected.artifacts.push(input_artifact);
                        rejected.diagnostics.extend(diagnostics);
                        rejected.diagnostics.push(format!(
                            "native trust_mc typed CHC/PDR proof artifacts rejected: {reason}"
                        ));
                        return rejected;
                    }
                };
            }
            Err(reasons) => {
                let mut rejected = self.unsupported_evidence(bundle, obligation);
                rejected.artifacts.push(input_artifact);
                rejected.diagnostics.extend(diagnostics);
                rejected.diagnostics.push(format!(
                    "native trust_mc typed CHC/PDR proof transport rejected: {}",
                    reasons.join("; ")
                ));
                return rejected;
            }
        }
        evidence_with_direct_typed_chc_context(evidence, input_artifact, diagnostics)
    }

    #[cfg(feature = "trust-mc-native-solver")]
    #[allow(clippy::too_many_arguments)]
    fn typed_chc_pdr_solver_outcome_evidence(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        status: EvidenceStatus,
        input_artifact: EvidenceArtifact,
        diagnostics: Vec<String>,
        artifacts: Vec<EvidenceArtifact>,
        summary: String,
    ) -> ObligationEvidence {
        let mut evidence = self.evidence_with_status(bundle, obligation, status);
        evidence.artifacts.push(input_artifact);
        evidence.artifacts.extend(artifacts);
        sort_public_artifacts(&mut evidence.artifacts);
        // Only a `Failed` verdict carries a public counterexample record. The
        // typed-CHC Refuted route reaches this branch with `Failed` ONLY after
        // the refutation soundness gate above validated a digest-bound
        // refutation witness; witnessless or rejected-witness refutations
        // arrive here demoted to Unknown. The record built for `Failed` still
        // claims only a solver-level refutation of the encoded VC — the
        // witness detail (verification kind, binding checks) rides in the
        // summary diagnostic, not as an overclaim here.
        if status == EvidenceStatus::Failed {
            evidence.counterexample =
                Some(trust_mc_counterexample_from_solver_outcome(obligation, &evidence.artifacts));
        }
        evidence.diagnostics.extend(diagnostics);
        evidence.diagnostics.push(summary);
        evidence
    }

    fn native_full_verifier_evidence_for(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
    ) -> Result<Option<TrustMcNativeFullVerifierEvidence>, String> {
        let mut saw_trust_mc_metadata = false;
        let mut skipped_mismatched = Vec::new();

        for candidate in trust_mc_full_verification_metadata_candidates(bundle, obligation) {
            saw_trust_mc_metadata = true;
            let parsed =
                parse_trust_mc_full_verification_metadata(candidate.entry).map_err(|err| {
                    format!(
                        "invalid trust_mc full-verification metadata `{}` from {}: {err}",
                        candidate.entry.key,
                        candidate.scope.description()
                    )
                })?;

            match parsed.match_for_obligation(obligation, candidate.scope)? {
                ParsedMetadataMatch::Applies(verdict) => {
                    return Ok(Some(native_evidence_from_trust_mc_core_verdict(*verdict)));
                }
                ParsedMetadataMatch::DoesNotApply { reason } => skipped_mismatched.push(reason),
            }
        }

        if saw_trust_mc_metadata && !skipped_mismatched.is_empty() {
            Err(format!(
                "trust-mc full-verification metadata was present but did not match obligation {}: {}",
                obligation.obligation_id,
                skipped_mismatched.join("; ")
            ))
        } else {
            Ok(None)
        }
    }
}

/// Build a metadata entry for diagnostic trust-mc-core full-verification verdict data.
///
/// Serialized verdict metadata is never upgraded into public proof evidence by
/// `verify`; proof-grade results can arrive only through the private live
/// native-bundle path that retains its opaque exact-module authority.
#[cfg(feature = "trust-mc-core-types")]
pub fn trust_mc_full_verification_verdict_metadata_entry(
    obligation_id: impl Into<String>,
    verdict: &trust_mc_core::FullVerificationVerdict,
) -> Result<MetadataEntry, serde_json::Error> {
    trust_mc_core_full_verification_verdict_metadata_entry(obligation_id, verdict)
}

#[cfg(any(test, feature = "trust-mc-core-types"))]
fn trust_mc_core_full_verification_verdict_metadata_entry(
    obligation_id: impl Into<String>,
    verdict: &trust_mc_core::FullVerificationVerdict,
) -> Result<MetadataEntry, serde_json::Error> {
    let envelope = TrustMcFullVerificationVerdictEnvelope {
        schema_version: TRUST_MC_FULL_VERIFICATION_VERDICT_METADATA_SCHEMA_VERSION.to_string(),
        obligation_id: obligation_id.into(),
        verdict: verdict.clone(),
    };
    Ok(MetadataEntry {
        key: TRUST_MC_FULL_VERIFICATION_VERDICT_METADATA_KEY.to_string(),
        value: serde_json::to_string(&envelope)?,
    })
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct TrustMcFullVerificationVerdictEnvelope {
    #[serde(default = "default_trust_mc_full_verification_verdict_metadata_schema_version")]
    schema_version: String,
    obligation_id: String,
    verdict: trust_mc_core::FullVerificationVerdict,
}

fn default_trust_mc_full_verification_verdict_metadata_schema_version() -> String {
    TRUST_MC_FULL_VERIFICATION_VERDICT_METADATA_SCHEMA_VERSION.to_string()
}

fn default_trust_mc_typed_chc_obligation_schema_version() -> String {
    TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION.to_string()
}

#[derive(Debug, Clone)]
struct DirectTypedChcPdrInput {
    trust_mc_obligation: trust_mc_core::MirChcPdrObligation,
    input_artifact: EvidenceArtifact,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct TrustMcTypedChcObligationInput {
    #[serde(default = "default_trust_mc_typed_chc_obligation_schema_version")]
    schema_version: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    obligation_id: Option<String>,
    origin: TrustMcTypedChcOrigin,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    function_name: Option<String>,
    query: TrustMcTypedChcQueryInput,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    vars: Vec<TrustMcTypedChcVarInput>,
    relations: Vec<TrustMcTypedChcRelationInput>,
    rules: Vec<TrustMcTypedChcRuleInput>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    native_metadata: Option<trust_mc_core::NativeTypedChcObligationMetadata>,
}

impl TrustMcTypedChcObligationInput {
    fn to_trust_mc_obligation(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
    ) -> Result<trust_mc_core::MirChcPdrObligation, String> {
        if self.schema_version != TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION {
            return Err(format!(
                "unsupported typed trust_mc CHC/PDR schema `{}`",
                self.schema_version
            ));
        }
        if self.origin != TrustMcTypedChcOrigin::MirDerived {
            return Err(
                "typed trust_mc CHC/PDR input is not MIR-derived; router placeholders are not proof input"
                    .to_string(),
            );
        }
        if let Some(input_obligation_id) = self.obligation_id.as_deref()
            && !trust_mc_obligation_identity_matches(obligation, input_obligation_id)
        {
            return Err(format!(
                "typed trust_mc CHC/PDR input names obligation `{input_obligation_id}`, but adapter is verifying `{}` with native TrustIr identity {:?}",
                obligation.obligation_id,
                native_trust_ir_expected_trust_mc_obligation_id(obligation)
            ));
        }

        let kind = trust_mc_mir_kind_from_obligation(&obligation.kind).ok_or_else(|| {
            format!("trust-mc typed CHC/PDR adapter does not own {:?} obligations", obligation.kind)
        })?;
        let function_name = self
            .function_name
            .as_deref()
            .filter(|name| !name.trim().is_empty())
            .map(str::to_string)
            .unwrap_or_else(|| function_name_from_bundle_subject(bundle));
        let vc = self.to_trust_mc_chc_vc()?;
        let native_metadata = self.native_metadata.clone().ok_or_else(|| {
            "typed trust_mc CHC/PDR input is missing native typed CHC obligation metadata; \
proof-grade trust_mc evidence must be bound to native Trust/TrustIr metadata"
                .to_string()
        })?;
        if native_metadata.proof_obligation_ids.len() != 1 {
            return Err(format!(
                "typed trust_mc CHC/PDR native metadata binds grouped proof obligations {:?}; proof-grade public evidence requires exactly one MIR proof obligation",
                native_metadata.proof_obligation_ids
            ));
        }
        let trust_mc_obligation_id = self
            .obligation_id
            .clone()
            .or_else(|| native_trust_ir_expected_trust_mc_obligation_id(obligation))
            .unwrap_or_else(|| obligation.obligation_id.clone());
        native_metadata.validate_for_obligation_id(&trust_mc_obligation_id).map_err(|reasons| {
            format!(
                "typed trust_mc CHC/PDR native metadata failed proof-grade validation: {}",
                reasons.join("; ")
            )
        })?;
        let trust_mc_obligation = trust_mc_core::MirChcPdrObligation::new(
            trust_mc_obligation_id,
            function_name,
            kind,
            vc,
        )
        .with_native_metadata(native_metadata);
        trust_mc_obligation
            .validate()
            .map_err(|err| format!("typed trust_mc CHC/PDR validation failed: {err}"))?;
        Ok(trust_mc_obligation)
    }

    fn to_trust_mc_chc_vc(&self) -> Result<trust_mc_core::ChcVc, String> {
        let mut vc = trust_mc_core::ChcVc::new();
        let mut var_sorts = BTreeMap::new();
        let mut relation_sorts = BTreeMap::new();

        for var in &self.vars {
            if var.name.trim().is_empty() {
                return Err("typed trust_mc CHC/PDR variable name must not be empty".to_string());
            }
            let sort = var.sort.to_trust_mc_sort()?;
            if var_sorts.insert(var.name.clone(), sort.clone()).is_some() {
                return Err(format!(
                    "typed trust_mc CHC/PDR variable `{}` is declared more than once",
                    var.name
                ));
            }
            vc.add_var(trust_mc_core::VarDecl::new(var.name.clone(), sort));
        }

        for relation in &self.relations {
            if relation.name.trim().is_empty() {
                return Err("typed trust_mc CHC/PDR relation name must not be empty".to_string());
            }
            let sorts = relation
                .arg_sorts
                .iter()
                .map(TrustMcTypedChcSortInput::to_trust_mc_sort)
                .collect::<Result<Vec<_>, _>>()?;
            if relation_sorts.insert(relation.name.clone(), sorts.clone()).is_some() {
                return Err(format!(
                    "typed trust_mc CHC/PDR relation `{}` is declared more than once",
                    relation.name
                ));
            }
            vc.add_relation(trust_mc_core::RelationDecl::new(relation.name.clone(), sorts));
        }

        if self.query.target.trim().is_empty() {
            return Err("typed trust_mc CHC/PDR query target must not be empty".to_string());
        }
        if self.rules.is_empty() {
            return Err(
                "typed trust_mc CHC/PDR input has no MIR-derived rules; vacuous CHC input is not proof-grade"
                    .to_string(),
            );
        }
        self.validate_non_vacuous_mir_rule_binding()?;
        vc.query = trust_mc_core::ChcQuery::new().with_target(self.query.target.clone());

        for rule in &self.rules {
            let head = rule.head.to_trust_mc_relation_app(&relation_sorts, &var_sorts)?;
            let body = rule.body.to_trust_mc_rule_body(&relation_sorts, &var_sorts)?;
            vc.add_rule(trust_mc_core::Rule::new(body, head));
        }

        Ok(vc)
    }

    fn validate_non_vacuous_mir_rule_binding(&self) -> Result<(), String> {
        // The LITERAL target, not a trimmed one: this admission check and the
        // driver's own route selection must be asking the same question. The
        // driver matches `rule.head.name` against the query target byte for byte,
        // so a padded target with an unpadded rule head satisfies a trimmed check
        // here while leaving the driver with no rule deriving the query — a
        // trivially-safe rule set admitted as if it carried the violation.
        let query_target = self.query.target.as_str();
        let mut saw_query_rule = false;
        let mut saw_non_vacuous_query_rule = false;

        for rule in &self.rules {
            if rule.body.is_generic_bool_true_fact() {
                return Err(
                    "typed trust_mc CHC/PDR input contains a generic Bool true fact; proof-grade trust_mc input must be bound to MIR-derived rule structure"
                        .to_string(),
                );
            }

            if rule.head.name == query_target {
                saw_query_rule = true;
                if rule.body.has_mir_derived_premise() {
                    saw_non_vacuous_query_rule = true;
                }
            }
        }

        if !saw_query_rule {
            return Err(format!(
                "typed trust_mc CHC/PDR query target `{query_target}` has no MIR-derived rule; vacuous unreachable-query input is not proof-grade"
            ));
        }
        if !saw_non_vacuous_query_rule {
            return Err(format!(
                "typed trust_mc CHC/PDR query target `{query_target}` is derived only by generic facts; proof-grade input requires MIR-derived relation or constraint premises"
            ));
        }

        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum TrustMcTypedChcOrigin {
    MirDerived,
    RouterPlaceholder,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct TrustMcTypedChcQueryInput {
    target: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct TrustMcTypedChcVarInput {
    name: String,
    sort: TrustMcTypedChcSortInput,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct TrustMcTypedChcRelationInput {
    name: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    arg_sorts: Vec<TrustMcTypedChcSortInput>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct TrustMcTypedChcRuleInput {
    head: TrustMcTypedChcRelationAppInput,
    #[serde(default)]
    body: TrustMcTypedChcRuleBodyInput,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct TrustMcTypedChcRuleBodyInput {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    relation: Option<TrustMcTypedChcRelationAppInput>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    constraints: Vec<TrustMcTypedChcExprInput>,
}

impl TrustMcTypedChcRuleBodyInput {
    fn is_generic_bool_true_fact(&self) -> bool {
        self.relation.is_none()
            && self.constraints.len() == 1
            && self.constraints[0].is_bool_const_true()
    }

    fn has_mir_derived_premise(&self) -> bool {
        self.relation.is_some()
            || self.constraints.iter().any(|constraint| !constraint.is_bool_const_true())
    }

    fn to_trust_mc_rule_body(
        &self,
        relation_sorts: &BTreeMap<String, Vec<Sort>>,
        var_sorts: &BTreeMap<String, Sort>,
    ) -> Result<trust_mc_core::RuleBody, String> {
        let relation = self
            .relation
            .as_ref()
            .map(|relation| relation.to_trust_mc_relation_app(relation_sorts, var_sorts))
            .transpose()?;
        let constraints = self
            .constraints
            .iter()
            .map(|constraint| constraint.to_trust_mc_expr(var_sorts))
            .collect::<Result<Vec<_>, _>>()?;
        if let Some(non_bool) = constraints.iter().find(|expr| *expr.sort() != Sort::bool()) {
            return Err(format!(
                "typed trust_mc CHC/PDR rule constraint has non-Bool sort {:?}",
                non_bool.sort()
            ));
        }
        Ok(trust_mc_core::RuleBody::new(relation, constraints))
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct TrustMcTypedChcRelationAppInput {
    name: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    args: Vec<TrustMcTypedChcExprInput>,
}

impl TrustMcTypedChcRelationAppInput {
    fn to_trust_mc_relation_app(
        &self,
        relation_sorts: &BTreeMap<String, Vec<Sort>>,
        var_sorts: &BTreeMap<String, Sort>,
    ) -> Result<trust_mc_core::RelationApp, String> {
        if self.name.trim().is_empty() {
            return Err(
                "typed trust_mc CHC/PDR relation application name must not be empty".to_string()
            );
        }
        let Some(expected_sorts) = relation_sorts.get(&self.name) else {
            return Err(format!(
                "typed trust_mc CHC/PDR relation application `{}` is undeclared",
                self.name
            ));
        };
        let args = self
            .args
            .iter()
            .map(|arg| arg.to_trust_mc_expr(var_sorts))
            .collect::<Result<Vec<_>, _>>()?;
        if args.len() != expected_sorts.len() {
            return Err(format!(
                "typed trust_mc CHC/PDR relation `{}` expects {} argument(s), got {}",
                self.name,
                expected_sorts.len(),
                args.len()
            ));
        }
        for (index, (arg, expected)) in args.iter().zip(expected_sorts).enumerate() {
            if arg.sort() != expected {
                return Err(format!(
                    "typed trust_mc CHC/PDR relation `{}` argument {index} has sort {:?}, expected {:?}",
                    self.name,
                    arg.sort(),
                    expected
                ));
            }
        }
        Ok(trust_mc_core::RelationApp::new(self.name.clone(), args))
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum TrustMcTypedChcSortInput {
    Bool,
    Int,
    Real,
    BitVec { width: u32 },
    Array { index: Box<TrustMcTypedChcSortInput>, element: Box<TrustMcTypedChcSortInput> },
}

impl TrustMcTypedChcSortInput {
    fn to_trust_mc_sort(&self) -> Result<Sort, String> {
        match self {
            Self::Bool => Ok(Sort::bool()),
            Self::Int => Ok(Sort::int()),
            Self::Real => Ok(Sort::real()),
            Self::BitVec { width } if *width > 0 => Ok(Sort::bitvec(*width)),
            Self::BitVec { width } => Err(format!(
                "typed trust_mc CHC/PDR bit-vector width must be positive, got {width}"
            )),
            Self::Array { index, element } => {
                if !matches!(index.as_ref(), Self::Int) {
                    return Err(
                        "typed trust_mc CHC/PDR public arrays require Int indices".to_string()
                    );
                }
                if !matches!(element.as_ref(), Self::Bool | Self::Int | Self::BitVec { width: 1.. })
                {
                    return Err(
                        "typed trust_mc CHC/PDR public arrays require scalar Bool, Int, or positive-width BitVec elements"
                            .to_string(),
                    );
                }
                Ok(Sort::array(index.to_trust_mc_sort()?, element.to_trust_mc_sort()?))
            }
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum TrustMcTypedChcExprInput {
    BoolConst {
        value: bool,
    },
    IntConst {
        value: serde_json::Value,
    },
    RealConst {
        value: serde_json::Value,
    },
    BitVecConst {
        value: serde_json::Value,
        width: u32,
    },
    Var {
        name: String,
        sort: TrustMcTypedChcSortInput,
    },
    Unary {
        op: TrustMcTypedChcUnaryOpInput,
        expr: Box<TrustMcTypedChcExprInput>,
        // Operator parameters for `bv_sign_ext` (`extend_by`), `bv_extract`
        // (`high`/`low`), `int_to_bv` (`width`), and `bv_to_int` (`signed`);
        // absent for every other unary op. Defaults keep pre-existing payloads
        // parsing unchanged.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        extend_by: Option<u32>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        high: Option<u32>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        low: Option<u32>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        width: Option<u32>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        signed: Option<bool>,
    },
    Binary {
        op: TrustMcTypedChcBinaryOpInput,
        lhs: Box<TrustMcTypedChcExprInput>,
        rhs: Box<TrustMcTypedChcExprInput>,
    },
    Select {
        array: Box<TrustMcTypedChcExprInput>,
        index: Box<TrustMcTypedChcExprInput>,
    },
}

impl TrustMcTypedChcExprInput {
    fn is_bool_const_true(&self) -> bool {
        matches!(self, Self::BoolConst { value: true })
    }

    fn to_trust_mc_expr(&self, var_sorts: &BTreeMap<String, Sort>) -> Result<Expr, String> {
        match self {
            Self::BoolConst { value } => Ok(Expr::bool_const(*value)),
            Self::IntConst { value } => {
                trust_mc_typed_chc_int_const_expr(value, "integer constant")
            }
            Self::RealConst { value } => {
                Ok(Expr::real_const(trust_mc_typed_chc_integer_to_i128(value, "real constant")?))
            }
            Self::BitVecConst { value, width } if *width > 0 => Ok(Expr::bitvec_const(
                trust_mc_typed_chc_bitvector_to_i128(value, "bit-vector constant")?,
                *width,
            )),
            Self::BitVecConst { width, .. } => Err(format!(
                "typed trust_mc CHC/PDR bit-vector constant width must be positive, got {width}"
            )),
            Self::Var { name, sort } => {
                if name.trim().is_empty() {
                    return Err(
                        "typed trust_mc CHC/PDR variable reference must not be empty".to_string()
                    );
                }
                let actual_sort = sort.to_trust_mc_sort()?;
                let Some(expected_sort) = var_sorts.get(name) else {
                    return Err(format!(
                        "typed trust_mc CHC/PDR variable reference `{name}` is undeclared"
                    ));
                };
                if &actual_sort != expected_sort {
                    return Err(format!(
                        "typed trust_mc CHC/PDR variable reference `{name}` has sort {:?}, expected {:?}",
                        actual_sort, expected_sort
                    ));
                }
                Ok(Expr::var(name.clone(), actual_sort))
            }
            Self::Unary { op, expr, extend_by, high, low, width, signed } => {
                let expr = expr.to_trust_mc_expr(var_sorts)?;
                trust_mc_typed_chc_unary_expr(*op, expr, *extend_by, *high, *low, *width, *signed)
            }
            Self::Binary { op, lhs, rhs } => {
                let lhs = lhs.to_trust_mc_expr(var_sorts)?;
                let rhs = rhs.to_trust_mc_expr(var_sorts)?;
                trust_mc_typed_chc_binary_expr(*op, lhs, rhs)
            }
            Self::Select { array, index } => {
                let array = array.to_trust_mc_expr(var_sorts)?;
                let index = index.to_trust_mc_expr(var_sorts)?;
                array
                    .try_select(index)
                    .map_err(|err| format!("typed trust_mc CHC/PDR select sort error: {err}"))
            }
        }
    }
}

/// Strict-i128 parse for typed trust_mc CHC/PDR REAL constants (and any
/// other caller that genuinely needs an `i128` value). Real constants keep
/// the strict parse deliberately: a value beyond i128 must fail closed, never
/// wrap. INTEGER constants no longer route through here — they go through
/// `trust_mc_typed_chc_int_const_expr`, which ADMITS the full producer range
/// `i128::MIN ..= u128::MAX` exactly (see its soundness invariant).
fn trust_mc_typed_chc_integer_to_i128(
    value: &serde_json::Value,
    context: &str,
) -> Result<i128, String> {
    if let Some(value) = value.as_i64() {
        return Ok(i128::from(value));
    }
    if let Some(value) = value.as_u64() {
        return Ok(i128::from(value));
    }
    if let Some(value) = value.as_str() {
        let value = value.trim();
        if value.is_empty() {
            return Err(format!("typed trust_mc CHC/PDR {context} must not be empty"));
        }
        return value.parse::<i128>().map_err(|err| {
            format!("typed trust_mc CHC/PDR {context} `{value}` is outside i128: {err}")
        });
    }
    Err(format!("typed trust_mc CHC/PDR {context} must be an integer number or decimal string"))
}

/// Convert a typed trust_mc CHC/PDR INTEGER constant into an Int-sorted
/// expression, admitting the full producer range `i128::MIN ..= u128::MAX`
/// EXACTLY.
///
/// The typed payload carries mathematical-integer constants as decimal
/// strings copied verbatim from the compiler's `TrustSpecExprKind::IntLiteral`
/// (`Formula::Int(i128)` / `Formula::UInt(u128)` stringified by
/// trust-mir-extract), so a `u128`-width type-range bound such as `u128::MAX`
/// in a `#[requires]` predicate arrives here UNDECOMPOSED. The downstream
/// solver lane models Int as UNBOUNDED mathematical integers (ay's LIA stack
/// is BigInt end-to-end), but its literal NODES are i128-wide
/// (`ay_chc::ChcExpr::Int(i128)`; trust-mc-driver's `lower_int_constant`
/// fail-closes past i128), so:
///  - a constant within i128 lowers as a single plain literal (unchanged
///    behavior);
///  - a constant in `i128::MAX+1 ..= u128::MAX` is composed as a base-10^9
///    Horner tree of i64-only literals — the exact shape ay's own SMT-LIB
///    parser emits for out-of-range literals (`encode_large_int`) and that
///    trust-mc's typed lowering already consumes — which evaluates EXACTLY to
///    the constant under unbounded-Int semantics;
///  - anything else (malformed text, beyond `u128::MAX`, below `i128::MIN`)
///    still fails closed.
///
/// SOUNDNESS INVARIANT: this widening only ADMITS well-formed wider constants
/// and re-encodes them exactly (a pure integer identity — no host arithmetic
/// that can wrap, no `as` truncation of a value that does not fit); every
/// constant this function cannot represent exactly keeps failing closed.
fn trust_mc_typed_chc_int_const_expr(
    value: &serde_json::Value,
    context: &str,
) -> Result<Expr, String> {
    if let Some(value) = value.as_i64() {
        return Ok(Expr::int_const(i128::from(value)));
    }
    if let Some(value) = value.as_u64() {
        return Ok(Expr::int_const(i128::from(value)));
    }
    if let Some(text) = value.as_str() {
        let text = text.trim();
        if text.is_empty() {
            return Err(format!("typed trust_mc CHC/PDR {context} must not be empty"));
        }
        if let Ok(narrow) = text.parse::<i128>() {
            return Ok(Expr::int_const(narrow));
        }
        // Reaching this u128 parse means the value is positive and above
        // i128::MAX (anything smaller took the i128 branch; malformed text
        // fails both parses), so it only admits i128::MAX+1 ..= u128::MAX.
        if let Ok(wide) = text.parse::<u128>() {
            return Ok(trust_mc_typed_chc_wide_uint_expr(wide));
        }
        return Err(format!(
            "typed trust_mc CHC/PDR {context} `{text}` is outside the supported mathematical \
             integer constant range (i128::MIN ..= u128::MAX)"
        ));
    }
    Err(format!("typed trust_mc CHC/PDR {context} must be an integer number or decimal string"))
}

/// Base-10^9 Horner composition of an out-of-i128 unsigned constant using
/// i64-only literals: `((c0 * 10^9 + c1) * 10^9 + c2) …` — the identical
/// encoding `ay-chc`'s parser (`encode_large_int`) emits for out-of-range
/// SMT-LIB literals and trust-mc's `lower_int_constant` historically emitted
/// past i64, so every node the composed tree contains is one the downstream
/// typed lowering accepts. Every literal fits i64, every operation is
/// Int-sorted (unbounded mathematical integers), and the tree evaluates
/// EXACTLY to `value`: no step wraps or truncates.
fn trust_mc_typed_chc_wide_uint_expr(value: u128) -> Expr {
    const BASE: u128 = 1_000_000_000;
    let mut chunks = Vec::new();
    let mut rest = value;
    while rest > 0 {
        // Exact by construction: rest % BASE < 10^9 always fits i64.
        chunks.push(i64::try_from(rest % BASE).expect("base-10^9 chunk fits i64"));
        rest /= BASE;
    }
    if chunks.is_empty() {
        chunks.push(0);
    }
    let mut chunks = chunks.into_iter().rev();
    let first = Expr::int_const(i128::from(chunks.next().expect("chunk list is non-empty")));
    // `int_mul`/`int_add` assert Int×Int sorts; both operands here are always
    // freshly built Int constants/compositions, so the assertion cannot fire.
    chunks.fold(first, |acc, chunk| {
        acc.int_mul(Expr::int_const(i128::try_from(BASE).expect("base fits i128")))
            .int_add(Expr::int_const(i128::from(chunk)))
    })
}

/// Parse a BIT-VECTOR constant's bit pattern into the `i128` that
/// `Expr::bitvec_const` masks to `width`. Unlike a mathematical integer, a
/// 128-bit BV value ranges over `0..=u128::MAX`, so accept the full unsigned
/// range by reinterpreting a u128 bit pattern into i128 (e.g. `u128::MAX` ->
/// all-ones -> `-1`). Signed is tried first so negatives and `0..=i128::MAX`
/// keep their natural value; the unsigned fallback only covers
/// `i128::MAX+1 ..= u128::MAX`. (The REAL path deliberately keeps the strict
/// i128 parse — a real constant beyond i128 must fail closed, not wrap. The
/// INT path admits `i128::MAX+1 ..= u128::MAX` via exact Horner composition
/// in `trust_mc_typed_chc_int_const_expr` — never a bit reinterpretation.)
fn trust_mc_typed_chc_bitvector_to_i128(
    value: &serde_json::Value,
    context: &str,
) -> Result<i128, String> {
    if let Some(value) = value.as_i64() {
        return Ok(i128::from(value));
    }
    if let Some(value) = value.as_u64() {
        return Ok(i128::from(value));
    }
    if let Some(value) = value.as_str() {
        let value = value.trim();
        if value.is_empty() {
            return Err(format!("typed trust_mc CHC/PDR {context} must not be empty"));
        }
        return value
            .parse::<i128>()
            .or_else(|_| value.parse::<u128>().map(|bits| bits as i128))
            .map_err(|err| {
                format!(
                    "typed trust_mc CHC/PDR {context} `{value}` is outside the 128-bit range \
                     (neither i128 nor u128): {err}"
                )
            });
    }
    Err(format!("typed trust_mc CHC/PDR {context} must be an integer number or decimal string"))
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum TrustMcTypedChcUnaryOpInput {
    Not,
    Neg,
    BvNot,
    BvSignExt,
    BvExtract,
    /// Int→BV conversion (`int2bv`); carries the target `width` operator param.
    IntToBv,
    /// BV→Int conversion (`bv2nat` / signed two's-complement); carries the
    /// `signed` operator param.
    BvToInt,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum TrustMcTypedChcBinaryOpInput {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    Implies,
    BvAdd,
    BvSub,
    BvMul,
    BvUdiv,
    BvUrem,
    BvAnd,
    BvOr,
    BvXor,
    BvShl,
    BvLshr,
    BvAshr,
    BvUlt,
    BvUle,
    BvUgt,
    BvUge,
    BvSlt,
    BvSle,
}

fn trust_mc_typed_chc_unary_expr(
    op: TrustMcTypedChcUnaryOpInput,
    expr: Expr,
    extend_by: Option<u32>,
    high: Option<u32>,
    low: Option<u32>,
    width: Option<u32>,
    signed: Option<bool>,
) -> Result<Expr, String> {
    // Fail closed on malformed operator parameters: a parameterized op with a
    // missing parameter (or a parameter on an op that takes none) is a
    // producer bug, never something to guess around.
    match op {
        TrustMcTypedChcUnaryOpInput::IntToBv => {
            if extend_by.is_some() || high.is_some() || low.is_some() || signed.is_some() {
                return Err("typed trust_mc CHC/PDR int_to_bv takes only `width`".to_string());
            }
            let Some(width) = width else {
                return Err(
                    "typed trust_mc CHC/PDR int_to_bv requires a `width` parameter".to_string()
                );
            };
            if width == 0 {
                return Err("typed trust_mc CHC/PDR int_to_bv `width` must be positive".to_string());
            }
            return expr
                .try_int2bv(width)
                .map_err(|err| format!("typed trust_mc CHC/PDR unary {op:?} sort error: {err}"));
        }
        TrustMcTypedChcUnaryOpInput::BvToInt => {
            if extend_by.is_some() || high.is_some() || low.is_some() || width.is_some() {
                return Err("typed trust_mc CHC/PDR bv_to_int takes only `signed`".to_string());
            }
            // `signed` selects two's-complement (`bv2int_signed`) vs unsigned
            // magnitude (`bv2int`). The distinction is load-bearing: a top-bit-set
            // byte (u8 0xFF) must yield 255 unsigned, not -1 signed. Mirror
            // `Formula::BvToInt`'s `signed` flag exactly (ay_bridge reference).
            let Some(signed) = signed else {
                return Err(
                    "typed trust_mc CHC/PDR bv_to_int requires a `signed` parameter".to_string()
                );
            };
            let converted = if signed { expr.try_bv2int_signed() } else { expr.try_bv2int() };
            return converted
                .map_err(|err| format!("typed trust_mc CHC/PDR unary {op:?} sort error: {err}"));
        }
        TrustMcTypedChcUnaryOpInput::BvSignExt => {
            if high.is_some() || low.is_some() {
                return Err("typed trust_mc CHC/PDR bv_sign_ext takes only `extend_by`".to_string());
            }
            let Some(extend_by) = extend_by else {
                return Err("typed trust_mc CHC/PDR bv_sign_ext requires an `extend_by` parameter"
                    .to_string());
            };
            if extend_by == 0 {
                return Err(
                    "typed trust_mc CHC/PDR bv_sign_ext `extend_by` must be positive".to_string()
                );
            }
            return expr
                .try_sign_extend(extend_by)
                .map_err(|err| format!("typed trust_mc CHC/PDR unary {op:?} sort error: {err}"));
        }
        TrustMcTypedChcUnaryOpInput::BvExtract => {
            if extend_by.is_some() {
                return Err("typed trust_mc CHC/PDR bv_extract takes only `high`/`low`".to_string());
            }
            let (Some(high), Some(low)) = (high, low) else {
                return Err(
                    "typed trust_mc CHC/PDR bv_extract requires `high` and `low` parameters"
                        .to_string(),
                );
            };
            if high < low {
                return Err(format!(
                    "typed trust_mc CHC/PDR bv_extract requires high >= low, got [{high}:{low}]"
                ));
            }
            return expr
                .try_extract(high, low)
                .map_err(|err| format!("typed trust_mc CHC/PDR unary {op:?} sort error: {err}"));
        }
        _ => {}
    }
    if extend_by.is_some() || high.is_some() || low.is_some() || width.is_some() || signed.is_some()
    {
        return Err(format!("typed trust_mc CHC/PDR unary {op:?} takes no operator parameters"));
    }
    match op {
        TrustMcTypedChcUnaryOpInput::Not => expr.try_not(),
        TrustMcTypedChcUnaryOpInput::Neg => expr.try_int_neg(),
        TrustMcTypedChcUnaryOpInput::BvNot => expr.try_bvnot(),
        TrustMcTypedChcUnaryOpInput::BvSignExt
        | TrustMcTypedChcUnaryOpInput::BvExtract
        | TrustMcTypedChcUnaryOpInput::IntToBv
        | TrustMcTypedChcUnaryOpInput::BvToInt => {
            unreachable!("handled above")
        }
    }
    .map_err(|err| format!("typed trust_mc CHC/PDR unary {op:?} sort error: {err}"))
}

fn trust_mc_typed_chc_binary_expr(
    op: TrustMcTypedChcBinaryOpInput,
    lhs: Expr,
    rhs: Expr,
) -> Result<Expr, String> {
    match op {
        TrustMcTypedChcBinaryOpInput::Add => lhs.try_int_add(rhs),
        TrustMcTypedChcBinaryOpInput::Sub => lhs.try_int_sub(rhs),
        TrustMcTypedChcBinaryOpInput::Mul => lhs.try_int_mul(rhs),
        TrustMcTypedChcBinaryOpInput::Div => lhs.try_int_div(rhs),
        TrustMcTypedChcBinaryOpInput::Mod => lhs.try_int_mod(rhs),
        TrustMcTypedChcBinaryOpInput::Eq => lhs.try_eq(rhs),
        TrustMcTypedChcBinaryOpInput::Ne => lhs.try_eq(rhs).map(Expr::not),
        TrustMcTypedChcBinaryOpInput::Lt => lhs.try_int_lt(rhs),
        TrustMcTypedChcBinaryOpInput::Le => lhs.try_int_le(rhs),
        TrustMcTypedChcBinaryOpInput::Gt => lhs.try_int_gt(rhs),
        TrustMcTypedChcBinaryOpInput::Ge => lhs.try_int_ge(rhs),
        TrustMcTypedChcBinaryOpInput::And => lhs.try_and(rhs),
        TrustMcTypedChcBinaryOpInput::Or => lhs.try_or(rhs),
        TrustMcTypedChcBinaryOpInput::Implies => lhs.try_implies(rhs),
        TrustMcTypedChcBinaryOpInput::BvAdd => lhs.try_bvadd(rhs),
        TrustMcTypedChcBinaryOpInput::BvSub => lhs.try_bvsub(rhs),
        TrustMcTypedChcBinaryOpInput::BvMul => lhs.try_bvmul(rhs),
        TrustMcTypedChcBinaryOpInput::BvUdiv => lhs.try_bvudiv(rhs),
        TrustMcTypedChcBinaryOpInput::BvUrem => lhs.try_bvurem(rhs),
        TrustMcTypedChcBinaryOpInput::BvAnd => lhs.try_bvand(rhs),
        TrustMcTypedChcBinaryOpInput::BvOr => lhs.try_bvor(rhs),
        TrustMcTypedChcBinaryOpInput::BvXor => lhs.try_bvxor(rhs),
        TrustMcTypedChcBinaryOpInput::BvShl => lhs.try_bvshl(rhs),
        TrustMcTypedChcBinaryOpInput::BvLshr => lhs.try_bvlshr(rhs),
        TrustMcTypedChcBinaryOpInput::BvAshr => lhs.try_bvashr(rhs),
        TrustMcTypedChcBinaryOpInput::BvUlt => lhs.try_bvult(rhs),
        TrustMcTypedChcBinaryOpInput::BvUle => lhs.try_bvule(rhs),
        TrustMcTypedChcBinaryOpInput::BvUgt => lhs.try_bvugt(rhs),
        TrustMcTypedChcBinaryOpInput::BvUge => lhs.try_bvuge(rhs),
        TrustMcTypedChcBinaryOpInput::BvSlt => lhs.try_bvslt(rhs),
        TrustMcTypedChcBinaryOpInput::BvSle => lhs.try_bvsle(rhs),
    }
    .map_err(|err| format!("typed trust_mc CHC/PDR binary {op:?} sort error: {err}"))
}

fn trust_mc_typed_chc_input_from_contract(
    contract: &TrustContract,
) -> Result<Option<TrustMcTypedChcObligationInput>, String> {
    let (schema, value) = match &contract.predicate {
        ContractPredicate::MathIr { schema, value }
        | ContractPredicate::CanonicalJson { schema, value }
        | ContractPredicate::TrustIr { schema, value } => (schema, value),
        ContractPredicate::TrustExpr { .. }
        | ContractPredicate::MemoryIr { .. }
        | ContractPredicate::TemporalModelRef { .. }
        | ContractPredicate::Unsupported { .. } => return Ok(None),
        _ => return Ok(None),
    };

    if schema != TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION {
        return Ok(None);
    }
    serde_json::from_value(value.clone()).map(Some).map_err(|err| {
        format!(
            "invalid typed trust_mc CHC/PDR input in contract `{}`: {err}",
            contract.contract_id
        )
    })
}

fn validate_compiler_canonical_trust_mc_typed_chc_contract(
    contract: &TrustContract,
    obligation: &TrustObligation,
    input: &TrustMcTypedChcObligationInput,
) -> Result<(), String> {
    if contract.kind != ContractKind::Asserts {
        return Err(format!(
            "compiler canonical typed trust_mc contract `{}` has kind {:?}, expected Asserts",
            contract.contract_id, contract.kind
        ));
    }
    let value = match &contract.predicate {
        ContractPredicate::MathIr { schema, value }
            if schema == TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION =>
        {
            value
        }
        ContractPredicate::MathIr { schema, .. } => {
            return Err(format!(
                "compiler canonical typed trust_mc contract `{}` has MathIr schema `{schema}`, expected `{TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION}`",
                contract.contract_id
            ));
        }
        _ => {
            return Err(format!(
                "compiler canonical typed trust_mc contract `{}` must use exact ContractPredicate::MathIr schema `{TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION}`",
                contract.contract_id
            ));
        }
    };
    if contract.source != obligation.source {
        return Err(format!(
            "compiler canonical typed trust_mc contract `{}` source does not exactly match public obligation `{}` source",
            contract.contract_id, obligation.obligation_id
        ));
    }
    if input.schema_version != TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION {
        return Err(format!(
            "compiler canonical typed trust_mc contract `{}` payload schema is `{}`, expected `{TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION}`",
            contract.contract_id, input.schema_version
        ));
    }
    if input.origin != TrustMcTypedChcOrigin::MirDerived {
        return Err(format!(
            "compiler canonical typed trust_mc contract `{}` is not MIR-derived",
            contract.contract_id
        ));
    }
    if input.obligation_id.as_deref() != Some(obligation.obligation_id.as_str()) {
        return Err(format!(
            "compiler canonical typed trust_mc contract `{}` must name exact public obligation `{}`, got {:?}",
            contract.contract_id, obligation.obligation_id, input.obligation_id
        ));
    }
    if input.native_metadata.is_some()
        || value.get("native_metadata").is_some()
        || contract.metadata.iter().any(|entry| {
            matches!(
                entry.key.as_str(),
                TRUST_MC_TYPED_CHC_SOURCE_DIGEST_METADATA_KEY
                    | TRUST_MC_TYPED_CHC_VC_DIGEST_METADATA_KEY
                    | TRUST_MC_TYPED_CHC_SYNTHETIC_DIGEST_METADATA_KEY
                    | TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY
            )
        })
    {
        return Err(format!(
            "compiler canonical typed trust_mc contract `{}` must not carry request-local native metadata or binding metadata",
            contract.contract_id
        ));
    }
    Ok(())
}

fn validate_compiler_canonical_trust_mc_semantic_projection(
    canonical_contract: &TrustContract,
    native_contract: &TrustContract,
) -> Result<(), String> {
    let semantic_projection = |contract: &TrustContract, role: &str| {
        let ContractPredicate::MathIr { schema, value } = &contract.predicate else {
            return Err(format!(
                "{role} typed trust_mc contract `{}` is not exact MathIr input",
                contract.contract_id
            ));
        };
        if schema != TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION {
            return Err(format!(
                "{role} typed trust_mc contract `{}` has schema `{schema}`, expected `{TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION}`",
                contract.contract_id
            ));
        }
        let mut value = value.clone();
        let object = value.as_object_mut().ok_or_else(|| {
            format!(
                "{role} typed trust_mc contract `{}` payload is not an object",
                contract.contract_id
            )
        })?;
        // These are the only request-local fields. Every semantic field,
        // including schema_version, origin, function, query, variables,
        // relations, rules, and any future field, remains in the comparison.
        object.remove("obligation_id");
        object.remove("native_metadata");
        Ok(value)
    };

    let canonical = semantic_projection(canonical_contract, "compiler canonical")?;
    let native = semantic_projection(native_contract, "authenticated native marker")?;
    if canonical != native {
        return Err(format!(
            "compiler canonical typed trust_mc contract `{}` semantic CHC fields differ from authenticated native marker contract `{}` after reconciling only obligation_id and native_metadata",
            canonical_contract.contract_id, native_contract.contract_id
        ));
    }
    Ok(())
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct TrustMcTypedChcBindingMetadata {
    schema_version: String,
    typed_chc_schema: String,
    public_obligation_id: String,
    native_obligation_id: String,
    synthetic_contract_id: String,
    source_digest: TrustMcTypedChcBindingDigest,
    vc_digest: TrustMcTypedChcBindingDigest,
    synthetic_chc_digest: TrustMcTypedChcBindingDigest,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct TrustMcTypedChcBindingDigest {
    algorithm: String,
    value: String,
}

fn validate_trust_mc_typed_chc_binding(
    contract: &TrustContract,
    obligation: &TrustObligation,
    input: &TrustMcTypedChcObligationInput,
) -> Result<String, String> {
    let input_obligation_id = trust_mc_typed_chc_input_obligation_id(obligation, input);
    let obligation_binding =
        validate_public_trust_mc_typed_chc_binding_for_native_id(obligation, &input_obligation_id)?;
    let contract_binding = trust_mc_typed_chc_binding_from_metadata(
        &contract.metadata,
        "synthetic typed trust_mc contract",
        &contract.contract_id,
    )?;
    if contract_binding != obligation_binding {
        return Err(format!(
            "typed trust_mc CHC/PDR binding metadata mismatch between contract `{}` and obligation `{}`",
            contract.contract_id, obligation.obligation_id
        ));
    }

    let binding = contract_binding;
    if binding.schema_version != TRUST_MC_TYPED_CHC_BINDING_SCHEMA_VERSION {
        return Err(format!(
            "typed trust_mc CHC/PDR binding metadata has unsupported schema `{}`",
            binding.schema_version
        ));
    }
    if binding.typed_chc_schema != TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION {
        return Err(format!(
            "typed trust_mc CHC/PDR binding metadata names input schema `{}`, expected `{}`",
            binding.typed_chc_schema, TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION
        ));
    }
    if binding.public_obligation_id != obligation.obligation_id {
        return Err(format!(
            "typed trust_mc CHC/PDR binding metadata names public obligation `{}`, but adapter is verifying `{}`",
            binding.public_obligation_id, obligation.obligation_id
        ));
    }
    if binding.synthetic_contract_id != contract.contract_id {
        return Err(format!(
            "typed trust_mc CHC/PDR binding metadata names synthetic contract `{}`, but obligation references `{}`",
            binding.synthetic_contract_id, contract.contract_id
        ));
    }

    require_matching_digest_metadata(
        &contract.metadata,
        TRUST_MC_TYPED_CHC_SOURCE_DIGEST_METADATA_KEY,
        &binding.source_digest.value,
        "synthetic typed trust_mc contract",
        &contract.contract_id,
    )?;
    require_matching_digest_metadata(
        &contract.metadata,
        TRUST_MC_TYPED_CHC_VC_DIGEST_METADATA_KEY,
        &binding.vc_digest.value,
        "synthetic typed trust_mc contract",
        &contract.contract_id,
    )?;
    require_matching_digest_metadata(
        &contract.metadata,
        TRUST_MC_TYPED_CHC_SYNTHETIC_DIGEST_METADATA_KEY,
        &binding.synthetic_chc_digest.value,
        "synthetic typed trust_mc contract",
        &contract.contract_id,
    )?;
    require_matching_digest_metadata(
        &obligation.metadata,
        TRUST_MC_TYPED_CHC_SOURCE_DIGEST_METADATA_KEY,
        &binding.source_digest.value,
        "rewritten public trust_mc obligation",
        &obligation.obligation_id,
    )?;
    require_matching_digest_metadata(
        &obligation.metadata,
        TRUST_MC_TYPED_CHC_VC_DIGEST_METADATA_KEY,
        &binding.vc_digest.value,
        "rewritten public trust_mc obligation",
        &obligation.obligation_id,
    )?;
    require_matching_digest_metadata(
        &obligation.metadata,
        TRUST_MC_TYPED_CHC_SYNTHETIC_DIGEST_METADATA_KEY,
        &binding.synthetic_chc_digest.value,
        "rewritten public trust_mc obligation",
        &obligation.obligation_id,
    )?;
    require_matching_digest_metadata(
        &obligation.metadata,
        TRUST_SOURCE_DIGEST_METADATA_KEY,
        &binding.source_digest.value,
        "rewritten public trust_mc obligation",
        &obligation.obligation_id,
    )?;
    require_matching_digest_metadata(
        &obligation.metadata,
        TRUST_VC_DIGEST_METADATA_KEY,
        &binding.vc_digest.value,
        "rewritten public trust_mc obligation",
        &obligation.obligation_id,
    )?;

    let contract_input_digest = trust_mc_typed_chc_contract_input_digest(contract)?;
    if binding.synthetic_chc_digest.value != contract_input_digest {
        return Err(format!(
            "typed trust_mc CHC/PDR binding synthetic digest mismatch: metadata has {}, parsed solver input has {contract_input_digest}",
            binding.synthetic_chc_digest.value
        ));
    }

    Ok(contract_input_digest)
}

fn validate_public_trust_mc_typed_chc_binding(
    obligation: &TrustObligation,
) -> Result<TrustMcTypedChcBindingMetadata, String> {
    let expected_native_obligation_id = native_trust_ir_expected_trust_mc_obligation_id(obligation)
        .unwrap_or_else(|| obligation.obligation_id.clone());
    validate_public_trust_mc_typed_chc_binding_for_native_id(
        obligation,
        &expected_native_obligation_id,
    )
}

fn validate_public_trust_mc_typed_chc_binding_for_native_id(
    obligation: &TrustObligation,
    expected_native_obligation_id: &str,
) -> Result<TrustMcTypedChcBindingMetadata, String> {
    validate_native_trust_ir_identity_metadata_if_present(obligation)?;
    let binding = trust_mc_typed_chc_binding_from_metadata(
        &obligation.metadata,
        "rewritten public trust_mc obligation",
        &obligation.obligation_id,
    )?;
    validate_trust_mc_typed_chc_binding_identity(
        &binding,
        obligation,
        expected_native_obligation_id,
    )?;
    validate_public_trust_mc_typed_chc_digest_metadata(obligation, &binding)?;
    Ok(binding)
}

fn trust_mc_typed_chc_input_obligation_id(
    obligation: &TrustObligation,
    input: &TrustMcTypedChcObligationInput,
) -> String {
    input
        .obligation_id
        .clone()
        .or_else(|| native_trust_ir_expected_trust_mc_obligation_id(obligation))
        .unwrap_or_else(|| obligation.obligation_id.clone())
}

fn validate_trust_mc_typed_chc_binding_identity(
    binding: &TrustMcTypedChcBindingMetadata,
    obligation: &TrustObligation,
    expected_native_obligation_id: &str,
) -> Result<(), String> {
    if binding.schema_version != TRUST_MC_TYPED_CHC_BINDING_SCHEMA_VERSION {
        return Err(format!(
            "typed trust_mc CHC/PDR binding metadata has unsupported schema `{}`",
            binding.schema_version
        ));
    }
    if binding.typed_chc_schema != TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION {
        return Err(format!(
            "typed trust_mc CHC/PDR binding metadata names input schema `{}`, expected `{}`",
            binding.typed_chc_schema, TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION
        ));
    }
    if binding.public_obligation_id != obligation.obligation_id {
        return Err(format!(
            "typed trust_mc CHC/PDR binding metadata names public obligation `{}`, but adapter is verifying `{}`",
            binding.public_obligation_id, obligation.obligation_id
        ));
    }
    // Compiler emits the suite token as crate name `trust-mc` (hyphen); trust-mc
    // native ids use the identifier form `trust_mc` (underscore). Same obligation
    // — canonicalize the separator so the binding gate accepts matching evidence.
    if binding.native_obligation_id.replace('-', "_")
        != expected_native_obligation_id.replace('-', "_")
    {
        return Err(format!(
            "typed trust_mc CHC/PDR binding metadata names native obligation `{}`, but public obligation requires `{expected_native_obligation_id}`",
            binding.native_obligation_id
        ));
    }
    if binding.synthetic_contract_id.trim().is_empty() {
        return Err(
            "typed trust_mc CHC/PDR binding metadata is missing synthetic contract id".to_string()
        );
    }
    validate_binding_digest("source", &binding.source_digest)?;
    validate_binding_digest("VC", &binding.vc_digest)?;
    validate_binding_digest("synthetic typed CHC", &binding.synthetic_chc_digest)?;
    Ok(())
}

fn validate_public_trust_mc_typed_chc_digest_metadata(
    obligation: &TrustObligation,
    binding: &TrustMcTypedChcBindingMetadata,
) -> Result<(), String> {
    require_matching_digest_metadata(
        &obligation.metadata,
        TRUST_MC_TYPED_CHC_SOURCE_DIGEST_METADATA_KEY,
        &binding.source_digest.value,
        "rewritten public trust_mc obligation",
        &obligation.obligation_id,
    )?;
    require_matching_digest_metadata(
        &obligation.metadata,
        TRUST_MC_TYPED_CHC_VC_DIGEST_METADATA_KEY,
        &binding.vc_digest.value,
        "rewritten public trust_mc obligation",
        &obligation.obligation_id,
    )?;
    require_matching_digest_metadata(
        &obligation.metadata,
        TRUST_MC_TYPED_CHC_SYNTHETIC_DIGEST_METADATA_KEY,
        &binding.synthetic_chc_digest.value,
        "rewritten public trust_mc obligation",
        &obligation.obligation_id,
    )?;
    require_matching_digest_metadata(
        &obligation.metadata,
        TRUST_SOURCE_DIGEST_METADATA_KEY,
        &binding.source_digest.value,
        "rewritten public trust_mc obligation",
        &obligation.obligation_id,
    )?;
    require_matching_digest_metadata(
        &obligation.metadata,
        TRUST_VC_DIGEST_METADATA_KEY,
        &binding.vc_digest.value,
        "rewritten public trust_mc obligation",
        &obligation.obligation_id,
    )?;
    Ok(())
}

fn trust_mc_typed_chc_binding_from_metadata(
    metadata: &[MetadataEntry],
    owner_kind: &str,
    owner_id: &str,
) -> Result<TrustMcTypedChcBindingMetadata, String> {
    let value =
        metadata_value(metadata, TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY).ok_or_else(|| {
            format!(
                "{owner_kind} `{owner_id}` is missing proof-grade typed trust_mc CHC/PDR binding metadata `{TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY}`"
            )
        })?;
    serde_json::from_str(value).map_err(|error| {
        format!(
            "{owner_kind} `{owner_id}` has invalid typed trust_mc CHC/PDR binding metadata: {error}"
        )
    })
}

fn validate_binding_digest(
    label: &str,
    digest: &TrustMcTypedChcBindingDigest,
) -> Result<(), String> {
    if digest.algorithm != "sha256" {
        return Err(format!(
            "typed trust_mc CHC/PDR {label} binding digest uses unsupported algorithm `{}`",
            digest.algorithm
        ));
    }
    if !is_lowercase_sha256_hex(&digest.value) {
        return Err(format!(
            "typed trust_mc CHC/PDR {label} binding digest is not canonical lowercase SHA-256"
        ));
    }
    Ok(())
}

fn require_matching_digest_metadata(
    metadata: &[MetadataEntry],
    key: &str,
    expected: &str,
    owner_kind: &str,
    owner_id: &str,
) -> Result<(), String> {
    let actual = metadata_value(metadata, key).ok_or_else(|| {
        format!(
            "{owner_kind} `{owner_id}` is missing typed trust_mc CHC/PDR digest metadata `{key}`"
        )
    })?;
    if actual != expected {
        return Err(format!(
            "{owner_kind} `{owner_id}` has typed trust_mc CHC/PDR digest metadata `{key}`={actual}, expected {expected}"
        ));
    }
    if !is_lowercase_sha256_hex(actual) {
        return Err(format!(
            "{owner_kind} `{owner_id}` has non-canonical typed trust_mc CHC/PDR digest metadata `{key}`"
        ));
    }
    Ok(())
}

fn metadata_value<'a>(metadata: &'a [MetadataEntry], key: &str) -> Option<&'a str> {
    let mut matches = metadata.iter().filter(|entry| entry.key == key);
    let value = matches.next()?.value.as_str();
    matches.next().is_none().then_some(value)
}

fn trust_mc_typed_chc_contract_input_digest(contract: &TrustContract) -> Result<String, String> {
    let (schema, value) = match &contract.predicate {
        ContractPredicate::MathIr { schema, value }
        | ContractPredicate::CanonicalJson { schema, value }
        | ContractPredicate::TrustIr { schema, value } => (schema, value),
        _ => {
            return Err(format!(
                "contract `{}` does not contain typed trust_mc CHC/PDR input",
                contract.contract_id
            ));
        }
    };
    if schema != TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION {
        return Err(format!(
            "contract `{}` has typed trust_mc CHC/PDR binding metadata but input schema `{schema}`",
            contract.contract_id
        ));
    }
    trust_mc_typed_chc_value_digest(value)
}

fn trust_mc_typed_chc_value_digest(value: &serde_json::Value) -> Result<String, String> {
    let canonical = trust_types::canonical_json_value(value);
    let bytes = serde_json::to_vec(&canonical).map_err(|error| {
        format!("failed to serialize canonical typed trust_mc CHC/PDR input: {error}")
    })?;
    let mut material = b"trust-mc.typed-chc-obligation.digest.v1\0".to_vec();
    material.extend(bytes);
    Ok(stable_sha256_hex(&material))
}

fn is_lowercase_sha256_hex(value: &str) -> bool {
    value.len() == 64
        && value.bytes().all(|byte| byte.is_ascii_hexdigit())
        && value.bytes().all(|byte| !byte.is_ascii_uppercase())
}

fn trust_mc_typed_chc_engine_input_artifact(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    contract_id: &str,
    input_digest: &str,
) -> EvidenceArtifact {
    EvidenceArtifact {
        kind: EvidenceArtifactKind::EngineInput,
        uri: format!(
            "trust-verifier-api://bundle/{}/contract/{contract_id}/obligation/{}/typed-trust-mc-chc",
            bundle.bundle_id, obligation.obligation_id
        ),
        hash: ArtifactHash { algorithm: "sha256".to_string(), value: input_digest.to_string() },
        materialization: None,
    }
}

fn function_name_from_bundle_subject(bundle: &TrustContractBundle) -> String {
    match &bundle.subject {
        trust_verifier_api::BundleSubject::Function { path, .. } => path.clone(),
        trust_verifier_api::BundleSubject::Crate { name } => name.clone(),
        trust_verifier_api::BundleSubject::Artifact { name, .. } => name.clone(),
        _ => bundle.bundle_id.clone(),
    }
}

fn trust_mc_mir_kind_from_obligation(
    kind: &ObligationKind,
) -> Option<trust_mc_core::MirObligationKind> {
    match kind {
        ObligationKind::Assertion => Some(trust_mc_core::MirObligationKind::Assertion),
        ObligationKind::ArithmeticSafety => {
            Some(trust_mc_core::MirObligationKind::ArithmeticSafety)
        }
        ObligationKind::Invariant => Some(trust_mc_core::MirObligationKind::Invariant),
        ObligationKind::Protocol => Some(trust_mc_core::MirObligationKind::Protocol),
        ObligationKind::Custom { namespace, .. } if namespace == TRUST_VC_HARDENED_NAMESPACE => {
            Some(trust_mc_core::MirObligationKind::Assertion)
        }
        // Trust (P1.2): a body-aware `#[ensures]` VC's CHC is `¬postcond ∧
        // body_defs` — an assertion-style reachability goal (prove the negated
        // postcondition unreachable), so it verifies through the same
        // `Assertion` MIR obligation lane as panic/arithmetic goals.
        ObligationKind::Postcondition => Some(trust_mc_core::MirObligationKind::Assertion),
        // Trust (P1.2 precedent, extended to preconditions): the call-site
        // `#[requires]` VC's CHC is `¬precond ∧ body_defs` — the same
        // assertion-unreachability goal, so it rides the same `Assertion` lane.
        // Only router-dispatched payload-carrying VCs reach this mapping.
        ObligationKind::Precondition => Some(trust_mc_core::MirObligationKind::Assertion),
        // E4 initiation/consecution and E5 decrease rows are closed violation
        // formulas. They reach this kind-only conversion only after the
        // obligation-aware typed-payload ownership gate above and the typed CHC
        // contract/binding validators have both succeeded.
        ObligationKind::LoopInvariant | ObligationKind::Termination => {
            Some(trust_mc_core::MirObligationKind::Assertion)
        }
        ObligationKind::MemorySafety
        | ObligationKind::Ownership
        | ObligationKind::Refinement
        | ObligationKind::TemporalSafety
        | ObligationKind::Liveness
        | ObligationKind::Custom { .. } => None,
        _ => None,
    }
}

#[derive(Debug, Clone, Deserialize)]
#[serde(untagged)]
enum TrustMcFullVerificationMetadata {
    Envelope(TrustMcFullVerificationVerdictEnvelope),
    DirectVerdict(trust_mc_core::FullVerificationVerdict),
}

#[derive(Debug, Clone, Copy)]
enum MetadataScope {
    Bundle,
    Obligation,
    ProofItem,
}

impl MetadataScope {
    fn description(self) -> &'static str {
        match self {
            Self::Bundle => "bundle metadata",
            Self::Obligation => "obligation metadata",
            Self::ProofItem => "proof-item metadata",
        }
    }

    fn is_obligation_scoped(self) -> bool {
        matches!(self, Self::Obligation | Self::ProofItem)
    }
}

struct TrustMcFullVerificationMetadataCandidate<'a> {
    entry: &'a MetadataEntry,
    scope: MetadataScope,
}

#[derive(Debug)]
enum ParsedMetadataMatch {
    Applies(Box<trust_mc_core::FullVerificationVerdict>),
    DoesNotApply { reason: String },
}

struct ParsedTrustMcFullVerificationMetadata {
    envelope_obligation_id: Option<String>,
    verdict: trust_mc_core::FullVerificationVerdict,
}

impl ParsedTrustMcFullVerificationMetadata {
    fn match_for_obligation(
        self,
        obligation: &TrustObligation,
        scope: MetadataScope,
    ) -> Result<ParsedMetadataMatch, String> {
        let proof_obligation_id =
            trust_mc_core_verdict_obligation_id(&self.verdict).map(str::to_string);
        if let Some(envelope_id) = self.envelope_obligation_id.as_deref()
            && envelope_id != obligation.obligation_id
        {
            return Ok(ParsedMetadataMatch::DoesNotApply {
                reason: format!("{} names obligation `{envelope_id}`", scope.description()),
            });
        }
        if let Some(proof_id) = proof_obligation_id.as_deref()
            && proof_id != obligation.obligation_id
        {
            return Err(format!(
                "native trust_mc verdict proof obligation id `{proof_id}` does not match requested obligation `{}`",
                obligation.obligation_id
            ));
        }
        if self.envelope_obligation_id.is_none()
            && proof_obligation_id.is_none()
            && !scope.is_obligation_scoped()
        {
            return Ok(ParsedMetadataMatch::DoesNotApply {
                reason: format!("{} direct verdict has no obligation id", scope.description()),
            });
        }
        Ok(ParsedMetadataMatch::Applies(Box::new(self.verdict)))
    }
}

fn trust_mc_full_verification_metadata_candidates<'a>(
    bundle: &'a TrustContractBundle,
    obligation: &'a TrustObligation,
) -> Vec<TrustMcFullVerificationMetadataCandidate<'a>> {
    let mut candidates = Vec::new();
    candidates.extend(
        obligation
            .metadata
            .iter()
            .filter(|entry| entry.key == TRUST_MC_FULL_VERIFICATION_VERDICT_METADATA_KEY)
            .map(|entry| TrustMcFullVerificationMetadataCandidate {
                entry,
                scope: MetadataScope::Obligation,
            }),
    );

    if let Some(proof_item_id) = obligation.proof_item_id.as_deref() {
        for proof_item in
            bundle.proof_items.iter().filter(|item| item.proof_item_id == proof_item_id)
        {
            candidates.extend(
                proof_item
                    .metadata
                    .iter()
                    .filter(|entry| entry.key == TRUST_MC_FULL_VERIFICATION_VERDICT_METADATA_KEY)
                    .map(|entry| TrustMcFullVerificationMetadataCandidate {
                        entry,
                        scope: MetadataScope::ProofItem,
                    }),
            );
        }
    }

    candidates.extend(
        bundle
            .metadata
            .iter()
            .filter(|entry| entry.key == TRUST_MC_FULL_VERIFICATION_VERDICT_METADATA_KEY)
            .map(|entry| TrustMcFullVerificationMetadataCandidate {
                entry,
                scope: MetadataScope::Bundle,
            }),
    );
    candidates
}

fn parse_trust_mc_full_verification_metadata(
    entry: &MetadataEntry,
) -> Result<ParsedTrustMcFullVerificationMetadata, String> {
    let metadata: TrustMcFullVerificationMetadata =
        serde_json::from_str(&entry.value).map_err(|err| err.to_string())?;
    match metadata {
        TrustMcFullVerificationMetadata::Envelope(envelope) => {
            if envelope.schema_version != TRUST_MC_FULL_VERIFICATION_VERDICT_METADATA_SCHEMA_VERSION
            {
                return Err(format!("unsupported metadata schema `{}`", envelope.schema_version));
            }
            Ok(ParsedTrustMcFullVerificationMetadata {
                envelope_obligation_id: Some(envelope.obligation_id),
                verdict: envelope.verdict,
            })
        }
        TrustMcFullVerificationMetadata::DirectVerdict(verdict) => {
            Ok(ParsedTrustMcFullVerificationMetadata { envelope_obligation_id: None, verdict })
        }
    }
}

fn trust_mc_core_verdict_obligation_id(
    verdict: &trust_mc_core::FullVerificationVerdict,
) -> Option<&str> {
    match verdict {
        trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
        } => Some(proof.obligation.obligation_id.as_str()),
        trust_mc_core::FullVerificationVerdict::Failed { .. }
        | trust_mc_core::FullVerificationVerdict::Unknown { .. }
        | trust_mc_core::FullVerificationVerdict::DiagnosticOnly { .. } => None,
    }
}

fn native_evidence_from_trust_mc_core_verdict(
    verdict: trust_mc_core::FullVerificationVerdict,
) -> TrustMcNativeFullVerifierEvidence {
    // This bridge preserves a structurally validated serialized candidate for
    // diagnostics only. It must not ask the public `accepted_*` surface for
    // proof authority: that surface correctly requires a fresh private consumer
    // replay, while the caller below always routes `ChcPdrProof` through the
    // diagnostic-only raw-evidence rejection path. Using candidate validation
    // here retains replay/artifact identity without minting `Proved`.
    let native_candidate = trust_mc_core::validated_native_typed_chc_pdr_candidate(&verdict)
        .map(|accepted| accepted.proof_kind)
        .map_err(|rejection| (rejection.problem_kind, rejection.reasons));
    match verdict {
        trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
        } => match native_candidate {
            Ok(_) => match trust_mc_chc_pdr_proof_from_core(proof) {
                Ok(proof) => TrustMcNativeFullVerifierEvidence::ChcPdrProof(Box::new(proof)),
                Err(reason) => diagnostic_only_from_core_rejection(
                    Some(trust_mc_core::FullVerificationProblemKind::ChcPdr),
                    format!("native trust_mc CHC/PDR proof conversion failed: {reason}"),
                    Vec::new(),
                ),
            },
            Err((problem_kind, reasons)) => diagnostic_only_from_core_rejection(
                problem_kind,
                format!(
                    "native trust_mc full-verification verdict is not native proof-grade: {}",
                    reasons.join("; ")
                ),
                Vec::new(),
            ),
        },
        trust_mc_core::FullVerificationVerdict::Failed { counterexample_artifacts } => {
            diagnostic_only_from_core_rejection(
                Some(trust_mc_core::FullVerificationProblemKind::ChcPdr),
                "native trust_mc CHC/PDR verdict found a counterexample; counterexample evidence is not a proof",
                counterexample_artifacts,
            )
        }
        trust_mc_core::FullVerificationVerdict::Unknown { reason } => {
            diagnostic_only_from_core_rejection(
                Some(trust_mc_core::FullVerificationProblemKind::ChcPdr),
                format!("native trust_mc CHC/PDR verdict was unknown: {reason}"),
                Vec::new(),
            )
        }
        trust_mc_core::FullVerificationVerdict::DiagnosticOnly { evidence } => {
            diagnostic_only_from_core_rejection(
                Some(evidence.problem_kind),
                format!("native trust_mc diagnostic-only verdict: {}", evidence.summary),
                evidence.artifacts,
            )
        }
    }
}

fn diagnostic_only_from_core_rejection(
    problem_kind: Option<trust_mc_core::FullVerificationProblemKind>,
    summary: impl Into<String>,
    artifacts: Vec<trust_mc_core::FullVerificationArtifact>,
) -> TrustMcNativeFullVerifierEvidence {
    let mut diagnostic = TrustMcDiagnosticOnlyEvidence::new(
        problem_kind
            .map_or(TrustMcFullVerificationProblemKind::Chc, trust_mc_problem_kind_from_core),
        summary,
    );
    diagnostic.artifacts = artifacts
        .iter()
        .filter_map(|artifact| trust_mc_artifact_from_core(artifact).ok())
        .collect();
    TrustMcNativeFullVerifierEvidence::DiagnosticOnly(diagnostic)
}

fn trust_mc_chc_pdr_proof_from_core(
    proof: trust_mc_core::ChcPdrProofEvidence,
) -> Result<TrustMcChcPdrProofEvidence, String> {
    let metadata = TrustMcFullProofEvidenceMetadata {
        producer: proof.metadata.producer,
        cache_key: proof.metadata.cache_key.as_ref().map(trust_mc_hash_from_core).transpose()?,
        normalized_input_hash: proof
            .metadata
            .normalized_input_hash
            .as_ref()
            .map(trust_mc_hash_from_core)
            .transpose()?,
        transcript_hashes: trust_mc_hashes_from_core(
            &proof.metadata.transcript_hashes,
            "solver transcript",
        )?,
        replay_log_hashes: trust_mc_hashes_from_core(
            &proof.metadata.replay_log_hashes,
            "replay log",
        )?,
        checked_report_hashes: trust_mc_hashes_from_core(
            &proof.metadata.checked_report_hashes,
            "checked proof report",
        )?,
        replay_check_status: proof
            .metadata
            .replay_check_status
            .map(trust_mc_replay_status_from_core),
    };

    Ok(TrustMcChcPdrProofEvidence {
        kind: trust_mc_proof_kind_from_core(proof.kind),
        stats: TrustMcChcPdrStats {
            relation_count: proof.stats.relation_count,
            clause_count: proof.stats.clause_count,
        },
        metadata,
        native_metadata: proof
            .obligation
            .native_metadata
            .clone()
            .map(TrustMcNativeTypedChcObligationMetadata::from_core),
        invariant_count: proof.invariant_count,
        artifacts: proof
            .artifacts
            .iter()
            .map(trust_mc_artifact_from_core)
            .collect::<Result<Vec<_>, _>>()?,
    })
}

fn trust_mc_hashes_from_core(
    hashes: &[trust_mc_core::EvidenceHash],
    label: &str,
) -> Result<Vec<TrustMcEvidenceHash>, String> {
    hashes
        .iter()
        .map(|hash| {
            trust_mc_hash_from_core(hash)
                .map_err(|err| format!("invalid {label} hash `{}`: {err}", hash.value))
        })
        .collect()
}

fn trust_mc_hash_from_core(
    hash: &trust_mc_core::EvidenceHash,
) -> Result<TrustMcEvidenceHash, String> {
    if hash.algorithm != "sha256" {
        return Err(format!(
            "unsupported evidence hash algorithm `{}`; expected sha256",
            hash.algorithm
        ));
    }
    TrustMcEvidenceHash::sha256(hash.value.clone()).map_err(|err| err.to_string())
}

fn trust_mc_proof_kind_from_core(kind: trust_mc_core::ChcPdrProofKind) -> TrustMcChcPdrProofKind {
    match kind {
        trust_mc_core::ChcPdrProofKind::ChcValidity => TrustMcChcPdrProofKind::ChcValidity,
        trust_mc_core::ChcPdrProofKind::PdrInvariant => TrustMcChcPdrProofKind::PdrInvariant,
    }
}

fn trust_mc_replay_status_from_core(
    status: trust_mc_core::ProofReplayCheckStatus,
) -> TrustMcProofReplayCheckStatus {
    TrustMcProofReplayCheckStatus {
        replay: match status.replay {
            trust_mc_core::ProofReplayStatus::Replayed => TrustMcProofReplayStatus::Replayed,
            trust_mc_core::ProofReplayStatus::Failed => TrustMcProofReplayStatus::Failed,
            trust_mc_core::ProofReplayStatus::Unknown => TrustMcProofReplayStatus::Unknown,
        },
        check: match status.check {
            trust_mc_core::ProofCheckStatus::Accepted => TrustMcProofCheckStatus::Accepted,
            trust_mc_core::ProofCheckStatus::Rejected => TrustMcProofCheckStatus::Rejected,
            trust_mc_core::ProofCheckStatus::Unknown => TrustMcProofCheckStatus::Unknown,
        },
    }
}

#[cfg(feature = "trust-mc-native-solver")]
fn chc_pdr_engine_from_config(proof_mode: TrustMcProofMode) -> trust_mc_core::ChcPdrEngine {
    match proof_mode {
        TrustMcProofMode::Chc => trust_mc_core::ChcPdrEngine::AdaptivePortfolio,
        TrustMcProofMode::PdrIc3 => trust_mc_core::ChcPdrEngine::Pdr,
        TrustMcProofMode::Bmc | TrustMcProofMode::FiniteAcyclicBmc => {
            trust_mc_core::ChcPdrEngine::Auto
        }
    }
}

#[cfg(feature = "trust-mc-native-solver")]
fn native_typed_chc_pdr_error_reason(error: trust_mc_driver::NativeSolveError) -> String {
    match error {
        trust_mc_driver::NativeSolveError::Unsupported(unsupported) => {
            format!("unsupported native solve `{}`: {}", unsupported.reason, unsupported.detail)
        }
        trust_mc_driver::NativeSolveError::InvalidInput { field, detail } => {
            format!("invalid native solve input `{field}`: {detail}")
        }
        trust_mc_driver::NativeSolveError::SolverFailed { reason } => {
            format!("native solver failed: {reason}")
        }
        trust_mc_driver::NativeSolveError::ProofGradeRejected { rejection } => {
            format!("native proof-grade evidence rejected: {rejection}")
        }
        other => format!("unrecognized native solve error: {other}"),
    }
}

#[cfg(feature = "trust-mc-native-solver")]
fn native_typed_chc_pdr_error_status(error: &trust_mc_driver::NativeSolveError) -> EvidenceStatus {
    match error {
        trust_mc_driver::NativeSolveError::Unsupported(_)
        | trust_mc_driver::NativeSolveError::InvalidInput { .. }
        | trust_mc_driver::NativeSolveError::ProofGradeRejected { .. } => {
            EvidenceStatus::Unsupported
        }
        trust_mc_driver::NativeSolveError::SolverFailed { reason } if is_timeout_reason(reason) => {
            EvidenceStatus::Timeout
        }
        trust_mc_driver::NativeSolveError::SolverFailed { .. } => EvidenceStatus::Unknown,
        _ => EvidenceStatus::Unknown,
    }
}

#[cfg(feature = "trust-mc-native-solver")]
fn unknown_typed_chc_pdr_status(reason: &str) -> EvidenceStatus {
    if is_timeout_reason(reason) { EvidenceStatus::Timeout } else { EvidenceStatus::Unknown }
}

#[cfg(feature = "trust-mc-native-solver")]
fn is_timeout_reason(reason: &str) -> bool {
    let reason = reason.to_ascii_lowercase();
    reason.contains("timeout") || reason.contains("timed out")
}

#[cfg(feature = "trust-mc-native-solver")]
fn evidence_status_label(status: EvidenceStatus) -> &'static str {
    status.outcome().as_str()
}

#[cfg(feature = "trust-mc-native-solver")]
fn typed_chc_pdr_full_verification_diagnostics(
    solved: &trust_mc_driver::TypedChcPdrFullVerification,
) -> Vec<String> {
    let outcome = &solved.outcome;
    let mut diagnostics = vec![format!(
        "native trust_mc typed CHC/PDR full-verification runner selected {:?} for obligation {}",
        solved.route, outcome.obligation_id
    )];
    match &outcome.status {
        trust_mc_core::ChcPdrSolveStatus::Proved { proof_kind } => diagnostics.push(format!(
            "native trust_mc typed CHC/PDR full-verification runner proved obligation {} with {:?}: relations={}, clauses={}",
            outcome.obligation_id,
            proof_kind,
            outcome.stats.relation_count,
            outcome.stats.clause_count
        )),
        trust_mc_core::ChcPdrSolveStatus::Refuted { .. } => diagnostics.push(format!(
            "native trust_mc typed CHC/PDR full-verification runner refuted obligation {}; refusing to emit proof evidence",
            outcome.obligation_id
        )),
        trust_mc_core::ChcPdrSolveStatus::Unknown { reason } => diagnostics.push(format!(
            "native trust_mc typed CHC/PDR full-verification runner returned unknown for obligation {}: {reason}",
            outcome.obligation_id
        )),
        _ => diagnostics.push(format!(
            "native trust_mc typed CHC/PDR full-verification runner returned an unrecognized status for obligation {}; refusing to emit proof evidence",
            outcome.obligation_id
        )),
    }
    diagnostics.extend(outcome.diagnostics.clone());
    diagnostics
}

#[cfg(feature = "trust-mc-native-solver")]
fn non_proof_artifacts_from_trust_mc_core_verdict(
    verdict: &trust_mc_core::FullVerificationVerdict,
) -> Vec<EvidenceArtifact> {
    let artifacts = match verdict {
        trust_mc_core::FullVerificationVerdict::Failed { counterexample_artifacts } => {
            counterexample_artifacts.as_slice()
        }
        trust_mc_core::FullVerificationVerdict::DiagnosticOnly { evidence } => {
            evidence.artifacts.as_slice()
        }
        trust_mc_core::FullVerificationVerdict::Proved { .. }
        | trust_mc_core::FullVerificationVerdict::Unknown { .. } => &[],
    };
    artifacts
        .iter()
        .filter_map(|artifact| trust_mc_artifact_from_core(artifact).ok())
        .filter_map(|artifact| public_unmaterialized_artifact_from_trust_mc(&artifact))
        .collect()
}

#[cfg(feature = "trust-mc-native-solver")]
fn trust_mc_counterexample_from_solver_outcome(
    obligation: &TrustObligation,
    artifacts: &[EvidenceArtifact],
) -> ApiCounterexample {
    let artifact_refs = serde_json::to_value(artifacts).unwrap_or_else(|_| serde_json::json!([]));
    ApiCounterexample {
        format: "trust_mc.typed-chc-pdr-counterexample.v1".to_string(),
        data: serde_json::json!({
            "schema": "trust_mc.typed-chc-pdr-counterexample.v1",
            "obligation_id": obligation.obligation_id,
            // Exactly what is known: the solver refuted the ENCODED VC. Nothing
            // here validates the refutation against program semantics — do not
            // claim a "verified" counterexample.
            "source": "native trust_mc typed CHC/PDR solver refuted the encoded VC (solver-level refutation; not independently validated against program semantics)",
            "artifacts": artifact_refs,
        }),
    }
}

/// Validate a typed CHC/PDR refutation witness against consumer-recomputed
/// facts (refutation soundness gate, see the `Refuted` arm of
/// `evidence_from_typed_chc_pdr_full_verification`).
///
/// Nothing producer-supplied is trusted as a certificate by itself: the
/// encoded-formula digest is compared against the consumer's OWN pre-solve
/// `normalized_typed_chc_pdr_input` recomputation over its OWN retained
/// request, the semantic-configuration digest is recomputed from the
/// consumer's OWN engine configuration and route, and the obligation identity
/// is checked against the public obligation. The concreteness attestation must
/// be the typed exact-encoding form with all-zero counts, and the
/// counterexample verification kind must be one of the recognized
/// machine-checked forms (any future kind fails closed).
///
/// Returns `Ok(summary)` describing the accepted counterexample verification,
/// or `Err(reason)` naming the first failed check; every `Err` keeps the
/// refutation demoted to `Unknown`.
#[cfg(feature = "trust-mc-native-solver")]
fn validate_bound_typed_chc_pdr_refutation_witness(
    bundle: &TrustContractBundle,
    witness: &trust_mc_core::ChcPdrRefutationWitness,
    obligation: &TrustObligation,
    solved: &trust_mc_driver::TypedChcPdrFullVerification,
    expected_normalized_input: &TrustMcNativeTypedChcPdrNormalizedInput,
    expected_engine: trust_mc_core::ChcPdrEngine,
) -> Result<String, String> {
    // The public request and every solver-side identity must agree. The
    // bundle is revalidated here so a detached call cannot reuse a witness
    // against an unauthenticated public row.
    bundle.validate_requested_obligations(std::slice::from_ref(obligation)).map_err(|reason| {
        format!("public obligation failed bundle/request authentication: {reason}")
    })?;
    // Compiler-native requests intentionally carry two authenticated names:
    // the stable public VC row and the request-local TrustIR/TrustMC id.  The
    // typed-input admission gate above already binds that pair, and the
    // witness validator below repeats the same check.  Requiring literal
    // equality here made every otherwise-valid compiler-native refutation
    // fail closed solely because it used the native half of the bound pair.
    // Keep literal equality for ordinary rows; admit only the exact native id
    // derived from the public row's authenticated TrustIR metadata.
    if !trust_mc_obligation_identity_matches(obligation, &solved.outcome.obligation_id) {
        return Err(format!(
            "solver outcome obligation `{}` does not match public obligation `{}` or its authenticated native TrustIR identity",
            solved.outcome.obligation_id, obligation.obligation_id,
        ));
    }
    // Recompute the encoded-formula digest from the retained normalized
    // bytes, then require the solver route and cache key to bind those exact
    // bytes and this exact obligation set. Producer-carried digests alone do
    // not authorize a refutation.
    let recomputed_normalized_hash = trust_mc_core::EvidenceHash::sha256_bytes(
        expected_normalized_input.normalized_input.as_bytes(),
    );
    if expected_normalized_input.normalized_input_hash != recomputed_normalized_hash {
        return Err(
            "retained normalized typed-CHC bytes do not match their recorded digest".to_string()
        );
    }
    if solved.route != expected_normalized_input.route {
        return Err(format!(
            "solver route {:?} differs from the retained pre-solve route {:?}",
            solved.route, expected_normalized_input.route
        ));
    }
    solved.cache_key.validate().map_err(|reasons| {
        format!("refutation cache key failed validation: {}", reasons.join("; "))
    })?;
    if solved.cache_key.parts.normalized_input_hash
        != expected_normalized_input.normalized_input_hash
    {
        return Err(
            "refutation cache key is detached from the retained normalized input".to_string()
        );
    }
    if solved.cache_key.parts.obligation_set_hash != expected_normalized_input.obligation_set_hash {
        return Err("refutation cache key is detached from the retained obligation set".to_string());
    }
    let verification_summary = validate_typed_chc_pdr_refutation_witness(
        witness,
        obligation,
        &solved.outcome.obligation_id,
        expected_normalized_input,
        expected_engine,
    )?;

    // Validate the recognized machine-check kind's materialized payload shape.
    // Any future variant fails closed.
    let counterexample: serde_json::Value = serde_json::from_str(&witness.counterexample_json)
        .map_err(|error| format!("counterexample witness is not valid JSON: {error}"))?;
    if counterexample.get("schema").and_then(serde_json::Value::as_str)
        != Some("trust_mc.typed-chc-pdr-counterexample/v1")
    {
        return Err("counterexample witness has an unsupported or missing schema".to_string());
    }
    match &witness.verification {
        trust_mc_core::ChcPdrCexVerification::AyChcReplayVerified { step_count } => {
            if *step_count == 0
                || counterexample.get("step_count").and_then(serde_json::Value::as_u64)
                    != Some(*step_count)
                || counterexample
                    .get("counterexample_debug")
                    .and_then(serde_json::Value::as_str)
                    .is_none_or(str::is_empty)
            {
                return Err(
                    "ay-chc replay witness has an empty or mismatched trace payload".to_string()
                );
            }
            if let Some(source) = counterexample.get("source").and_then(serde_json::Value::as_str)
                && source != "ay-chc-replay-verified-counterexample"
            {
                return Err(format!("ay-chc replay witness has an unrecognized source `{source}`"));
            }
        }
        trust_mc_core::ChcPdrCexVerification::DirectSmtModel => {
            if counterexample.get("source").and_then(serde_json::Value::as_str)
                != Some("direct-smt-acyclic-error-derivation")
                || counterexample.get("witness_model").is_none_or(serde_json::Value::is_null)
            {
                return Err(
                    "direct-SMT witness has no recognized concrete model payload".to_string()
                );
            }
        }
        other => {
            return Err(format!(
                "unrecognized counterexample verification kind {other:?}; failing closed"
            ));
        }
    }

    // The full-verification verdict must carry exactly the materialized
    // counterexample bytes bound above. A digest-valid witness detached from
    // the public artifact is diagnostic only.
    let trust_mc_core::FullVerificationVerdict::Failed { counterexample_artifacts } =
        &solved.verdict
    else {
        return Err("refuted solver outcome is not paired with a failed full-verification verdict"
            .to_string());
    };
    let matching = counterexample_artifacts
        .iter()
        .filter(|artifact| {
            artifact.kind == trust_mc_core::FullVerificationArtifactKind::CounterexampleTrace
        })
        .collect::<Vec<_>>();
    let [artifact] = matching.as_slice() else {
        return Err(format!(
            "full-verification verdict carries {} counterexample-trace artifacts; expected exactly one",
            matching.len()
        ));
    };
    if artifact.materialized_bytes() != Some(witness.counterexample_json.as_bytes()) {
        return Err("materialized counterexample artifact differs from the bound witness payload"
            .to_string());
    }

    Ok(verification_summary)
}

/// Validate the witness fields that bind a refutation to consumer-recomputed
/// obligation, formula, solver-configuration, and exact-lowering facts.
/// Production admission additionally calls
/// [`validate_bound_typed_chc_pdr_refutation_witness`] to bind the solver route,
/// cache key, payload schema, and materialized verdict artifact.
#[cfg(feature = "trust-mc-native-solver")]
fn validate_typed_chc_pdr_refutation_witness(
    witness: &trust_mc_core::ChcPdrRefutationWitness,
    obligation: &TrustObligation,
    solver_obligation_id: &str,
    expected_normalized_input: &TrustMcNativeTypedChcPdrNormalizedInput,
    expected_engine: trust_mc_core::ChcPdrEngine,
) -> Result<String, String> {
    if witness.obligation_id != solver_obligation_id {
        return Err(format!(
            "witness names obligation `{}` but the solver outcome names `{solver_obligation_id}`",
            witness.obligation_id
        ));
    }
    if !trust_mc_obligation_identity_matches(obligation, &witness.obligation_id) {
        return Err(format!(
            "witness obligation `{}` does not match public obligation `{}`",
            witness.obligation_id, obligation.obligation_id
        ));
    }

    if !is_canonical_sha256_digest(&expected_normalized_input.normalized_input_hash) {
        return Err("consumer-recomputed normalized-input digest is not a canonical sha256 digest"
            .to_string());
    }
    if witness.encoded_formula_sha256 != expected_normalized_input.normalized_input_hash.value {
        return Err(format!(
            "witness encoded-formula digest {} does not match the consumer-recomputed normalized-input digest {}",
            witness.encoded_formula_sha256, expected_normalized_input.normalized_input_hash.value
        ));
    }

    let expected_semantic_config = trust_mc_driver::typed_chc_pdr_semantic_config_sha256(
        expected_engine,
        expected_normalized_input.route,
    );
    if witness.semantic_config_sha256 != expected_semantic_config {
        return Err(format!(
            "witness semantic-configuration digest {} does not match the consumer-recomputed digest {}",
            witness.semantic_config_sha256, expected_semantic_config
        ));
    }

    match &witness.concreteness {
        trust_mc_core::ChcPdrEncodingConcreteness::ExactEncoding {
            translation_drops: 0,
            havocs: 0,
            undef_diagnostic_havocs: 0,
        } => {}
        other => {
            return Err(format!(
                "witness concreteness attestation is not an all-zero exact encoding: {other:?}"
            ));
        }
    }

    match &witness.verification {
        trust_mc_core::ChcPdrCexVerification::AyChcReplayVerified { step_count } => {
            Ok(format!("ay-chc replay-verified counterexample trace ({step_count} steps)"))
        }
        trust_mc_core::ChcPdrCexVerification::DirectSmtModel => {
            Ok("direct-SMT acyclic error-derivation witness model".to_string())
        }
        other => {
            Err(format!("unrecognized counterexample verification kind {other:?}; failing closed"))
        }
    }
}

#[cfg(feature = "trust-mc-native-solver")]
fn evidence_with_direct_typed_chc_context(
    mut evidence: ObligationEvidence,
    input_artifact: EvidenceArtifact,
    diagnostics: Vec<String>,
) -> ObligationEvidence {
    evidence.artifacts.push(input_artifact);
    let mut combined_diagnostics = diagnostics;
    combined_diagnostics.extend(evidence.diagnostics);
    evidence.diagnostics = combined_diagnostics;
    evidence
}

#[cfg(feature = "trust-mc-native-solver")]
fn evidence_with_native_typed_transport_context(
    mut evidence: ObligationEvidence,
    obligation: &TrustObligation,
    transport: &TrustMcNativeTypedChcPdrProofTransport,
) -> Result<ObligationEvidence, String> {
    for artifact in public_artifacts_from_native_typed_transport(obligation, transport)? {
        if !evidence.artifacts.contains(&artifact) {
            evidence.artifacts.push(artifact);
        }
    }
    sort_public_artifacts(&mut evidence.artifacts);
    evidence.diagnostics.extend(native_typed_transport_diagnostics(transport));
    Ok(evidence)
}

fn trust_mc_problem_kind_from_core(
    kind: trust_mc_core::FullVerificationProblemKind,
) -> TrustMcFullVerificationProblemKind {
    match kind {
        trust_mc_core::FullVerificationProblemKind::ChcPdr => {
            TrustMcFullVerificationProblemKind::Chc
        }
        trust_mc_core::FullVerificationProblemKind::DiagnosticBmc => {
            TrustMcFullVerificationProblemKind::Bmc
        }
    }
}

fn trust_mc_artifact_from_core(
    artifact: &trust_mc_core::FullVerificationArtifact,
) -> Result<TrustMcFullVerificationArtifact, String> {
    Ok(TrustMcFullVerificationArtifact {
        kind: trust_mc_artifact_kind_from_core(artifact.kind),
        label: artifact.label.clone(),
        digest: artifact.digest.as_ref().map(trust_mc_hash_from_core).transpose()?,
        materialized_bytes: artifact.materialized_bytes().map(<[u8]>::to_vec),
        proof_binding_id: artifact.proof_binding_id().map(|binding| binding.as_str().to_string()),
        referenced_artifacts: artifact
            .referenced_artifacts()
            .iter()
            .map(|reference| {
                Ok((
                    trust_mc_artifact_kind_from_core(reference.kind),
                    trust_mc_hash_from_core(&reference.digest)?,
                ))
            })
            .collect::<Result<Vec<_>, String>>()?,
    })
}

fn trust_mc_artifact_kind_from_core(
    kind: trust_mc_core::FullVerificationArtifactKind,
) -> TrustMcFullVerificationArtifactKind {
    match kind {
        trust_mc_core::FullVerificationArtifactKind::CompilerInput => {
            TrustMcFullVerificationArtifactKind::CompilerInput
        }
        trust_mc_core::FullVerificationArtifactKind::ObligationSet => {
            TrustMcFullVerificationArtifactKind::ObligationSet
        }
        trust_mc_core::FullVerificationArtifactKind::TypedBmcProblem => {
            TrustMcFullVerificationArtifactKind::TypedBmcProblem
        }
        trust_mc_core::FullVerificationArtifactKind::TypedChcProblem => {
            TrustMcFullVerificationArtifactKind::TypedChcProblem
        }
        trust_mc_core::FullVerificationArtifactKind::SmtRendering => {
            TrustMcFullVerificationArtifactKind::SmtRendering
        }
        trust_mc_core::FullVerificationArtifactKind::SolverBinary => {
            TrustMcFullVerificationArtifactKind::SolverBinary
        }
        trust_mc_core::FullVerificationArtifactKind::VerificationOptions => {
            TrustMcFullVerificationArtifactKind::VerificationOptions
        }
        trust_mc_core::FullVerificationArtifactKind::ResourceLimits => {
            TrustMcFullVerificationArtifactKind::ResourceLimits
        }
        trust_mc_core::FullVerificationArtifactKind::NormalizedInput => {
            TrustMcFullVerificationArtifactKind::NormalizedInput
        }
        trust_mc_core::FullVerificationArtifactKind::SolverTranscript => {
            TrustMcFullVerificationArtifactKind::SolverTranscript
        }
        trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel => {
            TrustMcFullVerificationArtifactKind::PdrInvariantModel
        }
        trust_mc_core::FullVerificationArtifactKind::ReplayLog => {
            TrustMcFullVerificationArtifactKind::ReplayLog
        }
        trust_mc_core::FullVerificationArtifactKind::CheckedProofReport => {
            TrustMcFullVerificationArtifactKind::CheckedProofReport
        }
        trust_mc_core::FullVerificationArtifactKind::CounterexampleTrace => {
            TrustMcFullVerificationArtifactKind::CounterexampleTrace
        }
        trust_mc_core::FullVerificationArtifactKind::DiagnosticTrace => {
            TrustMcFullVerificationArtifactKind::DiagnosticTrace
        }
        trust_mc_core::FullVerificationArtifactKind::EvidenceManifest => {
            TrustMcFullVerificationArtifactKind::EvidenceManifest
        }
    }
}

/// Bridge representation of trust-mc's native full-verifier evidence.
///
/// The local shape intentionally mirrors the native trust_mc `FullVerificationVerdict`
/// cases needed by this adapter without making this crate depend on a partially
/// synchronized trust_mc checkout while the factory workers are landing pieces in
/// parallel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TrustMcNativeFullVerifierEvidence {
    /// `FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(..) }`.
    ChcPdrProof(Box<TrustMcChcPdrProofEvidence>),

    /// Native typed CHC/PDR proof transport record.
    #[cfg(feature = "trust-mc-native-solver")]
    TypedChcPdrProofTransport(TrustMcNativeTypedChcPdrProofTransport),

    /// `FullVerificationVerdict::DiagnosticOnly { .. }`.
    DiagnosticOnly(TrustMcDiagnosticOnlyEvidence),
}

/// Proof evidence accepted from trust-mc's CHC/PDR-family full verifier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustMcChcPdrProofEvidence {
    pub kind: TrustMcChcPdrProofKind,
    pub stats: TrustMcChcPdrStats,
    pub metadata: TrustMcFullProofEvidenceMetadata,
    pub native_metadata: Option<TrustMcNativeTypedChcObligationMetadata>,
    pub invariant_count: usize,
    pub artifacts: Vec<TrustMcFullVerificationArtifact>,
}

impl TrustMcChcPdrProofEvidence {
    /// Creates CHC validity proof evidence.
    #[must_use]
    pub fn chc_validity(stats: TrustMcChcPdrStats) -> Self {
        Self {
            kind: TrustMcChcPdrProofKind::ChcValidity,
            stats,
            metadata: TrustMcFullProofEvidenceMetadata::default(),
            native_metadata: None,
            invariant_count: 0,
            artifacts: Vec::new(),
        }
    }

    /// Creates PDR invariant proof evidence.
    #[must_use]
    pub fn pdr_invariant(stats: TrustMcChcPdrStats, invariant_count: usize) -> Self {
        Self {
            kind: TrustMcChcPdrProofKind::PdrInvariant,
            stats,
            metadata: TrustMcFullProofEvidenceMetadata::default(),
            native_metadata: None,
            invariant_count,
            artifacts: Vec::new(),
        }
    }

    /// Attaches proof metadata.
    #[must_use]
    pub fn with_metadata(mut self, metadata: TrustMcFullProofEvidenceMetadata) -> Self {
        self.metadata = metadata;
        self
    }

    /// Attaches native Trust/TrustIr provenance metadata.
    #[must_use]
    pub fn with_native_metadata(
        mut self,
        metadata: TrustMcNativeTypedChcObligationMetadata,
    ) -> Self {
        self.native_metadata = Some(metadata);
        self
    }

    /// Attaches native Trust/TrustIr provenance metadata from trust-mc-core.
    #[cfg(feature = "trust-mc-core-types")]
    #[must_use]
    pub fn with_trust_mc_core_native_metadata(
        self,
        metadata: trust_mc_core::NativeTypedChcObligationMetadata,
    ) -> Self {
        self.with_native_metadata(metadata.into())
    }

    /// Attaches a proof artifact.
    #[must_use]
    pub fn with_artifact(mut self, artifact: TrustMcFullVerificationArtifact) -> Self {
        self.artifacts.push(artifact);
        self
    }
}

/// Local wrapper for native Trust/TrustIr CHC obligation provenance.
///
/// The wrapped core metadata is still used by trust-bmc's implementation while
/// the solver split is staged, but default public evidence no longer exposes a
/// trust-mc-core type directly.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustMcNativeTypedChcObligationMetadata {
    core: trust_mc_core::NativeTypedChcObligationMetadata,
}

impl Serialize for TrustMcNativeTypedChcObligationMetadata {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.core.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for TrustMcNativeTypedChcObligationMetadata {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        trust_mc_core::NativeTypedChcObligationMetadata::deserialize(deserializer)
            .map(Self::from_core)
    }
}

impl TrustMcNativeTypedChcObligationMetadata {
    fn from_core(metadata: trust_mc_core::NativeTypedChcObligationMetadata) -> Self {
        Self { core: metadata }
    }

    /// Return the trust-mc native request id.
    #[must_use]
    pub fn native_request_id(&self) -> u32 {
        self.core.native_request_id
    }

    /// Return the bound native proof obligation ids.
    #[must_use]
    pub fn proof_obligation_ids(&self) -> &[u32] {
        &self.core.proof_obligation_ids
    }

    /// Return the bound native lineage root ids.
    #[must_use]
    pub fn lineage_root_ids(&self) -> &[u32] {
        &self.core.lineage_root_ids
    }

    /// Return the native function id.
    #[must_use]
    pub fn function_id(&self) -> u32 {
        self.core.function_id
    }

    /// Return the native verification mode label.
    #[must_use]
    pub fn verification_mode(&self) -> &str {
        &self.core.verification_mode
    }

    fn validate_for_obligation_id(&self, obligation_id: &str) -> Result<(), Vec<String>> {
        self.core.validate_for_obligation_id(obligation_id)
    }

    #[cfg(test)]
    fn core_mut(&mut self) -> &mut trust_mc_core::NativeTypedChcObligationMetadata {
        &mut self.core
    }
}

#[cfg(feature = "trust-mc-core-types")]
impl From<trust_mc_core::NativeTypedChcObligationMetadata>
    for TrustMcNativeTypedChcObligationMetadata
{
    fn from(metadata: trust_mc_core::NativeTypedChcObligationMetadata) -> Self {
        Self::from_core(metadata)
    }
}

#[cfg(feature = "trust-mc-core-types")]
impl From<TrustMcNativeTypedChcObligationMetadata>
    for trust_mc_core::NativeTypedChcObligationMetadata
{
    fn from(metadata: TrustMcNativeTypedChcObligationMetadata) -> Self {
        metadata.core
    }
}

/// CHC/PDR proof kinds that are strong enough for full verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TrustMcChcPdrProofKind {
    ChcValidity,
    PdrInvariant,
}

#[cfg(feature = "trust-mc-native-solver")]
fn native_typed_proof_strength(strength: TrustMcNativeTypedProofStrength) -> Option<ProofStrength> {
    match strength {
        TrustMcNativeTypedProofStrength::ChcValidity => Some(ProofStrength {
            reasoning: ReasoningKind::Chc,
            assurance: AssuranceLevel::SmtBacked,
        }),
        TrustMcNativeTypedProofStrength::PdrInvariant => Some(ProofStrength {
            reasoning: ReasoningKind::Pdr,
            assurance: AssuranceLevel::SmtBacked,
        }),
        _ => None,
    }
}

/// Stable CHC/PDR problem statistics carried by native evidence.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct TrustMcChcPdrStats {
    pub relation_count: usize,
    pub clause_count: usize,
}

/// Typed replay outcome recorded with digest-backed trust_mc CHC/PDR artifacts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TrustMcProofReplayStatus {
    Replayed,
    Failed,
    Unknown,
}

/// Typed proof-checker outcome recorded with digest-backed trust_mc CHC/PDR artifacts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TrustMcProofCheckStatus {
    Accepted,
    Rejected,
    Unknown,
}

/// Replay/check decision required before local trust_mc evidence is proof-grade.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TrustMcProofReplayCheckStatus {
    pub replay: TrustMcProofReplayStatus,
    pub check: TrustMcProofCheckStatus,
}

impl TrustMcProofReplayCheckStatus {
    /// Replay and checking both succeeded.
    #[must_use]
    pub const fn accepted() -> Self {
        Self {
            replay: TrustMcProofReplayStatus::Replayed,
            check: TrustMcProofCheckStatus::Accepted,
        }
    }

    const fn is_accepted(self) -> bool {
        matches!(self.replay, TrustMcProofReplayStatus::Replayed)
            && matches!(self.check, TrustMcProofCheckStatus::Accepted)
    }
}

/// Proof metadata required before CHC/PDR evidence can become public proof evidence.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TrustMcFullProofEvidenceMetadata {
    pub producer: Option<String>,
    pub cache_key: Option<TrustMcEvidenceHash>,
    pub normalized_input_hash: Option<TrustMcEvidenceHash>,
    pub transcript_hashes: Vec<TrustMcEvidenceHash>,
    pub replay_log_hashes: Vec<TrustMcEvidenceHash>,
    pub checked_report_hashes: Vec<TrustMcEvidenceHash>,
    pub replay_check_status: Option<TrustMcProofReplayCheckStatus>,
}

impl TrustMcFullProofEvidenceMetadata {
    /// Sets the producer label.
    #[must_use]
    pub fn with_producer(mut self, producer: impl Into<String>) -> Self {
        self.producer = Some(producer.into());
        self
    }

    /// Sets the full-verification cache key SHA-256 digest.
    #[must_use]
    pub fn with_cache_key(mut self, hash: TrustMcEvidenceHash) -> Self {
        self.cache_key = Some(hash);
        self
    }

    /// Sets the normalized CHC/PDR input SHA-256 digest.
    #[must_use]
    pub fn with_normalized_input_hash(mut self, hash: TrustMcEvidenceHash) -> Self {
        self.normalized_input_hash = Some(hash);
        self
    }

    /// Adds a solver transcript SHA-256 digest.
    #[must_use]
    pub fn with_transcript_hash(mut self, hash: TrustMcEvidenceHash) -> Self {
        self.transcript_hashes.push(hash);
        self
    }

    /// Adds a proof replay log SHA-256 digest.
    #[must_use]
    pub fn with_replay_log_hash(mut self, hash: TrustMcEvidenceHash) -> Self {
        self.replay_log_hashes.push(hash);
        self
    }

    /// Adds a checked proof report SHA-256 digest.
    #[must_use]
    pub fn with_checked_report_hash(mut self, hash: TrustMcEvidenceHash) -> Self {
        self.checked_report_hashes.push(hash);
        self
    }

    /// Sets the typed replay/check decision from the native trust_mc proof checker.
    #[must_use]
    pub fn with_replay_check_status(mut self, status: TrustMcProofReplayCheckStatus) -> Self {
        self.replay_check_status = Some(status);
        self
    }
}

/// Diagnostic-only native full-verifier evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustMcDiagnosticOnlyEvidence {
    pub problem_kind: TrustMcFullVerificationProblemKind,
    pub summary: String,
    pub artifacts: Vec<TrustMcFullVerificationArtifact>,
}

impl TrustMcDiagnosticOnlyEvidence {
    /// Creates diagnostic evidence for the given problem kind.
    #[must_use]
    pub fn new(
        problem_kind: TrustMcFullVerificationProblemKind,
        summary: impl Into<String>,
    ) -> Self {
        Self { problem_kind, summary: summary.into(), artifacts: Vec::new() }
    }

    /// Attaches a diagnostic artifact.
    #[must_use]
    pub fn with_artifact(mut self, artifact: TrustMcFullVerificationArtifact) -> Self {
        self.artifacts.push(artifact);
        self
    }
}

/// Native full-verification problem shape.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TrustMcFullVerificationProblemKind {
    Bmc,
    Chc,
}

impl std::fmt::Display for TrustMcFullVerificationProblemKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bmc => f.write_str("BMC"),
            Self::Chc => f.write_str("CHC/PDR"),
        }
    }
}

/// Native full-verification artifact descriptor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustMcFullVerificationArtifact {
    pub kind: TrustMcFullVerificationArtifactKind,
    pub label: String,
    pub digest: Option<TrustMcEvidenceHash>,
    materialized_bytes: Option<Vec<u8>>,
    proof_binding_id: Option<String>,
    referenced_artifacts: Vec<(TrustMcFullVerificationArtifactKind, TrustMcEvidenceHash)>,
}

impl TrustMcFullVerificationArtifact {
    /// Creates an artifact descriptor.
    #[must_use]
    pub fn new(kind: TrustMcFullVerificationArtifactKind, label: impl Into<String>) -> Self {
        Self {
            kind,
            label: label.into(),
            digest: None,
            materialized_bytes: None,
            proof_binding_id: None,
            referenced_artifacts: Vec::new(),
        }
    }

    /// Creates a solver transcript artifact with a digest.
    #[must_use]
    pub fn solver_transcript(label: impl Into<String>, digest: TrustMcEvidenceHash) -> Self {
        Self {
            kind: TrustMcFullVerificationArtifactKind::SolverTranscript,
            label: label.into(),
            digest: Some(digest),
            materialized_bytes: None,
            proof_binding_id: None,
            referenced_artifacts: Vec::new(),
        }
    }

    /// Attaches a digest.
    #[must_use]
    pub fn with_digest(mut self, digest: TrustMcEvidenceHash) -> Self {
        self.digest = Some(digest);
        self
    }
}

/// Native artifact kinds emitted by trust_mc full verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TrustMcFullVerificationArtifactKind {
    CompilerInput,
    ObligationSet,
    TypedBmcProblem,
    TypedChcProblem,
    SmtRendering,
    SolverBinary,
    VerificationOptions,
    ResourceLimits,
    NormalizedInput,
    SolverTranscript,
    PdrInvariantModel,
    ReplayLog,
    CheckedProofReport,
    CounterexampleTrace,
    DiagnosticTrace,
    EvidenceManifest,
}

impl TrustMcFullVerificationArtifactKind {
    fn to_public_kind(self) -> EvidenceArtifactKind {
        match self {
            Self::CompilerInput | Self::NormalizedInput => EvidenceArtifactKind::EngineInput,
            Self::ObligationSet => EvidenceArtifactKind::NormalizedObligation,
            Self::TypedBmcProblem | Self::TypedChcProblem | Self::SmtRendering => {
                EvidenceArtifactKind::SolverQuery
            }
            Self::SolverBinary | Self::VerificationOptions | Self::ResourceLimits => {
                EvidenceArtifactKind::BuildManifest
            }
            Self::SolverTranscript => EvidenceArtifactKind::SolverTranscript,
            Self::PdrInvariantModel => EvidenceArtifactKind::Model,
            Self::ReplayLog => EvidenceArtifactKind::ReplayLog,
            Self::CheckedProofReport => EvidenceArtifactKind::ProofCheckReport,
            Self::CounterexampleTrace => EvidenceArtifactKind::Counterexample,
            Self::DiagnosticTrace => EvidenceArtifactKind::Log,
            Self::EvidenceManifest => EvidenceArtifactKind::SummaryEvidence,
        }
    }
}

/// Stable SHA-256 evidence digest descriptor.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TrustMcEvidenceHash {
    hex: String,
}

impl TrustMcEvidenceHash {
    /// Creates a validated SHA-256 digest from lowercase or uppercase hex.
    pub fn sha256(hex: impl Into<String>) -> Result<Self, TrustMcEvidenceHashError> {
        let hex = hex.into().to_ascii_lowercase();
        if hex.len() != 64 {
            return Err(TrustMcEvidenceHashError::InvalidLength {
                expected: 64,
                actual: hex.len(),
            });
        }
        if !hex.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err(TrustMcEvidenceHashError::InvalidHex);
        }
        Ok(Self { hex })
    }

    fn to_artifact_hash(&self) -> ArtifactHash {
        ArtifactHash { algorithm: "sha256".to_string(), value: self.hex.clone() }
    }
}

/// Invalid SHA-256 evidence digest metadata.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TrustMcEvidenceHashError {
    InvalidLength { expected: usize, actual: usize },
    InvalidHex,
}

impl std::fmt::Display for TrustMcEvidenceHashError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidLength { expected, actual } => {
                write!(f, "invalid SHA-256 evidence hash length: expected {expected}, got {actual}")
            }
            Self::InvalidHex => {
                f.write_str("invalid SHA-256 evidence hash: digest must be hexadecimal")
            }
        }
    }
}

impl std::error::Error for TrustMcEvidenceHashError {}

fn missing_proof_grade_metadata(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    proof: &TrustMcChcPdrProofEvidence,
) -> Vec<String> {
    let mut missing = Vec::new();
    if proof.metadata.producer.as_deref().is_none_or(|producer| producer.trim().is_empty()) {
        missing.push("missing proof evidence producer identity".to_string());
    }
    if proof.stats.relation_count == 0 || proof.stats.clause_count == 0 {
        missing.push(
            "CHC/PDR proof stats must include nonzero relation and clause counts".to_string(),
        );
    }
    if proof.metadata.normalized_input_hash.is_none() {
        missing.push("missing normalized SHA-256 input digest".to_string());
    }
    // Trust (structural default-function / panic-freedom transport): the
    // per-function trust-mc default-admission obligation and the whole-function
    // panic-freedom AGGREGATE carry NO per-VC typed-CHC public binding metadata
    // by design — their proof is the STRUCTURAL whole-CFG reachability CHC, not a
    // per-VC typed CHC (see the identical carve-out in
    // `validate_native_typed_transport_with_expected_normalized_input`). Skip
    // ONLY the per-VC public-binding demand for them; every other proof-grade
    // gate in this function still holds — a nonzero-stat CHC/PDR proof with a
    // SHA-256 normalized-input digest, an independently normalized pre-solve
    // typed request (`pre_solve_normalized_input_validated`), native typed-CHC
    // metadata that `validate_native_metadata_for_public_obligation` still binds
    // to THIS obligation's id/native-id, digest-matched solver/replay/checked
    // artifacts, and an accepted replay/check status. So this cannot admit an
    // unproved obligation: without a genuine proof-grade structural CHC proof the
    // remaining checks still fail closed.
    let obligation_uses_structural_default_function_chc = obligation.is_default_admission()
        || obligation_is_whole_function_panic_freedom(bundle, obligation);
    if !obligation_uses_structural_default_function_chc {
        let public_binding = validate_public_trust_mc_typed_chc_binding(obligation);
        if let Err(reason) = public_binding {
            missing
                .push(format!("public typed trust_mc CHC/PDR binding failed validation: {reason}"));
        }
    }
    missing.push(
        "raw native CHC/PDR proof lacks live opaque native-bundle authority; public typed-contract semantic digests and native solver-input digests are distinct domains"
            .to_string(),
    );
    match &proof.native_metadata {
        Some(metadata) => {
            if let Err(reasons) =
                validate_native_metadata_for_public_obligation(metadata, obligation)
            {
                missing.push(format!(
                    "native typed CHC obligation metadata failed validation: {}",
                    reasons.join("; ")
                ));
            }
        }
        None => missing.push("missing native typed CHC obligation metadata".to_string()),
    }
    require_trust_mc_hashes("solver transcript", &proof.metadata.transcript_hashes, &mut missing);
    require_trust_mc_hashes("replay log", &proof.metadata.replay_log_hashes, &mut missing);
    require_trust_mc_hashes(
        "checked proof report",
        &proof.metadata.checked_report_hashes,
        &mut missing,
    );
    match proof.metadata.replay_check_status {
        Some(status) if status.is_accepted() => {}
        Some(status) => missing.push(format!(
            "replay/check status must be Replayed/Accepted, got {:?}/{:?}",
            status.replay, status.check
        )),
        None => missing.push("missing replay/check status metadata".to_string()),
    }

    if let Some(input_hash) = proof.metadata.normalized_input_hash.as_ref()
        && !has_matching_trust_mc_artifact(
            proof,
            TrustMcFullVerificationArtifactKind::NormalizedInput,
            std::slice::from_ref(input_hash),
        )
    {
        missing.push("missing normalized input artifact matching input digest".to_string());
    }
    if !has_matching_trust_mc_artifact(
        proof,
        TrustMcFullVerificationArtifactKind::SolverTranscript,
        &proof.metadata.transcript_hashes,
    ) {
        missing.push(
            "missing solver transcript artifact matching transcript digest metadata".to_string(),
        );
    }
    if !has_matching_trust_mc_artifact(
        proof,
        TrustMcFullVerificationArtifactKind::ReplayLog,
        &proof.metadata.replay_log_hashes,
    ) {
        missing.push("missing replay log artifact matching replay metadata".to_string());
    }
    if !has_matching_trust_mc_artifact(
        proof,
        TrustMcFullVerificationArtifactKind::CheckedProofReport,
        &proof.metadata.checked_report_hashes,
    ) {
        missing.push("missing checked proof report artifact matching report metadata".to_string());
    }
    if proof.kind == TrustMcChcPdrProofKind::PdrInvariant
        && proof.invariant_count == 0
        && !has_trust_mc_digest_artifact(
            proof,
            TrustMcFullVerificationArtifactKind::PdrInvariantModel,
        )
    {
        missing.push("PDR invariant proof is missing invariant evidence".to_string());
    }

    missing
}

fn require_trust_mc_hashes(label: &str, hashes: &[TrustMcEvidenceHash], missing: &mut Vec<String>) {
    if hashes.is_empty() {
        missing.push(format!("missing {label} digest metadata"));
    }
}

fn has_matching_trust_mc_artifact(
    proof: &TrustMcChcPdrProofEvidence,
    kind: TrustMcFullVerificationArtifactKind,
    hashes: &[TrustMcEvidenceHash],
) -> bool {
    proof.artifacts.iter().any(|artifact| {
        artifact.kind == kind
            && artifact.digest.as_ref().is_some_and(|digest| hashes.contains(digest))
    })
}

fn has_trust_mc_digest_artifact(
    proof: &TrustMcChcPdrProofEvidence,
    kind: TrustMcFullVerificationArtifactKind,
) -> bool {
    proof.artifacts.iter().any(|artifact| artifact.kind == kind && artifact.digest.is_some())
}

fn diagnostic_artifacts(diagnostic: &TrustMcDiagnosticOnlyEvidence) -> Vec<EvidenceArtifact> {
    diagnostic.artifacts.iter().filter_map(public_unmaterialized_artifact_from_trust_mc).collect()
}

fn public_unmaterialized_artifact_from_trust_mc(
    artifact: &TrustMcFullVerificationArtifact,
) -> Option<EvidenceArtifact> {
    artifact.digest.as_ref().map(|digest| EvidenceArtifact {
        kind: artifact.kind.to_public_kind(),
        uri: artifact.label.clone(),
        hash: digest.to_artifact_hash(),
        materialization: None,
    })
}

fn trust_mc_public_artifact_kind_label(kind: EvidenceArtifactKind) -> &'static str {
    match kind {
        EvidenceArtifactKind::EngineInput => "engine-input",
        EvidenceArtifactKind::NormalizedObligation => "normalized-obligation",
        EvidenceArtifactKind::SolverQuery => "solver-query",
        EvidenceArtifactKind::SolverTranscript => "solver-transcript",
        EvidenceArtifactKind::ProofReplayTrace => "proof-replay-trace",
        EvidenceArtifactKind::ProofCheckReport => "proof-check-report",
        EvidenceArtifactKind::ReplayLog => "replay-log",
        EvidenceArtifactKind::Model => "model",
        _ => "supplemental",
    }
}

#[cfg(feature = "trust-mc-native-solver")]
fn validate_native_full_verification_normalized_input(
    verification: &trust_mc_driver::TypedChcPdrFullVerification,
    expected: &TrustMcNativeTypedChcPdrNormalizedInput,
) -> Result<(), String> {
    let recomputed =
        trust_mc_core::EvidenceHash::sha256_bytes(expected.normalized_input.as_bytes());
    if recomputed != expected.normalized_input_hash {
        return Err("shared trust_mc pre-solve normalizer returned inconsistent bytes and digest"
            .to_string());
    }
    if verification.route != expected.route {
        return Err(format!(
            "native full-verification route {:?} differs from pre-solve request route {:?}",
            verification.route, expected.route
        ));
    }
    verification.cache_key.validate().map_err(|reasons| {
        format!("in-process trust_mc cache key failed validation: {}", reasons.join("; "))
    })?;
    if verification.cache_key.parts.normalized_input_hash != expected.normalized_input_hash {
        return Err(format!(
            "native cache normalized-input digest {}:{} differs from pre-solve request digest {}:{}",
            verification.cache_key.parts.normalized_input_hash.algorithm,
            verification.cache_key.parts.normalized_input_hash.value,
            expected.normalized_input_hash.algorithm,
            expected.normalized_input_hash.value
        ));
    }
    if verification.cache_key.parts.obligation_set_hash != expected.obligation_set_hash {
        return Err(format!(
            "native cache obligation-set digest {}:{} differs from pre-solve request digest {}:{}",
            verification.cache_key.parts.obligation_set_hash.algorithm,
            verification.cache_key.parts.obligation_set_hash.value,
            expected.obligation_set_hash.algorithm,
            expected.obligation_set_hash.value
        ));
    }
    let trust_mc_core::FullVerificationVerdict::Proved {
        evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
    } = &verification.verdict
    else {
        return Err("in-process normalized-input binding requires one proof-grade CHC/PDR verdict"
            .to_string());
    };
    if proof.obligation.normalized_input != expected.normalized_input {
        return Err(
            "native proof obligation normalized bytes differ from the pre-solve typed request"
                .to_string(),
        );
    }
    if proof.obligation.normalized_input_hash != expected.normalized_input_hash
        || proof.metadata.normalized_input_hash.as_ref() != Some(&expected.normalized_input_hash)
    {
        return Err(format!(
            "native proof obligation/metadata normalized digest does not match pre-solve request digest {}:{}",
            expected.normalized_input_hash.algorithm, expected.normalized_input_hash.value
        ));
    }
    let normalized_artifacts = proof
        .artifacts
        .iter()
        .filter(|artifact| {
            artifact.kind == trust_mc_core::FullVerificationArtifactKind::NormalizedInput
        })
        .collect::<Vec<_>>();
    let [artifact] = normalized_artifacts.as_slice() else {
        return Err(format!(
            "native proof contains {} materialized NormalizedInput artifacts; expected one",
            normalized_artifacts.len()
        ));
    };
    if artifact.digest.as_ref() != Some(&expected.normalized_input_hash)
        || artifact.materialized_bytes() != Some(expected.normalized_input.as_bytes())
    {
        return Err(
            "native proof materialized NormalizedInput artifact does not match the pre-solve typed request"
                .to_string(),
        );
    }
    Ok(())
}

#[cfg(feature = "trust-mc-native-solver")]
fn validated_native_typed_transport_artifacts(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    transport: &TrustMcNativeTypedChcPdrProofTransport,
) -> Result<Vec<EvidenceArtifact>, Vec<String>> {
    validated_native_typed_transport_artifacts_with_expected_normalized_input(
        bundle, obligation, transport, None,
    )
}

#[cfg(feature = "trust-mc-native-solver")]
fn validated_native_typed_transport_artifacts_with_expected_normalized_input(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    transport: &TrustMcNativeTypedChcPdrProofTransport,
    expected: Option<&TrustMcNativeTypedChcPdrNormalizedInput>,
) -> Result<Vec<EvidenceArtifact>, Vec<String>> {
    validate_native_typed_transport_with_expected_normalized_input(
        bundle, obligation, transport, expected,
    )?;
    let mut artifacts = public_artifacts_from_native_typed_transport(obligation, transport)
        .map_err(|reason| vec![reason])?;
    sort_public_artifacts(&mut artifacts);
    Ok(artifacts)
}

#[cfg(feature = "trust-mc-native-solver")]
fn validated_authorized_native_typed_transport_artifacts(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    authority: &trust_mc_driver::AuthorizedNativeTypedChcPdrProof<'_>,
    expected: &TrustMcNativeTypedChcPdrNormalizedInput,
) -> Result<(TrustMcNativeTypedChcPdrProofTransport, Vec<EvidenceArtifact>), Vec<String>> {
    // Derive the payload inside the authority-taking function. No caller can
    // pair a raw/deserialized record with a boolean or marker that skips the
    // public replay-status gate.
    let transport = authority.transport_record();
    validate_native_typed_transport_common(bundle, obligation, &transport, Some(expected))?;
    let mut artifacts = public_artifacts_from_native_typed_transport(obligation, &transport)
        .map_err(|reason| vec![reason])?;
    sort_public_artifacts(&mut artifacts);
    Ok((transport, artifacts))
}

#[cfg(feature = "trust-mc-native-solver")]
fn validate_native_typed_transport(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    transport: &TrustMcNativeTypedChcPdrProofTransport,
) -> Result<(), Vec<String>> {
    validate_native_typed_transport_with_expected_normalized_input(
        bundle, obligation, transport, None,
    )
}

#[cfg(feature = "trust-mc-native-solver")]
fn validate_native_typed_transport_with_expected_normalized_input(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    transport: &TrustMcNativeTypedChcPdrProofTransport,
    expected: Option<&TrustMcNativeTypedChcPdrNormalizedInput>,
) -> Result<(), Vec<String>> {
    let mut reasons =
        match validate_native_typed_transport_common(bundle, obligation, transport, expected) {
            Ok(()) => Vec::new(),
            Err(reasons) => reasons,
        };
    // A raw record never becomes authority. Preserve this strict status check
    // for useful diagnostics; the only private admission helper above takes a
    // live opaque authority directly and derives its own transport snapshot.
    if transport.replay_check_status.as_ref()
        != Some(&trust_mc_core::ProofReplayCheckStatus::accepted())
    {
        reasons.push("native proof transport lacks an accepted replay/check status".to_string());
    }
    finish_native_typed_transport_validation(reasons)
}

#[cfg(feature = "trust-mc-native-solver")]
fn validate_native_typed_transport_common(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    transport: &TrustMcNativeTypedChcPdrProofTransport,
    expected: Option<&TrustMcNativeTypedChcPdrNormalizedInput>,
) -> Result<(), Vec<String>> {
    let mut reasons = Vec::new();
    if transport.schema_version != TrustMcNativeTypedChcPdrProofTransport::SCHEMA_VERSION {
        reasons.push(format!(
            "unsupported native typed proof transport schema {}; expected {}",
            transport.schema_version,
            TrustMcNativeTypedChcPdrProofTransport::SCHEMA_VERSION
        ));
    }
    if !canonical_native_transport_text(&transport.suite) {
        reasons.push("native proof transport suite is empty or non-canonical".to_string());
    }
    if !canonical_native_transport_text(&transport.backend)
        || !transport.backend.starts_with("trust_mc::typed-chc-pdr::")
    {
        reasons.push(format!(
            "native proof transport backend `{}` is not a typed CHC/PDR backend",
            transport.backend
        ));
    }
    if let Some(expected) = expected {
        let route_suffix = match expected.route {
            trust_mc_driver::TypedChcPdrRoute::TriviallySafe => Some("::trivial-safe"),
            trust_mc_driver::TypedChcPdrRoute::PdrProof => Some("::pdr-proof"),
            _ => {
                reasons.push(format!(
                    "pre-solve typed request selected unsupported route {:?}",
                    expected.route
                ));
                None
            }
        };
        if route_suffix.is_some_and(|suffix| !transport.backend.ends_with(suffix)) {
            reasons.push(format!(
                "native proof transport backend `{}` does not match pre-solve request route {:?}",
                transport.backend, expected.route
            ));
        }
    }
    match native_trust_ir_expected_trust_mc_obligation_id(obligation) {
        Some(expected_native_id)
            if native_trust_mc_obligation_lookup_key(&transport.native_id)
                != native_trust_mc_obligation_lookup_key(&expected_native_id) =>
        {
            reasons.push(format!(
                "native proof transport id `{}` does not match obligation `{}` canonical native TrustIr identity `{expected_native_id}`",
                transport.native_id, obligation.obligation_id
            ));
        }
        None => reasons.push(format!(
            "obligation `{}` lacks a unique canonical native TrustIr identity",
            obligation.obligation_id
        )),
        Some(_) => {}
    }
    // Trust (structural default-function / panic-freedom transport): the
    // compiler-synthesized per-function default-admission obligation and the
    // whole-function panic-freedom AGGREGATE carry NO per-VC typed-CHC public
    // binding metadata (`trust-mc.typed-chc-obligation.binding.v1`) — by design.
    // Their proof is not a per-VC typed CHC but the STRUCTURAL whole-CFG
    // reachability CHC that `trust_mc_default_function_chc_from_trust_ir` routes
    // to the transport solve. Requiring the per-VC public binding here would
    // reject that genuine structural proof and leave the function runtime-checked
    // forever (Unsupported → unknown).
    //
    // SOUNDNESS: skipping ONLY the per-VC public-binding demand does not admit
    // any unproved obligation. Every other gate in this validator still holds for
    // these obligations: the transport must carry `proof_status == Proved` (the
    // structural CHC was solved valid/UNSAT — a not-proved or absent transport
    // still fails closed to Unsupported), an accepted replay/check status, a
    // `native_id` that matches this obligation's canonical native TrustIr identity
    // (which `validate_native_trust_ir_public_claim_binding` has already bound,
    // atom-for-atom, to the embedded public claim + semantic digest for exactly
    // this request/proof/function/source), a NormalizedInput digest equal to the
    // independently derived pre-solve request (`expected`), and the exact
    // digest-chained solver/replay/checked-report artifact set with one canonical
    // producer binding. `public_binding` is consumed below only on the untrusted
    // raw-serialized (`expected == None`) surface; in-process transports (this
    // path, `expected == Some`) never read it, so `None` here changes no other
    // check. The literal `false` formula these obligations carry is an IDENTITY
    // placeholder for claim binding, never the solved CHC — it is not consulted
    // here and cannot manufacture a proof.
    //
    // The carve-out and the per-VC binding demand are two readings of ONE
    // question — "does the solved rule set encode this obligation's violation?"
    // — so they are decided once, by the positive-witness gate, and can no longer
    // drift apart. A row with neither witness is rejected here rather than
    // silently taking the structural carve-out.
    let credit_witness =
        match trust_mc_chc_credit_witness(bundle, obligation, expected.map(|input| input.route)) {
            Ok(witness) => Some(witness),
            Err(reason) => {
                reasons.push(reason);
                None
            }
        };
    let public_binding = match credit_witness {
        Some(TrustMcChcCreditWitness::WholeFunctionStructuralQuery) | None => None,
        Some(TrustMcChcCreditWitness::PerObligationViolationPredicate) => {
            match validate_public_trust_mc_typed_chc_binding_for_native_id(
                obligation,
                &transport.native_id,
            ) {
                Ok(binding) => Some(binding),
                Err(reason) => {
                    reasons.push(format!(
                        "public typed trust_mc CHC/PDR binding failed validation: {reason}"
                    ));
                    None
                }
            }
        }
    };
    let Some(proof_id) = transport.proof_id else {
        reasons.push(
            "native proof transport is grouped and has no single proof_id; proof-grade public evidence requires an individual MIR proof transport"
                .to_string(),
        );
        return finish_native_typed_transport_validation(reasons);
    };
    let expected_native_id =
        format!("trust_ir-native-trust_mc-request-{}-proof-{proof_id}", transport.request_id);
    if native_trust_mc_obligation_lookup_key(&transport.native_id)
        != native_trust_mc_obligation_lookup_key(&expected_native_id)
    {
        reasons.push(format!(
            "native proof transport id `{}` does not match request/proof identity `{expected_native_id}`",
            transport.native_id
        ));
    }
    if transport.proof_status != TrustMcNativeTypedProofStatus::Proved {
        reasons.push(format!(
            "native proof transport status must be proved, got {:?}",
            transport.proof_status
        ));
    }
    if native_typed_proof_strength(transport.proof_strength).is_none() {
        reasons.push(format!(
            "native proof transport has unsupported proof strength {:?}",
            transport.proof_strength
        ));
    }

    let solver = require_exact_native_typed_transport_artifact(
        "solver transcript",
        trust_mc_core::FullVerificationArtifactKind::SolverTranscript,
        &transport.solver_artifacts,
        &mut reasons,
    );
    let replay = require_exact_native_typed_transport_artifact(
        "replay log",
        trust_mc_core::FullVerificationArtifactKind::ReplayLog,
        &transport.replay_artifacts,
        &mut reasons,
    );
    let check = require_exact_native_typed_transport_artifact(
        "checked proof report",
        trust_mc_core::FullVerificationArtifactKind::CheckedProofReport,
        &transport.check_artifacts,
        &mut reasons,
    );

    if transport.response_artifacts.len() > 64 {
        reasons.push("native proof transport response artifact inventory is oversized".to_string());
    }
    for artifact in &transport.response_artifacts {
        validate_native_typed_transport_response_artifact(artifact, &mut reasons);
    }
    for (index, artifact) in transport.response_artifacts.iter().enumerate() {
        if transport.response_artifacts[..index]
            .iter()
            .any(|previous| previous.kind == artifact.kind && previous.digest == artifact.digest)
        {
            reasons.push(format!(
                "native proof transport response contains duplicate {:?} artifact identity",
                artifact.kind
            ));
        }
    }

    let normalized = exactly_one_native_response_artifact(
        transport,
        trust_mc_core::FullVerificationArtifactKind::NormalizedInput,
        "normalized input",
        &mut reasons,
    );
    let invariant_model_count = transport
        .response_artifacts
        .iter()
        .filter(|artifact| {
            artifact.kind == trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel
        })
        .count();
    let invariant_model = if transport.proof_strength
        == TrustMcNativeTypedProofStrength::PdrInvariant
    {
        let invariant = exactly_one_native_response_artifact(
            transport,
            trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel,
            "PDR invariant model",
            &mut reasons,
        );
        if let Some(invariant) = invariant {
            validate_native_typed_transport_artifact(
                "PDR invariant model",
                trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel,
                invariant,
                &mut reasons,
            );
        }
        invariant
    } else {
        if invariant_model_count != 0 {
            reasons.push(format!(
                    "native CHC-validity transport carries {invariant_model_count} stray PDR invariant model artifact(s)"
                ));
        }
        None
    };
    if let Some(normalized) = normalized {
        if let Some(expected) = expected {
            match normalized.digest.as_ref() {
                Some(digest) if digest == &expected.normalized_input_hash => {}
                Some(digest) => reasons.push(format!(
                    "native proof transport NormalizedInput digest {}:{} does not match pre-solve request digest {}:{}",
                    digest.algorithm,
                    digest.value,
                    expected.normalized_input_hash.algorithm,
                    expected.normalized_input_hash.value
                )),
                None => reasons.push(
                    "native proof transport NormalizedInput has no digest to match the pre-solve typed request"
                        .to_string(),
                ),
            }
            if normalized.materialized_bytes() != Some(expected.normalized_input.as_bytes()) {
                reasons.push(
                    "native proof transport materialized NormalizedInput bytes do not match the pre-solve typed request"
                        .to_string(),
                );
            }
        } else if let Some(binding) = public_binding.as_ref() {
            // Raw serialized transports are never proof authority. Preserve
            // the legacy strict diagnostic check for that untrusted surface;
            // genuine in-process transports use the independently derived
            // normalized obligation-set binding above because the public
            // synthetic digest intentionally inhabits a different domain.
            match normalized.digest.as_ref() {
                Some(digest)
                    if digest.algorithm == binding.synthetic_chc_digest.algorithm
                        && digest.value == binding.synthetic_chc_digest.value => {}
                Some(digest) => reasons.push(format!(
                    "native proof transport NormalizedInput digest {}:{} does not match public typed trust_mc synthetic CHC binding {}:{}",
                    digest.algorithm,
                    digest.value,
                    binding.synthetic_chc_digest.algorithm,
                    binding.synthetic_chc_digest.value
                )),
                None => reasons.push(
                    "native proof transport NormalizedInput has no digest to match the public typed trust_mc synthetic CHC binding"
                        .to_string(),
                ),
            }
        }
    }
    for (label, kind, role) in [
        (
            "solver transcript",
            trust_mc_core::FullVerificationArtifactKind::SolverTranscript,
            solver,
        ),
        ("replay log", trust_mc_core::FullVerificationArtifactKind::ReplayLog, replay),
        (
            "checked proof report",
            trust_mc_core::FullVerificationArtifactKind::CheckedProofReport,
            check,
        ),
    ] {
        let response = exactly_one_native_response_artifact(transport, kind, label, &mut reasons);
        if let (Some(role), Some(response)) = (role, response)
            && role != response
        {
            reasons.push(format!(
                "native proof transport {label} role does not exactly match its response artifact"
            ));
        }
    }

    if let (Some(normalized), Some(solver), Some(replay), Some(check)) =
        (normalized, solver, replay, check)
    {
        if let (Some(normalized_digest), Some(solver_digest), Some(replay_digest)) =
            (normalized.digest.as_ref(), solver.digest.as_ref(), replay.digest.as_ref())
        {
            require_exact_native_artifact_references(
                "normalized input",
                normalized,
                &[],
                &mut reasons,
            );
            require_exact_native_artifact_references(
                "solver transcript",
                solver,
                &[(
                    trust_mc_core::FullVerificationArtifactKind::NormalizedInput,
                    normalized_digest,
                )],
                &mut reasons,
            );
            let mut replay_references = vec![(
                trust_mc_core::FullVerificationArtifactKind::SolverTranscript,
                solver_digest,
            )];
            let mut check_references = vec![(
                trust_mc_core::FullVerificationArtifactKind::SolverTranscript,
                solver_digest,
            )];
            if let Some(invariant) = invariant_model
                && let Some(invariant_digest) = invariant.digest.as_ref()
            {
                require_exact_native_artifact_references(
                    "PDR invariant model",
                    invariant,
                    &[(
                        trust_mc_core::FullVerificationArtifactKind::NormalizedInput,
                        normalized_digest,
                    )],
                    &mut reasons,
                );
                replay_references.push((
                    trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel,
                    invariant_digest,
                ));
                check_references.push((
                    trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel,
                    invariant_digest,
                ));
            }
            check_references
                .push((trust_mc_core::FullVerificationArtifactKind::ReplayLog, replay_digest));
            require_exact_native_artifact_references(
                "replay log",
                replay,
                &replay_references,
                &mut reasons,
            );
            require_exact_native_artifact_references(
                "checked proof report",
                check,
                &check_references,
                &mut reasons,
            );
        }

        let mut bindings = [normalized, solver, replay, check]
            .map(TrustMcNativeTypedProofArtifactRef::proof_binding_id)
            .to_vec();
        if let Some(invariant) = invariant_model {
            bindings.push(invariant.proof_binding_id());
        }
        let producer_binding = bindings[0];
        if !producer_binding.is_some_and(canonical_native_proof_binding_id)
            || bindings.iter().any(|binding| *binding != producer_binding)
        {
            reasons.push(
                "native proof transport required artifacts lack one exact canonical producer binding"
                    .to_string(),
            );
        }
    }

    finish_native_typed_transport_validation(reasons)
}

#[cfg(feature = "trust-mc-native-solver")]
fn finish_native_typed_transport_validation(reasons: Vec<String>) -> Result<(), Vec<String>> {
    if reasons.is_empty() { Ok(()) } else { Err(reasons) }
}

#[cfg(feature = "trust-mc-native-solver")]
fn require_exact_native_typed_transport_artifact<'a>(
    label: &str,
    expected_kind: trust_mc_core::FullVerificationArtifactKind,
    artifacts: &'a [TrustMcNativeTypedProofArtifactRef],
    reasons: &mut Vec<String>,
) -> Option<&'a TrustMcNativeTypedProofArtifactRef> {
    let [artifact] = artifacts else {
        reasons.push(format!(
            "native proof transport requires exactly one {label} artifact; found {}",
            artifacts.len()
        ));
        return None;
    };
    validate_native_typed_transport_artifact(label, expected_kind, artifact, reasons);
    Some(artifact)
}

#[cfg(feature = "trust-mc-native-solver")]
fn validate_native_typed_transport_artifact(
    label: &str,
    expected_kind: trust_mc_core::FullVerificationArtifactKind,
    artifact: &TrustMcNativeTypedProofArtifactRef,
    reasons: &mut Vec<String>,
) {
    if artifact.kind != expected_kind {
        reasons.push(format!(
            "native proof transport {label} artifact `{}` has kind {:?}, expected {:?}",
            artifact.uri, artifact.kind, expected_kind
        ));
    }
    if !canonical_native_transport_uri(&artifact.uri) {
        reasons.push(format!("native proof transport {label} artifact has a non-canonical URI"));
    }
    match artifact.digest.as_ref() {
        Some(digest) if is_canonical_sha256_digest(digest) => {}
        Some(digest) => reasons.push(format!(
            "native proof transport {label} artifact `{}` has non-canonical digest {}:{}",
            artifact.uri, digest.algorithm, digest.value
        )),
        None => reasons.push(format!(
            "native proof transport {label} artifact `{}` is text-only; digest required",
            artifact.uri
        )),
    }
    if artifact.materialized_bytes().is_none() {
        reasons.push(format!(
            "native proof transport {label} artifact `{}` lacks exact digest-matched bytes",
            artifact.uri
        ));
    }
    if !artifact.proof_binding_id().is_some_and(canonical_native_proof_binding_id) {
        reasons.push(format!(
            "native proof transport {label} artifact `{}` lacks a canonical producer binding",
            artifact.uri
        ));
    }
}

#[cfg(feature = "trust-mc-native-solver")]
fn validate_native_typed_transport_response_artifact(
    artifact: &TrustMcNativeTypedProofArtifactRef,
    reasons: &mut Vec<String>,
) {
    if !canonical_native_transport_uri(&artifact.uri) {
        reasons.push(format!(
            "native proof transport response {:?} artifact has a non-canonical URI",
            artifact.kind
        ));
    }
    match artifact.digest.as_ref() {
        Some(digest) if is_canonical_sha256_digest(digest) => {}
        Some(digest) => reasons.push(format!(
            "native proof transport response artifact `{}` has non-canonical digest {}:{}",
            artifact.uri, digest.algorithm, digest.value
        )),
        None => reasons.push(format!(
            "native proof transport response artifact `{}` is text-only; digest required",
            artifact.uri
        )),
    }
    if artifact.materialization.is_some() && artifact.materialized_bytes().is_none() {
        reasons.push(format!(
            "native proof transport response artifact `{}` has a mismatched materialization",
            artifact.uri
        ));
    }
}

#[cfg(feature = "trust-mc-native-solver")]
fn exactly_one_native_response_artifact<'a>(
    transport: &'a TrustMcNativeTypedChcPdrProofTransport,
    kind: trust_mc_core::FullVerificationArtifactKind,
    label: &str,
    reasons: &mut Vec<String>,
) -> Option<&'a TrustMcNativeTypedProofArtifactRef> {
    let matches = transport
        .response_artifacts
        .iter()
        .filter(|artifact| artifact.kind == kind)
        .collect::<Vec<_>>();
    let [artifact] = matches.as_slice() else {
        reasons.push(format!(
            "native proof transport requires exactly one materialized {label} response artifact; found {}",
            matches.len()
        ));
        return None;
    };
    Some(*artifact)
}

#[cfg(feature = "trust-mc-native-solver")]
fn require_exact_native_artifact_references(
    label: &str,
    artifact: &TrustMcNativeTypedProofArtifactRef,
    expected: &[(trust_mc_core::FullVerificationArtifactKind, &trust_mc_core::EvidenceHash)],
    reasons: &mut Vec<String>,
) {
    let actual = artifact.referenced_artifacts();
    if actual.len() != expected.len()
        || expected.iter().any(|(kind, digest)| {
            !actual.iter().any(|reference| reference.kind == *kind && &reference.digest == *digest)
        })
    {
        reasons.push(format!(
            "native proof transport {label} references do not match the exact normalized-input/transcript/replay/check lineage"
        ));
    }
}

#[cfg(feature = "trust-mc-native-solver")]
fn canonical_native_proof_binding_id(value: &str) -> bool {
    value.strip_prefix("trust_mc-proof-set-sha256:").is_some_and(|digest| {
        digest.len() == 64
            && digest.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    })
}

#[cfg(feature = "trust-mc-native-solver")]
fn canonical_native_transport_text(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 1024
        && value.trim() == value
        && !value.chars().any(char::is_control)
}

#[cfg(feature = "trust-mc-native-solver")]
fn canonical_native_transport_uri(value: &str) -> bool {
    canonical_native_transport_text(value)
        && value.split_once(':').is_some_and(|(scheme, remainder)| {
            !remainder.is_empty()
                && scheme.as_bytes().first().is_some_and(u8::is_ascii_alphabetic)
                && scheme.bytes().all(|byte| {
                    byte.is_ascii_alphanumeric() || matches!(byte, b'+' | b'-' | b'.' | b'_')
                })
        })
}

#[cfg(feature = "trust-mc-native-solver")]
fn public_artifacts_from_native_typed_transport(
    obligation: &TrustObligation,
    transport: &TrustMcNativeTypedChcPdrProofTransport,
) -> Result<Vec<EvidenceArtifact>, String> {
    let public_binding =
        native_trust_ir_expected_trust_mc_obligation_id(obligation).ok_or_else(|| {
            "native trust-mc transport lacks canonical public TrustIr identity".to_string()
        })?;
    let normalized_inputs = transport
        .response_artifacts
        .iter()
        .filter(|artifact| {
            artifact.kind == trust_mc_core::FullVerificationArtifactKind::NormalizedInput
        })
        .collect::<Vec<_>>();
    let [normalized_input] = normalized_inputs.as_slice() else {
        return Err(format!(
            "native trust-mc transport requires exactly one materialized NormalizedInput response artifact; found {}",
            normalized_inputs.len()
        ));
    };
    let invariant_model = if transport.proof_strength
        == TrustMcNativeTypedProofStrength::PdrInvariant
    {
        Some(
            transport
                .response_artifacts
                .iter()
                .find(|artifact| {
                    artifact.kind == trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel
                })
                .ok_or_else(|| {
                    "native PDR transport has no proof-critical invariant model".to_string()
                })?,
        )
    } else {
        None
    };
    let mut all_transport_artifacts = vec![*normalized_input];
    if let Some(invariant_model) = invariant_model {
        all_transport_artifacts.push(invariant_model);
    }
    all_transport_artifacts.extend(
        transport
            .solver_artifacts
            .iter()
            .chain(&transport.replay_artifacts)
            .chain(&transport.check_artifacts),
    );
    let mut producer_bindings =
        all_transport_artifacts.iter().map(|artifact| artifact.proof_binding_id());
    let producer_binding = producer_bindings.next().flatten().ok_or_else(|| {
        "native trust-mc materialized proof set has no producer binding".to_string()
    })?;
    if producer_bindings.any(|binding| binding != Some(producer_binding)) {
        return Err(
            "native trust-mc materialized artifacts mix producer proof bindings".to_string()
        );
    }
    let mut pending = all_transport_artifacts;
    let mut converted = Vec::<(
        trust_mc_core::FullVerificationArtifactKind,
        trust_mc_core::EvidenceHash,
        EvidenceArtifact,
    )>::new();
    while !pending.is_empty() {
        let mut progress = false;
        let mut next = Vec::new();
        for artifact in pending {
            let Some(digest) = artifact.digest.as_ref() else {
                return Err(format!("native trust-mc artifact `{}` has no digest", artifact.uri));
            };
            let Some(bytes) = artifact.materialized_bytes() else {
                return Err(format!(
                    "native trust-mc artifact `{}` has no exact bounded bytes",
                    artifact.uri
                ));
            };
            let Some(_producer_binding) = artifact.proof_binding_id() else {
                return Err(format!(
                    "native trust-mc artifact `{}` has no producer proof binding",
                    artifact.uri
                ));
            };
            let mut references = Vec::new();
            let mut unresolved = false;
            for reference in artifact.referenced_artifacts() {
                let Some((_, _, target)) =
                    converted.iter().find(|(candidate_kind, candidate_digest, _)| {
                        *candidate_kind == reference.kind && *candidate_digest == reference.digest
                    })
                else {
                    unresolved = true;
                    break;
                };
                references.push(EvidenceArtifactReference {
                    kind: target.kind,
                    hash: target.hash.clone(),
                });
            }
            if unresolved {
                next.push(artifact);
                continue;
            }
            references.sort();
            references.dedup();
            let kind = trust_mc_artifact_kind_from_core(artifact.kind).to_public_kind();
            let (materialization, hash) = EvidenceArtifactMaterialization::new_bound(
                kind,
                bytes,
                &public_binding,
                &obligation.obligation_id,
                references,
            )
            .ok_or_else(|| {
                format!("native trust-mc artifact `{}` has invalid materialization", artifact.uri)
            })?;
            converted.push((
                artifact.kind,
                digest.clone(),
                EvidenceArtifact {
                    kind,
                    uri: format!(
                        "artifact://trust-mc/proof-artifacts/{}/{}",
                        trust_mc_public_artifact_kind_label(kind),
                        hash.value
                    ),
                    hash,
                    materialization: Some(materialization),
                },
            ));
            progress = true;
        }
        if !progress {
            return Err("native trust-mc artifact references do not form a resolvable acyclic DAG"
                .to_string());
        }
        pending = next;
    }
    // Preserve every supplemental response descriptor without promoting it
    // into the proof DAG. A PDR invariant model is not supplemental: fresh
    // replay consumed its exact bytes and both replay/check nodes reference it,
    // so it was materialized in the proof DAG above. Other response artifacts
    // remain hash-addressed diagnostic context.
    for artifact in transport.response_artifacts.iter().filter(|artifact| {
        !matches!(
            artifact.kind,
            trust_mc_core::FullVerificationArtifactKind::NormalizedInput
                | trust_mc_core::FullVerificationArtifactKind::SolverTranscript
                | trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel
                | trust_mc_core::FullVerificationArtifactKind::ReplayLog
                | trust_mc_core::FullVerificationArtifactKind::CheckedProofReport
        )
    }) {
        let digest = artifact.digest.as_ref().ok_or_else(|| {
            format!("native trust-mc supplemental artifact `{}` has no digest", artifact.uri)
        })?;
        converted.push((
            artifact.kind,
            digest.clone(),
            EvidenceArtifact {
                kind: trust_mc_artifact_kind_from_core(artifact.kind).to_public_kind(),
                uri: artifact.uri.clone(),
                hash: ArtifactHash {
                    algorithm: digest.algorithm.clone(),
                    value: digest.value.clone(),
                },
                materialization: None,
            },
        ));
    }

    Ok(converted.into_iter().map(|(_, _, artifact)| artifact).collect())
}

#[cfg(feature = "trust-mc-native-solver")]
fn native_typed_transport_diagnostics(
    transport: &TrustMcNativeTypedChcPdrProofTransport,
) -> Vec<String> {
    let mut diagnostics = vec![
        ACCEPTED_NATIVE_TYPED_TRANSPORT_REASON.to_string(),
        format!(
            "native typed CHC/PDR proof transport: schema={}, suite={}, backend={}, request_id={}, proof_id={:?}, native_id={}, status={:?}, strength={:?}, solver_artifacts={}, replay_artifacts={}, check_artifacts={}",
            transport.schema_version,
            transport.suite,
            transport.backend,
            transport.request_id,
            transport.proof_id,
            transport.native_id,
            transport.proof_status,
            transport.proof_strength,
            transport.solver_artifacts.len(),
            transport.replay_artifacts.len(),
            transport.check_artifacts.len()
        ),
    ];
    diagnostics.extend(transport.diagnostics.clone());
    diagnostics
}

#[cfg(feature = "trust-mc-native-solver")]
fn sort_public_artifacts(artifacts: &mut Vec<EvidenceArtifact>) {
    artifacts.sort_by(|left, right| {
        (left.kind, left.uri.as_str(), left.hash.value.as_str()).cmp(&(
            right.kind,
            right.uri.as_str(),
            right.hash.value.as_str(),
        ))
    });
    artifacts.dedup();
}

#[cfg(feature = "trust-mc-native-solver")]
fn is_canonical_sha256_digest(digest: &trust_mc_core::EvidenceHash) -> bool {
    digest.algorithm == "sha256"
        && digest.value.len() == 64
        && digest.value.bytes().all(|byte| byte.is_ascii_hexdigit())
        && digest.value.bytes().all(|byte| !byte.is_ascii_uppercase())
}

fn trust_mc_obligation_identity_matches(obligation: &TrustObligation, candidate: &str) -> bool {
    if let Some(native_id) = native_trust_ir_expected_trust_mc_obligation_id(obligation) {
        // The compiler emits the suite token as the crate name `trust-mc`
        // (hyphen); trust-mc's native evidence ids use the identifier form
        // `trust_mc` (underscore). They denote the same obligation, so the
        // separator-insensitive comparison stops the identity gate from
        // rejecting genuinely-matching native CHC/PDR evidence. request/proof
        // ids are numeric, so canonicalizing `-`→`_` cannot merge distinct
        // obligations.
        native_trust_mc_obligation_lookup_key(candidate)
            == native_trust_mc_obligation_lookup_key(&native_id)
    } else {
        candidate == obligation.obligation_id
    }
}

fn native_trust_mc_obligation_lookup_key(obligation_id: &str) -> String {
    // Compiler metadata uses the crate token `trust-mc`, while trust-mc's
    // native transport IDs use the identifier token `trust_mc`. Request and
    // proof components are numeric, so normalizing this separator cannot merge
    // distinct native obligations.
    obligation_id.strip_prefix("trust_ir-native-trust-mc-request-").map_or_else(
        || obligation_id.to_string(),
        |suffix| format!("trust_ir-native-trust_mc-request-{suffix}"),
    )
}

fn native_trust_ir_expected_trust_mc_obligation_id(obligation: &TrustObligation) -> Option<String> {
    let suite =
        obligation_metadata_value(obligation, TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY)?;
    if suite != "trust-mc" {
        return None;
    }
    let request_id = canonical_u32_metadata_value(obligation_metadata_value(
        obligation,
        TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY,
    )?)?;
    let proof_id = canonical_u32_metadata_value(obligation_metadata_value(
        obligation,
        TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
    )?)?;
    Some(format!("trust_ir-native-trust-mc-request-{request_id}-proof-{proof_id}"))
}

/// One immutable, per-call index for reconciling public verifier obligations
/// with the native TrustIr proof inventory.
///
/// Values are stored as indices instead of references so the context stays
/// small and its ownership/cardinality checks remain explicit. Duplicate IDs
/// are deliberately retained in the vectors: row validation must reject them,
/// never let a map insertion silently choose an authority record.
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
#[derive(Debug)]
struct NativeTrustIrPublicClaimBindingContext {
    canonical_public_digests: trust_verifier_api::CanonicalObligationSemanticDigestIndex,
    trust_mc_requests: BTreeMap<u32, Vec<usize>>,
    request_proof_occurrences: BTreeMap<(usize, u32), usize>,
    proof_owners: BTreeMap<u32, Vec<u32>>,
    proofs: BTreeMap<u32, Vec<usize>>,
    functions: BTreeMap<u32, Vec<usize>>,
    obligation_sources: BTreeMap<u32, Vec<usize>>,
    monomorphizations: BTreeMap<u32, Vec<usize>>,
    replay_assertions: BTreeMap<(usize, u32), Vec<usize>>,
    contracts: BTreeMap<String, Vec<usize>>,
}

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
impl NativeTrustIrPublicClaimBindingContext {
    fn build(
        public_bundle: &TrustContractBundle,
        requested: &[TrustObligation],
        native_bundle: &trust_ir::NativeVerificationBundle,
    ) -> Result<Self, String> {
        // This batch API performs the full bundle validation, exact requested
        // subset reconciliation, duplicate detection, reference indexing, and
        // canonical digest construction in one pass. Calling the single-row
        // convenience API here would rebuild those maps once per obligation.
        let canonical_public_digests = public_bundle
            .canonical_obligation_semantic_digest_index_sha256(requested)
            .map_err(|reason| {
                format!("cannot bind/digest the canonical public-obligation inventory: {reason}")
            })?;

        let mut trust_mc_requests = BTreeMap::<u32, Vec<usize>>::new();
        let mut request_proof_occurrences = BTreeMap::<(usize, u32), usize>::new();
        let mut proof_owners = BTreeMap::<u32, Vec<u32>>::new();
        let mut replay_assertions = BTreeMap::<(usize, u32), Vec<usize>>::new();
        for (request_index, request) in native_bundle.requests.iter().enumerate() {
            let trust_ir::NativeVerificationRequest::TrustMc(request) = request else {
                continue;
            };
            trust_mc_requests.entry(request.id.index()).or_default().push(request_index);
            let mut owned_proofs = BTreeSet::new();
            for proof in &request.obligations {
                *request_proof_occurrences.entry((request_index, proof.index())).or_default() += 1;
                if owned_proofs.insert(proof.index()) {
                    proof_owners.entry(proof.index()).or_default().push(request.id.index());
                }
            }
            for (atom_index, atom) in request.provenance.replay_context.atoms.iter().enumerate() {
                if atom.kind == trust_ir::NativeReplayAtomKind::Assertion
                    && let Some(proof) = atom.obligation
                {
                    replay_assertions
                        .entry((request_index, proof.index()))
                        .or_default()
                        .push(atom_index);
                }
            }
        }

        let mut proofs = BTreeMap::<u32, Vec<usize>>::new();
        for (index, proof) in native_bundle.module.proof_obligations.iter().enumerate() {
            proofs.entry(proof.id.index()).or_default().push(index);
        }
        let mut functions = BTreeMap::<u32, Vec<usize>>::new();
        for (index, function) in native_bundle.module.functions.iter().enumerate() {
            functions.entry(function.id.index()).or_default().push(index);
        }
        let mut obligation_sources = BTreeMap::<u32, Vec<usize>>::new();
        for (index, source) in native_bundle.compiler_facts.obligation_sources.iter().enumerate() {
            obligation_sources.entry(source.obligation.index()).or_default().push(index);
        }
        let mut monomorphizations = BTreeMap::<u32, Vec<usize>>::new();
        for (index, fact) in native_bundle.compiler_facts.monomorphizations.iter().enumerate() {
            monomorphizations.entry(fact.id.index()).or_default().push(index);
        }
        let mut contracts = BTreeMap::<String, Vec<usize>>::new();
        for (index, contract) in public_bundle.contracts.iter().enumerate() {
            contracts.entry(contract.contract_id.clone()).or_default().push(index);
        }

        Ok(Self {
            canonical_public_digests,
            trust_mc_requests,
            request_proof_occurrences,
            proof_owners,
            proofs,
            functions,
            obligation_sources,
            monomorphizations,
            replay_assertions,
            contracts,
        })
    }
}

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
fn validate_native_trust_ir_public_claim_binding(
    public_bundle: &TrustContractBundle,
    public_obligation: &TrustObligation,
    native_bundle: &trust_ir::NativeVerificationBundle,
    context: &NativeTrustIrPublicClaimBindingContext,
) -> Result<(), String> {
    let canonical_public_digest = context
        .canonical_public_digests
        .get(&public_obligation.obligation_id)
        .ok_or_else(|| {
            format!(
                "public obligation `{}` was not part of the batch-validated request inventory",
                public_obligation.obligation_id
            )
        })?;

    let request_id = canonical_u32_metadata_value(
        obligation_metadata_value(public_obligation, TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY)
            .ok_or_else(|| {
                format!(
                    "public obligation `{}` is missing its unique native request id",
                    public_obligation.obligation_id
                )
            })?,
    )
    .ok_or_else(|| {
        format!(
            "public obligation `{}` has a non-canonical native request id",
            public_obligation.obligation_id
        )
    })?;
    let proof_id = canonical_u32_metadata_value(
        obligation_metadata_value(
            public_obligation,
            TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
        )
        .ok_or_else(|| {
            format!(
                "public obligation `{}` is missing its unique native proof-obligation id",
                public_obligation.obligation_id
            )
        })?,
    )
    .ok_or_else(|| {
        format!(
            "public obligation `{}` has a non-canonical native proof-obligation id",
            public_obligation.obligation_id
        )
    })?;
    let expected_native_id = native_trust_ir_expected_trust_mc_obligation_id(public_obligation)
        .ok_or_else(|| {
            format!(
                "public obligation `{}` lacks one complete canonical trust-mc native identity",
                public_obligation.obligation_id
            )
        })?;
    let expected_native_id_from_parts =
        format!("trust_ir-native-trust-mc-request-{request_id}-proof-{proof_id}");
    if expected_native_id != expected_native_id_from_parts {
        return Err(format!(
            "public obligation `{}` native identity `{expected_native_id}` does not match its exact request/proof projection `{expected_native_id_from_parts}`",
            public_obligation.obligation_id
        ));
    }

    let proof_id = trust_ir::ProofId::new(proof_id);
    let exact_request_indices =
        context.trust_mc_requests.get(&request_id).map_or(&[][..], Vec::as_slice);
    let [request_index] = exact_request_indices else {
        return Err(format!(
            "native TrustIr bundle contains {} trust-mc requests with exact request id {request_id}; expected one",
            exact_request_indices.len()
        ));
    };
    let trust_ir::NativeVerificationRequest::TrustMc(request) =
        &native_bundle.requests[*request_index]
    else {
        unreachable!("trust-mc request index was built from a different request variant")
    };
    let request_proof_occurrences = context
        .request_proof_occurrences
        .get(&(*request_index, proof_id.index()))
        .copied()
        .unwrap_or_default();
    if request_proof_occurrences != 1 {
        return Err(format!(
            "native trust-mc request {request_id} contains proof obligation {} {request_proof_occurrences} times; expected exactly once",
            proof_id.index()
        ));
    }
    let proof_owners = context.proof_owners.get(&proof_id.index()).map_or(&[][..], Vec::as_slice);
    if proof_owners != [request_id] {
        return Err(format!(
            "native TrustIr proof obligation {} is owned by trust-mc requests {proof_owners:?}; expected only request {request_id}",
            proof_id.index()
        ));
    }

    let matching_proof_indices =
        context.proofs.get(&proof_id.index()).map_or(&[][..], Vec::as_slice);
    let [proof_index] = matching_proof_indices else {
        return Err(format!(
            "native TrustIr module contains {} proof obligations with id {}; expected one",
            matching_proof_indices.len(),
            proof_id.index()
        ));
    };
    let proof = &native_bundle.module.proof_obligations[*proof_index];
    if !trust_mc_public_native_obligation_kind_matches(public_obligation, &proof.kind) {
        return Err(format!(
            "public trust-mc obligation `{}` kind {:?} does not match native proof obligation {} kind {:?}",
            public_obligation.obligation_id,
            public_obligation.kind,
            proof_id.index(),
            proof.kind
        ));
    }
    if proof.function != Some(request.function) {
        return Err(format!(
            "native trust-mc request {request_id} function {} does not exactly match proof obligation {} function {:?}",
            request.function.index(),
            proof_id.index(),
            proof.function
        ));
    }
    let matching_function_indices =
        context.functions.get(&request.function.index()).map_or(&[][..], Vec::as_slice);
    let [function_index] = matching_function_indices else {
        return Err(format!(
            "native TrustIr module contains {} functions with id {} for trust-mc request {request_id}; expected one",
            matching_function_indices.len(),
            request.function.index()
        ));
    };
    let native_function = &native_bundle.module.functions[*function_index];

    let embedded_source = proof.source.as_ref().ok_or_else(|| {
        format!(
            "native TrustIr proof obligation {} is missing its embedded source identity",
            proof_id.index()
        )
    })?;
    let embedded_public = embedded_source.public.as_ref().ok_or_else(|| {
        format!(
            "native TrustIr proof obligation {} source is missing its atomic public-obligation identity",
            proof_id.index()
        )
    })?;
    if embedded_public.obligation_id != public_obligation.obligation_id {
        return Err(format!(
            "native TrustIr proof obligation {} embeds public obligation id {:?}, but the verifier requested {:?}",
            proof_id.index(),
            embedded_public.obligation_id,
            public_obligation.obligation_id
        ));
    }
    let expected_embedded_digest = format!("sha256:{canonical_public_digest}");
    if embedded_public.semantic_digest.algorithm != trust_ir::ProofDigestAlgorithm::Sha256
        || embedded_public.semantic_digest.is_zero()
        || embedded_public.semantic_digest.to_string() != expected_embedded_digest
    {
        return Err(format!(
            "native TrustIr proof obligation {} embedded public semantic digest {} does not match canonical public claim {expected_embedded_digest}",
            proof_id.index(),
            embedded_public.semantic_digest
        ));
    }

    let expected_source_id = public_obligation
        .contract_id
        .as_deref()
        .or(public_obligation.proof_item_id.as_deref())
        .unwrap_or(&public_obligation.obligation_id);
    let expected_assertion_id = format!("trust-assertion:{expected_source_id}");
    if embedded_source.source_id != expected_source_id
        || embedded_source.assertion_id != expected_assertion_id
    {
        return Err(format!(
            "native TrustIr proof obligation {} source/assertion identity {:?}/{:?} does not match canonical public projection {:?}/{:?}",
            proof_id.index(),
            embedded_source.source_id,
            embedded_source.assertion_id,
            expected_source_id,
            expected_assertion_id
        ));
    }
    validate_native_trust_ir_public_source_range(
        public_obligation,
        native_bundle,
        proof_id,
        embedded_source.range,
    )?;

    let matching_source_indices =
        context.obligation_sources.get(&proof_id.index()).map_or(&[][..], Vec::as_slice);
    let [source_index] = matching_source_indices else {
        return Err(format!(
            "native TrustIr proof obligation {} has {} compiler-fact source bindings; expected one",
            proof_id.index(),
            matching_source_indices.len()
        ));
    };
    let compiler_source = &native_bundle.compiler_facts.obligation_sources[*source_index];
    if compiler_source.public_obligation_id != embedded_public.obligation_id {
        return Err(format!(
            "native TrustIr proof obligation {} compiler facts bind public id {:?}, embedded source binds {:?}",
            proof_id.index(),
            compiler_source.public_obligation_id,
            embedded_public.obligation_id
        ));
    }
    if compiler_source.function != proof.function
        || compiler_source.function != Some(request.function)
    {
        return Err(format!(
            "native TrustIr proof obligation {} function projection disagrees across request/module/compiler facts: request={}, module={:?}, compiler={:?}",
            proof_id.index(),
            request.function.index(),
            proof.function,
            compiler_source.function
        ));
    }
    let embedded_span = embedded_source.range.map(|range| trust_ir::SourceSpan {
        file: range.file,
        line: range.start_line,
        col: range.start_col,
    });
    if compiler_source.span != embedded_span {
        return Err(format!(
            "native TrustIr proof obligation {} compiler-fact span {:?} does not exactly project embedded range start {:?}",
            proof_id.index(),
            compiler_source.span,
            embedded_span
        ));
    }
    let embedded_assertion_id = trust_ir::NativeAssertionId::new(trust_types::stable_u32_id(
        embedded_source.assertion_id.as_bytes(),
    ));
    if compiler_source.assertion_id != Some(embedded_assertion_id) {
        return Err(format!(
            "native TrustIr proof obligation {} compiler-fact assertion {:?} does not match embedded assertion projection {}",
            proof_id.index(),
            compiler_source.assertion_id,
            embedded_assertion_id.index()
        ));
    }
    let expected_cause = native_trust_ir_obligation_cause_projection(&proof.kind);
    if compiler_source.cause != expected_cause {
        return Err(format!(
            "native TrustIr proof obligation {} compiler-fact cause {:?} does not match native kind {:?} projection {:?}",
            proof_id.index(),
            compiler_source.cause,
            proof.kind,
            expected_cause
        ));
    }
    let monomorphization = compiler_source.monomorphization.ok_or_else(|| {
        format!(
            "native TrustIr proof obligation {} compiler source lacks its function monomorphization",
            proof_id.index()
        )
    })?;
    if compiler_source.facts.as_slice()
        != [trust_ir::NativeCompilerFactRef::Monomorphization(monomorphization)]
    {
        return Err(format!(
            "native TrustIr proof obligation {} compiler source fact projection {:?} is not the exact monomorphization {:?}",
            proof_id.index(),
            compiler_source.facts,
            monomorphization
        ));
    }
    let matching_monomorphization_indices =
        context.monomorphizations.get(&monomorphization.index()).map_or(&[][..], Vec::as_slice);
    let [monomorphization_index] = matching_monomorphization_indices else {
        return Err(format!(
            "native TrustIr bundle contains {} monomorphization facts with id {}; expected one",
            matching_monomorphization_indices.len(),
            monomorphization.index()
        ));
    };
    let monomorphization_fact =
        &native_bundle.compiler_facts.monomorphizations[*monomorphization_index];
    if monomorphization_fact.function != Some(request.function) {
        return Err(format!(
            "native TrustIr monomorphization {} function {:?} does not match request {request_id} function {}",
            monomorphization.index(),
            monomorphization_fact.function,
            request.function.index()
        ));
    }

    let formula = proof.formula.as_ref().ok_or_else(|| {
        format!(
            "native TrustIr proof obligation {} is missing its authenticated claim formula",
            proof_id.index()
        )
    })?;
    validate_native_trust_ir_public_formula_binding(
        public_obligation,
        proof_id,
        embedded_source,
        formula,
    )?;
    let replay_assertion_indices = context
        .replay_assertions
        .get(&(*request_index, proof_id.index()))
        .map_or(&[][..], Vec::as_slice);
    let [replay_assertion_index] = replay_assertion_indices else {
        return Err(format!(
            "native trust-mc request {request_id} contains {} assertion replay atoms for proof obligation {}; expected one",
            replay_assertion_indices.len(),
            proof_id.index()
        ));
    };
    let replay_assertion = &request.provenance.replay_context.atoms[*replay_assertion_index];
    if replay_assertion.formula != *formula
        || replay_assertion.assertion_id != compiler_source.assertion_id
        || replay_assertion.span != compiler_source.span
    {
        return Err(format!(
            "native trust-mc request {request_id} assertion replay atom {} does not exactly project proof obligation {} formula/assertion/span",
            replay_assertion.id.index(),
            proof_id.index()
        ));
    }

    validate_native_trust_ir_public_chc_marker_binding(
        public_bundle,
        public_obligation,
        context,
        native_function.name.as_str(),
        request.function.index(),
        request_id,
        proof_id.index(),
    )?;
    Ok(())
}

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
fn trust_mc_public_native_obligation_kind_matches(
    public: &TrustObligation,
    native: &trust_ir::ObligationKind,
) -> bool {
    match (&public.kind, native) {
        (
            ObligationKind::Assertion | ObligationKind::ArithmeticSafety,
            trust_ir::ObligationKind::PanicFreedom | trust_ir::ObligationKind::ArithmeticSafety,
        ) => true,
        (
            ObligationKind::Precondition | ObligationKind::Postcondition,
            trust_ir::ObligationKind::PanicFreedom,
        ) => obligation_metadata_value(public, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY).is_some(),
        (
            ObligationKind::LoopInvariant | ObligationKind::Termination,
            trust_ir::ObligationKind::PanicFreedom,
        ) => is_typed_body_aware_e4_e5_obligation(public),
        (
            ObligationKind::Invariant | ObligationKind::Protocol,
            trust_ir::ObligationKind::TranslationValidation,
        ) => true,
        (
            ObligationKind::Custom { namespace, .. },
            trust_ir::ObligationKind::TranslationValidation,
        ) => namespace == TRUST_VC_HARDENED_NAMESPACE,
        _ => false,
    }
}

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
fn native_trust_ir_obligation_cause_projection(
    kind: &trust_ir::ObligationKind,
) -> trust_ir::NativeObligationCause {
    match kind {
        trust_ir::ObligationKind::Precondition => trust_ir::NativeObligationCause::Precondition,
        trust_ir::ObligationKind::Postcondition => trust_ir::NativeObligationCause::Postcondition,
        trust_ir::ObligationKind::LoopInvariant
        | trust_ir::ObligationKind::TypeInvariant
        | trust_ir::ObligationKind::RefinementType => trust_ir::NativeObligationCause::Assert,
        trust_ir::ObligationKind::MemorySafety => trust_ir::NativeObligationCause::BorrowCheck,
        trust_ir::ObligationKind::TranslationValidation => {
            trust_ir::NativeObligationCause::Translation
        }
        trust_ir::ObligationKind::PanicFreedom
        | trust_ir::ObligationKind::ArithmeticSafety
        | trust_ir::ObligationKind::BoundsCheck => trust_ir::NativeObligationCause::Panic,
        trust_ir::ObligationKind::TemporalSafety | trust_ir::ObligationKind::Liveness => {
            trust_ir::NativeObligationCause::Temporal
        }
        _ => trust_ir::NativeObligationCause::Panic,
    }
}

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
fn validate_native_trust_ir_public_source_range(
    public: &TrustObligation,
    native_bundle: &trust_ir::NativeVerificationBundle,
    proof_id: trust_ir::ProofId,
    embedded: Option<trust_ir::ProofObligationSourceRange>,
) -> Result<(), String> {
    match (public.source.file.as_deref(), embedded) {
        (None, None) => Ok(()),
        (None, Some(range)) => Err(format!(
            "native TrustIr proof obligation {} embeds source range {range:?}, but public source has no file",
            proof_id.index()
        )),
        (Some(file), None) => Err(format!(
            "native TrustIr proof obligation {} omits its source range for public file {file:?}",
            proof_id.index()
        )),
        (Some(file), Some(range)) => {
            let embedded_file = native_bundle.module.file_name(range.file).ok_or_else(|| {
                format!(
                    "native TrustIr proof obligation {} source range references missing file index {}",
                    proof_id.index(),
                    range.file
                )
            })?;
            let start_line = public.source.line.unwrap_or_default();
            let start_col = public.source.column.unwrap_or_default();
            let end_line = public.source.end_line.unwrap_or(start_line);
            let end_col = public.source.end_column.unwrap_or(start_col);
            if embedded_file != file
                || range.start_line != start_line
                || range.start_col != start_col
                || range.end_line != end_line
                || range.end_col != end_col
            {
                return Err(format!(
                    "native TrustIr proof obligation {} embedded source range {embedded_file:?}:{}:{}-{}:{} does not exactly match public source {file:?}:{start_line}:{start_col}-{end_line}:{end_col}",
                    proof_id.index(),
                    range.start_line,
                    range.start_col,
                    range.end_line,
                    range.end_col
                ));
            }
            Ok(())
        }
    }
}

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
fn validate_native_trust_ir_public_formula_binding(
    public: &TrustObligation,
    proof_id: trust_ir::ProofId,
    embedded_source: &trust_ir::ProofObligationSourceIdentity,
    formula: &trust_ir::ProofFormula,
) -> Result<(), String> {
    let schema = obligation_metadata_value(public, TRUST_VC_FORMULA_SCHEMA_METADATA_KEY);
    let payload = obligation_metadata_value(public, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY);
    let smtlib = obligation_metadata_value(public, TRUST_VC_FORMULA_SMTLIB_METADATA_KEY);
    let sort = obligation_metadata_value(public, TRUST_VC_FORMULA_SORT_METADATA_KEY);
    match (schema, payload) {
        (Some(schema), Some(payload)) => {
            if formula.schema != schema
                || formula.payload != payload
                || formula.smtlib.as_deref() != smtlib
                || formula.sort.as_deref() != sort
            {
                return Err(format!(
                    "native TrustIr proof obligation {} formula does not exactly match canonical public formula metadata",
                    proof_id.index()
                ));
            }
        }
        (Some(_), None) | (None, Some(_)) => {
            return Err(format!(
                "public obligation `{}` carries a partial formula schema/payload pair",
                public.obligation_id
            ));
        }
        (None, None) => {
            if smtlib.is_some() || sort.is_some() {
                return Err(format!(
                    "public obligation `{}` carries formula rendering metadata without a schema/payload claim",
                    public.obligation_id
                ));
            }
            if public.contract_id.is_some() || public.proof_item_id.is_some() {
                return Err(format!(
                    "public obligation `{}` references semantic contract/proof-item data but its native TrustIr proof unit carries no public formula metadata",
                    public.obligation_id
                ));
            }
            let expected_payload = serde_json::json!({
                "source_id": embedded_source.source_id,
                "assertion_id": embedded_source.assertion_id,
                "native_assertion_id": trust_types::stable_u32_id(
                    embedded_source.assertion_id.as_bytes()
                ),
                "span": {
                    "file": public.source.file.clone().unwrap_or_default(),
                    "line_start": public.source.line.unwrap_or_default(),
                    "col_start": public.source.column.unwrap_or_default(),
                    "line_end": public.source.end_line.unwrap_or_else(|| public.source.line.unwrap_or_default()),
                    "col_end": public.source.end_column.unwrap_or_else(|| public.source.column.unwrap_or_default()),
                },
                "public_obligation_id": public.obligation_id,
            })
            .to_string();
            if formula.schema != TRUST_IR_OBLIGATION_SOURCE_FORMULA_SCHEMA
                || formula.payload != expected_payload
                || formula.smtlib.is_some()
                || formula.sort.is_some()
            {
                return Err(format!(
                    "native TrustIr proof obligation {} source-only formula is not the exact canonical public source envelope",
                    proof_id.index()
                ));
            }
        }
    }
    Ok(())
}

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
fn validate_native_trust_ir_public_chc_marker_binding(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    context: &NativeTrustIrPublicClaimBindingContext,
    native_function_name: &str,
    native_function_id: u32,
    request_id: u32,
    proof_id: u32,
) -> Result<(), String> {
    let marker_id = native_trust_ir_synthetic_trust_mc_contract_id(obligation)?;
    let marker = if let Some(marker_id) = marker_id {
        let matching_marker_indices =
            context.contracts.get(marker_id).map_or(&[][..], Vec::as_slice);
        let [marker_index] = matching_marker_indices else {
            return Err(format!(
                "obligation `{}` names diagnostic native trust-mc synthetic contract `{marker_id}`, but the bundle contains {} matching contracts; expected exactly one",
                obligation.obligation_id,
                matching_marker_indices.len()
            ));
        };
        let marker = &bundle.contracts[*marker_index];
        validate_native_trust_ir_synthetic_trust_mc_contract_value(marker, obligation, marker_id)?;
        let marker_input = trust_mc_typed_chc_input_from_contract(marker)?.ok_or_else(|| {
            format!(
                "authenticated native trust-mc marker contract `{marker_id}` has no typed CHC input"
            )
        })?;
        validate_trust_mc_typed_chc_binding(marker, obligation, &marker_input)?;
        validate_native_trust_ir_typed_chc_function_projection(
            marker,
            &marker_input,
            native_function_name,
            native_function_id,
            request_id,
            proof_id,
            true,
        )?;
        Some((marker, marker_input))
    } else {
        None
    };

    let Some(contract_id) = obligation.contract_id.as_deref() else {
        return Ok(());
    };
    let matching_contract_indices =
        context.contracts.get(contract_id).map_or(&[][..], Vec::as_slice);
    let [contract_index] = matching_contract_indices else {
        return Err(format!(
            "public obligation `{}` references contract `{contract_id}`, but the bundle contains {} exact matches",
            obligation.obligation_id,
            matching_contract_indices.len()
        ));
    };
    let contract = &bundle.contracts[*contract_index];
    let Some(input) = trust_mc_typed_chc_input_from_contract(contract)? else {
        return Ok(());
    };
    validate_native_trust_ir_typed_chc_function_projection(
        contract,
        &input,
        native_function_name,
        native_function_id,
        request_id,
        proof_id,
        input.native_metadata.is_some(),
    )?;
    let carries_binding =
        contract.metadata.iter().any(|entry| entry.key == TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY);
    if carries_binding || input.native_metadata.is_some() {
        validate_trust_mc_typed_chc_binding(contract, obligation, &input)?;
        return Ok(());
    }

    validate_compiler_canonical_trust_mc_typed_chc_contract(contract, obligation, &input)?;
    let Some((marker, _)) = marker else {
        return Err(format!(
            "compiler canonical typed trust-mc contract `{contract_id}` has no authenticated native marker"
        ));
    };
    validate_compiler_canonical_trust_mc_semantic_projection(contract, marker)
}

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
fn validate_native_trust_ir_typed_chc_function_projection(
    contract: &TrustContract,
    input: &TrustMcTypedChcObligationInput,
    native_function_name: &str,
    native_function_id: u32,
    request_id: u32,
    proof_id: u32,
    require_native_metadata: bool,
) -> Result<(), String> {
    if input.function_name.as_deref() != Some(native_function_name) {
        return Err(format!(
            "typed trust-mc contract `{}` function {:?} does not exactly match native module function {:?}",
            contract.contract_id, input.function_name, native_function_name
        ));
    }
    let Some(metadata) = input.native_metadata.as_ref() else {
        if require_native_metadata {
            return Err(format!(
                "typed trust-mc contract `{}` is missing native request/proof/function metadata",
                contract.contract_id
            ));
        }
        return Ok(());
    };
    if metadata.native_request_id != request_id
        || metadata.proof_obligation_ids != [proof_id]
        || metadata.function_id != native_function_id
    {
        return Err(format!(
            "typed trust-mc contract `{}` native metadata does not exactly bind request {request_id}, proof {proof_id}, and one function",
            contract.contract_id
        ));
    }
    Ok(())
}

fn native_trust_ir_synthetic_trust_mc_contract_id(
    obligation: &TrustObligation,
) -> Result<Option<&str>, String> {
    let mut matches = obligation
        .metadata
        .iter()
        .filter(|entry| entry.key == TRUST_MC_TYPED_CHC_SYNTHETIC_CONTRACT_METADATA_KEY);
    let Some(entry) = matches.next() else {
        return Ok(None);
    };
    if matches.next().is_some() {
        return Err(format!(
            "obligation `{}` carries duplicate native trust-mc synthetic contract identities",
            obligation.obligation_id
        ));
    }
    validate_native_trust_ir_identity_metadata_if_present(obligation)?;
    let Some(native_obligation_id) = native_trust_ir_expected_trust_mc_obligation_id(obligation)
    else {
        return Err(format!(
            "obligation `{}` names a native trust-mc synthetic contract without one complete native TrustIr identity",
            obligation.obligation_id
        ));
    };
    let expected = format!(
        "contract:trust-mc-typed-chc:{}",
        native_trust_mc_obligation_lookup_key(&native_obligation_id)
    );
    if entry.value != expected {
        return Err(format!(
            "obligation `{}` carries native trust-mc synthetic contract identity `{}`, expected deterministic identity `{expected}`",
            obligation.obligation_id, entry.value
        ));
    }
    Ok(Some(entry.value.as_str()))
}

fn validate_native_trust_ir_synthetic_trust_mc_contract(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    contract_id: &str,
) -> Result<(), String> {
    let contract = native_trust_ir_synthetic_trust_mc_contract(bundle, obligation, contract_id)?;
    validate_native_trust_ir_synthetic_trust_mc_contract_value(contract, obligation, contract_id)
}

fn validate_native_trust_ir_synthetic_trust_mc_contract_value(
    contract: &TrustContract,
    obligation: &TrustObligation,
    contract_id: &str,
) -> Result<(), String> {
    if contract.kind != ContractKind::Asserts {
        return Err(format!(
            "diagnostic native trust-mc synthetic contract `{contract_id}` has kind {:?}, expected Asserts",
            contract.kind
        ));
    }
    match &contract.predicate {
        ContractPredicate::MathIr { schema, .. }
            if schema == TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION => {}
        ContractPredicate::MathIr { schema, .. } => {
            return Err(format!(
                "diagnostic native trust-mc synthetic contract `{contract_id}` has MathIr schema `{schema}`, expected `{TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION}`"
            ));
        }
        _ => {
            return Err(format!(
                "diagnostic native trust-mc synthetic contract `{contract_id}` must use ContractPredicate::MathIr with schema `{TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION}`"
            ));
        }
    }
    if contract.source != obligation.source {
        return Err(format!(
            "diagnostic native trust-mc synthetic contract `{contract_id}` source does not exactly match public obligation `{}` source",
            obligation.obligation_id
        ));
    }
    Ok(())
}

fn native_trust_ir_synthetic_trust_mc_contract<'a>(
    bundle: &'a TrustContractBundle,
    obligation: &TrustObligation,
    contract_id: &str,
) -> Result<&'a TrustContract, String> {
    let matching_contracts = bundle
        .contracts
        .iter()
        .filter(|contract| contract.contract_id == contract_id)
        .collect::<Vec<_>>();
    let [contract] = matching_contracts.as_slice() else {
        return Err(format!(
            "obligation `{}` names diagnostic native trust-mc synthetic contract `{contract_id}`, but the bundle contains {} matching contracts; expected exactly one",
            obligation.obligation_id,
            matching_contracts.len()
        ));
    };
    Ok(contract)
}

fn validate_native_trust_ir_identity_metadata_if_present(
    obligation: &TrustObligation,
) -> Result<(), String> {
    let carries_native_identity = obligation.metadata.iter().any(|entry| {
        matches!(
            entry.key.as_str(),
            TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY
                | TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY
                | TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY
        )
    });
    if carries_native_identity
        && native_trust_ir_expected_trust_mc_obligation_id(obligation).is_none()
    {
        return Err(format!(
            "obligation `{}` has incomplete, duplicate, or non-canonical native TrustIr identity metadata",
            obligation.obligation_id
        ));
    }
    Ok(())
}

fn obligation_metadata_value<'a>(obligation: &'a TrustObligation, key: &str) -> Option<&'a str> {
    metadata_value(&obligation.metadata, key)
}

fn canonical_u32_metadata_value(value: &str) -> Option<u32> {
    let parsed = value.parse::<u32>().ok()?;
    (parsed.to_string() == value).then_some(parsed)
}

fn validate_native_metadata_for_public_obligation(
    metadata: &TrustMcNativeTypedChcObligationMetadata,
    obligation: &TrustObligation,
) -> Result<(), Vec<String>> {
    let mut grouped_rejections = Vec::new();
    if metadata.proof_obligation_ids().len() != 1 {
        grouped_rejections.push(format!(
            "native typed CHC metadata binds grouped proof obligations {:?}; proof-grade public evidence requires exactly one MIR proof obligation",
            metadata.proof_obligation_ids()
        ));
    }
    let mut candidate_ids = vec![obligation.obligation_id.as_str()];
    let native_id = native_trust_ir_expected_trust_mc_obligation_id(obligation);
    if let Some(native_id) = native_id.as_deref() {
        candidate_ids.push(native_id);
    }

    let mut last_reasons = Vec::new();
    for candidate_id in candidate_ids {
        match metadata.validate_for_obligation_id(candidate_id) {
            Ok(()) if grouped_rejections.is_empty() => return Ok(()),
            Ok(()) => return Err(grouped_rejections),
            Err(reasons) => last_reasons = reasons,
        }
    }
    if !grouped_rejections.is_empty() {
        grouped_rejections.extend(last_reasons);
        return Err(grouped_rejections);
    }
    Err(last_reasons)
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ChcPdrEvidenceExpectation {
    proof_kind: &'static str,
    proof_strength: ProofStrength,
}

impl ChcPdrEvidenceExpectation {
    fn diagnostic(&self) -> String {
        format!(
            "native CHC/PDR candidate required: {}; expected proof_strength is {:?}/{:?}, but a generic solver verdict or serialized candidate is diagnostic-only and Proved additionally requires live opaque native-bundle authority",
            self.proof_kind, self.proof_strength.reasoning, self.proof_strength.assurance
        )
    }
}

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
#[derive(Debug)]
struct NativeTrustIrChcPdrAuthorizedProof {
    // Keep the live, non-serializable authority carrier until the exact
    // obligation is consumed. Extracting only `evidence.transport` here would
    // turn a forgeable diagnostic record back into a proof capability.
    evidence: trust_mc_driver::NativeTrustIrChcPdrEvidence,
    expected_normalized_input: TrustMcNativeTypedChcPdrNormalizedInput,
    request_id: u32,
    proof_ids: Vec<u32>,
    lineage_roots: Vec<u32>,
    function_id: u32,
    translation_diagnostic_count: usize,
    route: String,
    cache_key: String,
    artifact_directory: String,
    relation_count: usize,
    clause_count: usize,
}

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
impl NativeTrustIrChcPdrAuthorizedProof {
    fn try_from_bundle_evidence(
        evidence: trust_mc_driver::NativeTrustIrChcPdrEvidence,
    ) -> Result<Self, String> {
        // Derive proof identity from the exact translated request before
        // consulting any producer-authored verification/cache/transport field.
        let expected_normalized_input =
            trust_mc_driver::normalized_typed_chc_pdr_input(&evidence.translated.obligation)
                .map_err(|error| {
                    format!(
                        "native TrustIr pre-solve typed obligation could not be normalized independently: {}",
                        native_typed_chc_pdr_error_reason(error)
                    )
                })?;
        validate_native_full_verification_normalized_input(
            &evidence.verification,
            &expected_normalized_input,
        )
        .map_err(|reason| {
            format!(
                "native TrustIr full-verification normalized input failed consumer binding: {reason}"
            )
        })?;
        let authority = evidence.verification.authorized_native_proof().map_err(|error| {
            format!(
                "native TrustIr full-verification did not retain opaque proof authority: {}",
                native_typed_chc_pdr_error_reason(error)
            )
        })?;
        if authority.transport_record() != evidence.transport {
            return Err(
                "native TrustIr diagnostic transport differs from the live opaque-authority snapshot"
                    .to_string(),
            );
        }
        let route = format!("{:?}", evidence.verification.route);
        let cache_key = evidence.verification.cache_key.key.value.clone();
        let artifact_directory = evidence.verification.artifact_directory.clone();
        let relation_count = evidence.verification.outcome.stats.relation_count;
        let clause_count = evidence.verification.outcome.stats.clause_count;
        Ok(Self {
            expected_normalized_input,
            request_id: evidence.translated.request_id.index(),
            proof_ids: evidence.translated.obligations.iter().map(|id| id.index()).collect(),
            lineage_roots: evidence.translated.lineage_roots.iter().map(|id| id.index()).collect(),
            function_id: evidence.translated.function.index(),
            translation_diagnostic_count: evidence.translated.diagnostics.len(),
            route,
            cache_key,
            artifact_directory,
            relation_count,
            clause_count,
            evidence,
        })
    }

    fn diagnostic_transport(&self) -> &TrustMcNativeTypedChcPdrProofTransport {
        &self.evidence.transport
    }

    fn native_trust_ir_context_diagnostic(&self) -> String {
        format!(
            "native trust_mc TrustIr CHC/PDR proof-grade result accepted: request_id={}, proof_ids={:?}, lineage_roots={:?}, function_id={}, route={}, relations={}, clauses={}, cache_key_sha256={}, artifact_directory={}, translation_diagnostics={}",
            self.request_id,
            self.proof_ids,
            self.lineage_roots,
            self.function_id,
            self.route,
            self.relation_count,
            self.clause_count,
            self.cache_key,
            self.artifact_directory,
            self.translation_diagnostic_count
        )
    }
}

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
fn native_trust_ir_direct_typed_context_diagnostic(
    translated: &trust_mc_trust_bmc::NativeTrustMcChcPdrObligation,
) -> String {
    format!(
        "native trust_mc TrustIr CHC/PDR direct typed input consumed: request_id={}, proof_ids={:?}, lineage_roots={:?}, function_id={}, native_id={}, translation_diagnostics={}",
        translated.request_id.index(),
        translated.obligations.iter().map(|id| id.index()).collect::<Vec<_>>(),
        translated.lineage_roots.iter().map(|id| id.index()).collect::<Vec<_>>(),
        translated.function.index(),
        translated.obligation.obligation_id,
        translated.diagnostics.len()
    )
}

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
fn validate_trust_mc_native_admission_contract(
    native_bundle: &trust_ir::NativeVerificationBundle,
) -> Result<(), String> {
    let mut rejections = Vec::new();
    for request in &native_bundle.requests {
        let trust_ir::NativeVerificationRequest::TrustMc(request) = request else {
            continue;
        };
        if request.provenance.expected_verifier.version.as_deref()
            != Some(TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION)
        {
            rejections.push(format!(
                "request {} expected_verifier.version is {:?}, expected {}",
                request.id.index(),
                request.provenance.expected_verifier.version.as_deref(),
                TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION
            ));
        }
        if request.provenance.replay.as_ref().is_none_or(|replay| {
            !replay.invocation.contains(TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION)
        }) {
            rejections.push(format!(
                "request {} replay identity does not name admission contract {}",
                request.id.index(),
                TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION
            ));
        }
        for unsupported in &request.provenance.replay_context.unsupported_modes {
            rejections.push(format!(
                "request {} carries unsupported native mode {:?}: {}",
                request.id.index(),
                unsupported.reason,
                unsupported.detail
            ));
        }
    }

    if rejections.is_empty() {
        Ok(())
    } else {
        Err(format!("native trust_mc admission contract rejected: {}", rejections.join("; ")))
    }
}

impl Default for TrustMcVerifierApiAdapter {
    fn default() -> Self {
        Self::new(TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3))
    }
}

impl VerificationEngine for TrustMcVerifierApiAdapter {
    fn manifest(&self) -> &EngineManifest {
        &self.manifest
    }

    fn supports(&self, obligation: &TrustObligation) -> SupportLevel {
        if is_trust_mc_owned_obligation(obligation) {
            SupportLevel::Supported
        } else {
            SupportLevel::Unsupported {
                reason: format!(
                    "trust-mc verifier-api adapter does not own {:?} obligations",
                    obligation.kind
                ),
            }
        }
    }

    fn verify_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
    ) -> Vec<ObligationEvidence> {
        let (bundle, obligations) = request.into_parts();
        obligations.iter().map(|obligation| self.verify_obligation(bundle, obligation)).collect()
    }
}

/// Obligation kinds owned by the trust_mc verifier-api adapter.
#[must_use]
pub fn trust_mc_owned_obligation_kinds() -> Vec<ObligationKind> {
    let mut kinds = vec![
        ObligationKind::Precondition,
        ObligationKind::Postcondition,
        ObligationKind::Assertion,
        ObligationKind::ArithmeticSafety,
        ObligationKind::Invariant,
        ObligationKind::Protocol,
    ];
    kinds.extend(hardened_custom_obligation_kinds());
    kinds
}

/// Returns true when trust_mc owns the obligation lane.
#[must_use]
pub fn is_trust_mc_owned_obligation_kind(kind: &ObligationKind) -> bool {
    matches!(
        kind,
        ObligationKind::Assertion
            | ObligationKind::ArithmeticSafety
            | ObligationKind::Invariant
            | ObligationKind::Protocol
            // Trust (P1.2): a body-aware `#[ensures]` VC reaches the trust-mc
            // adapter as a `Postcondition` obligation carrying a typed CHC
            // (`¬postcond ∧ body_defs`) — the router only dispatches the VC (never
            // the claim-based marker, which stays on trust-wp) to trust-mc. A
            // Postcondition WITHOUT a typed CHC payload fails closed to Unsupported
            // in `trust_mc_typed_chc_lowering`, so owning the kind never fabricates
            // a proof.
            | ObligationKind::Postcondition
            // Trust (P1.2 precedent, extended to preconditions): the call-site
            // `#[requires]` VC is the same payload shape (`¬precond ∧ body_defs`)
            // and reaches the adapter only when the router's payload-aware route
            // dispatched it (the def-site marker stays on trust-wp); a
            // Precondition without a typed CHC payload fails closed identically.
            | ObligationKind::Precondition
    ) || is_hardened_custom_obligation_kind(kind)
}

fn is_hardened_custom_obligation_kind(kind: &ObligationKind) -> bool {
    matches!(
        kind,
        ObligationKind::Custom { namespace, .. } if namespace == TRUST_VC_HARDENED_NAMESPACE
    )
}

fn hardened_custom_obligation_kinds() -> Vec<ObligationKind> {
    [
        "raw_path_api",
        "path_identity",
        "permission_change",
        "permission_create",
        "permission_window",
        "utf8_reject",
        "byte_loss",
        "error_discard",
        "panic_boundary",
        "compat_observable",
        "process_semantics",
        "trust_domain",
        "trust_domain_order",
        "unsafe_operation",
        "ffi_boundary",
        "unknown",
        TRUST_VC_HARDENED_WILDCARD,
    ]
    .into_iter()
    .map(|name| ObligationKind::Custom {
        namespace: TRUST_VC_HARDENED_NAMESPACE.to_string(),
        name: name.to_string(),
    })
    .collect()
}

fn trust_mc_manifest() -> EngineManifest {
    let mut manifest =
        EngineManifest::new(ENGINE_NAME, env!("CARGO_PKG_VERSION"), EngineKind::Reachability);
    manifest.capabilities = trust_mc_owned_obligation_kinds()
        .into_iter()
        .map(|obligation_kind| EngineCapability {
            obligation_kind,
            support: SupportLevel::Supported,
        })
        .collect();
    manifest.proof_modes = vec![ReasoningKind::Chc, ReasoningKind::Pdr];
    manifest
}

#[cfg(test)]
mod tests {
    use trust_verifier_api::{
        BundleSubject, ContractKind, EvidenceDisposition, SourceLocation, TrustContract,
        VerificationRunResult, VerificationRunStatus, VerifierExecutionContext,
    };

    use super::*;

    const TEST_SOURCE_DIGEST: &str =
        "1111111111111111111111111111111111111111111111111111111111111111";
    const TEST_VC_DIGEST: &str = "2222222222222222222222222222222222222222222222222222222222222222";

    fn obligation(kind: ObligationKind, id: &str) -> TrustObligation {
        TrustObligation {
            obligation_id: id.to_string(),
            kind,
            contract_id: None,
            proof_item_id: None,
            source: SourceLocation::default(),
            description: "test obligation".to_string(),
            required_strength: None,
            summary_facts: Vec::new(),
            metadata: Vec::new(),
        }
    }

    fn bundle_with(obligations: Vec<TrustObligation>) -> TrustContractBundle {
        let mut bundle = TrustContractBundle::empty(
            "bundle-trust-mc",
            BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
        );
        bundle.publication.dpub_plan_hash = Some("sha256:plan".to_string());
        bundle.publication.trust_engines_lock_hash = Some("sha256:lock".to_string());
        bundle.obligations = obligations;
        bundle
    }

    fn obligation_with_contract(
        kind: ObligationKind,
        id: &str,
        contract_id: &str,
    ) -> TrustObligation {
        let mut obligation = obligation(kind, id);
        obligation.contract_id = Some(contract_id.to_string());
        add_source_vc_digest_metadata(&mut obligation);
        obligation
    }

    fn add_source_vc_digest_metadata(obligation: &mut TrustObligation) {
        obligation.metadata.extend([
            MetadataEntry {
                key: TRUST_SOURCE_DIGEST_METADATA_KEY.to_string(),
                value: TEST_SOURCE_DIGEST.to_string(),
            },
            MetadataEntry {
                key: TRUST_VC_DIGEST_METADATA_KEY.to_string(),
                value: TEST_VC_DIGEST.to_string(),
            },
        ]);
    }

    fn add_typed_body_aware_vc_formula(obligation: &mut TrustObligation) {
        add_typed_body_aware_vc_formula_value(obligation, false);
    }

    fn add_typed_body_aware_vc_formula_value(obligation: &mut TrustObligation, value: bool) {
        let predicate = trust_verifier_api::TrustSpecPredicate::new(
            trust_verifier_api::TrustSpecExpr::bool_literal(value),
            Vec::new(),
        );
        obligation.metadata.extend([
            trust_verifier_api::ObligationContext::new(
                trust_verifier_api::ObligationProducer::CompilerMirExtract,
                trust_verifier_api::ObligationOrigin::VerificationCondition {
                    vc_kind: "loop_contract".to_string(),
                    vc_index: 0,
                    formula_schema: Some(
                        trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
                    ),
                },
            )
            .to_metadata_entry()
            .expect("typed VC context should serialize"),
            MetadataEntry {
                key: TRUST_VC_FORMULA_SCHEMA_METADATA_KEY.to_string(),
                value: trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
            },
            MetadataEntry {
                key: TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY.to_string(),
                value: serde_json::to_string(&predicate)
                    .expect("typed VC predicate should serialize"),
            },
        ]);
    }

    fn spec_var(name: &str) -> trust_verifier_api::TrustSpecExpr {
        trust_verifier_api::TrustSpecExpr::variable(name, trust_verifier_api::TrustSpecSort::Int)
    }

    fn spec_var_decl(name: &str) -> trust_verifier_api::TrustSpecVariable {
        trust_verifier_api::TrustSpecVariable {
            name: name.to_string(),
            sort: trust_verifier_api::TrustSpecSort::Int,
            origin: trust_verifier_api::TrustSpecVariableOrigin::Inferred,
        }
    }

    /// Attach a body-aware violation formula in the REAL dumped shape of a
    /// post-state-constraining clause (the `inc` fixture class):
    /// `_0 = x ∧ ¬(_0 = x)` — the return slot appears both as a positive def
    /// conjunct AND inside the negated clause.
    fn add_result_referencing_vc_formula(obligation: &mut TrustObligation) {
        use trust_verifier_api::TrustSpecBinaryOp as Op;
        let eq = |lhs, rhs| trust_verifier_api::TrustSpecExpr::binary(Op::Eq, lhs, rhs);
        let mut predicate = trust_verifier_api::TrustSpecPredicate::new(
            trust_verifier_api::TrustSpecExpr::binary(
                Op::And,
                eq(spec_var("_0"), spec_var("x")),
                trust_verifier_api::TrustSpecExpr::unary(
                    trust_verifier_api::TrustSpecUnaryOp::Not,
                    eq(spec_var("_0"), spec_var("x")),
                ),
            ),
            vec![spec_var_decl("_0"), spec_var_decl("x")],
        );
        predicate.validate().expect("result-referencing predicate must validate");
        add_vc_formula_payload(obligation, &predicate, "postcondition");
    }

    /// Attach a body-aware violation formula in the REAL dumped shape of the
    /// E9 citation-undischarged tautology class (`x >= x` on `no_citation`):
    /// `_0 = x ∧ ¬(x >= x)` — the return slot is pinned as a positive def
    /// conjunct but the NEGATED CLAUSE never references it. Global `_0`
    /// presence must NOT admit this row (that is exactly the caveat the
    /// payload probe established).
    fn add_result_free_vc_formula(obligation: &mut TrustObligation) {
        use trust_verifier_api::TrustSpecBinaryOp as Op;
        let mut predicate = trust_verifier_api::TrustSpecPredicate::new(
            trust_verifier_api::TrustSpecExpr::binary(
                Op::And,
                trust_verifier_api::TrustSpecExpr::binary(Op::Eq, spec_var("_0"), spec_var("x")),
                trust_verifier_api::TrustSpecExpr::unary(
                    trust_verifier_api::TrustSpecUnaryOp::Not,
                    trust_verifier_api::TrustSpecExpr::binary(Op::Ge, spec_var("x"), spec_var("x")),
                ),
            ),
            vec![spec_var_decl("_0"), spec_var_decl("x")],
        );
        predicate.validate().expect("tautology predicate must validate");
        add_vc_formula_payload(obligation, &predicate, "postcondition");
    }

    fn add_vc_formula_payload(
        obligation: &mut TrustObligation,
        predicate: &trust_verifier_api::TrustSpecPredicate,
        vc_kind: &str,
    ) {
        obligation.metadata.extend([
            trust_verifier_api::ObligationContext::new(
                trust_verifier_api::ObligationProducer::CompilerMirExtract,
                trust_verifier_api::ObligationOrigin::VerificationCondition {
                    vc_kind: vc_kind.to_string(),
                    vc_index: 0,
                    formula_schema: Some(
                        trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
                    ),
                },
            )
            .to_metadata_entry()
            .expect("typed VC context should serialize"),
            MetadataEntry {
                key: TRUST_VC_FORMULA_SCHEMA_METADATA_KEY.to_string(),
                value: trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
            },
            MetadataEntry {
                key: TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY.to_string(),
                value: serde_json::to_string(predicate)
                    .expect("typed VC predicate should serialize"),
            },
        ]);
    }

    /// The fresh-exact postcondition admission and its two guardrails: the
    /// discriminator admits ONLY post-state-referencing postcondition rows
    /// (the E9 tautology tripwires stay out), and E4/E5 admission is
    /// unchanged.
    #[test]
    fn exact_direct_admission_scopes_to_result_referencing_postconditions() {
        let mut admitted = obligation(ObligationKind::Postcondition, "obligation:demo::f:post:0");
        add_result_referencing_vc_formula(&mut admitted);
        assert!(
            is_typed_body_aware_exact_direct_obligation(&admitted),
            "result-referencing postcondition must enter the fresh-exact lane"
        );
        assert!(
            !is_typed_body_aware_e4_e5_obligation(&admitted),
            "the postcondition admission must not leak into the E4/E5 predicate"
        );

        let mut tautology = obligation(ObligationKind::Postcondition, "obligation:demo::f:post:1");
        add_result_free_vc_formula(&mut tautology);
        assert!(
            !is_typed_body_aware_exact_direct_obligation(&tautology),
            "a post-state-free clause (x >= x) must stay OUT of the fresh-exact lane: \
             admitting it would flip the E9 citation-undischarged tripwire"
        );

        let mut loop_row = obligation(ObligationKind::LoopInvariant, "obligation:demo::f:e4:0");
        add_typed_body_aware_vc_formula(&mut loop_row);
        assert!(is_typed_body_aware_e4_e5_obligation(&loop_row), "E4/E5 admission unchanged");
        assert!(
            is_typed_body_aware_exact_direct_obligation(&loop_row),
            "the widened predicate is a superset of E4/E5"
        );

        let mut assertion = obligation(ObligationKind::Assertion, "obligation:demo::f:assert:0");
        add_result_referencing_vc_formula(&mut assertion);
        assert!(
            !is_typed_body_aware_exact_direct_obligation(&assertion),
            "non-postcondition kinds outside E4/E5 stay out regardless of payload"
        );
    }

    fn typed_chc_contract(
        contract_id: &str,
        obligation_id: &str,
        derive_error: bool,
    ) -> TrustContract {
        typed_chc_contract_for_public(contract_id, obligation_id, obligation_id, derive_error)
    }

    fn typed_chc_contract_for_public(
        contract_id: &str,
        public_obligation_id: &str,
        obligation_id: &str,
        derive_error: bool,
    ) -> TrustContract {
        let error_rule = if derive_error {
            serde_json::json!({
                "head": { "name": "error" },
                "body": {
                    "relation": {
                        "name": "entry",
                        "args": [
                            { "kind": "var", "name": "ok", "sort": { "kind": "bool" } }
                        ]
                    }
                },
            })
        } else {
            serde_json::json!({
                "head": { "name": "error" },
                "body": {
                    "relation": {
                        "name": "entry",
                        "args": [
                            { "kind": "var", "name": "ok", "sort": { "kind": "bool" } }
                        ]
                    },
                    "constraints": [
                        { "kind": "var", "name": "ok", "sort": { "kind": "bool" } }
                    ]
                },
            })
        };
        let rules = vec![
            serde_json::json!({
                "head": {
                    "name": "entry",
                    "args": [
                        { "kind": "bool_const", "value": false }
                    ]
                },
            }),
            error_rule,
        ];
        let mut value = serde_json::json!({
            "origin": "mir_derived",
            "obligation_id": obligation_id,
            "function_name": "demo::f",
            "query": { "target": "error" },
            "vars": [
                { "name": "ok", "sort": { "kind": "bool" } }
            ],
            "relations": [
                { "name": "entry", "arg_sorts": [{ "kind": "bool" }] },
                { "name": "error" }
            ],
            "rules": rules,
        });
        if let Some((native_request_id, proof_obligation_id)) =
            parse_native_typed_chc_obligation_id(obligation_id)
        {
            value["native_metadata"] = serde_json::to_value(native_typed_chc_metadata(
                native_request_id,
                proof_obligation_id,
                "chc",
            ))
            .expect("native metadata should serialize");
        }
        let metadata =
            typed_chc_binding_metadata(contract_id, public_obligation_id, obligation_id, &value);

        TrustContract {
            contract_id: contract_id.to_string(),
            kind: ContractKind::Asserts,
            predicate: ContractPredicate::MathIr {
                schema: TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA.to_string(),
                value,
            },
            source: SourceLocation::default(),
            metadata,
        }
    }

    #[cfg(feature = "trust-mc-native-solver")]
    fn cyclic_safe_typed_chc_contract(
        contract_id: &str,
        public_obligation_id: &str,
        native_obligation_id: &str,
    ) -> TrustContract {
        let int_var = || {
            serde_json::json!({
                "kind": "var",
                "name": "x",
                "sort": { "kind": "int" }
            })
        };
        let mut contract = typed_chc_contract_for_public(
            contract_id,
            public_obligation_id,
            native_obligation_id,
            false,
        );
        let ContractPredicate::MathIr { value, .. } = &mut contract.predicate else {
            unreachable!("typed fixture uses MathIr")
        };
        value["vars"] = serde_json::json!([
            { "name": "x", "sort": { "kind": "int" } }
        ]);
        value["relations"] = serde_json::json!([
            { "name": "loop", "arg_sorts": [{ "kind": "int" }] },
            { "name": "error" }
        ]);
        value["rules"] = serde_json::json!([
            {
                "head": {
                    "name": "loop",
                    "args": [{ "kind": "int_const", "value": 0 }]
                }
            },
            {
                "head": {
                    "name": "loop",
                    "args": [{
                        "kind": "binary",
                        "op": "add",
                        "lhs": int_var(),
                        "rhs": { "kind": "int_const", "value": 1 }
                    }]
                },
                "body": {
                    "relation": { "name": "loop", "args": [int_var()] },
                    "constraints": [{
                        "kind": "binary",
                        "op": "lt",
                        "lhs": int_var(),
                        "rhs": { "kind": "int_const", "value": 10 }
                    }]
                }
            },
            {
                "head": { "name": "error" },
                "body": {
                    "relation": { "name": "loop", "args": [int_var()] },
                    "constraints": [{
                        "kind": "binary",
                        "op": "lt",
                        "lhs": int_var(),
                        "rhs": { "kind": "int_const", "value": 0 }
                    }]
                }
            }
        ]);
        refresh_typed_chc_binding_metadata(
            &mut contract,
            public_obligation_id,
            native_obligation_id,
        );
        contract
    }

    /// Typed-CHC contract whose error rule guards on `n == <constant> && n <= 0`
    /// over an Int variable. With an out-of-i128 `constant` this is the
    /// direct-lane shape of a routed call-site `#[requires]` precondition VC
    /// whose predicate carries a u128-width type-range bound (the
    /// generate::Lcg::range_i128 / range_usize / small_rat corpus): the
    /// producer passes the decimal string through verbatim, and the error
    /// query is unreachable (the wide constant is positive, contradicting
    /// `n <= 0`), so admitting the constant must yield a real solve — never
    /// the historic "outside i128" Unsupported.
    fn typed_chc_contract_with_int_guard_constant(
        contract_id: &str,
        obligation_id: &str,
        constant: &str,
    ) -> TrustContract {
        let int_var =
            || serde_json::json!({ "kind": "var", "name": "n", "sort": { "kind": "int" } });
        let rules = vec![
            serde_json::json!({
                "head": { "name": "entry", "args": [int_var()] },
            }),
            serde_json::json!({
                "head": { "name": "error" },
                "body": {
                    "relation": { "name": "entry", "args": [int_var()] },
                    "constraints": [
                        {
                            "kind": "binary",
                            "op": "eq",
                            "lhs": int_var(),
                            "rhs": { "kind": "int_const", "value": constant },
                        },
                        {
                            "kind": "binary",
                            "op": "le",
                            "lhs": int_var(),
                            "rhs": { "kind": "int_const", "value": "0" },
                        }
                    ]
                },
            }),
        ];
        let mut value = serde_json::json!({
            "origin": "mir_derived",
            "obligation_id": obligation_id,
            "function_name": "generate::Lcg::range_i128",
            "query": { "target": "error" },
            "vars": [
                { "name": "n", "sort": { "kind": "int" } }
            ],
            "relations": [
                { "name": "entry", "arg_sorts": [{ "kind": "int" }] },
                { "name": "error" }
            ],
            "rules": rules,
        });
        if let Some((native_request_id, proof_obligation_id)) =
            parse_native_typed_chc_obligation_id(obligation_id)
        {
            value["native_metadata"] = serde_json::to_value(native_typed_chc_metadata(
                native_request_id,
                proof_obligation_id,
                "chc",
            ))
            .expect("native metadata should serialize");
        }
        let metadata =
            typed_chc_binding_metadata(contract_id, obligation_id, obligation_id, &value);

        TrustContract {
            contract_id: contract_id.to_string(),
            kind: ContractKind::Asserts,
            predicate: ContractPredicate::MathIr {
                schema: TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA.to_string(),
                value,
            },
            source: SourceLocation::default(),
            metadata,
        }
    }

    fn typed_chc_binding_metadata(
        contract_id: &str,
        public_obligation_id: &str,
        native_obligation_id: &str,
        value: &serde_json::Value,
    ) -> Vec<MetadataEntry> {
        serde_json::from_value::<TrustMcTypedChcObligationInput>(value.clone())
            .expect("typed CHC test input should parse");
        let synthetic_digest =
            trust_mc_typed_chc_value_digest(value).expect("typed CHC test input should digest");
        let binding = serde_json::json!({
            "schema_version": TRUST_MC_TYPED_CHC_BINDING_SCHEMA_VERSION,
            "typed_chc_schema": TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION,
            "public_obligation_id": public_obligation_id,
            "native_obligation_id": native_obligation_id,
            "synthetic_contract_id": contract_id,
            "source_digest": {
                "algorithm": "sha256",
                "value": TEST_SOURCE_DIGEST,
            },
            "vc_digest": {
                "algorithm": "sha256",
                "value": TEST_VC_DIGEST,
            },
            "synthetic_chc_digest": {
                "algorithm": "sha256",
                "value": synthetic_digest,
            },
        });
        vec![
            MetadataEntry {
                key: "trust-mc.typed-chc-obligation.source".to_string(),
                value: "compiler-native-trust-ir-trust-spec-vc".to_string(),
            },
            MetadataEntry {
                key: TRUST_MC_TYPED_CHC_SOURCE_DIGEST_METADATA_KEY.to_string(),
                value: TEST_SOURCE_DIGEST.to_string(),
            },
            MetadataEntry {
                key: TRUST_MC_TYPED_CHC_VC_DIGEST_METADATA_KEY.to_string(),
                value: TEST_VC_DIGEST.to_string(),
            },
            MetadataEntry {
                key: TRUST_MC_TYPED_CHC_SYNTHETIC_DIGEST_METADATA_KEY.to_string(),
                value: synthetic_digest,
            },
            MetadataEntry {
                key: TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY.to_string(),
                value: serde_json::to_string(&binding).expect("binding metadata should serialize"),
            },
        ]
    }

    fn public_typed_chc_binding_metadata(
        synthetic_contract_id: &str,
        public_obligation_id: &str,
        native_obligation_id: &str,
        synthetic_digest: &str,
    ) -> Vec<MetadataEntry> {
        let binding = serde_json::json!({
            "schema_version": TRUST_MC_TYPED_CHC_BINDING_SCHEMA_VERSION,
            "typed_chc_schema": TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION,
            "public_obligation_id": public_obligation_id,
            "native_obligation_id": native_obligation_id,
            "synthetic_contract_id": synthetic_contract_id,
            "source_digest": {
                "algorithm": "sha256",
                "value": TEST_SOURCE_DIGEST,
            },
            "vc_digest": {
                "algorithm": "sha256",
                "value": TEST_VC_DIGEST,
            },
            "synthetic_chc_digest": {
                "algorithm": "sha256",
                "value": synthetic_digest,
            },
        });
        vec![
            MetadataEntry {
                key: TRUST_MC_TYPED_CHC_SOURCE_DIGEST_METADATA_KEY.to_string(),
                value: TEST_SOURCE_DIGEST.to_string(),
            },
            MetadataEntry {
                key: TRUST_MC_TYPED_CHC_VC_DIGEST_METADATA_KEY.to_string(),
                value: TEST_VC_DIGEST.to_string(),
            },
            MetadataEntry {
                key: TRUST_MC_TYPED_CHC_SYNTHETIC_DIGEST_METADATA_KEY.to_string(),
                value: synthetic_digest.to_string(),
            },
            MetadataEntry {
                key: TRUST_SOURCE_DIGEST_METADATA_KEY.to_string(),
                value: TEST_SOURCE_DIGEST.to_string(),
            },
            MetadataEntry {
                key: TRUST_VC_DIGEST_METADATA_KEY.to_string(),
                value: TEST_VC_DIGEST.to_string(),
            },
            MetadataEntry {
                key: TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY.to_string(),
                value: serde_json::to_string(&binding).expect("binding metadata should serialize"),
            },
        ]
    }

    fn set_test_native_trust_ir_identity(
        obligation: &mut TrustObligation,
        native_obligation_id: &str,
    ) {
        // Only (re)write the native-identity metadata when we actually have a
        // native id to install. A non-native id (e.g. a public `vc:...`
        // obligation id, which `push_typed_chc_contract` passes as the obligation's
        // own id) must NOT clobber an identity a caller set deliberately —
        // otherwise pushing a typed-CHC contract onto a manually-identified
        // obligation silently erases its native identity.
        if let Some((request_id, proof_id)) =
            parse_native_typed_chc_obligation_id(native_obligation_id)
        {
            obligation.metadata.retain(|entry| {
                !matches!(
                    entry.key.as_str(),
                    TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY
                        | TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY
                        | TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY
                )
            });
            obligation.metadata.extend([
                MetadataEntry {
                    key: TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY.to_string(),
                    value: "trust-mc".to_string(),
                },
                MetadataEntry {
                    key: TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY.to_string(),
                    value: request_id.to_string(),
                },
                MetadataEntry {
                    key: TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY.to_string(),
                    value: proof_id.to_string(),
                },
            ]);
        }
    }

    fn add_public_typed_chc_binding_metadata(
        obligation: &mut TrustObligation,
        native_obligation_id: &str,
        synthetic_digest: &str,
    ) {
        let synthetic_contract_id = format!("synthetic-contract-{}", obligation.obligation_id);
        obligation.metadata.retain(|entry| {
            !matches!(
                entry.key.as_str(),
                TRUST_MC_TYPED_CHC_SOURCE_DIGEST_METADATA_KEY
                    | TRUST_MC_TYPED_CHC_VC_DIGEST_METADATA_KEY
                    | TRUST_MC_TYPED_CHC_SYNTHETIC_DIGEST_METADATA_KEY
                    | TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY
                    | TRUST_SOURCE_DIGEST_METADATA_KEY
                    | TRUST_VC_DIGEST_METADATA_KEY
            )
        });
        set_test_native_trust_ir_identity(obligation, native_obligation_id);
        obligation.metadata.extend(public_typed_chc_binding_metadata(
            &synthetic_contract_id,
            &obligation.obligation_id,
            native_obligation_id,
            synthetic_digest,
        ));
    }

    fn refresh_typed_chc_binding_metadata(
        contract: &mut TrustContract,
        public_obligation_id: &str,
        native_obligation_id: &str,
    ) {
        let ContractPredicate::MathIr { value, .. } = &contract.predicate else {
            panic!("typed CHC test contract should use MathIr");
        };
        contract.metadata = typed_chc_binding_metadata(
            &contract.contract_id,
            public_obligation_id,
            native_obligation_id,
            value,
        );
    }

    fn push_typed_chc_contract(bundle: &mut TrustContractBundle, contract: TrustContract) {
        let contract_id = contract.contract_id.clone();
        let binding_entries: Vec<_> = contract
            .metadata
            .iter()
            .filter(|entry| {
                matches!(
                    entry.key.as_str(),
                    TRUST_MC_TYPED_CHC_SOURCE_DIGEST_METADATA_KEY
                        | TRUST_MC_TYPED_CHC_VC_DIGEST_METADATA_KEY
                        | TRUST_MC_TYPED_CHC_SYNTHETIC_DIGEST_METADATA_KEY
                        | TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY
                )
            })
            .cloned()
            .collect();
        for obligation in &mut bundle.obligations {
            if obligation.contract_id.as_deref() == Some(contract_id.as_str()) {
                let native_obligation_id = obligation.obligation_id.clone();
                set_test_native_trust_ir_identity(obligation, &native_obligation_id);
                obligation.metadata.extend(binding_entries.clone());
            }
        }
        bundle.contracts.push(contract);
    }

    fn replace_public_typed_chc_binding_from_contract(
        obligation: &mut TrustObligation,
        contract: &TrustContract,
    ) {
        obligation.metadata.retain(|entry| {
            !matches!(
                entry.key.as_str(),
                TRUST_MC_TYPED_CHC_SOURCE_DIGEST_METADATA_KEY
                    | TRUST_MC_TYPED_CHC_VC_DIGEST_METADATA_KEY
                    | TRUST_MC_TYPED_CHC_SYNTHETIC_DIGEST_METADATA_KEY
                    | TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY
            )
        });
        obligation.metadata.extend(
            contract
                .metadata
                .iter()
                .filter(|entry| {
                    matches!(
                        entry.key.as_str(),
                        TRUST_MC_TYPED_CHC_SOURCE_DIGEST_METADATA_KEY
                            | TRUST_MC_TYPED_CHC_VC_DIGEST_METADATA_KEY
                            | TRUST_MC_TYPED_CHC_SYNTHETIC_DIGEST_METADATA_KEY
                            | TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY
                    )
                })
                .cloned(),
        );
    }

    fn compiler_canonical_trust_mc_bundle(
        public_obligation_id: &str,
        native_request_id: u32,
        proof_obligation_id: u32,
    ) -> (TrustContractBundle, String, String, String) {
        compiler_canonical_trust_mc_bundle_with_error_derivation(
            public_obligation_id,
            native_request_id,
            proof_obligation_id,
            false,
        )
    }

    fn compiler_canonical_trust_mc_bundle_with_error_derivation(
        public_obligation_id: &str,
        native_request_id: u32,
        proof_obligation_id: u32,
        derive_error: bool,
    ) -> (TrustContractBundle, String, String, String) {
        let native_obligation_id =
            native_typed_chc_obligation_id(native_request_id, proof_obligation_id);
        let marker_contract_id = format!("contract:trust-mc-typed-chc:{native_obligation_id}");
        let canonical_contract_id =
            format!("contract:trust-mc-typed-chc-public:{public_obligation_id}");
        let mut marker = typed_chc_contract_for_public(
            &marker_contract_id,
            public_obligation_id,
            &native_obligation_id,
            derive_error,
        );
        let ContractPredicate::MathIr { value, .. } = &mut marker.predicate else {
            unreachable!("fixture marker uses exact MathIr")
        };
        value["schema_version"] = serde_json::json!(TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION);
        refresh_typed_chc_binding_metadata(
            &mut marker,
            public_obligation_id,
            &native_obligation_id,
        );

        let mut canonical = marker.clone();
        canonical.contract_id = canonical_contract_id.clone();
        let ContractPredicate::MathIr { value, .. } = &mut canonical.predicate else {
            unreachable!("fixture canonical contract uses exact MathIr")
        };
        value["obligation_id"] = serde_json::json!(public_obligation_id);
        value.as_object_mut().expect("typed CHC payload object").remove("native_metadata");
        canonical.metadata = vec![MetadataEntry {
            key: "trust-trust-mc.typed-chc-obligation.source".to_string(),
            value: "compiler-public-trust-spec-vc".to_string(),
        }];

        let mut public_obligation = obligation_with_contract(
            ObligationKind::ArithmeticSafety,
            public_obligation_id,
            &canonical_contract_id,
        );
        set_test_native_trust_ir_identity(&mut public_obligation, &native_obligation_id);
        public_obligation.metadata.push(MetadataEntry {
            key: TRUST_MC_TYPED_CHC_SYNTHETIC_CONTRACT_METADATA_KEY.to_string(),
            value: marker_contract_id.clone(),
        });
        replace_public_typed_chc_binding_from_contract(&mut public_obligation, &marker);

        let bundle = TrustContractBundle {
            contracts: vec![canonical, marker],
            obligations: vec![public_obligation],
            ..bundle_with(Vec::new())
        };
        (bundle, canonical_contract_id, marker_contract_id, native_obligation_id)
    }

    fn native_typed_chc_obligation_id(native_request_id: u32, proof_obligation_id: u32) -> String {
        format!("trust_ir-native-trust_mc-request-{native_request_id}-proof-{proof_obligation_id}")
    }

    fn parse_native_typed_chc_obligation_id(obligation_id: &str) -> Option<(u32, u32)> {
        let suffix = obligation_id.strip_prefix("trust_ir-native-trust_mc-request-")?;
        let (request, proof) = suffix.split_once("-proof-")?;
        Some((request.parse().ok()?, proof.parse().ok()?))
    }

    fn native_digest(seed: u8) -> trust_mc_core::NativeArtifactDigest {
        trust_mc_core::NativeArtifactDigest::new("sha256", format!("{seed:02x}").repeat(32))
    }

    fn native_typed_chc_metadata(
        native_request_id: u32,
        proof_obligation_id: u32,
        verification_mode: &str,
    ) -> trust_mc_core::NativeTypedChcObligationMetadata {
        trust_mc_core::NativeTypedChcObligationMetadata::new(
            "Trust",
            "rust-mir",
            Some(native_digest(0x11)),
            native_digest(0x22),
            trust_mc_core::NativeArtifactDigest::new("trust_ir-stable-v1", "33".repeat(32)),
            native_request_id,
            verification_mode,
            9,
            vec![proof_obligation_id],
            vec![0],
        )
        .with_compiler_facts(
            trust_mc_core::NativeArtifactDigest::new("trust_ir-stable-v1", "44".repeat(32)),
            trust_mc_core::NativeCompilerFactCounts {
                monomorphizations: 1,
                obligation_sources: 1,
                ..trust_mc_core::NativeCompilerFactCounts::default()
            },
            vec![trust_mc_core::NativeObligationCompilerFacts {
                proof_obligation_id,
                function_id: Some(9),
                span: Some(trust_mc_core::NativeSourceSpanMetadata { file: 0, line: 10, col: 3 }),
                cause: trust_mc_core::NativeObligationCauseMetadata::Translation,
                monomorphization_id: Some(0),
                fact_refs: vec![trust_mc_core::NativeCompilerFactReference::new(
                    trust_mc_core::NativeCompilerFactKind::Monomorphization,
                    0,
                )],
            }],
        )
        .with_replay_metadata(
            trust_mc_core::NativeReplayIdentityMetadata {
                engine: "trust-mc".to_string(),
                invocation: format!("trust-mc native request {native_request_id}"),
                transcript_digest: native_digest(0x55),
            },
            trust_mc_core::NativeReplayContextMetadata {
                atoms: vec![trust_mc_core::NativeReplayAtomMetadata {
                    atom_id: 0,
                    kind: trust_mc_core::NativeReplayAtomKindMetadata::Assertion,
                    formula_schema: "smtlib2".to_string(),
                    payload_digest: trust_mc_core::NativeArtifactDigest::new(
                        "trust_ir-stable-v1",
                        "66".repeat(32),
                    ),
                    proof_obligation_id: Some(proof_obligation_id),
                    assertion_id: Some(7),
                    span: Some(trust_mc_core::NativeSourceSpanMetadata {
                        file: 0,
                        line: 10,
                        col: 3,
                    }),
                }],
                unsupported_modes: Vec::new(),
            },
        )
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn compiler_style_safe_tmir_bundle() -> trust_ir::NativeVerificationBundle {
        compiler_style_tmir_bundle(true)
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn compiler_style_proof_grade_target() -> trust_ir::TargetInfo {
        trust_ir::TargetInfo {
            triple: "x86_64-unknown-linux-gnu".to_string(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        }
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn compiler_style_unsafe_tmir_bundle() -> trust_ir::NativeVerificationBundle {
        compiler_style_tmir_bundle(false)
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn compiler_style_tmir_bundle(assert_safe: bool) -> trust_ir::NativeVerificationBundle {
        use trust_ir::inst::ICmpOp;
        use trust_ir::ty::Ty;
        use trust_ir::{
            NativeAdapterInput, NativeAssertionId, NativeBundleProducer, NativeCompilerFactRef,
            NativeCompilerFacts, NativeMonomorphizationFact, NativeMonomorphizationId,
            NativeObligationCause, NativeObligationSource, NativeReplayAtom, NativeReplayAtomId,
            NativeReplayContext, NativeRequestId, NativeRequestProvenance, NativeToolIdentity,
            NativeVerificationBundle, NativeVerificationRequest, ObligationKind, ProofDigest,
            ProofFormula, ProofId, ProofLineageId, ProofLineageManifest, ProofLineageNode,
            ProofObligation, ProofReplayIdentity, ProofStatus, ProofTransform, ProofTransformStage,
            TrustMcNativeRequest, TrustMcVerificationMode,
        };
        use trust_ir_build::ModuleBuilder;

        let source_digest = ProofDigest::sha256([0x61; 32]);

        let mut mb = ModuleBuilder::new("native_trust_ir_chc_safe_bundle");
        let ft = mb.add_func_type(vec![Ty::I32], vec![]);
        {
            let mut fb = mb.function("tmir_native_checked_branch", ft);
            let entry = fb.create_block();
            let then_block = fb.create_block();
            let exit_block = fb.create_block();

            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let x = fb.add_block_param(entry, Ty::I32);
            let zero = fb.iconst(Ty::I32, 0);
            let is_non_negative = fb.icmp(ICmpOp::Sge, Ty::I32, x, zero);
            fb.condbr(is_non_negative, then_block, vec![is_non_negative], exit_block, vec![]);

            let branch_fact = fb.add_block_param(then_block, Ty::Bool);
            fb.switch_to_block(then_block);
            let assertion = if assert_safe { branch_fact } else { fb.bool_const(false) };
            fb.assert(assertion);
            fb.ret(vec![]);

            fb.switch_to_block(exit_block);
            fb.ret(vec![]);
            fb.build();
        }

        let mut module = mb.build();
        module.target_info = Some(compiler_style_proof_grade_target());
        let trust_mc_function = module
            .functions
            .iter()
            .find(|func| func.name == "tmir_native_checked_branch")
            .expect("fixture includes requested trust_mc function")
            .id;
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::PanicFreedom,
                ProofStatus::Pending,
                "native TrustIr branch assertion is unreachable",
            )
            .with_formula(ProofFormula::smtlib2("tmir_native_checked_branch_safe", "Bool")),
        );
        // NativeVerificationBundle admission binds the declared digest to the
        // canonical digest recomputed from the embedded module. Keep the test
        // fixture honest instead of using the historical placeholder digest.
        let tmir_module_digest = module.stable_digest();

        let mut lineage_node = ProofLineageNode::new(
            ProofLineageId::new(0),
            ProofTransform::new(
                ProofTransformStage::Frontend,
                "rustc-mir-to-trust_ir",
                "Trust",
                "native-request-schema-v1",
            ),
            source_digest,
            tmir_module_digest,
        );
        lineage_node.obligations.push(ProofId::new(0));

        let lineage = ProofLineageManifest {
            schema_version: ProofLineageManifest::SCHEMA_VERSION,
            nodes: vec![lineage_node],
            roots: vec![ProofLineageId::new(0)],
        };

        let mut bundle = NativeVerificationBundle::new(
            NativeBundleProducer::TRust,
            NativeAdapterInput::RustMir { body_digest: source_digest },
            tmir_module_digest,
            module,
            lineage,
        );
        let source_span = trust_ir::SourceSpan { file: 0, line: 18, col: 13 };
        bundle.compiler_facts = NativeCompilerFacts {
            monomorphizations: vec![NativeMonomorphizationFact {
                id: NativeMonomorphizationId::new(0),
                source_item: "native_trust_ir_chc_safe_bundle::tmir_native_checked_branch"
                    .to_owned(),
                symbol: "_RNvNtC6native26tmir_native_checked_branch".to_owned(),
                generic_args: Vec::new(),
                function: Some(trust_mc_function),
                stable_digest: ProofDigest::sha256([0x63; 32]),
            }],
            obligation_sources: vec![NativeObligationSource {
                obligation: ProofId::new(0),
                public_obligation_id: "vc:trust-bmc:safe:0".to_string(),
                function: Some(trust_mc_function),
                span: Some(source_span),
                assertion_id: Some(NativeAssertionId::new(0)),
                cause: NativeObligationCause::Assert,
                monomorphization: Some(NativeMonomorphizationId::new(0)),
                facts: vec![NativeCompilerFactRef::Monomorphization(
                    NativeMonomorphizationId::new(0),
                )],
            }],
            ..NativeCompilerFacts::default()
        };
        bundle.requests.push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
            id: NativeRequestId::new(7),
            mode: TrustMcVerificationMode::Chc,
            function: trust_mc_function,
            obligations: vec![ProofId::new(0)],
            lineage_roots: vec![ProofLineageId::new(0)],
            options: {
                let mut options = trust_ir::TrustMcRequestOptions::default();
                options.chc.emit_horn_clauses = true;
                options
            },
            diagnostics: Default::default(),
            provenance: NativeRequestProvenance::trust_mc(
                NativeToolIdentity::new("trust-mc")
                    .with_version(TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION)
                    .with_revision("native-request-schema-v1"),
            )
            .with_solver(NativeToolIdentity::new("ay-chc").with_version("native-v1"))
            .with_replay(
                ProofReplayIdentity::new(
                    "trust-mc",
                    format!(
                        "trust-mc native typed CHC/PDR test replay --trust-native-admission-contract {}",
                        TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION
                    ),
                )
                .with_transcript_digest(ProofDigest::sha256([0x64; 32])),
            )
            .with_replay_context(
                NativeReplayContext::default()
                    .with_atom(
                        NativeReplayAtom::assumption(
                            NativeReplayAtomId::new(0),
                            ProofFormula::smtlib2("tmir_native_checked_branch_guard", "Bool"),
                        )
                        .with_obligation(ProofId::new(0))
                        .with_span(source_span),
                    )
                    .with_atom(
                        NativeReplayAtom::assertion(
                            NativeReplayAtomId::new(1),
                            ProofFormula::smtlib2("tmir_native_checked_branch_safe", "Bool"),
                        )
                        .with_obligation(ProofId::new(0))
                        .with_assertion_id(NativeAssertionId::new(0))
                        .with_span(source_span),
                    ),
            ),
        }));
        bundle
    }

    // Trust (T3, per-obligation transport delivery): the safe compiler-style
    // bundle plus a second REFUTABLE trust_mc request (id 8, an unguarded
    // `assert(x >= 0)` on an unconstrained i32 param, so `error` is
    // derivable). Request 7 proves exactly like
    // `compiler_style_safe_tmir_bundle`; request 8's solve runs and does not
    // prove, so the producer delivers it in
    // `NativeTrustIrChcPdrBundleEvidence::not_proved` and the T3 dispatch must
    // surface its own reason on the matching public obligation.
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn compiler_style_mixed_tmir_bundle() -> trust_ir::NativeVerificationBundle {
        use trust_ir::inst::ICmpOp;
        use trust_ir::ty::Ty;
        use trust_ir::{
            NativeAdapterInput, NativeAssertionId, NativeBundleProducer, NativeCompilerFactRef,
            NativeCompilerFacts, NativeMonomorphizationFact, NativeMonomorphizationId,
            NativeObligationCause, NativeObligationSource, NativeReplayAtom, NativeReplayAtomId,
            NativeReplayContext, NativeRequestId, NativeRequestProvenance, NativeToolIdentity,
            NativeVerificationBundle, NativeVerificationRequest, ObligationKind, ProofDigest,
            ProofFormula, ProofId, ProofLineageId, ProofLineageManifest, ProofLineageNode,
            ProofObligation, ProofReplayIdentity, ProofStatus, ProofTransform, ProofTransformStage,
            TrustMcNativeRequest, TrustMcVerificationMode,
        };
        use trust_ir_build::ModuleBuilder;

        let source_digest = ProofDigest::sha256([0x61; 32]);

        let mut mb = ModuleBuilder::new("native_trust_ir_chc_mixed_bundle");
        let ft = mb.add_func_type(vec![Ty::I32], vec![]);
        {
            let mut fb = mb.function("tmir_native_checked_branch", ft);
            let entry = fb.create_block();
            let then_block = fb.create_block();
            let exit_block = fb.create_block();

            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let x = fb.add_block_param(entry, Ty::I32);
            let zero = fb.iconst(Ty::I32, 0);
            let is_non_negative = fb.icmp(ICmpOp::Sge, Ty::I32, x, zero);
            fb.condbr(is_non_negative, then_block, vec![is_non_negative], exit_block, vec![]);

            let branch_fact = fb.add_block_param(then_block, Ty::Bool);
            fb.switch_to_block(then_block);
            fb.assert(branch_fact);
            fb.ret(vec![]);

            fb.switch_to_block(exit_block);
            fb.ret(vec![]);
            fb.build();
        }
        {
            let mut fb = mb.function("tmir_native_unchecked_assert", ft);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let x = fb.add_block_param(entry, Ty::I32);
            let zero = fb.iconst(Ty::I32, 0);
            let is_non_negative = fb.icmp(ICmpOp::Sge, Ty::I32, x, zero);
            fb.assert(is_non_negative);
            fb.ret(vec![]);
            fb.build();
        }

        let mut module = mb.build();
        module.target_info = Some(compiler_style_proof_grade_target());
        let safe_function = module
            .functions
            .iter()
            .find(|func| func.name == "tmir_native_checked_branch")
            .expect("fixture includes the safe trust_mc function")
            .id;
        let failing_function = module
            .functions
            .iter()
            .find(|func| func.name == "tmir_native_unchecked_assert")
            .expect("fixture includes the refutable trust_mc function")
            .id;
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::PanicFreedom,
                ProofStatus::Pending,
                "native TrustIr branch assertion is unreachable",
            )
            .with_formula(ProofFormula::smtlib2("tmir_native_checked_branch_safe", "Bool")),
        );
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(1),
                ObligationKind::PanicFreedom,
                ProofStatus::Pending,
                "native TrustIr unguarded assertion never fails",
            )
            .with_formula(ProofFormula::smtlib2("tmir_native_unchecked_assert_safe", "Bool")),
        );
        let tmir_module_digest = module.stable_digest();

        let mut safe_lineage_node = ProofLineageNode::new(
            ProofLineageId::new(0),
            ProofTransform::new(
                ProofTransformStage::Frontend,
                "rustc-mir-to-trust_ir",
                "Trust",
                "native-request-schema-v1",
            ),
            source_digest,
            tmir_module_digest,
        );
        safe_lineage_node.obligations.push(ProofId::new(0));
        let mut failing_lineage_node = ProofLineageNode::new(
            ProofLineageId::new(1),
            ProofTransform::new(
                ProofTransformStage::Frontend,
                "rustc-mir-to-trust_ir",
                "Trust",
                "native-request-schema-v1",
            ),
            source_digest,
            tmir_module_digest,
        );
        failing_lineage_node.obligations.push(ProofId::new(1));

        let lineage = ProofLineageManifest {
            schema_version: ProofLineageManifest::SCHEMA_VERSION,
            nodes: vec![safe_lineage_node, failing_lineage_node],
            roots: vec![ProofLineageId::new(0), ProofLineageId::new(1)],
        };

        let mut bundle = NativeVerificationBundle::new(
            NativeBundleProducer::TRust,
            NativeAdapterInput::RustMir { body_digest: source_digest },
            tmir_module_digest,
            module,
            lineage,
        );
        let safe_span = trust_ir::SourceSpan { file: 0, line: 18, col: 13 };
        let failing_span = trust_ir::SourceSpan { file: 0, line: 42, col: 9 };
        bundle.compiler_facts = NativeCompilerFacts {
            monomorphizations: vec![
                NativeMonomorphizationFact {
                    id: NativeMonomorphizationId::new(0),
                    source_item: "native_trust_ir_chc_mixed_bundle::tmir_native_checked_branch"
                        .to_owned(),
                    symbol: "_RNvNtC5mixed26tmir_native_checked_branch".to_owned(),
                    generic_args: Vec::new(),
                    function: Some(safe_function),
                    stable_digest: ProofDigest::sha256([0x63; 32]),
                },
                NativeMonomorphizationFact {
                    id: NativeMonomorphizationId::new(1),
                    source_item: "native_trust_ir_chc_mixed_bundle::tmir_native_unchecked_assert"
                        .to_owned(),
                    symbol: "_RNvNtC5mixed28tmir_native_unchecked_assert".to_owned(),
                    generic_args: Vec::new(),
                    function: Some(failing_function),
                    stable_digest: ProofDigest::sha256([0x65; 32]),
                },
            ],
            obligation_sources: vec![
                NativeObligationSource {
                    obligation: ProofId::new(0),
                    public_obligation_id: "vc:trust-bmc:mixed-safe:0".to_string(),
                    function: Some(safe_function),
                    span: Some(safe_span),
                    assertion_id: Some(NativeAssertionId::new(0)),
                    cause: NativeObligationCause::Assert,
                    monomorphization: Some(NativeMonomorphizationId::new(0)),
                    facts: vec![NativeCompilerFactRef::Monomorphization(
                        NativeMonomorphizationId::new(0),
                    )],
                },
                NativeObligationSource {
                    obligation: ProofId::new(1),
                    public_obligation_id: "vc:trust-bmc:mixed-failing:1".to_string(),
                    function: Some(failing_function),
                    span: Some(failing_span),
                    assertion_id: Some(NativeAssertionId::new(0)),
                    cause: NativeObligationCause::Assert,
                    monomorphization: Some(NativeMonomorphizationId::new(1)),
                    facts: vec![NativeCompilerFactRef::Monomorphization(
                        NativeMonomorphizationId::new(1),
                    )],
                },
            ],
            ..NativeCompilerFacts::default()
        };
        bundle.requests.push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
            id: NativeRequestId::new(7),
            mode: TrustMcVerificationMode::Chc,
            function: safe_function,
            obligations: vec![ProofId::new(0)],
            lineage_roots: vec![ProofLineageId::new(0)],
            options: {
                let mut options = trust_ir::TrustMcRequestOptions::default();
                options.chc.emit_horn_clauses = true;
                options
            },
            diagnostics: Default::default(),
            provenance: NativeRequestProvenance::trust_mc(
                NativeToolIdentity::new("trust-mc")
                    .with_version(TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION)
                    .with_revision("native-request-schema-v1"),
            )
            .with_solver(NativeToolIdentity::new("ay-chc").with_version("native-v1"))
            .with_replay(
                ProofReplayIdentity::new(
                    "trust-mc",
                    format!(
                        "trust-mc native typed CHC/PDR test replay --trust-native-admission-contract {}",
                        TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION
                    ),
                )
                .with_transcript_digest(ProofDigest::sha256([0x64; 32])),
            )
            .with_replay_context(
                NativeReplayContext::default()
                    .with_atom(
                        NativeReplayAtom::assumption(
                            NativeReplayAtomId::new(0),
                            ProofFormula::smtlib2("tmir_native_checked_branch_guard", "Bool"),
                        )
                        .with_obligation(ProofId::new(0))
                        .with_span(safe_span),
                    )
                    .with_atom(
                        NativeReplayAtom::assertion(
                            NativeReplayAtomId::new(1),
                            ProofFormula::smtlib2("tmir_native_checked_branch_safe", "Bool"),
                        )
                        .with_obligation(ProofId::new(0))
                        .with_assertion_id(NativeAssertionId::new(0))
                        .with_span(safe_span),
                    ),
            ),
        }));
        bundle.requests.push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
            id: NativeRequestId::new(8),
            mode: TrustMcVerificationMode::Chc,
            function: failing_function,
            obligations: vec![ProofId::new(1)],
            lineage_roots: vec![ProofLineageId::new(1)],
            options: {
                let mut options = trust_ir::TrustMcRequestOptions::default();
                options.chc.emit_horn_clauses = true;
                options
            },
            diagnostics: Default::default(),
            provenance: NativeRequestProvenance::trust_mc(
                NativeToolIdentity::new("trust-mc")
                    .with_version(TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION)
                    .with_revision("native-request-schema-v1"),
            )
            .with_solver(NativeToolIdentity::new("ay-chc").with_version("native-v1"))
            .with_replay(
                ProofReplayIdentity::new(
                    "trust-mc",
                    format!(
                        "trust-mc native typed CHC/PDR test replay --trust-native-admission-contract {}",
                        TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION
                    ),
                )
                .with_transcript_digest(ProofDigest::sha256([0x66; 32])),
            )
            .with_replay_context(
                NativeReplayContext::default().with_atom(
                    NativeReplayAtom::assertion(
                        NativeReplayAtomId::new(0),
                        ProofFormula::smtlib2("tmir_native_unchecked_assert_safe", "Bool"),
                    )
                    .with_obligation(ProofId::new(1))
                    .with_assertion_id(NativeAssertionId::new(0))
                    .with_span(failing_span),
                ),
            ),
        }));
        bundle
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    const COMPILER_STYLE_SAFE_NORMALIZED_INPUT_DIGEST: &str =
        "b2657ec88ca9895c83185a51f41dc81b83ea3d82d722e07e6f84cf2c3a86744c";
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    const COMPILER_STYLE_FAILING_NORMALIZED_INPUT_DIGEST: &str =
        "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn compiler_style_source(line: u32, column: u32) -> SourceLocation {
        SourceLocation {
            file: Some("native_trust_ir_chc.rs".to_string()),
            line: Some(line),
            column: Some(column),
            end_line: Some(line),
            end_column: Some(column.saturating_add(1)),
        }
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn compiler_style_public_bundle(
        rows: &[(&str, u32, u32, u32, u32, &str)],
    ) -> TrustContractBundle {
        let mut obligations = Vec::with_capacity(rows.len());
        for &(public_id, request_id, proof_id, line, column, synthetic_digest) in rows {
            let native_id = native_typed_chc_obligation_id(request_id, proof_id);
            let mut public = obligation(ObligationKind::Assertion, public_id);
            public.source = compiler_style_source(line, column);
            add_public_typed_chc_binding_metadata(&mut public, &native_id, synthetic_digest);
            obligations.push(public);
        }
        bundle_with(obligations)
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn compiler_style_safe_public_bundle() -> TrustContractBundle {
        compiler_style_public_bundle(&[(
            "vc:trust-bmc:safe:0",
            7,
            0,
            18,
            13,
            COMPILER_STYLE_SAFE_NORMALIZED_INPUT_DIGEST,
        )])
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn compiler_style_panic_freedom_public_bundle() -> TrustContractBundle {
        let path = "demo::f";
        let public_id = format!(
            "vc:{}:assertion:panic-freedom:0",
            trust_types::canonical_artifact_id_component(path)
        );
        let mut bundle = compiler_style_public_bundle(&[(
            public_id.as_str(),
            7,
            0,
            18,
            13,
            COMPILER_STYLE_SAFE_NORMALIZED_INPUT_DIGEST,
        )]);
        let context = trust_verifier_api::ObligationContext::new(
            trust_verifier_api::ObligationProducer::CompilerMirExtract,
            trust_verifier_api::ObligationOrigin::VerificationCondition {
                vc_kind: "panic_freedom".to_string(),
                vc_index: 0,
                formula_schema: None,
            },
        )
        .with_function(trust_verifier_api::FunctionContext {
            crate_name: "demo".to_string(),
            path: path.to_string(),
        });
        bundle.obligations[0].metadata.extend([
            context.to_metadata_entry().expect("aggregate context serializes"),
            MetadataEntry {
                key: TRUST_MC_PANIC_FREEDOM_OBLIGATION_METADATA_KEY.to_string(),
                value: "enabled".to_string(),
            },
            MetadataEntry { key: "trust.vc.kind".to_string(), value: "panic_freedom".to_string() },
        ]);
        assert!(obligation_is_whole_function_panic_freedom(&bundle, &bundle.obligations[0]));
        bundle
    }

    /// The compiler's own record that this row's typed-CHC lowering produced no
    /// constraint — the shape `annotate_trust_mc_typed_chc_lowering_status`
    /// stamps whenever `trust_mc_typed_chc_lowering_for_obligation` is
    /// unsupported.
    #[cfg(feature = "trust-mc-native-solver")]
    fn mark_typed_chc_lowering_unsupported(obligation: &mut TrustObligation, reason: &str) {
        obligation.metadata.extend([
            MetadataEntry {
                key: TRUST_MC_TYPED_CHC_LOWERING_STATUS_METADATA_KEY.to_string(),
                value: TRUST_MC_TYPED_CHC_LOWERING_STATUS_UNSUPPORTED.to_string(),
            },
            MetadataEntry {
                key: TRUST_MC_TYPED_CHC_UNSUPPORTED_REASON_METADATA_KEY.to_string(),
                value: reason.to_string(),
            },
        ]);
    }

    /// RED (false-PROVE class 1 — laundered `undocumented_unsafe_sig_call`): a
    /// fail-closed unsafe-demand FINDING carries an always-SAT ground violation
    /// that no CHC encoding can express, so the compiler records its lowering as
    /// unsupported and the driver finds no rule deriving the query. "No
    /// counterexample" here means "nothing was asked", and must never be read as
    /// a proof.
    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn credit_witness_rejects_unsafe_demand_finding_on_trivially_safe_route() {
        let mut obligation = obligation(
            ObligationKind::Custom {
                namespace: TRUST_VC_HARDENED_NAMESPACE.to_string(),
                name: "unsafe_operation".to_string(),
            },
            "vc:demo_f:hardened:unsafe_operation:0",
        );
        mark_typed_chc_lowering_unsupported(
            &mut obligation,
            "TrustSpecPredicate lowered to boolean true; no trust-mc CHC error condition was emitted",
        );
        let bundle = bundle_with(vec![obligation]);

        let rejection = trust_mc_chc_credit_witness(
            &bundle,
            &bundle.obligations[0],
            Some(trust_mc_driver::TypedChcPdrRoute::TriviallySafe),
        )
        .expect_err("an unsafe-demand finding contributes no CHC constraint");
        assert!(
            rejection.contains("contributed no typed CHC constraint"),
            "unexpected rejection reason: {rejection}"
        );
    }

    /// RED (false-PROVE class 2 — forged `Proved` for a forced over-budget
    /// allocation): the allocation-budget violation `count >= ceiling` is not a
    /// panic edge, so the trust-mc encoding never carries it. Even when the
    /// function's own panic sites give the solve a non-trivial rule set, the
    /// allocation row has no witness in it.
    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn credit_witness_rejects_unbounded_allocation_row_on_pdr_route() {
        let mut obligation = obligation(
            ObligationKind::Custom {
                namespace: "trust.vc.unbounded_allocation".to_string(),
                name: "unbounded_allocation".to_string(),
            },
            "vc:demo_f:unbounded_allocation:0",
        );
        mark_typed_chc_lowering_unsupported(
            &mut obligation,
            "trust-mc typed CHC lowering is not configured for the allocation budget",
        );
        let bundle = bundle_with(vec![obligation]);

        assert!(
            trust_mc_chc_credit_witness(
                &bundle,
                &bundle.obligations[0],
                Some(trust_mc_driver::TypedChcPdrRoute::PdrProof),
            )
            .is_err(),
            "an allocation-budget row must not ride a rule set that never encoded the budget"
        );
    }

    /// RED (false-PROVE class 3 — the `sr_vec_from_elem_*` families): the row
    /// that a sibling obligation's whole-function proof used to cover. It is an
    /// ordinary arithmetic-safety kind, so nothing about the KIND is suspicious;
    /// the only thing that separates it from a real proof is that the compiler
    /// produced no constraint for it.
    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn credit_witness_rejects_arithmetic_row_that_contributed_no_constraint() {
        let mut obligation =
            obligation(ObligationKind::ArithmeticSafety, "vc:demo_f:arithmetic_safety:3");
        mark_typed_chc_lowering_unsupported(
            &mut obligation,
            "missing `trust.vc.formula.payload` typed formula payload metadata",
        );
        let bundle = bundle_with(vec![obligation]);

        assert!(
            trust_mc_chc_credit_witness(
                &bundle,
                &bundle.obligations[0],
                Some(trust_mc_driver::TypedChcPdrRoute::PdrProof),
            )
            .is_err(),
            "a routable kind is not a witness; the constraint is"
        );
    }

    /// GREEN (the exemption): the counted whole-function panic-freedom aggregate
    /// legitimately has no per-VC predicate, because the obligation IS the query
    /// the structural CHC asks. A trivially-safe rule set is its proof, and
    /// demanding a per-VC constraint here would leave every panic-free function
    /// runtime-checked forever.
    #[cfg(all(feature = "trust-mc-native-solver", feature = "trust-mc-native-trust-ir-bundle"))]
    #[test]
    fn credit_witness_admits_whole_function_panic_freedom_on_trivially_safe_route() {
        let bundle = compiler_style_panic_freedom_public_bundle();

        assert_eq!(
            trust_mc_chc_credit_witness(
                &bundle,
                &bundle.obligations[0],
                Some(trust_mc_driver::TypedChcPdrRoute::TriviallySafe),
            ),
            Ok(TrustMcChcCreditWitness::WholeFunctionStructuralQuery)
        );
    }

    /// GREEN (the ordinary lane): a row whose compiler lowering produced a
    /// constraint, solved on a route that derives the query, keeps its proof.
    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn credit_witness_admits_per_vc_predicate_row_on_pdr_route() {
        let mut obligation =
            obligation(ObligationKind::ArithmeticSafety, "vc:demo_f:arithmetic_safety:0");
        obligation.metadata.push(MetadataEntry {
            key: TRUST_MC_TYPED_CHC_LOWERING_STATUS_METADATA_KEY.to_string(),
            value: "supported".to_string(),
        });
        let bundle = bundle_with(vec![obligation]);

        assert_eq!(
            trust_mc_chc_credit_witness(
                &bundle,
                &bundle.obligations[0],
                Some(trust_mc_driver::TypedChcPdrRoute::PdrProof),
            ),
            Ok(TrustMcChcCreditWitness::PerObligationViolationPredicate)
        );
    }

    /// A trivially-safe rule set says nothing about ANY row but the
    /// whole-function one — including a row whose own lowering succeeded. The
    /// route half of the gate is independent of the compiler-recorded half, so
    /// losing the predicate between admission and solve still fails closed.
    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn credit_witness_rejects_trivially_safe_route_even_with_supported_lowering() {
        let mut obligation =
            obligation(ObligationKind::ArithmeticSafety, "vc:demo_f:arithmetic_safety:1");
        obligation.metadata.push(MetadataEntry {
            key: TRUST_MC_TYPED_CHC_LOWERING_STATUS_METADATA_KEY.to_string(),
            value: "supported".to_string(),
        });
        let bundle = bundle_with(vec![obligation]);

        let rejection = trust_mc_chc_credit_witness(
            &bundle,
            &bundle.obligations[0],
            Some(trust_mc_driver::TypedChcPdrRoute::TriviallySafe),
        )
        .expect_err("no Horn rule derives the query target");
        assert!(
            rejection.contains("trivially-safe route"),
            "unexpected rejection reason: {rejection}"
        );
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn compiler_style_mixed_public_bundle() -> TrustContractBundle {
        compiler_style_public_bundle(&[
            (
                "vc:trust-bmc:mixed-safe:0",
                7,
                0,
                18,
                13,
                COMPILER_STYLE_SAFE_NORMALIZED_INPUT_DIGEST,
            ),
            (
                "vc:trust-bmc:mixed-failing:1",
                8,
                1,
                42,
                9,
                COMPILER_STYLE_FAILING_NORMALIZED_INPUT_DIGEST,
            ),
        ])
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn compiler_style_canonical_public_bundle() -> (TrustContractBundle, String, String) {
        let public_id = "vc:trust-bmc:canonical:0";
        let (mut bundle, canonical_id, marker_id, _) =
            compiler_canonical_trust_mc_bundle(public_id, 7, 0);
        let source = compiler_style_source(18, 13);
        bundle.obligations[0].source = source.clone();
        for contract in &mut bundle.contracts {
            contract.source = source.clone();
            let ContractPredicate::MathIr { value, .. } = &mut contract.predicate else {
                unreachable!("canonical native claim fixture uses MathIr contracts")
            };
            value["function_name"] = serde_json::json!("tmir_native_checked_branch");
            if contract.contract_id == marker_id {
                value["native_metadata"]["function_id"] = serde_json::json!(0);
            }
        }
        let marker_index = bundle
            .contracts
            .iter()
            .position(|contract| contract.contract_id == marker_id)
            .expect("canonical native claim fixture marker");
        refresh_typed_chc_binding_metadata(
            &mut bundle.contracts[marker_index],
            public_id,
            &native_typed_chc_obligation_id(7, 0),
        );
        let marker = bundle.contracts[marker_index].clone();
        replace_public_typed_chc_binding_from_contract(&mut bundle.obligations[0], &marker);
        bundle.obligations[0].metadata.extend([
            MetadataEntry {
                key: TRUST_VC_FORMULA_SCHEMA_METADATA_KEY.to_string(),
                value: "trust.vc.formula.canonical-json.v1".to_string(),
            },
            MetadataEntry {
                key: TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY.to_string(),
                value: r#"{"assertion":"canonical-native-claim"}"#.to_string(),
            },
            MetadataEntry {
                key: TRUST_VC_FORMULA_SORT_METADATA_KEY.to_string(),
                value: "Bool".to_string(),
            },
        ]);
        bundle.validate().expect("canonical native public fixture must validate");
        (bundle, canonical_id, marker_id)
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn trust_ir_sha256_from_hex(value: &str) -> trust_ir::ProofDigest {
        assert_eq!(value.len(), 64, "test SHA-256 digest must have 64 hex digits");
        let mut bytes = [0_u8; 32];
        for (index, pair) in value.as_bytes().chunks_exact(2).enumerate() {
            let high = (pair[0] as char).to_digit(16).expect("hex high digit") as u8;
            let low = (pair[1] as char).to_digit(16).expect("hex low digit") as u8;
            bytes[index] = (high << 4) | low;
        }
        trust_ir::ProofDigest::sha256(bytes)
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn compiler_style_public_formula(public: &TrustObligation) -> trust_ir::ProofFormula {
        if let (Some(schema), Some(payload)) = (
            obligation_metadata_value(public, TRUST_VC_FORMULA_SCHEMA_METADATA_KEY),
            obligation_metadata_value(public, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY),
        ) {
            return trust_ir::ProofFormula {
                schema: schema.to_string(),
                payload: payload.to_string(),
                smtlib: obligation_metadata_value(public, TRUST_VC_FORMULA_SMTLIB_METADATA_KEY)
                    .map(str::to_string),
                sort: obligation_metadata_value(public, TRUST_VC_FORMULA_SORT_METADATA_KEY)
                    .map(str::to_string),
            };
        }
        let source_id = public
            .contract_id
            .as_deref()
            .or(public.proof_item_id.as_deref())
            .unwrap_or(&public.obligation_id);
        let assertion_id = format!("trust-assertion:{source_id}");
        trust_ir::ProofFormula {
            schema: TRUST_IR_OBLIGATION_SOURCE_FORMULA_SCHEMA.to_string(),
            payload: serde_json::json!({
                "source_id": source_id,
                "assertion_id": assertion_id,
                "native_assertion_id": trust_types::stable_u32_id(assertion_id.as_bytes()),
                "span": {
                    "file": public.source.file.clone().unwrap_or_default(),
                    "line_start": public.source.line.unwrap_or_default(),
                    "col_start": public.source.column.unwrap_or_default(),
                    "line_end": public.source.end_line.unwrap_or_else(|| public.source.line.unwrap_or_default()),
                    "col_end": public.source.end_column.unwrap_or_else(|| public.source.column.unwrap_or_default()),
                },
                "public_obligation_id": public.obligation_id,
            })
            .to_string(),
            smtlib: None,
            sort: None,
        }
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn bind_compiler_style_native_bundle_to_public(
        mut native: trust_ir::NativeVerificationBundle,
        public_bundle: &TrustContractBundle,
    ) -> trust_ir::NativeVerificationBundle {
        public_bundle.validate().expect("public fixture must validate");
        for public in &public_bundle.obligations {
            let request_id = canonical_u32_metadata_value(
                obligation_metadata_value(public, TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY)
                    .expect("public fixture request id"),
            )
            .expect("canonical public fixture request id");
            let proof_id = canonical_u32_metadata_value(
                obligation_metadata_value(
                    public,
                    TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
                )
                .expect("public fixture proof id"),
            )
            .expect("canonical public fixture proof id");
            let proof_id = trust_ir::ProofId::new(proof_id);
            let function = native
                .requests
                .iter()
                .find_map(|request| match request {
                    trust_ir::NativeVerificationRequest::TrustMc(request)
                        if request.id.index() == request_id
                            && request.obligations.contains(&proof_id) =>
                    {
                        Some(request.function)
                    }
                    _ => None,
                })
                .expect("native fixture request owns public proof id");
            let file_name = public.source.file.as_deref().expect("public fixture source file");
            let file = native.module.intern_file(file_name.to_string());
            let start_line = public.source.line.unwrap_or_default();
            let start_col = public.source.column.unwrap_or_default();
            let range = trust_ir::ProofObligationSourceRange {
                file,
                start_line,
                start_col,
                end_line: public.source.end_line.unwrap_or(start_line),
                end_col: public.source.end_column.unwrap_or(start_col),
            };
            let span = trust_ir::SourceSpan { file, line: start_line, col: start_col };
            let source_id = public
                .contract_id
                .as_deref()
                .or(public.proof_item_id.as_deref())
                .unwrap_or(&public.obligation_id);
            let assertion_text = format!("trust-assertion:{source_id}");
            let assertion_id = trust_ir::NativeAssertionId::new(trust_types::stable_u32_id(
                assertion_text.as_bytes(),
            ));
            let semantic_digest = trust_ir_sha256_from_hex(
                &public_bundle
                    .canonical_obligation_semantic_digest_sha256(public)
                    .expect("public fixture semantic digest"),
            );
            let formula = compiler_style_public_formula(public);

            let proof = native
                .module
                .proof_obligations
                .iter_mut()
                .find(|proof| proof.id == proof_id)
                .expect("native fixture proof exists");
            proof.function = Some(function);
            proof.source = Some(
                trust_ir::ProofObligationSourceIdentity::new(source_id, assertion_text)
                    .with_range(range)
                    .with_public(trust_ir::PublicObligationIdentity {
                        obligation_id: public.obligation_id.clone(),
                        semantic_digest,
                    }),
            );
            proof.formula = Some(formula.clone());

            let compiler_source = native
                .compiler_facts
                .obligation_sources
                .iter_mut()
                .find(|source| source.obligation == proof_id)
                .expect("native fixture compiler source exists");
            compiler_source.public_obligation_id = public.obligation_id.clone();
            compiler_source.function = Some(function);
            compiler_source.span = Some(span);
            compiler_source.assertion_id = Some(assertion_id);
            compiler_source.cause = trust_ir::NativeObligationCause::Panic;

            let request = native
                .requests
                .iter_mut()
                .find_map(|request| match request {
                    trust_ir::NativeVerificationRequest::TrustMc(request)
                        if request.id.index() == request_id =>
                    {
                        Some(request)
                    }
                    _ => None,
                })
                .expect("native fixture request exists");
            request.provenance.replay_context.atoms = vec![
                trust_ir::NativeReplayAtom::assertion(
                    trust_ir::NativeReplayAtomId::new(0),
                    formula,
                )
                .with_obligation(proof_id)
                .with_assertion_id(assertion_id)
                .with_span(span),
            ];
        }

        let module_digest = native.module.stable_digest();
        native.trust_ir_module_digest = module_digest;
        for node in &mut native.lineage.nodes {
            node.target_module = module_digest;
        }
        native.validate().unwrap_or_else(|errors| {
            panic!("bound compiler-style native fixture must validate: {errors:#?}")
        });
        native
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn remint_native_public_digest_for_test(
        native: &mut trust_ir::NativeVerificationBundle,
        public_bundle: &TrustContractBundle,
        public_index: usize,
    ) {
        let public = &public_bundle.obligations[public_index];
        let proof_id = canonical_u32_metadata_value(
            obligation_metadata_value(
                public,
                TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
            )
            .expect("public fixture proof id"),
        )
        .expect("canonical public fixture proof id");
        let digest = public_bundle
            .canonical_obligation_semantic_digest_sha256(public)
            .expect("mutated public fixture semantic digest");
        native
            .module
            .proof_obligations
            .iter_mut()
            .find(|proof| proof.id.index() == proof_id)
            .and_then(|proof| proof.source.as_mut())
            .and_then(|source| source.public.as_mut())
            .expect("native fixture embedded public identity")
            .semantic_digest = trust_ir_sha256_from_hex(&digest);
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn validate_compiler_style_public_claim_for_test(
        public_bundle: &TrustContractBundle,
        native_bundle: &trust_ir::NativeVerificationBundle,
        public_index: usize,
    ) -> Result<(), String> {
        let context = NativeTrustIrPublicClaimBindingContext::build(
            public_bundle,
            &public_bundle.obligations,
            native_bundle,
        )?;
        validate_native_trust_ir_public_claim_binding(
            public_bundle,
            &public_bundle.obligations[public_index],
            native_bundle,
            &context,
        )
    }

    fn sha256(hex_digit: char) -> TrustMcEvidenceHash {
        TrustMcEvidenceHash::sha256(hex_digit.to_string().repeat(64)).expect("valid sha256")
    }

    fn sha256_hex(hex_digit: char) -> String {
        hex_digit.to_string().repeat(64)
    }

    fn proof_grade_artifact(
        kind: TrustMcFullVerificationArtifactKind,
        label: &str,
        bytes: &[u8],
        proof_binding_id: &str,
        referenced_artifacts: Vec<(TrustMcFullVerificationArtifactKind, TrustMcEvidenceHash)>,
    ) -> TrustMcFullVerificationArtifact {
        let digest = TrustMcEvidenceHash::sha256(stable_sha256_hex(bytes))
            .expect("test proof artifact bytes have a canonical SHA-256 digest");
        TrustMcFullVerificationArtifact {
            kind,
            label: label.to_string(),
            digest: Some(digest),
            materialized_bytes: Some(bytes.to_vec()),
            proof_binding_id: Some(proof_binding_id.to_string()),
            referenced_artifacts,
        }
    }

    fn proof_grade_normalized_input_bytes(obligation_id: &str) -> Vec<u8> {
        format!("normalized native CHC/PDR input for {obligation_id}").into_bytes()
    }

    fn proof_grade_normalized_input_digest(obligation_id: &str) -> String {
        stable_sha256_hex(&proof_grade_normalized_input_bytes(obligation_id))
    }

    #[cfg(feature = "trust-mc-native-solver")]
    fn native_typed_normalized_input_bytes(obligation_id: &str) -> Vec<u8> {
        format!("normalized input for {obligation_id}").into_bytes()
    }

    #[cfg(feature = "trust-mc-native-solver")]
    fn native_typed_normalized_input_digest(obligation_id: &str) -> String {
        stable_sha256_hex(&native_typed_normalized_input_bytes(obligation_id))
    }

    fn proof_grade_chc_pdr(
        kind: TrustMcChcPdrProofKind,
        obligation_id: &str,
    ) -> TrustMcChcPdrProofEvidence {
        let (native_request_id, proof_obligation_id) =
            parse_native_typed_chc_obligation_id(obligation_id)
                .expect("proof-grade fixture requires native TrustIr obligation id");
        let proof_binding_id = format!("trust_mc-proof-set-sha256:{}", "f".repeat(64));
        let input_bytes = proof_grade_normalized_input_bytes(obligation_id);
        let input = proof_grade_artifact(
            TrustMcFullVerificationArtifactKind::NormalizedInput,
            "artifact://trust-mc/normalized-input.chc",
            &input_bytes,
            &proof_binding_id,
            Vec::new(),
        );
        let input_hash = input.digest.clone().expect("normalized input digest");
        let transcript = proof_grade_artifact(
            TrustMcFullVerificationArtifactKind::SolverTranscript,
            "artifact://trust-mc/solver-transcript.smt2",
            b"exact native CHC/PDR solver transcript",
            &proof_binding_id,
            vec![(TrustMcFullVerificationArtifactKind::NormalizedInput, input_hash.clone())],
        );
        let transcript_hash = transcript.digest.clone().expect("solver transcript digest");
        // The invariant model is supplemental metadata, not part of the
        // transcript→replay→check proof DAG. Keep it hash-addressed but
        // unmaterialized so it cannot be mistaken for an unreferenced proof
        // artifact.
        let invariant = TrustMcFullVerificationArtifact::new(
            TrustMcFullVerificationArtifactKind::PdrInvariantModel,
            "artifact://trust-mc/pdr-invariant.json",
        )
        .with_digest(
            TrustMcEvidenceHash::sha256(stable_sha256_hex(
                b"native CHC/PDR supplemental invariant model",
            ))
            .expect("supplemental invariant digest is canonical"),
        );
        let replay = proof_grade_artifact(
            TrustMcFullVerificationArtifactKind::ReplayLog,
            "artifact://trust-mc/replay-log.json",
            b"exact native CHC/PDR replay log",
            &proof_binding_id,
            vec![(TrustMcFullVerificationArtifactKind::SolverTranscript, transcript_hash.clone())],
        );
        let replay_hash = replay.digest.clone().expect("replay log digest");
        let checked_report = proof_grade_artifact(
            TrustMcFullVerificationArtifactKind::CheckedProofReport,
            "artifact://trust-mc/checked-proof-report.json",
            b"exact native CHC/PDR checked-proof report",
            &proof_binding_id,
            vec![(TrustMcFullVerificationArtifactKind::ReplayLog, replay_hash.clone())],
        );
        let checked_report_hash =
            checked_report.digest.clone().expect("checked proof report digest");
        let metadata = TrustMcFullProofEvidenceMetadata::default()
            .with_producer("trust-mc-core")
            .with_normalized_input_hash(input_hash.clone())
            .with_transcript_hash(transcript_hash.clone())
            .with_replay_log_hash(replay_hash.clone())
            .with_checked_report_hash(checked_report_hash.clone())
            .with_replay_check_status(TrustMcProofReplayCheckStatus::accepted());
        let stats = TrustMcChcPdrStats { relation_count: 2, clause_count: 3 };
        let proof = match kind {
            TrustMcChcPdrProofKind::ChcValidity => TrustMcChcPdrProofEvidence::chc_validity(stats),
            TrustMcChcPdrProofKind::PdrInvariant => {
                TrustMcChcPdrProofEvidence::pdr_invariant(stats, 1)
            }
        };

        proof
            .with_metadata(metadata)
            .with_native_metadata(TrustMcNativeTypedChcObligationMetadata::from_core(
                native_typed_chc_metadata(
                    native_request_id,
                    proof_obligation_id,
                    match kind {
                        TrustMcChcPdrProofKind::ChcValidity => "chc",
                        TrustMcChcPdrProofKind::PdrInvariant => "pdr",
                    },
                ),
            ))
            .with_artifact(input)
            .with_artifact(transcript)
            .with_artifact(invariant)
            .with_artifact(replay)
            .with_artifact(checked_report)
    }

    #[cfg(feature = "trust-mc-native-solver")]
    fn native_typed_transport(
        obligation_id: &str,
        proof_strength: TrustMcNativeTypedProofStrength,
    ) -> TrustMcNativeTypedChcPdrProofTransport {
        let (request_id, proof_id) =
            parse_native_typed_chc_obligation_id(obligation_id).expect("native TrustIr id");
        let binding = format!("trust_mc-proof-set-sha256:{}", "f".repeat(64));
        let normalized_bytes = native_typed_normalized_input_bytes(obligation_id);
        let normalized_digest = trust_mc_core::EvidenceHash::sha256_bytes(&normalized_bytes);
        let normalized = native_typed_artifact_json(
            trust_mc_core::FullVerificationArtifactKind::NormalizedInput,
            format!("trust-mc://typed-chc/{obligation_id}/normalized-input.json"),
            &normalized_bytes,
            &binding,
            Vec::new(),
        );
        let transcript_bytes = b"exact native typed CHC/PDR solver transcript";
        let transcript_digest = trust_mc_core::EvidenceHash::sha256_bytes(transcript_bytes);
        let transcript = native_typed_artifact_json(
            trust_mc_core::FullVerificationArtifactKind::SolverTranscript,
            format!("trust-mc://typed-chc/{obligation_id}/solver-transcript.json"),
            transcript_bytes,
            &binding,
            vec![(
                trust_mc_core::FullVerificationArtifactKind::NormalizedInput,
                normalized_digest.clone(),
            )],
        );
        let invariant =
            (proof_strength == TrustMcNativeTypedProofStrength::PdrInvariant).then(|| {
                native_typed_artifact_json(
                    trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel,
                    format!("trust-mc://typed-chc/{obligation_id}/pdr-invariant-model.json"),
                    b"exact native typed CHC/PDR invariant model",
                    &binding,
                    vec![(
                        trust_mc_core::FullVerificationArtifactKind::NormalizedInput,
                        normalized_digest,
                    )],
                )
            });
        let invariant_digest = invariant.as_ref().map(|artifact| {
            serde_json::from_value::<TrustMcNativeTypedProofArtifactRef>(artifact.clone())
                .expect("invariant fixture artifact deserializes")
                .digest
                .expect("invariant fixture digest")
        });
        let replay_bytes = b"exact native typed CHC/PDR replay log";
        let replay_digest = trust_mc_core::EvidenceHash::sha256_bytes(replay_bytes);
        let mut replay_references = vec![(
            trust_mc_core::FullVerificationArtifactKind::SolverTranscript,
            transcript_digest.clone(),
        )];
        if let Some(invariant_digest) = invariant_digest.as_ref() {
            replay_references.push((
                trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel,
                invariant_digest.clone(),
            ));
        }
        let replay = native_typed_artifact_json(
            trust_mc_core::FullVerificationArtifactKind::ReplayLog,
            format!("trust-mc://typed-chc/{obligation_id}/replay-log.json"),
            replay_bytes,
            &binding,
            replay_references,
        );
        let mut check_references = vec![(
            trust_mc_core::FullVerificationArtifactKind::SolverTranscript,
            transcript_digest,
        )];
        if let Some(invariant_digest) = invariant_digest {
            check_references.push((
                trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel,
                invariant_digest,
            ));
        }
        check_references
            .push((trust_mc_core::FullVerificationArtifactKind::ReplayLog, replay_digest));
        let check = native_typed_artifact_json(
            trust_mc_core::FullVerificationArtifactKind::CheckedProofReport,
            format!("trust-mc://typed-chc/{obligation_id}/checked-proof-report.json"),
            b"exact native typed CHC/PDR proof-check report",
            &binding,
            check_references,
        );
        let backend = if proof_strength == TrustMcNativeTypedProofStrength::PdrInvariant {
            "trust_mc::typed-chc-pdr::pdr::pdr-proof"
        } else {
            "trust_mc::typed-chc-pdr::chc::trivial-safe"
        };
        let mut response_artifacts =
            vec![normalized, transcript.clone(), replay.clone(), check.clone()];
        if let Some(invariant) = invariant {
            response_artifacts.push(invariant);
        }
        serde_json::from_value(serde_json::json!({
            "schema_version": TrustMcNativeTypedChcPdrProofTransport::SCHEMA_VERSION,
            "suite": "Trust",
            "backend": backend,
            "request_id": request_id,
            "proof_id": proof_id,
            "native_id": obligation_id,
            "proof_status": TrustMcNativeTypedProofStatus::Proved,
            "proof_strength": proof_strength,
            "replay_check_status": trust_mc_core::ProofReplayCheckStatus::accepted(),
            "solver_artifacts": [transcript.clone()],
            "replay_artifacts": [replay.clone()],
            "check_artifacts": [check.clone()],
            "response_artifacts": response_artifacts,
            "diagnostics": ["transport exported from native typed runner"],
        }))
        .expect("native typed transport fixture should deserialize")
    }

    #[cfg(feature = "trust-mc-native-solver")]
    fn native_typed_artifact_json(
        kind: trust_mc_core::FullVerificationArtifactKind,
        uri: String,
        bytes: &[u8],
        proof_binding_id: &str,
        referenced_artifacts: Vec<(
            trust_mc_core::FullVerificationArtifactKind,
            trust_mc_core::EvidenceHash,
        )>,
    ) -> serde_json::Value {
        let digest = trust_mc_core::EvidenceHash::sha256_bytes(bytes);
        serde_json::json!({
            "kind": kind,
            "uri": uri,
            "digest": digest,
            "byte_len": bytes.len(),
            "materialization": {
                "bytes": bytes,
                "byte_len": bytes.len(),
                "proof_binding_id": proof_binding_id,
                "referenced_artifacts": referenced_artifacts
                    .into_iter()
                    .map(|(kind, digest)| serde_json::json!({
                        "kind": kind,
                        "digest": digest,
                    }))
                    .collect::<Vec<_>>(),
            },
        })
    }

    #[cfg(feature = "trust-mc-native-solver")]
    fn core_artifact_from_bytes(
        kind: trust_mc_core::FullVerificationArtifactKind,
        label: &str,
        bytes: &[u8],
    ) -> trust_mc_core::FullVerificationArtifact {
        trust_mc_core::FullVerificationArtifact::from_bytes(kind, label, bytes)
    }

    fn core_proof_grade_verdict(
        proof_kind: trust_mc_core::ChcPdrProofKind,
        obligation_id: &str,
    ) -> trust_mc_core::FullVerificationVerdict {
        let obligation = trust_mc_core::MirDerivedChcPdrObligation::new(
            obligation_id,
            trust_mc_core::MirObligationKind::ArithmeticSafety,
            "(declare-rel entry ())\n(rule entry)\n(query entry)\n",
        );
        let stats = trust_mc_core::ChcPdrStats { relation_count: 1, clause_count: 1 };
        // trust-mc 1430c4733: `proof_grade_from_bytes` is a compatibility
        // constructor whose artifacts intentionally stay non-proof-grade; a
        // proof-grade verdict must attest the transcript/replay/check linkage.
        let proof = match proof_kind {
            trust_mc_core::ChcPdrProofKind::ChcValidity => {
                trust_mc_core::ChcPdrProofEvidence::try_chc_validity_candidate_from_linked_bytes(
                    obligation,
                    stats,
                    ("ay://chc-pdr/proof-metadata.json", b"solver transcript"),
                    ("trust-mc://chc-pdr/replay-log.json", b"replay log"),
                    ("trust-mc://chc-pdr/checked-proof-report.json", b"checked report"),
                )
            }
            trust_mc_core::ChcPdrProofKind::PdrInvariant => {
                trust_mc_core::ChcPdrProofEvidence::try_pdr_invariant_candidate_from_linked_bytes(
                    obligation,
                    stats,
                    1,
                    ("ay://chc-pdr/proof-metadata.json", b"solver transcript"),
                    ("trust-mc://chc-pdr/replay-log.json", b"replay log"),
                    ("trust-mc://chc-pdr/checked-proof-report.json", b"checked report"),
                    ("trust-mc://chc-pdr/invariant-model.json", b"invariant model"),
                )
            }
        }
        .expect("linked candidate fixture must be non-empty and bounded");
        trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
        }
    }

    fn run_result_for(
        adapter: &TrustMcVerifierApiAdapter,
        bundle: &TrustContractBundle,
        evidence: ObligationEvidence,
    ) -> VerificationRunResult {
        let context = VerifierExecutionContext::new("trust-mc-native-evidence");
        VerificationRunResult::from_evidence(
            context.snapshot(),
            bundle,
            adapter.manifest().clone(),
            &bundle.obligations,
            vec![evidence],
        )
    }

    #[test]
    fn manifest_owns_expected_obligation_lanes() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let owned = trust_mc_owned_obligation_kinds();

        for kind in [
            ObligationKind::Precondition,
            ObligationKind::Postcondition,
            ObligationKind::Assertion,
            ObligationKind::ArithmeticSafety,
            ObligationKind::Invariant,
            ObligationKind::Protocol,
        ] {
            assert!(owned.contains(&kind), "owned-kind inventory omitted the actual {kind:?} lane");
            assert!(
                adapter
                    .manifest()
                    .capabilities
                    .iter()
                    .any(|capability| capability.obligation_kind == kind),
                "manifest omitted the actual {kind:?} lane"
            );
        }

        assert_eq!(adapter.manifest().capabilities.len(), owned.len());
        for kind in owned {
            let support = adapter.supports(&obligation(kind, "owned"));
            assert!(support.is_supported());
        }

        let unsupported = adapter.supports(&obligation(ObligationKind::Ownership, "ownership"));
        assert!(matches!(unsupported, SupportLevel::Unsupported { .. }));
        let unsupported = adapter.supports(&obligation(ObligationKind::MemorySafety, "memory"));
        assert!(matches!(unsupported, SupportLevel::Unsupported { .. }));
        let unsupported = adapter.supports(&obligation(ObligationKind::TemporalSafety, "temporal"));
        assert!(matches!(unsupported, SupportLevel::Unsupported { .. }));
    }

    #[test]
    fn manifest_wires_trust_build_to_native_trust_ir_bundle_runner() {
        let manifest = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml"),
        )
        .expect("trust-bmc manifest should be readable");
        let manifest: toml::Value =
            toml::from_str(&manifest).expect("trust-bmc manifest should parse");
        let features = manifest["features"].as_table().expect("features should be a table");
        let trust_build =
            features["trust-build"].as_array().expect("trust-build feature should be an array");
        let native_bundle = features["trust-mc-native-trust-ir-bundle"]
            .as_array()
            .expect("trust-mc-native-trust-ir-bundle feature should be an array");
        let native_driver = features["trust-mc-native-driver"]
            .as_array()
            .expect("trust-mc-native-driver feature should be an array");
        let native_solver = features["trust-mc-native-solver"]
            .as_array()
            .expect("trust-mc-native-solver feature should be an array");
        let dependencies =
            manifest["dependencies"].as_table().expect("dependencies should be a table");
        let trust_mc_driver = dependencies["trust-mc-driver"]
            .as_table()
            .expect("trust-mc-driver should be a dependency table");

        let trust_build_edges: Vec<_> = trust_build
            .iter()
            .map(|value| value.as_str().expect("feature edge should be a string"))
            .collect();
        let native_bundle_edges: Vec<_> = native_bundle
            .iter()
            .map(|value| value.as_str().expect("feature edge should be a string"))
            .collect();
        let native_driver_edges: Vec<_> = native_driver
            .iter()
            .map(|value| value.as_str().expect("feature edge should be a string"))
            .collect();
        let native_solver_edges: Vec<_> = native_solver
            .iter()
            .map(|value| value.as_str().expect("feature edge should be a string"))
            .collect();

        assert!(
            trust_build_edges.contains(&"trust-mc-native-trust-ir-bundle"),
            "trust-bmc/trust-build must enable the native TrustIr bundle adapter"
        );
        assert!(
            native_bundle_edges.contains(&"trust-mc-driver/native-trust-ir-bundle"),
            "trust-bmc/trust-mc-native-trust-ir-bundle must enable trust_mc driver's bundle runner"
        );
        assert_eq!(
            trust_mc_driver.get("optional").and_then(toml::Value::as_bool),
            Some(true),
            "trust-mc-driver must stay optional so default trust-bmc checks avoid native solver fanout"
        );
        assert!(
            native_driver_edges.contains(&"dep:trust-mc-driver"),
            "trust-mc-native-driver must be the narrow edge that enables trust-mc-driver"
        );
        assert!(
            native_solver_edges.contains(&"trust-mc-native-driver"),
            "trust-mc-native-solver must opt into the native driver before enabling solver features"
        );
        assert!(
            native_solver_edges.contains(&"trust-mc-driver/native-typed-chc-pdr"),
            "trust-mc-native-solver must enable trust-mc-driver/native-typed-chc-pdr"
        );
    }

    #[test]
    fn trust_types_manifest_keeps_ay_bridge_optional() {
        let trust_types_manifest = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../trust-types/Cargo.toml"),
        )
        .expect("trust-types manifest should be readable");
        let manifest: toml::Value =
            toml::from_str(&trust_types_manifest).expect("trust-types manifest should parse");
        let features = manifest["features"].as_table().expect("features should be a table");
        let ay_bridge =
            features["ay-bridge"].as_array().expect("ay-bridge feature should be an array");
        let dependencies =
            manifest["dependencies"].as_table().expect("dependencies should be a table");
        let ay_bindings = dependencies["ay-bindings"]
            .as_table()
            .expect("ay-bindings should be a dependency table");
        let ay_bridge_edges: Vec<_> = ay_bridge
            .iter()
            .map(|value| value.as_str().expect("feature edge should be a string"))
            .collect();

        assert_eq!(
            ay_bindings.get("optional").and_then(toml::Value::as_bool),
            Some(true),
            "trust-types ay-bindings must stay optional for default trust-types fanout"
        );
        assert!(
            ay_bridge_edges.contains(&"dep:ay-bindings"),
            "trust-types/ay-bridge must be the only feature edge that enables ay-bindings"
        );
    }

    #[test]
    fn manifest_and_support_cover_future_hardened_custom_lanes() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let future = ObligationKind::Custom {
            namespace: TRUST_VC_HARDENED_NAMESPACE.to_string(),
            name: "future_kernel_object_identity".to_string(),
        };
        let wildcard = ObligationKind::Custom {
            namespace: TRUST_VC_HARDENED_NAMESPACE.to_string(),
            name: TRUST_VC_HARDENED_WILDCARD.to_string(),
        };

        assert!(adapter.supports(&obligation(future, "future-hardened")).is_supported());
        assert!(adapter.manifest().capabilities.iter().any(|capability| {
            capability.obligation_kind == wildcard && capability.support.is_supported()
        }));
    }

    #[test]
    fn e4_e5_are_dynamic_trust_mc_lanes_only_with_a_valid_typed_vc_formula() {
        let adapter = TrustMcVerifierApiAdapter::default();
        for kind in [ObligationKind::LoopInvariant, ObligationKind::Termination] {
            let bare = obligation(kind.clone(), "bare-e4-e5");
            assert!(
                !adapter.supports(&bare).is_supported(),
                "a payload-less authored claim stays outside trust-mc"
            );

            let mut typed = obligation(kind, "typed-e4-e5");
            add_typed_body_aware_vc_formula(&mut typed);
            assert!(adapter.supports(&typed).is_supported());
            assert_eq!(
                trust_mc_mir_kind_from_obligation(&typed.kind),
                Some(trust_mc_core::MirObligationKind::Assertion),
            );
        }

        // Match the compiler's depth-tolerant typed-formula lane. A legitimate
        // recursive predicate can exceed serde_json's default recursion limit;
        // that must not make native and feature-gated ownership disagree.
        let mut root = trust_verifier_api::TrustSpecExpr::bool_literal(false);
        // Each typed expression node contributes multiple JSON object levels,
        // so 96 semantic nodes exceed serde_json's default recursion bound
        // while remaining below the public predicate validator's explicit
        // semantic-depth limit.
        for _ in 0..96 {
            root = trust_verifier_api::TrustSpecExpr::unary(
                trust_verifier_api::TrustSpecUnaryOp::Not,
                root,
            );
        }
        let encoded =
            serde_json::to_string(&trust_verifier_api::TrustSpecPredicate::new(root, Vec::new()))
                .expect("deep predicate should serialize");
        assert!(
            serde_json::from_str::<trust_verifier_api::TrustSpecPredicate>(&encoded).is_err(),
            "fixture must exceed serde_json's default recursion limit"
        );
        let mut deep = obligation(ObligationKind::LoopInvariant, "deep-e4");
        add_typed_body_aware_vc_formula(&mut deep);
        deep.metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
            .expect("typed formula payload")
            .value = encoded;
        assert!(adapter.supports(&deep).is_supported());

        let mut over_limit = trust_verifier_api::TrustSpecExpr::bool_literal(false);
        for _ in 0..=trust_verifier_api::MAX_CONTRACT_PREDICATE_JSON_DEPTH {
            over_limit = trust_verifier_api::TrustSpecExpr::unary(
                trust_verifier_api::TrustSpecUnaryOp::Not,
                over_limit,
            );
        }
        let mut over_limit_obligation = obligation(ObligationKind::LoopInvariant, "over-limit-e4");
        add_typed_body_aware_vc_formula(&mut over_limit_obligation);
        over_limit_obligation
            .metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
            .expect("typed formula payload")
            .value = serde_json::to_string(&trust_verifier_api::TrustSpecPredicate::new(
            over_limit,
            Vec::new(),
        ))
        .expect("over-limit fixture serializes");
        assert!(
            !adapter.supports(&over_limit_obligation).is_supported(),
            "deep parsing must not widen the public semantic-depth limit"
        );
    }

    #[test]
    fn malformed_or_ambiguous_e4_e5_formula_metadata_cannot_acquire_trust_mc_authority() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let mut malformed = obligation(ObligationKind::LoopInvariant, "forged-e4");
        add_typed_body_aware_vc_formula(&mut malformed);
        let payload = malformed
            .metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
            .expect("payload metadata");
        payload.value = "{}".to_string();
        assert!(!adapter.supports(&malformed).is_supported());

        let mut structurally_invalid =
            obligation(ObligationKind::LoopInvariant, "invalid-typed-e4");
        add_typed_body_aware_vc_formula(&mut structurally_invalid);
        let undeclared = trust_verifier_api::TrustSpecPredicate::new(
            trust_verifier_api::TrustSpecExpr::variable(
                "missing",
                trust_verifier_api::TrustSpecSort::Bool,
            ),
            Vec::new(),
        );
        structurally_invalid
            .metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
            .expect("payload metadata")
            .value = serde_json::to_string(&undeclared).expect("invalid fixture serializes");
        assert!(
            !adapter.supports(&structurally_invalid).is_supported(),
            "schema/root checks cannot grant E4 authority without full predicate validation"
        );

        let mut ambiguous = obligation(ObligationKind::Termination, "forged-e5");
        add_typed_body_aware_vc_formula(&mut ambiguous);
        ambiguous.metadata.push(MetadataEntry {
            key: TRUST_VC_FORMULA_SCHEMA_METADATA_KEY.to_string(),
            value: trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
        });
        assert!(!adapter.supports(&ambiguous).is_supported());

        let mut wrong_origin = obligation(ObligationKind::LoopInvariant, "wrong-origin-e4");
        add_typed_body_aware_vc_formula(&mut wrong_origin);
        let context = wrong_origin
            .metadata
            .iter_mut()
            .find(|entry| entry.key == trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY)
            .expect("obligation context metadata");
        *context = trust_verifier_api::ObligationContext::new(
            trust_verifier_api::ObligationProducer::CompilerMirExtract,
            trust_verifier_api::ObligationOrigin::UnsupportedContract {
                contract_index: 0,
                compiler_contract_kind: "loop_invariant".to_string(),
                reason: "unsupported source marker".to_string(),
            },
        )
        .to_metadata_entry()
        .expect("wrong-origin context should serialize");
        assert!(!adapter.supports(&wrong_origin).is_supported());

        let mut duplicate_context = obligation(ObligationKind::Termination, "duplicate-context-e5");
        add_typed_body_aware_vc_formula(&mut duplicate_context);
        let duplicate = duplicate_context
            .metadata
            .iter()
            .find(|entry| entry.key == trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY)
            .expect("obligation context metadata")
            .clone();
        duplicate_context.metadata.push(duplicate);
        assert!(!adapter.supports(&duplicate_context).is_supported());
    }

    #[test]
    fn typed_chc_decoder_supports_only_int_indexed_scalar_array_select() {
        let array_sort = TrustMcTypedChcSortInput::Array {
            index: Box::new(TrustMcTypedChcSortInput::Int),
            element: Box::new(TrustMcTypedChcSortInput::Int),
        };
        let ay_array_sort = array_sort.to_trust_mc_sort().expect("bounded array sort lowers");
        assert_eq!(ay_array_sort, Sort::array(Sort::int(), Sort::int()));

        let mut vars = BTreeMap::new();
        vars.insert("xs".to_string(), ay_array_sort);
        let select = TrustMcTypedChcExprInput::Select {
            array: Box::new(TrustMcTypedChcExprInput::Var {
                name: "xs".to_string(),
                sort: array_sort,
            }),
            index: Box::new(TrustMcTypedChcExprInput::IntConst { value: serde_json::json!("0") }),
        };
        assert_eq!(select.to_trust_mc_expr(&vars).expect("Select lowers").sort(), &Sort::int());

        let wrong_index = TrustMcTypedChcExprInput::Select {
            array: Box::new(TrustMcTypedChcExprInput::Var {
                name: "xs".to_string(),
                sort: TrustMcTypedChcSortInput::Array {
                    index: Box::new(TrustMcTypedChcSortInput::Int),
                    element: Box::new(TrustMcTypedChcSortInput::Int),
                },
            }),
            index: Box::new(TrustMcTypedChcExprInput::BoolConst { value: false }),
        };
        assert!(
            wrong_index
                .to_trust_mc_expr(&vars)
                .expect_err("wrong Select index sort must fail")
                .contains("select sort error")
        );

        for invalid in [
            TrustMcTypedChcSortInput::Array {
                index: Box::new(TrustMcTypedChcSortInput::Bool),
                element: Box::new(TrustMcTypedChcSortInput::Int),
            },
            TrustMcTypedChcSortInput::Array {
                index: Box::new(TrustMcTypedChcSortInput::Int),
                element: Box::new(TrustMcTypedChcSortInput::Real),
            },
            TrustMcTypedChcSortInput::Array {
                index: Box::new(TrustMcTypedChcSortInput::Int),
                element: Box::new(TrustMcTypedChcSortInput::Array {
                    index: Box::new(TrustMcTypedChcSortInput::Int),
                    element: Box::new(TrustMcTypedChcSortInput::Int),
                }),
            },
        ] {
            assert!(invalid.to_trust_mc_sort().is_err());
        }
    }

    #[test]
    fn hardened_custom_obligation_maps_to_trust_mc_assertion_kind() {
        let hardened = ObligationKind::Custom {
            namespace: TRUST_VC_HARDENED_NAMESPACE.to_string(),
            name: "ffi_boundary".to_string(),
        };
        let future = ObligationKind::Custom {
            namespace: TRUST_VC_HARDENED_NAMESPACE.to_string(),
            name: "future_kernel_object_identity".to_string(),
        };

        assert_eq!(
            trust_mc_mir_kind_from_obligation(&hardened),
            Some(trust_mc_core::MirObligationKind::Assertion)
        );
        assert_eq!(
            trust_mc_mir_kind_from_obligation(&future),
            Some(trust_mc_core::MirObligationKind::Assertion)
        );
        assert_eq!(
            trust_mc_mir_kind_from_obligation(&ObligationKind::Custom {
                namespace: "trust.vc.other".to_string(),
                name: "ffi_boundary".to_string(),
            }),
            None
        );
    }

    // Trust (P1.2 precedent, extended to preconditions): the trust-mc adapter
    // owns router-dispatched body-aware contract VCs for BOTH kinds, and both
    // ride the Assertion reachability lane (`¬cond ∧ body_defs` is an
    // assertion-unreachability goal). Without the ownership + kind mapping the
    // adapter rejected the routed precondition VC as "does not own
    // Precondition obligations" and the e2e row stayed Unknown.
    #[test]
    fn body_aware_contract_vc_kinds_are_owned_and_map_to_assertion_lane() {
        let adapter = TrustMcVerifierApiAdapter::default();
        for kind in [ObligationKind::Precondition, ObligationKind::Postcondition] {
            assert!(is_trust_mc_owned_obligation_kind(&kind), "{kind:?} must be trust-mc owned");
            assert!(
                adapter.supports(&obligation(kind.clone(), "contract-vc")).is_supported(),
                "{kind:?} must be supported by the trust-mc adapter"
            );
            assert_eq!(
                trust_mc_mir_kind_from_obligation(&kind),
                Some(trust_mc_core::MirObligationKind::Assertion),
                "{kind:?} must ride the Assertion reachability lane"
            );
        }
    }

    #[test]
    fn missing_native_bundle_lowering_returns_unsupported_evidence() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let bundle = bundle_with(vec![obligation(ObligationKind::Assertion, "assertion-1")]);

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert_eq!(evidence[0].proof_strength, None);
        assert_eq!(evidence[0].publication.publication_plan_hash.as_deref(), Some("sha256:plan"));
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("typed-input-required"))
        );
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("FullProofEvidence::ChcPdr"))
        );
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("ChcPdrProofKind::PdrInvariant"))
        );
    }

    #[test]
    #[cfg(not(feature = "trust-mc-native-solver"))]
    fn direct_typed_chc_contract_input_fails_closed_without_native_proof_transport() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        );
        let obligation_id = native_typed_chc_obligation_id(11, 7);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::Assertion,
            &obligation_id,
            "contract-typed",
        )]);
        push_typed_chc_contract(
            &mut bundle,
            typed_chc_contract("contract-typed", &obligation_id, false),
        );

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(evidence[0].artifacts.iter().any(|artifact| {
            artifact.kind == EvidenceArtifactKind::EngineInput
                && artifact.uri.contains("typed-trust-mc-chc")
        }));
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("constructed typed trust_mc ChcVc")
                && diagnostic.contains("relations=2")
                && diagnostic.contains("clauses=2")
        }));
        assert!(!evidence[0].has_solver_transcript_artifacts());
    }

    #[test]
    fn direct_typed_chc_rejects_missing_binding_metadata() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        );
        let obligation_id = native_typed_chc_obligation_id(22, 18);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::Assertion,
            &obligation_id,
            "contract-typed",
        )]);
        let mut contract = typed_chc_contract("contract-typed", &obligation_id, false);
        contract.metadata.retain(|entry| entry.key != TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY);
        push_typed_chc_contract(&mut bundle, contract);

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].artifacts.is_empty());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("missing proof-grade typed trust_mc CHC/PDR binding metadata")
        }));
    }

    #[test]
    fn direct_typed_chc_rejects_tampered_source_digest_binding() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        );
        let obligation_id = native_typed_chc_obligation_id(23, 19);
        let mut obligation =
            obligation_with_contract(ObligationKind::Assertion, &obligation_id, "contract-typed");
        for entry in &mut obligation.metadata {
            if entry.key == TRUST_SOURCE_DIGEST_METADATA_KEY {
                entry.value = "33".repeat(32);
            }
        }
        let mut bundle = bundle_with(vec![obligation]);
        push_typed_chc_contract(
            &mut bundle,
            typed_chc_contract("contract-typed", &obligation_id, false),
        );

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].artifacts.is_empty());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains(TRUST_SOURCE_DIGEST_METADATA_KEY) && diagnostic.contains("expected")
        }));
    }

    #[test]
    fn direct_typed_chc_rejects_tampered_synthetic_digest_binding() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        );
        let obligation_id = native_typed_chc_obligation_id(24, 20);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::Assertion,
            &obligation_id,
            "contract-typed",
        )]);
        let mut contract = typed_chc_contract("contract-typed", &obligation_id, false);
        if let ContractPredicate::MathIr { value, .. } = &mut contract.predicate {
            value["rules"][1]["body"]["constraints"][0] =
                serde_json::json!({ "kind": "bool_const", "value": true });
        }
        push_typed_chc_contract(&mut bundle, contract);

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].artifacts.is_empty());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("synthetic digest mismatch")
                || diagnostic.contains("parsed solver input")
        }));
    }

    #[test]
    #[cfg(not(feature = "trust-mc-native-solver"))]
    fn direct_typed_chc_contract_input_with_tmir_identity_fails_closed_without_transport() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        );
        let native_obligation_id = native_typed_chc_obligation_id(49, 6);
        let mut public_obligation = obligation_with_contract(
            ObligationKind::ArithmeticSafety,
            "vc:demo:f:arithmetic_safety:1",
            "contract-typed",
        );
        public_obligation.metadata.extend([
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY.to_string(),
                value: "trust-mc".to_string(),
            },
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY.to_string(),
                value: "49".to_string(),
            },
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY.to_string(),
                value: "6".to_string(),
            },
        ]);
        let mut bundle = bundle_with(vec![public_obligation]);
        push_typed_chc_contract(
            &mut bundle,
            typed_chc_contract_for_public(
                "contract-typed",
                "vc:demo:f:arithmetic_safety:1",
                &native_obligation_id,
                false,
            ),
        );

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].obligation_id, "vc:demo:f:arithmetic_safety:1");
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(!evidence[0].has_solver_transcript_artifacts());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("constructed typed trust_mc ChcVc")
                && diagnostic.contains(&native_obligation_id)
        }));
    }

    #[test]
    fn native_derived_typed_chc_contract_is_validated_but_not_direct_proof_authority() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        );
        let public_obligation_id = "vc:demo:f:arithmetic_safety:transport-linked";
        let native_obligation_id = native_typed_chc_obligation_id(71, 9);
        let synthetic_contract_id = format!("contract:trust-mc-typed-chc:{native_obligation_id}");
        let contract = typed_chc_contract_for_public(
            &synthetic_contract_id,
            public_obligation_id,
            &native_obligation_id,
            false,
        );
        let mut public_obligation =
            obligation(ObligationKind::ArithmeticSafety, public_obligation_id);
        assert!(public_obligation.contract_id.is_none());
        set_test_native_trust_ir_identity(&mut public_obligation, &native_obligation_id);
        public_obligation.metadata.extend(
            contract
                .metadata
                .iter()
                .filter(|entry| {
                    matches!(
                        entry.key.as_str(),
                        TRUST_MC_TYPED_CHC_SOURCE_DIGEST_METADATA_KEY
                            | TRUST_MC_TYPED_CHC_VC_DIGEST_METADATA_KEY
                            | TRUST_MC_TYPED_CHC_SYNTHETIC_DIGEST_METADATA_KEY
                            | TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY
                    )
                })
                .cloned(),
        );
        public_obligation.metadata.extend([
            MetadataEntry {
                key: TRUST_SOURCE_DIGEST_METADATA_KEY.to_string(),
                value: TEST_SOURCE_DIGEST.to_string(),
            },
            MetadataEntry {
                key: TRUST_VC_DIGEST_METADATA_KEY.to_string(),
                value: TEST_VC_DIGEST.to_string(),
            },
            MetadataEntry {
                key: TRUST_MC_TYPED_CHC_SYNTHETIC_CONTRACT_METADATA_KEY.to_string(),
                value: synthetic_contract_id.clone(),
            },
        ]);
        let bundle = TrustContractBundle {
            contracts: vec![contract],
            obligations: vec![public_obligation],
            ..bundle_with(Vec::new())
        };

        let input = adapter
            .typed_chc_pdr_obligation_for(&bundle, &bundle.obligations[0])
            .expect("native synthetic contract marker should be valid");

        assert!(
            input.is_none(),
            "a post-build native-derived contract is diagnostic transport data, not direct proof authority"
        );
        assert!(bundle.obligations[0].contract_id.is_none());
    }

    #[test]
    fn compiler_canonical_direct_typed_chc_uses_public_semantics_with_marker_provenance() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        );
        let (bundle, canonical_contract_id, _, native_obligation_id) =
            compiler_canonical_trust_mc_bundle("vc:compiler:canonical:positive", 81, 12);

        let input = adapter
            .typed_chc_pdr_obligation_for(&bundle, &bundle.obligations[0])
            .expect("compiler canonical lane must validate")
            .expect("compiler canonical lane must construct direct proof input");

        assert_eq!(input.trust_mc_obligation.obligation_id, native_obligation_id);
        assert_eq!(input.trust_mc_obligation.stats().relation_count, 2);
        assert_eq!(input.trust_mc_obligation.stats().clause_count, 2);
        assert!(input.input_artifact.uri.contains(&canonical_contract_id));
        let canonical_contract = bundle
            .contracts
            .iter()
            .find(|contract| contract.contract_id == canonical_contract_id)
            .expect("canonical contract");
        assert_eq!(
            input.input_artifact.hash.value,
            trust_mc_typed_chc_contract_input_digest(canonical_contract)
                .expect("canonical input digest")
        );
    }

    #[test]
    fn compiler_canonical_direct_typed_chc_rejects_semantic_substitution() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        );
        let (mut bundle, canonical_contract_id, _, _) =
            compiler_canonical_trust_mc_bundle("vc:compiler:canonical:substitution", 82, 13);
        let canonical = bundle
            .contracts
            .iter_mut()
            .find(|contract| contract.contract_id == canonical_contract_id)
            .expect("canonical contract");
        let ContractPredicate::MathIr { value, .. } = &mut canonical.predicate else {
            unreachable!("fixture uses exact MathIr")
        };
        value["rules"][1]["body"]["constraints"][0] =
            serde_json::json!({ "kind": "bool_const", "value": true });

        let error = adapter
            .typed_chc_pdr_obligation_for(&bundle, &bundle.obligations[0])
            .expect_err("canonical semantic substitution must fail closed");

        assert!(error.contains("semantic CHC fields differ"), "{error}");
    }

    #[test]
    fn compiler_canonical_direct_typed_chc_rejects_marker_without_native_metadata() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        );
        let (mut bundle, _, marker_contract_id, native_obligation_id) =
            compiler_canonical_trust_mc_bundle("vc:compiler:canonical:no-native-metadata", 83, 14);
        let marker = bundle
            .contracts
            .iter_mut()
            .find(|contract| contract.contract_id == marker_contract_id)
            .expect("marker contract");
        let ContractPredicate::MathIr { value, .. } = &mut marker.predicate else {
            unreachable!("fixture uses exact MathIr")
        };
        value.as_object_mut().expect("typed CHC payload object").remove("native_metadata");
        refresh_typed_chc_binding_metadata(
            marker,
            "vc:compiler:canonical:no-native-metadata",
            &native_obligation_id,
        );
        let marker = marker.clone();
        replace_public_typed_chc_binding_from_contract(&mut bundle.obligations[0], &marker);

        let error = adapter
            .typed_chc_pdr_obligation_for(&bundle, &bundle.obligations[0])
            .expect_err("marker without native metadata must fail closed");

        assert!(error.contains("missing native typed CHC obligation metadata"), "{error}");
    }

    #[test]
    fn compiler_canonical_direct_typed_chc_rejects_missing_marker() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        );
        let (mut bundle, _, _, _) =
            compiler_canonical_trust_mc_bundle("vc:compiler:canonical:no-marker", 84, 15);
        bundle.obligations[0]
            .metadata
            .retain(|entry| entry.key != TRUST_MC_TYPED_CHC_SYNTHETIC_CONTRACT_METADATA_KEY);

        let error = adapter
            .typed_chc_pdr_obligation_for(&bundle, &bundle.obligations[0])
            .expect_err("compiler canonical input without marker must fail closed");

        assert!(
            error.contains("requires one authenticated native synthetic-contract marker"),
            "{error}"
        );
    }

    #[test]
    fn native_direct_typed_chc_rejects_unbound_or_duplicate_derived_contract_markers() {
        let mut unbound = obligation(ObligationKind::ArithmeticSafety, "vc:marker:invalid");
        unbound.metadata.push(MetadataEntry {
            key: TRUST_MC_TYPED_CHC_SYNTHETIC_CONTRACT_METADATA_KEY.to_string(),
            value: "contract:derived".to_string(),
        });
        let error = native_trust_ir_synthetic_trust_mc_contract_id(&unbound)
            .expect_err("a derived contract without native request identity must fail closed");
        assert!(error.contains("without one complete native TrustIr identity"), "{error}");

        let native_obligation_id = native_typed_chc_obligation_id(3, 4);
        let mut mismatched = obligation(ObligationKind::ArithmeticSafety, "vc:marker:mismatch");
        set_test_native_trust_ir_identity(&mut mismatched, &native_obligation_id);
        mismatched.metadata.push(MetadataEntry {
            key: TRUST_MC_TYPED_CHC_SYNTHETIC_CONTRACT_METADATA_KEY.to_string(),
            value: "contract:derived".to_string(),
        });
        let error = native_trust_ir_synthetic_trust_mc_contract_id(&mismatched)
            .expect_err("a non-deterministic derived contract identity must fail closed");
        assert!(error.contains("expected deterministic identity"), "{error}");

        let expected_contract_id = format!("contract:trust-mc-typed-chc:{native_obligation_id}");
        let mut duplicate = obligation(ObligationKind::ArithmeticSafety, "vc:marker:duplicate");
        set_test_native_trust_ir_identity(&mut duplicate, &native_obligation_id);
        duplicate.metadata.extend([
            MetadataEntry {
                key: TRUST_MC_TYPED_CHC_SYNTHETIC_CONTRACT_METADATA_KEY.to_string(),
                value: expected_contract_id.clone(),
            },
            MetadataEntry {
                key: TRUST_MC_TYPED_CHC_SYNTHETIC_CONTRACT_METADATA_KEY.to_string(),
                value: expected_contract_id,
            },
        ]);
        let error = native_trust_ir_synthetic_trust_mc_contract_id(&duplicate)
            .expect_err("duplicate derived contract identities must fail closed");
        assert!(error.contains("duplicate"), "{error}");
    }

    #[test]
    fn native_derived_typed_chc_contract_requires_unique_exact_diagnostic_shape() {
        let native_obligation_id = native_typed_chc_obligation_id(72, 10);
        let contract_id = format!("contract:trust-mc-typed-chc:{native_obligation_id}");
        let source = SourceLocation {
            file: Some("src/lib.rs".to_string()),
            line: Some(17),
            column: Some(9),
            end_line: Some(17),
            end_column: Some(23),
        };
        let mut public_obligation = obligation(ObligationKind::ArithmeticSafety, "vc:marker:shape");
        public_obligation.source = source.clone();
        set_test_native_trust_ir_identity(&mut public_obligation, &native_obligation_id);
        public_obligation.metadata.push(MetadataEntry {
            key: TRUST_MC_TYPED_CHC_SYNTHETIC_CONTRACT_METADATA_KEY.to_string(),
            value: contract_id.clone(),
        });
        let mut exact = typed_chc_contract_for_public(
            &contract_id,
            &public_obligation.obligation_id,
            &native_obligation_id,
            false,
        );
        exact.source = source;
        let validate = |contracts| {
            let bundle = TrustContractBundle {
                contracts,
                obligations: vec![public_obligation.clone()],
                ..bundle_with(Vec::new())
            };
            validate_native_trust_ir_synthetic_trust_mc_contract(
                &bundle,
                &bundle.obligations[0],
                &contract_id,
            )
        };

        validate(vec![exact.clone()]).expect("exact diagnostic projection must validate");

        let error = validate(vec![exact.clone(), exact.clone()])
            .expect_err("duplicate matching contracts must fail closed");
        assert!(error.contains("expected exactly one"), "{error}");

        let mut wrong_kind = exact.clone();
        wrong_kind.kind = ContractKind::Requires;
        let error = validate(vec![wrong_kind]).expect_err("wrong contract kind must fail closed");
        assert!(error.contains("expected Asserts"), "{error}");

        let mut wrong_predicate = exact.clone();
        let ContractPredicate::MathIr { schema, value } = wrong_predicate.predicate else {
            unreachable!("fixture uses MathIr")
        };
        wrong_predicate.predicate = ContractPredicate::CanonicalJson { schema, value };
        let error =
            validate(vec![wrong_predicate]).expect_err("non-MathIr predicate must fail closed");
        assert!(error.contains("must use ContractPredicate::MathIr"), "{error}");

        let mut wrong_schema = exact.clone();
        let ContractPredicate::MathIr { schema, .. } = &mut wrong_schema.predicate else {
            unreachable!("fixture uses MathIr")
        };
        *schema = "trust-mc.typed-chc-obligation.v0".to_string();
        let error = validate(vec![wrong_schema]).expect_err("wrong schema must fail closed");
        assert!(error.contains("expected `trust-mc.typed-chc-obligation.v1`"), "{error}");

        let mut wrong_source = exact;
        wrong_source.source.line = Some(18);
        let error = validate(vec![wrong_source]).expect_err("source mismatch must fail closed");
        assert!(error.contains("source does not exactly match"), "{error}");
    }

    #[test]
    fn direct_typed_chc_contract_without_native_metadata_is_not_proof_grade() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        );
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::Assertion,
            "typed-metadata-free",
            "contract-typed",
        )]);
        push_typed_chc_contract(
            &mut bundle,
            typed_chc_contract("contract-typed", "typed-metadata-free", false),
        );

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(!evidence[0].has_solver_transcript_artifacts());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("missing native typed CHC obligation metadata")
                && diagnostic.contains("Trust/TrustIr metadata")
        }));
    }

    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn native_typed_chc_pdr_solver_feature_does_not_enable_trust_mc_compiler_facade() {
        let manifest = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml"),
        )
        .expect("trust-bmc manifest should be readable");
        let solver_feature = manifest
            .lines()
            .find(|line| line.trim_start().starts_with("trust-mc-native-solver ="))
            .expect("trust-mc-native-solver feature should be declared");
        assert!(
            solver_feature.contains("trust-mc-driver/native-typed-chc-pdr"),
            "trust-mc-native-solver must enable trust-mc-driver/native-typed-chc-pdr"
        );
        assert!(
            !solver_feature.contains("\"trust-mc-native\""),
            "trust-mc-native-solver must stay library-only and must not enable trust-mc-compiler"
        );

        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        );
        let obligation_id = native_typed_chc_obligation_id(12, 8);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::Assertion,
            &obligation_id,
            "contract-typed",
        )]);
        push_typed_chc_contract(
            &mut bundle,
            typed_chc_contract("contract-typed", &obligation_id, false),
        );

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(
            evidence[0].status,
            EvidenceStatus::Unknown,
            "generic direct typed CHC must remain non-authoritative: {:?}",
            evidence[0].diagnostics
        );
        assert_eq!(evidence[0].proof_strength, None);
        assert!(!evidence[0].is_unbounded_proof());
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("constructed typed trust_mc ChcVc"))
        );
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("fresh private consumer replay before proof-grade admission")
        }));
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .all(|diagnostic| { !diagnostic.contains("live opaque native-bundle authority") })
        );
    }

    #[test]
    #[cfg(not(feature = "trust-mc-native-solver"))]
    fn direct_typed_chc_tmir_payload_is_consumed_but_not_upgraded_without_transport() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3),
        );
        let obligation_id = native_typed_chc_obligation_id(13, 9);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::Assertion,
            &obligation_id,
            "contract-typed",
        )]);
        let mut contract = typed_chc_contract("contract-typed", &obligation_id, false);
        if let ContractPredicate::MathIr { schema, value } = contract.predicate {
            contract.predicate = ContractPredicate::TrustIr { schema, value };
        }
        push_typed_chc_contract(&mut bundle, contract);

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(evidence[0].artifacts.iter().any(|artifact| {
            artifact.kind == EvidenceArtifactKind::EngineInput
                && artifact.uri.contains("typed-trust-mc-chc")
        }));
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("constructed typed trust_mc ChcVc"))
        );
    }

    #[test]
    fn direct_typed_chc_reachable_error_refutation_with_validated_witness_is_failed() {
        // This CHC genuinely reaches `error`: `entry(false)` is a fact and
        // `error :- entry(ok)` has no constraint, so `error` is derivable with
        // ok = false. ay's PDR/Spacer cannot synthesize an invariant for a false
        // property and returns Unknown, but the sound direct-SMT acyclic
        // shortcut composes the concrete derivation and refutes.
        //
        // SOUNDNESS (refutation gate): `ChcPdrSolveStatus::Refuted` now carries
        // an optional machine-checked refutation witness. Here the driver
        // attaches one (direct-SMT witness model + exact-encoding concreteness
        // attestation), and the gate validates it against consumer-recomputed
        // digests, so the genuine refutation surfaces as `Failed` WITH a public
        // counterexample. The forged bundle metadata below plays no part in
        // that decision: only the digest-bound witness admits the upgrade.
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        );
        let obligation_id = native_typed_chc_obligation_id(14, 10);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::ArithmeticSafety,
            &obligation_id,
            "contract-typed",
        )]);
        push_typed_chc_contract(
            &mut bundle,
            typed_chc_contract("contract-typed", &obligation_id, true),
        );
        // Bundle metadata is producer-specific and unauthenticated at this API
        // boundary. A legacy or forged body-level claim must never influence
        // the refutation gate; only the validated witness may upgrade.
        bundle.metadata.push(MetadataEntry {
            key: "trust.function.havoc_free".to_string(),
            value: "true".to_string(),
        });

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        // SOUNDNESS GUARD (non-negotiable): a genuinely-reachable error must
        // never be reported Proved.
        assert_ne!(evidence[0].status, EvidenceStatus::Proved);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("constructed typed trust_mc ChcVc")
                && diagnostic.contains("relations=2")
                && diagnostic.contains("clauses=2")
        }));
        #[cfg(feature = "trust-mc-native-solver")]
        {
            // The direct-SMT fallback refutes the encoded VC with a witness the
            // gate validates: Failed, with the solver's counterexample artifact
            // AND a public counterexample record.
            assert_eq!(evidence[0].status, EvidenceStatus::Failed);
            assert!(
                evidence[0].counterexample.is_some(),
                "validated refutation witness must surface a public counterexample"
            );
            assert!(
                evidence[0].artifacts.iter().any(|artifact| {
                    artifact.kind == EvidenceArtifactKind::Counterexample
                        && artifact.uri.ends_with("/counterexample.json")
                }),
                "expected a counterexample artifact; artifacts: {:#?}",
                evidence[0].artifacts
            );
            assert!(
                evidence[0].diagnostics.iter().any(|diagnostic| {
                    diagnostic.contains("refutation witness validated")
                        && diagnostic.contains("direct-SMT acyclic error-derivation witness model")
                }),
                "diagnostics: {:#?}",
                evidence[0].diagnostics
            );
        }
        #[cfg(not(feature = "trust-mc-native-solver"))]
        {
            assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
            assert!(
                evidence[0].diagnostics.iter().any(|diagnostic| {
                    diagnostic.contains("native typed CHC/PDR solving is disabled")
                        && diagnostic.contains("enable trust-bmc/trust-mc-native-solver")
                }),
                "diagnostics: {:#?}",
                evidence[0].diagnostics
            );
        }
        assert!(!evidence[0].has_solver_transcript_artifacts());

        // ANTI-FORGERY DISCRIMINATOR: the forged `trust.function.havoc_free`
        // claim above must contribute NOTHING to the refutation gate. Verify
        // the byte-identical bundle WITHOUT the forged entry and require
        // identical evidence — if bundle metadata ever influences the upgrade
        // decision again, this equality breaks before it can ship.
        let mut unforged_bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::ArithmeticSafety,
            &obligation_id,
            "contract-typed",
        )]);
        push_typed_chc_contract(
            &mut unforged_bundle,
            typed_chc_contract("contract-typed", &obligation_id, true),
        );
        let unforged_evidence = adapter.verify(&unforged_bundle, &unforged_bundle.obligations);
        assert_eq!(
            evidence, unforged_evidence,
            "bundle metadata must never influence the refutation gate",
        );
    }

    /// (ε, validator level) Every single-field corruption of an otherwise
    /// valid refutation witness must be rejected, keeping the refutation
    /// demoted to Unknown. The baseline witness validates so each rejection is
    /// attributable to exactly the corrupted field.
    #[test]
    #[cfg(feature = "trust-mc-native-solver")]
    fn typed_chc_pdr_refutation_witness_single_field_corruptions_are_rejected() {
        let obligation_id = native_typed_chc_obligation_id(51, 47);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::ArithmeticSafety,
            &obligation_id,
            "contract-typed",
        )]);
        push_typed_chc_contract(
            &mut bundle,
            typed_chc_contract("contract-typed", &obligation_id, true),
        );
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3),
        );
        let input = adapter
            .typed_chc_pdr_obligation_for(&bundle, &bundle.obligations[0])
            .expect("typed input should validate")
            .expect("fixture carries one typed input");
        let request = input.trust_mc_obligation;
        let expected = trust_mc_driver::normalized_typed_chc_pdr_input(&request)
            .expect("pre-solve request should normalize");
        let engine = chc_pdr_engine_from_config(TrustMcProofMode::PdrIc3);

        let valid_witness = trust_mc_core::ChcPdrRefutationWitness::new(
            request.obligation_id.clone(),
            expected.normalized_input_hash.value.clone(),
            trust_mc_driver::typed_chc_pdr_semantic_config_sha256(engine, expected.route),
            r#"{"schema":"trust_mc.typed-chc-pdr-counterexample/v1"}"#,
            trust_mc_core::ChcPdrCexVerification::AyChcReplayVerified { step_count: 2 },
            trust_mc_core::ChcPdrEncodingConcreteness::ExactEncoding {
                translation_drops: 0,
                havocs: 0,
                undef_diagnostic_havocs: 0,
            },
        );
        let validate = |witness: &trust_mc_core::ChcPdrRefutationWitness| {
            validate_typed_chc_pdr_refutation_witness(
                witness,
                &bundle.obligations[0],
                &request.obligation_id,
                &expected,
                engine,
            )
        };

        validate(&valid_witness).expect("uncorrupted witness must validate");

        // (i) wrong obligation identity.
        let mut corrupted = valid_witness.clone();
        corrupted.obligation_id = "some-other-obligation".to_string();
        let reason = validate(&corrupted).expect_err("wrong obligation id must be rejected");
        assert!(reason.contains("obligation"), "unexpected rejection: {reason}");

        // (ii) wrong encoded-formula digest (well-formed but detached).
        let mut corrupted = valid_witness.clone();
        corrupted.encoded_formula_sha256 =
            trust_mc_core::EvidenceHash::sha256_bytes(b"a different formula").value;
        let reason = validate(&corrupted).expect_err("wrong formula digest must be rejected");
        assert!(reason.contains("encoded-formula digest"), "unexpected rejection: {reason}");

        // (iii) wrong semantic-configuration digest (a differently configured
        // solve: same formula, different engine).
        let mut corrupted = valid_witness.clone();
        corrupted.semantic_config_sha256 = trust_mc_driver::typed_chc_pdr_semantic_config_sha256(
            trust_mc_core::ChcPdrEngine::AdaptivePortfolio,
            expected.route,
        );
        let reason = validate(&corrupted).expect_err("wrong semantic config must be rejected");
        assert!(reason.contains("semantic-configuration digest"), "unexpected rejection: {reason}");

        // (iv) non-exact concreteness attestation, one nonzero count at a time
        // (including "sound" havoc, which is NOT exempt for refutations).
        for (translation_drops, havocs, undef_diagnostic_havocs) in
            [(1, 0, 0), (0, 1, 0), (0, 0, 1)]
        {
            let mut corrupted = valid_witness.clone();
            corrupted.concreteness = trust_mc_core::ChcPdrEncodingConcreteness::ExactEncoding {
                translation_drops,
                havocs,
                undef_diagnostic_havocs,
            };
            let reason =
                validate(&corrupted).expect_err("nonzero concreteness counts must be rejected");
            assert!(reason.contains("exact encoding"), "unexpected rejection: {reason}");
        }
    }

    /// (δ/ε, gate-arm level) A real refuted full verification flows through
    /// `evidence_from_typed_chc_pdr_full_verification`: with the consumer's own
    /// matching recomputation it is `Failed` with a public counterexample; with
    /// a detached formula digest or a differently configured consumer it stays
    /// demoted to `Unknown` with the witness-rejection note.
    #[test]
    #[cfg(feature = "trust-mc-native-solver")]
    fn typed_chc_full_verification_refuted_witness_binding_mismatch_demotes_to_unknown() {
        let obligation_id = native_typed_chc_obligation_id(52, 48);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::ArithmeticSafety,
            &obligation_id,
            "contract-typed",
        )]);
        push_typed_chc_contract(
            &mut bundle,
            typed_chc_contract("contract-typed", &obligation_id, true),
        );
        // PdrIc3 proof mode <-> ChcPdrEngine::Pdr: the runner below must use
        // the same engine this adapter's gate recomputes for check (iii).
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3),
        );
        let input = adapter
            .typed_chc_pdr_obligation_for(&bundle, &bundle.obligations[0])
            .expect("typed input should validate")
            .expect("fixture carries one typed input");
        let request = input.trust_mc_obligation.clone();
        let expected = trust_mc_driver::normalized_typed_chc_pdr_input(&request)
            .expect("pre-solve request should normalize");
        let runner = trust_mc_driver::NativeTypedChcPdrRunner::with_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(std::time::Duration::from_secs(10)),
        );
        let solved = runner.solve_full_verification(request).expect("reachable error should solve");
        assert!(
            matches!(
                &solved.outcome.status,
                trust_mc_core::ChcPdrSolveStatus::Refuted { witness: Some(_) }
            ),
            "fixture must refute with a witness: {:?}",
            solved.outcome.status
        );

        // Matching consumer recomputation -> Failed with a counterexample.
        let evidence = adapter.evidence_from_typed_chc_pdr_full_verification(
            &bundle,
            &bundle.obligations[0],
            input.input_artifact.clone(),
            Vec::new(),
            solved.clone(),
            expected.clone(),
            false,
        );
        assert_eq!(evidence.status, EvidenceStatus::Failed);
        assert!(evidence.counterexample.is_some());
        assert!(
            evidence
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("refutation witness validated"))
        );

        // Detached formula digest (well-formed, but not this obligation's
        // formula) -> Unknown with the witness-rejection note.
        let mut detached = expected.clone();
        detached.normalized_input_hash =
            trust_mc_core::EvidenceHash::sha256_bytes(b"a different formula");
        let evidence = adapter.evidence_from_typed_chc_pdr_full_verification(
            &bundle,
            &bundle.obligations[0],
            input.input_artifact.clone(),
            Vec::new(),
            solved.clone(),
            detached,
            false,
        );
        assert_eq!(evidence.status, EvidenceStatus::Unknown);
        assert!(evidence.counterexample.is_none());
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("refutation demoted to unknown")
                && diagnostic.contains("failed validation")
        }));

        // Differently configured consumer (Chc proof mode recomputes the
        // AdaptivePortfolio engine, not the Pdr engine that solved) -> Unknown.
        let differently_configured = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        );
        let evidence = differently_configured.evidence_from_typed_chc_pdr_full_verification(
            &bundle,
            &bundle.obligations[0],
            input.input_artifact.clone(),
            Vec::new(),
            solved,
            expected,
            false,
        );
        assert_eq!(evidence.status, EvidenceStatus::Unknown);
        assert!(evidence.counterexample.is_none());
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("refutation demoted to unknown")
                && diagnostic.contains("semantic-configuration digest")
        }));
    }

    /// A compiler-native row has a stable public VC id and a distinct
    /// request-local TrustIR/TrustMC id. Both are authenticated by the binding
    /// record, but the native solver (and therefore its witness) correctly
    /// names the latter. The production refutation gate must accept that exact
    /// pair while continuing to reject adjacent native ids.
    #[test]
    #[cfg(feature = "trust-mc-native-solver")]
    fn compiler_native_refutation_accepts_only_authenticated_split_identity() {
        let public_id = "vc:trust-bmc:compiler-native-refutation:0";
        let (bundle, _canonical_id, _marker_id, native_id) =
            compiler_canonical_trust_mc_bundle_with_error_derivation(public_id, 53, 49, true);
        bundle.validate().expect("compiler-native refutation fixture must validate");
        assert!(trust_mc_obligation_identity_matches(&bundle.obligations[0], &native_id));
        assert!(!trust_mc_obligation_identity_matches(
            &bundle.obligations[0],
            &native_typed_chc_obligation_id(53, 50),
        ));

        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3),
        );
        let evidence = adapter.verify(&bundle, &bundle.obligations);
        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].obligation_id, public_id);
        assert_eq!(evidence[0].status, EvidenceStatus::Failed);
        assert!(evidence[0].counterexample.is_some());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("refutation witness validated")
                && diagnostic.contains("direct-SMT acyclic error-derivation witness model")
        }));
    }

    #[test]
    fn direct_typed_chc_wide_int_constant_flows_to_solver_instead_of_unsupported() {
        // Regression for the wide-constant direct-lane gap: a routed call-site
        // `#[requires]` precondition VC whose predicate carries a u128-width
        // type-range bound (`u128::MAX`, the generate::Lcg::range_i128 corpus)
        // used to fail the strict-i128 IntConst parse — "typed trust_mc
        // CHC/PDR integer constant ... is outside i128" — and the whole
        // obligation landed Unsupported before any solve. The widened parse
        // must ADMIT the constant (exact Horner re-encoding) so a typed ChcVc
        // is constructed and the lane solves it.
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        );
        let obligation_id = native_typed_chc_obligation_id(57, 1);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::Precondition,
            &obligation_id,
            "contract-wide-int",
        )]);
        push_typed_chc_contract(
            &mut bundle,
            typed_chc_contract_with_int_guard_constant(
                "contract-wide-int",
                &obligation_id,
                "340282366920938463463374607431768211455",
            ),
        );

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        // The load-bearing regression bit: the parse ADMITTED the wide
        // constant, so the typed ChcVc was constructed (relations entry/error,
        // fact + guarded error clause) instead of the historic parse failure.
        assert!(
            evidence[0].diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("constructed typed trust_mc ChcVc")
                    && diagnostic.contains("relations=2")
                    && diagnostic.contains("clauses=2")
            }),
            "diagnostics: {:#?}",
            evidence[0].diagnostics
        );
        assert!(
            !evidence[0].diagnostics.iter().any(|diagnostic| diagnostic.contains("outside i128")),
            "diagnostics: {:#?}",
            evidence[0].diagnostics
        );
        #[cfg(feature = "trust-mc-native-solver")]
        {
            // `error :- entry(n), n == u128::MAX, n <= 0` is UNSAT (the wide
            // constant is positive), so the solver produces a safe candidate —
            // exact BigInt LIA, no wrap. Generic typed input is not a
            // source-completeness capability, so the public adapter retains the
            // candidate as Unknown.
            assert_eq!(
                evidence[0].status,
                EvidenceStatus::Unknown,
                "diagnostics: {:#?}",
                evidence[0].diagnostics
            );
            assert_eq!(evidence[0].proof_strength, None);
            assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("fresh private consumer replay before proof-grade admission")
            }));
        }
        #[cfg(not(feature = "trust-mc-native-solver"))]
        {
            // Without the native solver the lane stays fail-closed Unsupported,
            // but AFTER constructing the typed ChcVc (solving disabled), not
            // because of the constant.
            assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
            assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("native typed CHC/PDR solving is disabled")
            }));
        }
    }

    #[test]
    fn direct_typed_chc_beyond_u128_constant_still_fails_closed() {
        // u128::MAX + 1 has no producer integer type; the widened parse must
        // keep failing closed BEFORE any solve — admissibility only, never
        // coercion.
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        );
        let obligation_id = native_typed_chc_obligation_id(57, 2);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::Precondition,
            &obligation_id,
            "contract-beyond-u128",
        )]);
        push_typed_chc_contract(
            &mut bundle,
            typed_chc_contract_with_int_guard_constant(
                "contract-beyond-u128",
                &obligation_id,
                "340282366920938463463374607431768211456",
            ),
        );

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(
            evidence[0].diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("outside the supported mathematical integer constant range")
            }),
            "diagnostics: {:#?}",
            evidence[0].diagnostics
        );
        assert!(
            !evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic.contains("constructed typed trust_mc ChcVc") })
        );
    }

    #[test]
    #[cfg(feature = "trust-mc-native-solver")]
    fn typed_chc_full_verification_refuted_outcome_is_demoted_to_unknown_evidence() {
        // SOUNDNESS (refutation gate): a witnessless `Refuted { witness: None }`
        // certifies nothing about the encoding's havoc-freedom, so the Refuted
        // branch passes Unknown — never Failed — to
        // `typed_chc_pdr_solver_outcome_evidence` (Failed requires a validated
        // refutation witness). The solver's counterexample artifacts stay
        // attached as non-proof diagnostics, but no public counterexample
        // record is fabricated for a non-Failed status.
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3),
        );
        let obligation_id = native_typed_chc_obligation_id(25, 21);
        let bundle = bundle_with(vec![obligation(ObligationKind::Assertion, &obligation_id)]);
        let input_artifact = trust_mc_typed_chc_engine_input_artifact(
            &bundle,
            &bundle.obligations[0],
            "contract-refuted",
            &sha256_hex('9'),
        );
        let counterexample_artifact = core_artifact_from_bytes(
            trust_mc_core::FullVerificationArtifactKind::CounterexampleTrace,
            "trust-mc://typed-chc/refuted/counterexample.json",
            br#"{"schema":"trust_mc.typed-chc-pdr-counterexample/v1"}"#,
        );
        let verdict = trust_mc_core::FullVerificationVerdict::Failed {
            counterexample_artifacts: vec![counterexample_artifact],
        };

        let evidence = adapter.typed_chc_pdr_solver_outcome_evidence(
            &bundle,
            &bundle.obligations[0],
            EvidenceStatus::Unknown,
            input_artifact,
            vec![
                "constructed typed trust_mc ChcVc from test payload".to_string(),
                "native trust_mc typed CHC/PDR full-verification runner refuted obligation"
                    .to_string(),
            ],
            non_proof_artifacts_from_trust_mc_core_verdict(&verdict),
            "native trust_mc typed CHC/PDR solver refuted the encoded VC; refutation demoted to unknown: the solver returns no witness model and the encoding's concreteness (havoc-freedom) cannot be certified"
                .to_string(),
        );

        assert_eq!(evidence.status, EvidenceStatus::Unknown);
        assert_eq!(evidence.proof_strength, None);
        assert!(evidence.counterexample.is_none());
        assert!(evidence.artifacts.iter().any(|artifact| {
            artifact.kind == EvidenceArtifactKind::EngineInput
                && artifact.uri.contains("typed-trust-mc-chc")
        }));
        assert!(evidence.artifacts.iter().any(|artifact| {
            artifact.kind == EvidenceArtifactKind::Counterexample
                && artifact.uri.ends_with("/counterexample.json")
        }));
        assert!(
            evidence
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic.contains("refutation demoted to unknown") })
        );
    }

    #[test]
    #[cfg(feature = "trust-mc-native-solver")]
    fn typed_chc_failed_outcome_counterexample_claims_only_solver_level_refutation() {
        // The typed-CHC Refuted route produces `Failed` only through a
        // validated refutation witness (see the refutation soundness gate).
        // Pin that the counterexample record the helper fabricates for a
        // `Failed` status claims exactly what is known at THIS layer — a
        // solver-level refutation of the encoded VC — and NOT a "verified"
        // counterexample; the witness's machine-check detail is carried in the
        // summary diagnostic instead.
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3),
        );
        let obligation_id = native_typed_chc_obligation_id(25, 21);
        let bundle = bundle_with(vec![obligation(ObligationKind::Assertion, &obligation_id)]);
        let input_artifact = trust_mc_typed_chc_engine_input_artifact(
            &bundle,
            &bundle.obligations[0],
            "contract-refuted",
            &sha256_hex('9'),
        );

        let evidence = adapter.typed_chc_pdr_solver_outcome_evidence(
            &bundle,
            &bundle.obligations[0],
            EvidenceStatus::Failed,
            input_artifact,
            Vec::new(),
            Vec::new(),
            "hypothetical certified failure".to_string(),
        );

        assert_eq!(evidence.status, EvidenceStatus::Failed);
        let counterexample =
            evidence.counterexample.expect("Failed evidence carries a counterexample record");
        let source = counterexample.data["source"].as_str().unwrap_or_default();
        assert!(
            source.contains("solver-level refutation")
                && source.contains("not independently validated"),
            "counterexample source must not overclaim: {source}"
        );
        assert!(!source.contains("verified counterexample"));
    }

    #[test]
    #[cfg(feature = "trust-mc-native-solver")]
    fn typed_chc_full_verification_unknown_and_timeout_outcomes_are_structured() {
        for (reason, expected_status) in [
            ("ay-chc returned unknown: abstraction incomplete", EvidenceStatus::Unknown),
            ("ay-chc timed out after configured timeout", EvidenceStatus::Timeout),
        ] {
            let adapter = TrustMcVerifierApiAdapter::new(
                TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
            );
            let obligation_id = native_typed_chc_obligation_id(26, 22);
            let bundle = bundle_with(vec![obligation(ObligationKind::Assertion, &obligation_id)]);
            let input_artifact = trust_mc_typed_chc_engine_input_artifact(
                &bundle,
                &bundle.obligations[0],
                "contract-unknown",
                &sha256_hex('8'),
            );
            let status = unknown_typed_chc_pdr_status(reason);
            let evidence = adapter.typed_chc_pdr_solver_outcome_evidence(
                &bundle,
                &bundle.obligations[0],
                status,
                input_artifact,
                vec![
                    "constructed typed trust_mc ChcVc from test payload".to_string(),
                    format!(
                        "native trust_mc typed CHC/PDR full-verification runner returned {}",
                        evidence_status_label(status)
                    ),
                ],
                Vec::new(),
                format!(
                    "native trust_mc typed CHC/PDR solver returned {} for obligation: {reason}",
                    evidence_status_label(status)
                ),
            );

            assert_eq!(evidence.status, expected_status);
            assert_eq!(evidence.proof_strength, None);
            assert!(evidence.artifacts.iter().any(|artifact| {
                artifact.kind == EvidenceArtifactKind::EngineInput
                    && artifact.uri.contains("typed-trust-mc-chc")
            }));
            assert!(evidence.diagnostics.iter().any(|diagnostic| {
                diagnostic.contains(evidence_status_label(expected_status))
                    && diagnostic.contains(reason)
            }));
        }
    }

    #[test]
    #[cfg(feature = "trust-mc-native-solver")]
    fn native_typed_solver_errors_map_to_fail_closed_statuses() {
        let invalid = trust_mc_driver::NativeSolveError::InvalidInput {
            field: "obligation".to_string(),
            detail: "missing target relation".to_string(),
        };
        assert_eq!(native_typed_chc_pdr_error_status(&invalid), EvidenceStatus::Unsupported);

        let timeout = trust_mc_driver::NativeSolveError::SolverFailed {
            reason: "timed out after 10ms".to_string(),
        };
        assert_eq!(native_typed_chc_pdr_error_status(&timeout), EvidenceStatus::Timeout);

        let failed = trust_mc_driver::NativeSolveError::SolverFailed {
            reason: "solver returned unknown".to_string(),
        };
        assert_eq!(native_typed_chc_pdr_error_status(&failed), EvidenceStatus::Unknown);
    }

    #[test]
    fn direct_typed_chc_proof_certificate_request_fails_closed() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc).with_proofs(true),
        );
        let obligation_id = native_typed_chc_obligation_id(15, 11);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::Assertion,
            &obligation_id,
            "contract-typed",
        )]);
        push_typed_chc_contract(
            &mut bundle,
            typed_chc_contract("contract-typed", &obligation_id, false),
        );

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert_eq!(evidence[0].proof_strength, None);
        #[cfg(feature = "trust-mc-native-solver")]
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("proof_certificate_not_supported")
                && diagnostic.contains("did not complete proof-grade obligation")
        }));
        #[cfg(not(feature = "trust-mc-native-solver"))]
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("native typed CHC/PDR solving is disabled")
                && diagnostic.contains("enable trust-bmc/trust-mc-native-solver")
        }));
    }

    #[test]
    fn direct_typed_chc_rejects_undeclared_variables() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3),
        );
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::Assertion,
            "typed-dangling-var",
            "contract-typed",
        )]);
        let mut contract = typed_chc_contract("contract-typed", "typed-dangling-var", false);
        if let ContractPredicate::MathIr { value, .. } = &mut contract.predicate {
            value["relations"] = serde_json::json!([
                { "name": "entry", "arg_sorts": [{ "kind": "int" }] },
                { "name": "error" }
            ]);
            value["rules"] = serde_json::json!([
                {
                    "head": {
                        "name": "entry",
                        "args": [
                            { "kind": "int_const", "value": 0 }
                        ]
                    }
                },
                {
                    "head": { "name": "error" },
                    "body": {
                        "relation": {
                            "name": "entry",
                            "args": [
                                { "kind": "var", "name": "x", "sort": { "kind": "int" } }
                            ]
                        }
                    }
                }
            ]);
        }
        refresh_typed_chc_binding_metadata(
            &mut contract,
            "typed-dangling-var",
            "typed-dangling-var",
        );
        push_typed_chc_contract(&mut bundle, contract);

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("variable reference `x` is undeclared"))
        );
    }

    #[test]
    fn direct_typed_chc_router_placeholder_input_is_rejected_before_solving() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::Assertion,
            "typed-placeholder",
            "contract-placeholder",
        )]);
        let mut contract = typed_chc_contract("contract-placeholder", "typed-placeholder", false);
        if let ContractPredicate::MathIr { value, .. } = &mut contract.predicate {
            value["origin"] = serde_json::json!("router_placeholder");
        }
        refresh_typed_chc_binding_metadata(&mut contract, "typed-placeholder", "typed-placeholder");
        push_typed_chc_contract(&mut bundle, contract);

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("not MIR-derived") && diagnostic.contains("router placeholders")
        }));
    }

    #[test]
    fn direct_typed_chc_vacuous_input_without_rules_is_rejected_before_solving() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        );
        let obligation_id = native_typed_chc_obligation_id(16, 12);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::Assertion,
            &obligation_id,
            "contract-vacuous",
        )]);
        let mut contract = typed_chc_contract("contract-vacuous", &obligation_id, false);
        if let ContractPredicate::MathIr { value, .. } = &mut contract.predicate {
            value["rules"] = serde_json::json!([]);
        }
        refresh_typed_chc_binding_metadata(&mut contract, &obligation_id, &obligation_id);
        push_typed_chc_contract(&mut bundle, contract);

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(!evidence[0].has_solver_transcript_artifacts());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("no MIR-derived rules")
                && diagnostic.contains("vacuous CHC input is not proof-grade")
        }));
    }

    #[test]
    fn direct_typed_chc_without_query_target_rule_is_rejected_before_solving() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        );
        let obligation_id = native_typed_chc_obligation_id(17, 13);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::Assertion,
            &obligation_id,
            "contract-vacuous",
        )]);
        let mut contract = typed_chc_contract("contract-vacuous", &obligation_id, false);
        if let ContractPredicate::MathIr { value, .. } = &mut contract.predicate {
            value["rules"] = serde_json::json!([
                {
                    "head": {
                        "name": "entry",
                        "args": [{ "kind": "bool_const", "value": false }]
                    }
                }
            ]);
        }
        refresh_typed_chc_binding_metadata(&mut contract, &obligation_id, &obligation_id);
        push_typed_chc_contract(&mut bundle, contract);

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(!evidence[0].has_solver_transcript_artifacts());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("query target `error` has no MIR-derived rule")
                && diagnostic.contains("vacuous unreachable-query input is not proof-grade")
        }));
    }

    /// RED: the admission check and the driver's route selection must read the
    /// query target the same way. A padded target with a matching padded
    /// relation declaration passes the obligation's own shape validation, so a
    /// trimmed admission check would see the unpadded `error` rule head as the
    /// deriving rule while the driver — matching literally — finds none and takes
    /// the trivially-safe route over a rule set that never encoded the violation.
    #[test]
    fn direct_typed_chc_with_padded_query_target_is_rejected_before_solving() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        );
        let obligation_id = native_typed_chc_obligation_id(23, 19);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::Assertion,
            &obligation_id,
            "contract-padded-target",
        )]);
        let mut contract = typed_chc_contract("contract-padded-target", &obligation_id, false);
        if let ContractPredicate::MathIr { value, .. } = &mut contract.predicate {
            value["query"]["target"] = serde_json::json!(" error ");
            value["relations"] = serde_json::json!([
                { "name": " error " },
                { "name": "error" },
                {
                    "name": "entry",
                    "arg_sorts": [{ "kind": "bool" }]
                }
            ]);
        }
        refresh_typed_chc_binding_metadata(&mut contract, &obligation_id, &obligation_id);
        push_typed_chc_contract(&mut bundle, contract);

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(!evidence[0].has_solver_transcript_artifacts());
        assert!(
            evidence[0].diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("has no MIR-derived rule")
                    && diagnostic.contains("vacuous unreachable-query input is not proof-grade")
            }),
            "unexpected diagnostics: {:?}",
            evidence[0].diagnostics
        );
    }

    #[test]
    fn direct_typed_chc_generic_bool_true_fact_is_rejected_before_solving() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        );
        let obligation_id = native_typed_chc_obligation_id(18, 14);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::Assertion,
            &obligation_id,
            "contract-generic-true",
        )]);
        let mut contract = typed_chc_contract("contract-generic-true", &obligation_id, false);
        if let ContractPredicate::MathIr { value, .. } = &mut contract.predicate {
            value["rules"] = serde_json::json!([
                {
                    "head": { "name": "error" },
                    "body": {
                        "constraints": [{ "kind": "bool_const", "value": true }]
                    }
                }
            ]);
        }
        refresh_typed_chc_binding_metadata(&mut contract, &obligation_id, &obligation_id);
        push_typed_chc_contract(&mut bundle, contract);

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(!evidence[0].has_solver_transcript_artifacts());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("generic Bool true fact")
                && diagnostic.contains("MIR-derived rule structure")
        }));
    }

    #[test]
    fn direct_typed_chc_accepts_compiler_spec_binary_constraint_rule() {
        let obligation_id = native_typed_chc_obligation_id(19, 15);
        let mut contract = typed_chc_contract("contract-spec", &obligation_id, false);
        if let ContractPredicate::MathIr { value, .. } = &mut contract.predicate {
            apply_compiler_spec_binary_constraint_shape(value);
        }
        refresh_typed_chc_binding_metadata(&mut contract, &obligation_id, &obligation_id);

        let input = trust_mc_typed_chc_input_from_contract(&contract)
            .expect("typed trust_mc input should parse")
            .expect("contract should contain typed trust_mc input");
        let vc =
            input.to_trust_mc_chc_vc().expect("compiler spec constraint should lower to ChcVc");
        let horn = vc.to_horn_smt2();

        assert!(horn.contains("(declare-var x Int)"));
        assert!(horn.contains("(declare-rel error ())"));
        assert!(horn.contains("(>= x 0)"));
        assert!(horn.contains("(< x 0)"));
    }

    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn native_typed_chc_pdr_solver_keeps_compiler_spec_binary_candidate_non_authoritative() {
        let obligation_id = native_typed_chc_obligation_id(21, 17);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::Assertion,
            &obligation_id,
            "contract-spec",
        )]);
        let mut contract = typed_chc_contract("contract-spec", &obligation_id, false);
        if let ContractPredicate::MathIr { value, .. } = &mut contract.predicate {
            apply_compiler_spec_binary_constraint_shape(value);
        }
        refresh_typed_chc_binding_metadata(&mut contract, &obligation_id, &obligation_id);
        push_typed_chc_contract(&mut bundle, contract);
        // This historical flag is not bound to the obligation, formula digest,
        // or compiler provenance. Treat it as inert metadata: a caller must not
        // be able to forge a concrete program refutation with one string pair.
        bundle.metadata.push(MetadataEntry {
            key: "trust.function.havoc_free".to_string(),
            value: "true".to_string(),
        });

        let evidence = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3),
        )
        .verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unknown);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(!evidence[0].is_unbounded_proof());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("fresh private consumer replay before proof-grade admission")
        }));
    }

    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn fresh_exact_direct_pdr_dispatch_retains_nonserializable_e4_e5_receipt() {
        for (index, kind) in
            [ObligationKind::LoopInvariant, ObligationKind::Termination].into_iter().enumerate()
        {
            let native_obligation_id = native_typed_chc_obligation_id(91, index as u32);
            let contract_id = format!("contract-fresh-exact-{index}");
            let mut public = obligation_with_contract(kind, &native_obligation_id, &contract_id);
            add_typed_body_aware_vc_formula_value(&mut public, false);
            let mut bundle = bundle_with(vec![public]);
            push_typed_chc_contract(
                &mut bundle,
                cyclic_safe_typed_chc_contract(
                    &contract_id,
                    &native_obligation_id,
                    &native_obligation_id,
                ),
            );
            let adapter = TrustMcVerifierApiAdapter::new(
                TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
            );

            let dispatch = adapter
                .exact_direct_chc_pdr_evidence_with_fresh_receipt(
                    &bundle,
                    &bundle.obligations[0],
                    Some(Instant::now() + std::time::Duration::from_secs(10)),
                )
                .expect("exact direct receipt dispatch validates")
                .expect("fixture carries exact direct input");
            assert_eq!(
                dispatch.evidence.status,
                EvidenceStatus::Proved,
                "fresh exact E4/E5 dispatch was rejected: {:?}",
                dispatch.evidence.diagnostics
            );
            assert_eq!(
                dispatch.evidence.proof_strength,
                Some(ProofStrength {
                    reasoning: ReasoningKind::Pdr,
                    assurance: AssuranceLevel::SmtBacked,
                })
            );
            assert!(dispatch.evidence.artifacts.iter().any(|artifact| {
                artifact.kind == EvidenceArtifactKind::Model && artifact.materialization.is_some()
            }));
            assert!(
                dispatch.evidence.is_unbounded_proof(),
                "fresh exact PDR evidence must satisfy the public model-aware artifact DAG policy"
            );
            let receipt = dispatch.receipt.expect("fresh PDR replay retains a live receipt");
            assert_eq!(receipt.public_obligation_id(), native_obligation_id);
            assert_eq!(
                receipt
                    .still_authorizes(&bundle, &bundle.obligations[0])
                    .expect("exact live receipt rechecks"),
                ProofStrength {
                    reasoning: ReasoningKind::Pdr,
                    assurance: AssuranceLevel::SmtBacked,
                }
            );

            let mut mutated = bundle.clone();
            mutated.obligations[0]
                .metadata
                .iter_mut()
                .find(|entry| entry.key == TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
                .expect("typed E4/E5 payload")
                .value = serde_json::to_string(&trust_verifier_api::TrustSpecPredicate::new(
                trust_verifier_api::TrustSpecExpr::bool_literal(true),
                Vec::new(),
            ))
            .expect("mutated formula serializes");
            assert!(receipt.still_authorizes(&mutated, &mutated.obligations[0]).is_err());
        }
    }

    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn fresh_exact_direct_bundle_seal_is_batch_scoped_and_rejects_cross_seal_replay() {
        let mut obligations = Vec::new();
        let mut contracts = Vec::new();
        for index in 0..2 {
            let obligation_id = native_typed_chc_obligation_id(96, index);
            let contract_id = format!("contract-shared-seal-{index}");
            let mut obligation = obligation_with_contract(
                ObligationKind::LoopInvariant,
                &obligation_id,
                &contract_id,
            );
            add_typed_body_aware_vc_formula_value(&mut obligation, false);
            obligations.push(obligation);
            contracts.push(cyclic_safe_typed_chc_contract(
                &contract_id,
                &obligation_id,
                &obligation_id,
            ));
        }
        let mut bundle = bundle_with(obligations);
        for contract in contracts {
            push_typed_chc_contract(&mut bundle, contract);
        }
        bundle.validate().expect("shared-seal fixture must validate");

        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let shared_seal = FreshExactDirectChcPdrBundleSeal::from_validated_bundle(&bundle);
        let mut receipts = Vec::new();
        for obligation in &bundle.obligations {
            let digest = bundle
                .canonical_obligation_semantic_digest_sha256(obligation)
                .expect("fixture has a canonical public digest");
            let dispatch = adapter
                .exact_direct_chc_pdr_evidence_with_prevalidated_bundle_seal(
                    &bundle,
                    obligation,
                    digest,
                    shared_seal.clone(),
                    None,
                    Some(Instant::now() + std::time::Duration::from_secs(10)),
                )
                .expect("shared-seal exact dispatch validates")
                .expect("fixture carries exact direct input");
            assert_eq!(dispatch.evidence.status, EvidenceStatus::Proved);
            receipts.push(dispatch.receipt.expect("proved dispatch retains authority"));
        }

        assert!(shared_seal.matches_bundle(&bundle));
        for (receipt, obligation) in receipts.iter().zip(&bundle.obligations) {
            assert!(receipt.shares_bundle_seal(&shared_seal));
            receipt
                .still_authorizes_under_exact_bundle_seal(&shared_seal, obligation)
                .expect("same-batch seal authorizes its exact receipt row");
        }

        let independently_minted_seal =
            FreshExactDirectChcPdrBundleSeal::from_validated_bundle(&bundle);
        assert!(independently_minted_seal.matches_bundle(&bundle));
        assert!(!receipts[0].shares_bundle_seal(&independently_minted_seal));
        let reason = receipts[0]
            .still_authorizes_under_exact_bundle_seal(
                &independently_minted_seal,
                &bundle.obligations[0],
            )
            .expect_err("a byte-identical but independently minted seal must not replay");
        assert!(reason.contains("does not share the supplied opaque bundle seal"));

        let mut mutated = bundle.clone();
        let ContractPredicate::MathIr { value, .. } = &mut mutated.contracts[0].predicate else {
            unreachable!("shared-seal fixture contract is MathIr")
        };
        value["query"]["target"] = serde_json::json!("attacker_target");
        assert!(
            !shared_seal.matches_bundle(&mutated),
            "a seal must not reconcile a post-dispatch contract mutation"
        );
    }

    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn expired_exact_direct_dispatch_never_mints_a_receipt() {
        let native_obligation_id = native_typed_chc_obligation_id(92, 0);
        let contract_id = "contract-expired-exact";
        let mut public = obligation_with_contract(
            ObligationKind::LoopInvariant,
            &native_obligation_id,
            contract_id,
        );
        add_typed_body_aware_vc_formula_value(&mut public, false);
        let mut bundle = bundle_with(vec![public]);
        push_typed_chc_contract(
            &mut bundle,
            cyclic_safe_typed_chc_contract(
                contract_id,
                &native_obligation_id,
                &native_obligation_id,
            ),
        );
        let adapter = TrustMcVerifierApiAdapter::default();
        let dispatch = adapter
            .exact_direct_chc_pdr_evidence_with_fresh_receipt(
                &bundle,
                &bundle.obligations[0],
                Some(Instant::now() - std::time::Duration::from_secs(1)),
            )
            .expect("expired dispatch returns typed evidence")
            .expect("fixture carries exact direct input");
        assert_eq!(dispatch.evidence.status, EvidenceStatus::Timeout);
        assert!(dispatch.receipt.is_none());
    }

    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn exact_direct_deadline_clamps_driver_timeout_and_rejects_late_completion() {
        let public_id = "vc:trust-bmc:deadline-clamp:0";
        let (mut bundle, _canonical_id, _marker_id, _native_id) =
            compiler_canonical_trust_mc_bundle(public_id, 95, 0);
        bundle.obligations[0].kind = ObligationKind::LoopInvariant;
        add_typed_body_aware_vc_formula(&mut bundle.obligations[0]);
        bundle.validate().expect("deadline-clamp fixture must validate");
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let deadline = Instant::now() + std::time::Duration::from_secs(2);
        let dispatch = adapter
            .exact_direct_chc_pdr_evidence_with_fresh_receipt(
                &bundle,
                &bundle.obligations[0],
                Some(deadline),
            )
            .expect("deadline-clamped exact input validates")
            .expect("deadline-clamp fixture carries exact input");
        let receipt = dispatch.receipt.expect("timely exact solve retains receipt");
        let options: serde_json::Value = serde_json::from_slice(
            receipt
                .verification
                .cache_key
                .parts
                .options
                .materialized_bytes()
                .expect("applied options are materialized"),
        )
        .expect("applied options are JSON");
        let applied_timeout = std::time::Duration::new(
            options["timeout"]["secs"].as_u64().expect("timeout seconds"),
            options["timeout"]["nanos"].as_u64().expect("timeout nanos") as u32,
        );
        assert!(applied_timeout > std::time::Duration::ZERO);
        assert!(
            applied_timeout <= std::time::Duration::from_secs(2),
            "driver timeout {applied_timeout:?} exceeded the caller's remaining deadline"
        );
        assert!(applied_timeout < std::time::Duration::from_secs(10));

        let completion_deadline = Instant::now();
        assert!(fresh_exact_direct_completion_is_timely(
            Some(completion_deadline),
            completion_deadline
        ));
        assert!(
            !fresh_exact_direct_completion_is_timely(
                Some(completion_deadline),
                completion_deadline + std::time::Duration::from_nanos(1)
            ),
            "a success first observed after the frozen deadline must enter the Timeout/no-receipt branch"
        );
    }

    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn bare_e4_and_generic_direct_rows_cannot_request_a_fresh_receipt() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3),
        );
        for (index, kind) in
            [ObligationKind::LoopInvariant, ObligationKind::Assertion].into_iter().enumerate()
        {
            let native_id = native_typed_chc_obligation_id(94, index as u32);
            let contract_id = format!("contract-no-fresh-receipt-{index}");
            let mut bundle =
                bundle_with(vec![obligation_with_contract(kind, &native_id, &contract_id)]);
            push_typed_chc_contract(
                &mut bundle,
                cyclic_safe_typed_chc_contract(&contract_id, &native_id, &native_id),
            );

            assert!(
                adapter
                    .exact_direct_chc_pdr_evidence_with_fresh_receipt(
                        &bundle,
                        &bundle.obligations[0],
                        None,
                    )
                    .expect("ineligible row is rejected without solving")
                    .is_none(),
                "bare E4/E5 kinds and generic typed rows must not enter the receipt lane"
            );
        }
    }

    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn fresh_exact_direct_receipt_rejects_native_marker_mutation_outside_public_digest() {
        let public_id = "vc:trust-bmc:fresh-marker-binding:0";
        let (mut bundle, _canonical_id, marker_id, _native_id) =
            compiler_canonical_trust_mc_bundle(public_id, 93, 0);
        bundle.obligations[0].kind = ObligationKind::LoopInvariant;
        add_typed_body_aware_vc_formula(&mut bundle.obligations[0]);
        bundle.validate().expect("fresh marker fixture must validate");
        let public_digest = bundle
            .canonical_obligation_semantic_digest_sha256(&bundle.obligations[0])
            .expect("fresh marker fixture has a canonical public digest");

        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let dispatch = adapter
            .exact_direct_chc_pdr_evidence_with_fresh_receipt(
                &bundle,
                &bundle.obligations[0],
                Some(Instant::now() + std::time::Duration::from_secs(10)),
            )
            .expect("canonical/native direct binding validates")
            .expect("canonical fixture carries exact direct input");
        assert_eq!(dispatch.evidence.status, EvidenceStatus::Proved);
        let receipt = dispatch.receipt.expect("fresh exact solve retains authority");

        let mut mutated = bundle.clone();
        let marker = mutated
            .contracts
            .iter_mut()
            .find(|contract| contract.contract_id == marker_id)
            .expect("authenticated native marker");
        let ContractPredicate::MathIr { value, .. } = &mut marker.predicate else {
            unreachable!("fresh marker fixture is MathIr")
        };
        value["function_name"] = serde_json::json!("attacker::reminted_function_alias");
        assert_eq!(
            mutated
                .canonical_obligation_semantic_digest_sha256(&mutated.obligations[0])
                .expect("mutated fixture retains canonical public digest"),
            public_digest,
            "diagnostic native marker bytes are intentionally outside the canonical public digest"
        );
        let reason = receipt.still_authorizes(&mutated, &mutated.obligations[0]).expect_err(
            "a live receipt must rebind the native marker, not trust the public digest",
        );
        assert!(
            reason.contains("binding")
                || reason.contains("semantic CHC fields")
                || reason.contains("synthetic"),
            "unexpected marker-mutation rejection: {reason}"
        );
    }

    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn in_process_normalized_input_binding_rejects_result_and_transport_tampering() {
        let obligation_id = native_typed_chc_obligation_id(22, 18);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::Assertion,
            &obligation_id,
            "contract-normalized-binding",
        )]);
        let contract = typed_chc_contract("contract-normalized-binding", &obligation_id, false);
        push_typed_chc_contract(&mut bundle, contract);
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3),
        );
        let input = adapter
            .typed_chc_pdr_obligation_for(&bundle, &bundle.obligations[0])
            .expect("typed input should validate")
            .expect("fixture carries one typed input");
        let request = input.trust_mc_obligation;
        let expected = trust_mc_driver::normalized_typed_chc_pdr_input(&request)
            .expect("pre-solve request should normalize");
        let runner = trust_mc_driver::NativeTypedChcPdrRunner::with_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(std::time::Duration::from_secs(10)),
        );
        let solved = runner
            .solve_full_verification(request)
            .expect("fixture should produce proof-grade full verification");
        validate_native_full_verification_normalized_input(&solved, &expected)
            .expect("untampered result must bind to the pre-solve request");

        let mut route_tampered = solved.clone();
        route_tampered.route = trust_mc_driver::TypedChcPdrRoute::TriviallySafe;
        let reason = validate_native_full_verification_normalized_input(&route_tampered, &expected)
            .expect_err("a producer-authored route alias must fail closed");
        assert!(reason.contains("route") && reason.contains("pre-solve request"));

        let mut cache_tampered = solved.clone();
        let mut cache_parts = cache_tampered.cache_key.parts.clone();
        cache_parts.normalized_input_hash =
            trust_mc_core::EvidenceHash::sha256_bytes(b"self-consistent cache alias");
        cache_tampered.cache_key = trust_mc_core::FullVerificationCacheKey::from_parts(cache_parts);
        let reason = validate_native_full_verification_normalized_input(&cache_tampered, &expected)
            .expect_err("a self-consistent cache alias must fail closed");
        assert!(reason.contains("cache normalized-input digest"));

        let mut proof_tampered = solved.clone();
        let trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
        } = &mut proof_tampered.verdict
        else {
            panic!("fixture should carry CHC/PDR proof evidence");
        };
        proof.obligation.normalized_input = "self-consistent proof alias\n".to_string();
        proof.obligation.normalized_input_hash =
            trust_mc_core::EvidenceHash::sha256_bytes(proof.obligation.normalized_input.as_bytes());
        proof.metadata.normalized_input_hash = Some(proof.obligation.normalized_input_hash.clone());
        let reason = validate_native_full_verification_normalized_input(&proof_tampered, &expected)
            .expect_err("a self-consistent proof alias must fail closed");
        assert!(reason.contains("proof obligation normalized bytes"));

        let mut artifact_tampered = solved.clone();
        let trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
        } = &mut artifact_tampered.verdict
        else {
            panic!("fixture should carry CHC/PDR proof evidence");
        };
        let artifact = proof
            .artifacts
            .iter_mut()
            .find(|artifact| {
                artifact.kind == trust_mc_core::FullVerificationArtifactKind::NormalizedInput
            })
            .expect("fixture should materialize normalized input");
        *artifact = trust_mc_core::FullVerificationArtifact::from_bytes(
            trust_mc_core::FullVerificationArtifactKind::NormalizedInput,
            "trust-mc://tampered/normalized-input",
            b"self-consistent artifact alias\n",
        );
        let reason =
            validate_native_full_verification_normalized_input(&artifact_tampered, &expected)
                .expect_err("a materialized artifact alias must fail closed");
        assert!(reason.contains("materialized NormalizedInput artifact"));

        assert!(
            solved.authorized_native_proof().is_err(),
            "a generic submitted CHC cannot mint exact source/module authority"
        );
        assert!(
            solved.native_proof_transport_record().is_err(),
            "diagnostic transport export must remain gated by the live opaque authority"
        );
    }

    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn native_typed_chc_compiler_spec_satisfiable_refutation_with_validated_witness_is_failed() {
        // SOUNDNESS (refutation gate): the solver genuinely refutes this
        // satisfiable constraint and attaches a machine-checked refutation
        // witness (direct-SMT witness model + exact-encoding concreteness
        // attestation). The gate validates the witness against
        // consumer-recomputed digests and surfaces the refutation as `Failed`
        // with a public counterexample; never Proved.
        let obligation_id = native_typed_chc_obligation_id(26, 22);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::ArithmeticSafety,
            &obligation_id,
            "contract-spec",
        )]);
        let mut contract = typed_chc_contract("contract-spec", &obligation_id, false);
        if let ContractPredicate::MathIr { value, .. } = &mut contract.predicate {
            apply_compiler_spec_satisfiable_constraint_shape(value);
        }
        refresh_typed_chc_binding_metadata(&mut contract, &obligation_id, &obligation_id);
        push_typed_chc_contract(&mut bundle, contract);

        let evidence = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3),
        )
        .verify(&bundle, &bundle.obligations);

        // Never Proved; Failed only through the validated witness.
        assert_ne!(evidence[0].status, EvidenceStatus::Proved);
        assert_eq!(evidence[0].status, EvidenceStatus::Failed);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(
            evidence[0].counterexample.is_some(),
            "validated refutation witness must surface a public counterexample"
        );
        assert!(evidence[0].artifacts.iter().any(|artifact| {
            artifact.kind == EvidenceArtifactKind::Counterexample
                && artifact.uri.ends_with("/counterexample.json")
        }));
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("direct SMT confirmed a satisfiable typed query fact")
        }));
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("refutation witness validated")
                && diagnostic.contains("exact-encoding concreteness attestation")
        }));
    }

    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn native_typed_chc_nonlinear_int_mul_overflow_is_unknown_fallback() {
        // Nonlinear integer multiplication over *unbounded* Int (`width * height
        // > u32::MAX` with width, height : Int) is undecidable for ay's QF_LIA
        // core. ay honors its wall-clock bound and returns Unknown promptly
        // (its linear relaxation drops the product, so it cannot refute), and we
        // no longer fabricate a refutation with a bounded concrete-witness
        // search. The honest result is Unknown — we tried and could not decide
        // within the bound; never a proof, never a counterexample. The
        // *decidable* overflow path is the bit-vector encoding; see
        // `native_typed_chc_pdr_solver_refutes_bitvector_mul_overflow_with_
        // witness`, which refutes a fixed-width mul overflow with a real model.
        let obligation_id = native_typed_chc_obligation_id(31, 27);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::ArithmeticSafety,
            &obligation_id,
            "contract-spec",
        )]);
        let mut contract = typed_chc_contract("contract-spec", &obligation_id, false);
        if let ContractPredicate::MathIr { value, .. } = &mut contract.predicate {
            apply_compiler_spec_mul_overflow_constraint_shape(value);
        }
        refresh_typed_chc_binding_metadata(&mut contract, &obligation_id, &obligation_id);
        push_typed_chc_contract(&mut bundle, contract);

        let evidence = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(100),
        )
        .verify(&bundle, &bundle.obligations);

        // SOUNDNESS GUARD: an undecidable nonlinear obligation must never be
        // reported Proved (no fake proof) nor Failed with a fabricated witness.
        assert_ne!(evidence[0].status, EvidenceStatus::Proved);
        assert_eq!(evidence[0].status, EvidenceStatus::Unknown);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(evidence[0].counterexample.is_none());
    }

    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn native_typed_chc_pdr_solver_proves_bitvector_add_cannot_overflow() {
        // Bounded 8-bit add: a < 16 AND b < 16 AND bvult(bvadd(a, b), a).
        // With both operands below 16, the 8-bit sum never wraps, so the
        // unsigned-overflow witness bvult(bvadd(a,b), a) is unsatisfiable and
        // `error` is unreachable. A genuine BV UNSAT must Prove.
        let obligation_id = native_typed_chc_obligation_id(41, 37);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::ArithmeticSafety,
            &obligation_id,
            "contract-spec",
        )]);
        let mut contract = typed_chc_contract("contract-spec", &obligation_id, false);
        if let ContractPredicate::MathIr { value, .. } = &mut contract.predicate {
            apply_bv_add_no_overflow_constraint_shape(value);
        }
        refresh_typed_chc_binding_metadata(&mut contract, &obligation_id, &obligation_id);
        push_typed_chc_contract(&mut bundle, contract);

        let evidence = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3),
        )
        .verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unknown);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(!evidence[0].is_unbounded_proof());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("fresh private consumer replay before proof-grade admission")
        }));
    }

    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn native_typed_chc_bitvector_add_overflow_refutation_with_validated_witness_is_failed() {
        // Unbounded 8-bit add: bvult(bvadd(a, b), a) is satisfiable
        // (e.g. a = 255, b = 1 wraps to 0 < 255), so `error` is reachable.
        // A genuine BV overflow must never be Proved.
        let obligation_id = native_typed_chc_obligation_id(42, 38);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::ArithmeticSafety,
            &obligation_id,
            "contract-spec",
        )]);
        let mut contract = typed_chc_contract("contract-spec", &obligation_id, false);
        if let ContractPredicate::MathIr { value, .. } = &mut contract.predicate {
            apply_bv_add_overflow_constraint_shape(value);
        }
        refresh_typed_chc_binding_metadata(&mut contract, &obligation_id, &obligation_id);
        push_typed_chc_contract(&mut bundle, contract);

        let evidence = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(100),
        )
        .verify(&bundle, &bundle.obligations);

        // SOUNDNESS GUARD (non-negotiable): a genuinely-overflowing BV
        // obligation must NEVER be reported Proved. Marking a real bug "proved"
        // is the worst possible outcome, strictly worse than Unknown/Unsupported.
        assert_ne!(evidence[0].status, EvidenceStatus::Proved);
        assert_eq!(evidence[0].proof_strength, None);

        // ay's PDR/Spacer engine returns Unknown on BV refutation, but the
        // typed full-verification path applies the sound direct-SMT
        // acyclic-error-derivation shortcut, which composes a concrete
        // satisfiable derivation of `error` and refutes. SOUNDNESS (refutation
        // gate): the driver attaches a machine-checked refutation witness
        // (direct-SMT witness model + exact-encoding concreteness attestation)
        // and the gate validates it against consumer-recomputed digests, so
        // the refutation surfaces as `Failed` with a public counterexample.
        assert_eq!(evidence[0].status, EvidenceStatus::Failed);
        assert!(
            evidence[0].counterexample.is_some(),
            "validated refutation witness must surface a public counterexample"
        );
        assert!(evidence[0].artifacts.iter().any(|artifact| {
            artifact.kind == EvidenceArtifactKind::Counterexample
                && artifact.uri.ends_with("/counterexample.json")
        }));
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic.contains("refutation witness validated") })
        );
    }

    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn native_typed_chc_pdr_solver_proves_bitvector_mul_cannot_overflow() {
        // Bounded 8-bit multiply: a < 16 AND b < 16 AND <unsigned-mul-overflow
        // witness>. With both operands below 16 the 8-bit product is at most
        // 15*15 = 225 < 256, so it never wraps; the witness
        // `b != 0 && bvudiv(bvmul(a,b),b) != a` is unsatisfiable and `error`
        // is unreachable. A genuine BV UNSAT must Prove via bit-blasting — the
        // decidable counterpart of the undecidable Int-NIA mul obligation.
        let obligation_id = native_typed_chc_obligation_id(43, 39);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::ArithmeticSafety,
            &obligation_id,
            "contract-spec",
        )]);
        let mut contract = typed_chc_contract("contract-spec", &obligation_id, false);
        if let ContractPredicate::MathIr { value, .. } = &mut contract.predicate {
            apply_bv_mul_no_overflow_constraint_shape(value);
        }
        refresh_typed_chc_binding_metadata(&mut contract, &obligation_id, &obligation_id);
        push_typed_chc_contract(&mut bundle, contract);

        let evidence = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3),
        )
        .verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unknown);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(!evidence[0].is_unbounded_proof());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("fresh private consumer replay before proof-grade admission")
        }));
    }

    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn native_typed_chc_bitvector_mul_overflow_refutation_with_validated_witness_is_failed() {
        // Unbounded 8-bit multiply: `b != 0 && bvudiv(bvmul(a,b),b) != a` is
        // satisfiable (e.g. a = 16, b = 16 wraps 256 -> 0), so `error` is
        // reachable. A genuine BV overflow must never be proved; the refutation
        // carries a machine-checked witness the gate validates, so it surfaces
        // as `Failed` with a public counterexample.
        let obligation_id = native_typed_chc_obligation_id(44, 40);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::ArithmeticSafety,
            &obligation_id,
            "contract-spec",
        )]);
        let mut contract = typed_chc_contract("contract-spec", &obligation_id, false);
        if let ContractPredicate::MathIr { value, .. } = &mut contract.predicate {
            apply_bv_mul_overflow_constraint_shape(value);
        }
        refresh_typed_chc_binding_metadata(&mut contract, &obligation_id, &obligation_id);
        push_typed_chc_contract(&mut bundle, contract);

        let evidence = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(100),
        )
        .verify(&bundle, &bundle.obligations);

        // SOUNDNESS GUARD (non-negotiable): a genuinely-overflowing BV
        // obligation must NEVER be reported Proved.
        assert_ne!(evidence[0].status, EvidenceStatus::Proved);
        assert_eq!(evidence[0].proof_strength, None);
        // Refutation gate: validated witness (digest-bound, exact-encoding
        // concreteness, machine-checked model) → Failed.
        assert_eq!(evidence[0].status, EvidenceStatus::Failed);
        assert!(
            evidence[0].counterexample.is_some(),
            "validated refutation witness must surface a public counterexample"
        );
        assert!(evidence[0].artifacts.iter().any(|artifact| {
            artifact.kind == EvidenceArtifactKind::Counterexample
                && artifact.uri.ends_with("/counterexample.json")
        }));
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic.contains("refutation witness validated") })
        );
    }

    #[test]
    fn direct_typed_chc_rejects_mistyped_compiler_spec_binary_constraint() {
        let obligation_id = native_typed_chc_obligation_id(20, 16);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::Assertion,
            &obligation_id,
            "contract-mistyped-spec",
        )]);
        let mut contract = typed_chc_contract("contract-mistyped-spec", &obligation_id, false);
        if let ContractPredicate::MathIr { value, .. } = &mut contract.predicate {
            value["rules"] = serde_json::json!([
                {
                    "head": { "name": "error" },
                    "body": {
                        "constraints": [
                            {
                                "kind": "binary",
                                "op": "and",
                                "lhs": { "kind": "bool_const", "value": true },
                                "rhs": { "kind": "int_const", "value": 0 }
                            }
                        ]
                    }
                }
            ]);
        }
        refresh_typed_chc_binding_metadata(&mut contract, &obligation_id, &obligation_id);
        push_typed_chc_contract(&mut bundle, contract);

        let evidence = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        )
        .verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("binary And sort error") && diagnostic.contains("Bool")
        }));
    }

    fn apply_compiler_spec_binary_constraint_shape(value: &mut serde_json::Value) {
        value["vars"] = serde_json::json!([
            { "name": "x", "sort": { "kind": "int" } }
        ]);
        value["relations"] = serde_json::json!([
            { "name": "error" }
        ]);
        value["rules"] = serde_json::json!([
            {
                "head": { "name": "error" },
                "body": {
                    "constraints": [
                        {
                            "kind": "binary",
                            "op": "and",
                            "lhs": {
                                "kind": "binary",
                                "op": "ge",
                                "lhs": { "kind": "var", "name": "x", "sort": { "kind": "int" } },
                                "rhs": { "kind": "int_const", "value": "0" }
                            },
                            "rhs": {
                                "kind": "binary",
                                "op": "lt",
                                "lhs": { "kind": "var", "name": "x", "sort": { "kind": "int" } },
                                "rhs": { "kind": "int_const", "value": 0 }
                            }
                        }
                    ]
                }
            }
        ]);
    }

    #[cfg(feature = "trust-mc-native-solver")]
    fn apply_compiler_spec_mul_overflow_constraint_shape(value: &mut serde_json::Value) {
        value["vars"] = serde_json::json!([
            { "name": "width", "sort": { "kind": "int" } },
            { "name": "height", "sort": { "kind": "int" } }
        ]);
        value["relations"] = serde_json::json!([
            { "name": "error" }
        ]);
        value["rules"] = serde_json::json!([
            {
                "head": { "name": "error" },
                "body": {
                    "constraints": [
                        {
                            "kind": "binary",
                            "op": "and",
                            "lhs": {
                                "kind": "binary",
                                "op": "and",
                                "lhs": {
                                    "kind": "binary",
                                    "op": "ge",
                                    "lhs": { "kind": "var", "name": "width", "sort": { "kind": "int" } },
                                    "rhs": { "kind": "int_const", "value": "0" }
                                },
                                "rhs": {
                                    "kind": "binary",
                                    "op": "le",
                                    "lhs": { "kind": "var", "name": "width", "sort": { "kind": "int" } },
                                    "rhs": { "kind": "int_const", "value": "4294967295" }
                                }
                            },
                            "rhs": {
                                "kind": "binary",
                                "op": "and",
                                "lhs": {
                                    "kind": "binary",
                                    "op": "and",
                                    "lhs": {
                                        "kind": "binary",
                                        "op": "ge",
                                        "lhs": { "kind": "var", "name": "height", "sort": { "kind": "int" } },
                                        "rhs": { "kind": "int_const", "value": "0" }
                                    },
                                    "rhs": {
                                        "kind": "binary",
                                        "op": "le",
                                        "lhs": { "kind": "var", "name": "height", "sort": { "kind": "int" } },
                                        "rhs": { "kind": "int_const", "value": "4294967295" }
                                    }
                                },
                                "rhs": {
                                    "kind": "binary",
                                    "op": "gt",
                                    "lhs": {
                                        "kind": "binary",
                                        "op": "mul",
                                        "lhs": { "kind": "var", "name": "width", "sort": { "kind": "int" } },
                                        "rhs": { "kind": "var", "name": "height", "sort": { "kind": "int" } }
                                    },
                                    "rhs": { "kind": "int_const", "value": "4294967295" }
                                }
                            }
                        }
                    ]
                }
            }
        ]);
    }

    #[cfg(feature = "trust-mc-native-solver")]
    fn apply_compiler_spec_satisfiable_constraint_shape(value: &mut serde_json::Value) {
        value["vars"] = serde_json::json!([
            { "name": "y", "sort": { "kind": "int" } },
            { "name": "_3", "sort": { "kind": "bool" } }
        ]);
        value["relations"] = serde_json::json!([
            { "name": "error" }
        ]);
        value["rules"] = serde_json::json!([
            {
                "head": { "name": "error" },
                "body": {
                    "constraints": [
                        {
                            "kind": "binary",
                            "op": "and",
                            "lhs": {
                                "kind": "binary",
                                "op": "and",
                                "lhs": {
                                    "kind": "binary",
                                    "op": "and",
                                    "lhs": {
                                        "kind": "binary",
                                        "op": "ge",
                                        "lhs": { "kind": "var", "name": "y", "sort": { "kind": "int" } },
                                        "rhs": { "kind": "int_const", "value": "0" }
                                    },
                                    "rhs": {
                                        "kind": "binary",
                                        "op": "le",
                                        "lhs": { "kind": "var", "name": "y", "sort": { "kind": "int" } },
                                        "rhs": { "kind": "int_const", "value": "4294967295" }
                                    }
                                },
                                "rhs": {
                                    "kind": "binary",
                                    "op": "eq",
                                    "lhs": { "kind": "var", "name": "_3", "sort": { "kind": "bool" } },
                                    "rhs": {
                                        "kind": "binary",
                                        "op": "eq",
                                        "lhs": { "kind": "var", "name": "y", "sort": { "kind": "int" } },
                                        "rhs": { "kind": "int_const", "value": "0" }
                                    }
                                }
                            },
                            "rhs": { "kind": "var", "name": "_3", "sort": { "kind": "bool" } }
                        }
                    ]
                }
            }
        ]);
    }

    #[cfg(feature = "trust-mc-native-solver")]
    fn apply_bv_add_no_overflow_constraint_shape(value: &mut serde_json::Value) {
        value["vars"] = serde_json::json!([
            { "name": "a", "sort": { "kind": "bit_vec", "width": 8 } },
            { "name": "b", "sort": { "kind": "bit_vec", "width": 8 } }
        ]);
        value["relations"] = serde_json::json!([
            { "name": "error" }
        ]);
        value["rules"] = serde_json::json!([
            {
                "head": { "name": "error" },
                "body": {
                    "constraints": [
                        {
                            "kind": "binary",
                            "op": "and",
                            "lhs": {
                                "kind": "binary",
                                "op": "and",
                                "lhs": {
                                    "kind": "binary",
                                    "op": "bv_ult",
                                    "lhs": { "kind": "var", "name": "a", "sort": { "kind": "bit_vec", "width": 8 } },
                                    "rhs": { "kind": "bit_vec_const", "value": 16, "width": 8 }
                                },
                                "rhs": {
                                    "kind": "binary",
                                    "op": "bv_ult",
                                    "lhs": { "kind": "var", "name": "b", "sort": { "kind": "bit_vec", "width": 8 } },
                                    "rhs": { "kind": "bit_vec_const", "value": 16, "width": 8 }
                                }
                            },
                            "rhs": {
                                "kind": "binary",
                                "op": "bv_ult",
                                "lhs": {
                                    "kind": "binary",
                                    "op": "bv_add",
                                    "lhs": { "kind": "var", "name": "a", "sort": { "kind": "bit_vec", "width": 8 } },
                                    "rhs": { "kind": "var", "name": "b", "sort": { "kind": "bit_vec", "width": 8 } }
                                },
                                "rhs": { "kind": "var", "name": "a", "sort": { "kind": "bit_vec", "width": 8 } }
                            }
                        }
                    ]
                }
            }
        ]);
    }

    #[cfg(feature = "trust-mc-native-solver")]
    fn apply_bv_add_overflow_constraint_shape(value: &mut serde_json::Value) {
        value["vars"] = serde_json::json!([
            { "name": "a", "sort": { "kind": "bit_vec", "width": 8 } },
            { "name": "b", "sort": { "kind": "bit_vec", "width": 8 } }
        ]);
        value["relations"] = serde_json::json!([
            { "name": "error" }
        ]);
        value["rules"] = serde_json::json!([
            {
                "head": { "name": "error" },
                "body": {
                    "constraints": [
                        {
                            "kind": "binary",
                            "op": "bv_ult",
                            "lhs": {
                                "kind": "binary",
                                "op": "bv_add",
                                "lhs": { "kind": "var", "name": "a", "sort": { "kind": "bit_vec", "width": 8 } },
                                "rhs": { "kind": "var", "name": "b", "sort": { "kind": "bit_vec", "width": 8 } }
                            },
                            "rhs": { "kind": "var", "name": "a", "sort": { "kind": "bit_vec", "width": 8 } }
                        }
                    ]
                }
            }
        ]);
    }

    // Sound unsigned 8-bit multiplication-overflow witness:
    //   b != 0 AND bvudiv(bvmul(a, b), b) != a
    // When `a*b` fits in 8 bits, dividing the (untruncated) product back by a
    // nonzero `b` recovers `a`, so the witness is false. When `a*b` wraps, the
    // truncated product no longer divides back to `a`, so the witness is true.
    // This is the canonical no-first-class-overflow-predicate encoding.
    #[cfg(feature = "trust-mc-native-solver")]
    fn bv_mul_unsigned_overflow_witness() -> serde_json::Value {
        serde_json::json!({
            "kind": "binary",
            "op": "and",
            "lhs": {
                "kind": "binary",
                "op": "ne",
                "lhs": { "kind": "var", "name": "b", "sort": { "kind": "bit_vec", "width": 8 } },
                "rhs": { "kind": "bit_vec_const", "value": 0, "width": 8 }
            },
            "rhs": {
                "kind": "binary",
                "op": "ne",
                "lhs": {
                    "kind": "binary",
                    "op": "bv_udiv",
                    "lhs": {
                        "kind": "binary",
                        "op": "bv_mul",
                        "lhs": { "kind": "var", "name": "a", "sort": { "kind": "bit_vec", "width": 8 } },
                        "rhs": { "kind": "var", "name": "b", "sort": { "kind": "bit_vec", "width": 8 } }
                    },
                    "rhs": { "kind": "var", "name": "b", "sort": { "kind": "bit_vec", "width": 8 } }
                },
                "rhs": { "kind": "var", "name": "a", "sort": { "kind": "bit_vec", "width": 8 } }
            }
        })
    }

    #[cfg(feature = "trust-mc-native-solver")]
    fn apply_bv_mul_no_overflow_constraint_shape(value: &mut serde_json::Value) {
        value["vars"] = serde_json::json!([
            { "name": "a", "sort": { "kind": "bit_vec", "width": 8 } },
            { "name": "b", "sort": { "kind": "bit_vec", "width": 8 } }
        ]);
        value["relations"] = serde_json::json!([
            { "name": "error" }
        ]);
        value["rules"] = serde_json::json!([
            {
                "head": { "name": "error" },
                "body": {
                    "constraints": [
                        {
                            "kind": "binary",
                            "op": "and",
                            "lhs": {
                                "kind": "binary",
                                "op": "and",
                                "lhs": {
                                    "kind": "binary",
                                    "op": "bv_ult",
                                    "lhs": { "kind": "var", "name": "a", "sort": { "kind": "bit_vec", "width": 8 } },
                                    "rhs": { "kind": "bit_vec_const", "value": 16, "width": 8 }
                                },
                                "rhs": {
                                    "kind": "binary",
                                    "op": "bv_ult",
                                    "lhs": { "kind": "var", "name": "b", "sort": { "kind": "bit_vec", "width": 8 } },
                                    "rhs": { "kind": "bit_vec_const", "value": 16, "width": 8 }
                                }
                            },
                            "rhs": bv_mul_unsigned_overflow_witness()
                        }
                    ]
                }
            }
        ]);
    }

    #[cfg(feature = "trust-mc-native-solver")]
    fn apply_bv_mul_overflow_constraint_shape(value: &mut serde_json::Value) {
        value["vars"] = serde_json::json!([
            { "name": "a", "sort": { "kind": "bit_vec", "width": 8 } },
            { "name": "b", "sort": { "kind": "bit_vec", "width": 8 } }
        ]);
        value["relations"] = serde_json::json!([
            { "name": "error" }
        ]);
        value["rules"] = serde_json::json!([
            {
                "head": { "name": "error" },
                "body": {
                    "constraints": [ bv_mul_unsigned_overflow_witness() ]
                }
            }
        ]);
    }

    #[test]
    fn bounded_bmc_is_not_upgraded_to_full_proof() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_bmc_depth(8).with_proof_mode(TrustMcProofMode::Bmc),
        );
        let bundle = bundle_with(vec![obligation(ObligationKind::ArithmeticSafety, "arith-1")]);

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("bounded BMC at depth 8 is diagnostic-only")
        }));
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("FullVerificationError::UnsupportedProblem")
        }));
    }

    #[test]
    fn chc_pdr_modes_require_typed_native_input_before_proof_strength() {
        let chc_adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        );
        let pdr_adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3),
        );
        let bmc_adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Bmc),
        );

        assert_eq!(
            chc_adapter.accepted_chc_pdr_evidence_expectation(),
            Some(ChcPdrEvidenceExpectation {
                proof_kind: "ChcPdrProofKind::ChcValidity",
                proof_strength: ProofStrength {
                    reasoning: ReasoningKind::Chc,
                    assurance: AssuranceLevel::SmtBacked,
                },
            })
        );
        assert_eq!(
            pdr_adapter.accepted_chc_pdr_evidence_expectation(),
            Some(ChcPdrEvidenceExpectation {
                proof_kind: "ChcPdrProofKind::PdrInvariant",
                proof_strength: ProofStrength {
                    reasoning: ReasoningKind::Pdr,
                    assurance: AssuranceLevel::SmtBacked,
                },
            })
        );
        assert_eq!(bmc_adapter.accepted_chc_pdr_evidence_expectation(), None);

        let bundle = bundle_with(vec![obligation(ObligationKind::ArithmeticSafety, "arith-chc")]);
        let evidence = chc_adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("ChcPdrProofKind::ChcValidity")
                && diagnostic.contains("Chc")
                && diagnostic.contains("SmtBacked")
        }));
    }

    #[test]
    fn native_chc_pdr_evidence_rejects_missing_public_typed_chc_binding() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let obligation_id = native_typed_chc_obligation_id(53, 1);
        let bundle = bundle_with(vec![obligation(ObligationKind::Assertion, &obligation_id)]);

        let evidence = adapter.evidence_from_native_full_verifier_evidence(
            &bundle,
            &bundle.obligations[0],
            TrustMcNativeFullVerifierEvidence::ChcPdrProof(Box::new(proof_grade_chc_pdr(
                TrustMcChcPdrProofKind::ChcValidity,
                &obligation_id,
            ))),
        );

        assert_eq!(evidence.status, EvidenceStatus::Unsupported);
        assert_eq!(evidence.proof_strength, None);
        assert!(evidence.artifacts.is_empty());
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("public typed trust_mc CHC/PDR binding failed validation")
                && diagnostic
                    .contains("missing proof-grade typed trust_mc CHC/PDR binding metadata")
        }));
    }

    #[test]
    fn native_chc_pdr_evidence_rejects_tampered_public_source_digest() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let obligation_id = native_typed_chc_obligation_id(54, 1);
        let mut public_obligation = obligation(ObligationKind::Assertion, &obligation_id);
        add_public_typed_chc_binding_metadata(
            &mut public_obligation,
            &obligation_id,
            &proof_grade_normalized_input_digest(&obligation_id),
        );
        for entry in &mut public_obligation.metadata {
            if entry.key == TRUST_SOURCE_DIGEST_METADATA_KEY {
                entry.value = sha256_hex('3');
            }
        }
        let bundle = bundle_with(vec![public_obligation]);

        let evidence = adapter.evidence_from_native_full_verifier_evidence(
            &bundle,
            &bundle.obligations[0],
            TrustMcNativeFullVerifierEvidence::ChcPdrProof(Box::new(proof_grade_chc_pdr(
                TrustMcChcPdrProofKind::ChcValidity,
                &obligation_id,
            ))),
        );

        assert_eq!(evidence.status, EvidenceStatus::Unsupported);
        assert_eq!(evidence.proof_strength, None);
        assert!(evidence.artifacts.is_empty());
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains(TRUST_SOURCE_DIGEST_METADATA_KEY) && diagnostic.contains("expected")
        }));
    }

    #[test]
    fn raw_native_chc_pdr_evidence_rejects_without_pre_solve_request() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let obligation_id = native_typed_chc_obligation_id(55, 1);
        let mut public_obligation = obligation(ObligationKind::Assertion, &obligation_id);
        add_public_typed_chc_binding_metadata(
            &mut public_obligation,
            &obligation_id,
            &sha256_hex('f'),
        );
        let bundle = bundle_with(vec![public_obligation]);
        let proof = proof_grade_chc_pdr(TrustMcChcPdrProofKind::ChcValidity, &obligation_id);

        let evidence = adapter.evidence_from_native_full_verifier_evidence(
            &bundle,
            &bundle.obligations[0],
            TrustMcNativeFullVerifierEvidence::ChcPdrProof(Box::new(proof)),
        );

        assert_eq!(evidence.status, EvidenceStatus::Unsupported);
        assert_eq!(evidence.proof_strength, None);
        assert!(evidence.artifacts.is_empty());
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("lacks live opaque native-bundle authority")
                && diagnostic.contains("distinct domains")
        }));
    }

    #[test]
    fn raw_proof_grade_chc_pdr_native_evidence_is_diagnostic_only() {
        for proof_kind in
            [TrustMcChcPdrProofKind::ChcValidity, TrustMcChcPdrProofKind::PdrInvariant]
        {
            let adapter = TrustMcVerifierApiAdapter::default();
            let obligation_id = match proof_kind {
                TrustMcChcPdrProofKind::ChcValidity => native_typed_chc_obligation_id(41, 1),
                TrustMcChcPdrProofKind::PdrInvariant => native_typed_chc_obligation_id(42, 2),
            };
            let mut public_obligation = obligation(ObligationKind::Assertion, &obligation_id);
            add_public_typed_chc_binding_metadata(
                &mut public_obligation,
                &obligation_id,
                &proof_grade_normalized_input_digest(&obligation_id),
            );
            let bundle = bundle_with(vec![public_obligation]);
            let evidence = adapter.evidence_from_native_full_verifier_evidence(
                &bundle,
                &bundle.obligations[0],
                TrustMcNativeFullVerifierEvidence::ChcPdrProof(Box::new(proof_grade_chc_pdr(
                    proof_kind,
                    &obligation_id,
                ))),
            );

            assert_eq!(evidence.status, EvidenceStatus::Unsupported);
            assert_eq!(evidence.proof_strength, None);
            assert!(evidence.artifacts.is_empty());
            assert!(evidence.diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("lacks live opaque native-bundle authority")
                    && diagnostic.contains("distinct domains")
            }));

            let result = run_result_for(&adapter, &bundle, evidence);
            assert_eq!(result.status, VerificationRunStatus::Inconclusive);
            assert_eq!(result.summary.unsupported, 1);
            let manifest = result.to_manifest();
            assert!(manifest.accepted_evidence.is_empty());
            assert_eq!(manifest.rejected_evidence.len(), 1);
        }
    }

    #[test]
    fn raw_proof_grade_chc_pdr_native_evidence_with_tmir_identity_is_diagnostic_only() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let native_obligation_id = native_typed_chc_obligation_id(48, 5);
        let mut public_obligation =
            obligation(ObligationKind::ArithmeticSafety, "vc:demo:f:arithmetic_safety:0");
        public_obligation.metadata.extend([
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY.to_string(),
                value: "trust-mc".to_string(),
            },
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY.to_string(),
                value: "48".to_string(),
            },
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY.to_string(),
                value: "5".to_string(),
            },
        ]);
        add_public_typed_chc_binding_metadata(
            &mut public_obligation,
            &native_obligation_id,
            &proof_grade_normalized_input_digest(&native_obligation_id),
        );
        let bundle = bundle_with(vec![public_obligation.clone()]);

        let evidence = adapter.evidence_from_native_full_verifier_evidence(
            &bundle,
            &public_obligation,
            TrustMcNativeFullVerifierEvidence::ChcPdrProof(Box::new(proof_grade_chc_pdr(
                TrustMcChcPdrProofKind::ChcValidity,
                &native_obligation_id,
            ))),
        );

        assert_eq!(evidence.obligation_id, public_obligation.obligation_id);
        assert_eq!(evidence.status, EvidenceStatus::Unsupported);
        assert_eq!(evidence.proof_strength, None);
        assert!(evidence.artifacts.is_empty());
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("lacks live opaque native-bundle authority")
        }));
    }

    #[test]
    fn proof_grade_chc_pdr_native_evidence_rejects_grouped_native_metadata() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let grouped_obligation_id = "trust_ir-native-trust_mc-request-50";
        let mut proof = proof_grade_chc_pdr(
            TrustMcChcPdrProofKind::ChcValidity,
            &native_typed_chc_obligation_id(50, 5),
        );
        proof.native_metadata.as_mut().expect("native metadata").core_mut().proof_obligation_ids =
            vec![5, 6];
        let bundle =
            bundle_with(vec![obligation(ObligationKind::ArithmeticSafety, grouped_obligation_id)]);

        let evidence = adapter.evidence_from_native_full_verifier_evidence(
            &bundle,
            &bundle.obligations[0],
            TrustMcNativeFullVerifierEvidence::ChcPdrProof(Box::new(proof)),
        );

        assert_eq!(evidence.status, EvidenceStatus::Unsupported);
        assert_eq!(evidence.proof_strength, None);
        assert!(evidence.artifacts.is_empty());
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("grouped proof obligations")
                && diagnostic.contains("exactly one MIR proof obligation")
        }));
    }

    #[test]
    fn native_chc_pdr_evidence_rejects_mismatched_native_trust_ir_metadata() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let obligation_id = native_typed_chc_obligation_id(45, 1);
        let stale_metadata_obligation_id = native_typed_chc_obligation_id(46, 1);
        let bundle = bundle_with(vec![obligation(ObligationKind::Assertion, &obligation_id)]);
        let evidence = adapter.evidence_from_native_full_verifier_evidence(
            &bundle,
            &bundle.obligations[0],
            TrustMcNativeFullVerifierEvidence::ChcPdrProof(Box::new(proof_grade_chc_pdr(
                TrustMcChcPdrProofKind::ChcValidity,
                &stale_metadata_obligation_id,
            ))),
        );

        assert_eq!(evidence.status, EvidenceStatus::Unsupported);
        assert_eq!(evidence.proof_strength, None);
        assert!(evidence.artifacts.is_empty());
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("native typed CHC obligation metadata failed validation")
                && diagnostic.contains("does not match metadata identity")
                && diagnostic.contains(stale_metadata_obligation_id.as_str())
        }));
    }

    #[test]
    fn native_chc_pdr_evidence_rejects_metadata_without_tmir_artifact_surfaces() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let obligation_id = native_typed_chc_obligation_id(47, 3);
        let (native_request_id, proof_obligation_id) =
            parse_native_typed_chc_obligation_id(&obligation_id).expect("native TrustIr id");
        let mut proof = proof_grade_chc_pdr(TrustMcChcPdrProofKind::ChcValidity, &obligation_id);
        proof.native_metadata = Some(TrustMcNativeTypedChcObligationMetadata::from_core(
            trust_mc_core::NativeTypedChcObligationMetadata::new(
                "Trust",
                "rust-mir",
                Some(native_digest(0x11)),
                native_digest(0x22),
                trust_mc_core::NativeArtifactDigest::new("trust_ir-stable-v1", "33".repeat(32)),
                native_request_id,
                "chc",
                9,
                vec![proof_obligation_id],
                vec![0],
            ),
        ));
        let bundle = bundle_with(vec![obligation(ObligationKind::Assertion, &obligation_id)]);

        let evidence = adapter.evidence_from_native_full_verifier_evidence(
            &bundle,
            &bundle.obligations[0],
            TrustMcNativeFullVerifierEvidence::ChcPdrProof(Box::new(proof)),
        );

        assert_eq!(evidence.status, EvidenceStatus::Unsupported);
        assert_eq!(evidence.proof_strength, None);
        assert!(evidence.artifacts.is_empty());
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("native typed CHC obligation metadata failed validation")
                && diagnostic.contains("compiler_facts digest")
                && diagnostic.contains("replay identity")
        }));
    }

    #[test]
    #[cfg(feature = "trust-mc-native-solver")]
    fn native_typed_chc_pdr_proof_transport_rejects_missing_public_typed_chc_binding() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let obligation_id = native_typed_chc_obligation_id(56, 2);
        let bundle = bundle_with(vec![obligation(ObligationKind::Assertion, &obligation_id)]);
        let transport =
            native_typed_transport(&obligation_id, TrustMcNativeTypedProofStrength::ChcValidity);

        let evidence = adapter.evidence_from_native_typed_chc_pdr_proof_transport(
            &bundle,
            &bundle.obligations[0],
            transport,
        );

        assert_eq!(evidence.status, EvidenceStatus::Unsupported);
        assert_eq!(evidence.proof_strength, None);
        assert!(evidence.artifacts.is_empty());
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("public typed trust_mc CHC/PDR binding failed validation")
                && diagnostic
                    .contains("missing proof-grade typed trust_mc CHC/PDR binding metadata")
        }));
    }

    #[test]
    #[cfg(feature = "trust-mc-native-solver")]
    fn native_typed_transport_binds_normalized_input_digest_to_public_synthetic_chc() {
        let obligation_id = native_typed_chc_obligation_id(73, 11);
        let normalized_digest = native_typed_normalized_input_digest(&obligation_id);
        let transport =
            native_typed_transport(&obligation_id, TrustMcNativeTypedProofStrength::ChcValidity);
        let mut matching = obligation(ObligationKind::Assertion, &obligation_id);
        add_public_typed_chc_binding_metadata(&mut matching, &obligation_id, &normalized_digest);

        let matching_bundle = bundle_with(vec![matching]);
        validate_native_typed_transport(
            &matching_bundle,
            &matching_bundle.obligations[0],
            &transport,
        )
        .expect("matching NormalizedInput and public synthetic digest must validate");
        let diagnostic_only = TrustMcVerifierApiAdapter::default()
            .evidence_from_native_typed_chc_pdr_proof_transport(
                &matching_bundle,
                &matching_bundle.obligations[0],
                transport.clone(),
            );
        assert_eq!(diagnostic_only.status, EvidenceStatus::Unsupported);
        assert!(diagnostic_only.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("raw native typed CHC/PDR transport is diagnostic-only")
        }));

        let mut mismatched = obligation(ObligationKind::Assertion, &obligation_id);
        add_public_typed_chc_binding_metadata(&mut mismatched, &obligation_id, &"a".repeat(64));
        let mismatched_bundle = bundle_with(vec![mismatched]);
        let reasons = validate_native_typed_transport(
            &mismatched_bundle,
            &mismatched_bundle.obligations[0],
            &transport,
        )
        .expect_err("a substituted NormalizedInput digest must fail closed");
        assert!(reasons.iter().any(|reason| {
            reason.contains("NormalizedInput digest")
                && reason.contains("does not match public typed trust_mc synthetic CHC binding")
                && reason.contains(&normalized_digest)
        }));
        let rejected = TrustMcVerifierApiAdapter::default()
            .evidence_from_native_typed_chc_pdr_proof_transport(
                &mismatched_bundle,
                &mismatched_bundle.obligations[0],
                transport,
            );
        assert_eq!(rejected.status, EvidenceStatus::Unsupported);
        assert!(rejected.artifacts.is_empty());
        assert!(rejected.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("native trust_mc typed CHC/PDR proof transport rejected")
                && diagnostic.contains("NormalizedInput digest")
        }));
    }

    #[test]
    #[cfg(feature = "trust-mc-native-solver")]
    fn raw_native_typed_chc_pdr_proof_transport_is_diagnostic_only() {
        for proof_strength in [
            TrustMcNativeTypedProofStrength::ChcValidity,
            TrustMcNativeTypedProofStrength::PdrInvariant,
        ] {
            let adapter = TrustMcVerifierApiAdapter::default();
            let obligation_id = native_typed_chc_obligation_id(31, 2);
            let mut public_obligation = obligation(ObligationKind::Assertion, &obligation_id);
            add_public_typed_chc_binding_metadata(
                &mut public_obligation,
                &obligation_id,
                &native_typed_normalized_input_digest(&obligation_id),
            );
            let bundle = bundle_with(vec![public_obligation]);
            let transport = native_typed_transport(&obligation_id, proof_strength);

            let evidence = adapter.evidence_from_native_full_verifier_evidence(
                &bundle,
                &bundle.obligations[0],
                TrustMcNativeFullVerifierEvidence::TypedChcPdrProofTransport(transport),
            );

            assert_eq!(evidence.status, EvidenceStatus::Unsupported);
            assert_eq!(evidence.proof_strength, None);
            assert!(!evidence.is_unbounded_proof());
            assert!(evidence.artifacts.is_empty());
            assert!(evidence.diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("raw native typed CHC/PDR transport is diagnostic-only")
                    && diagnostic.contains("in-process trust-mc proof-grade runner")
            }));

            let result = run_result_for(&adapter, &bundle, evidence);
            assert_eq!(result.status, VerificationRunStatus::Inconclusive);
            assert!(result.to_manifest().accepted_evidence.is_empty());
        }
    }

    #[test]
    #[cfg(feature = "trust-mc-native-solver")]
    fn native_typed_transport_rejects_missing_replay_duplicate_roles_and_forged_lineage() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let obligation_id = native_typed_chc_obligation_id(31, 2);
        let mut public_obligation = obligation(ObligationKind::Assertion, &obligation_id);
        add_public_typed_chc_binding_metadata(
            &mut public_obligation,
            &obligation_id,
            &native_typed_normalized_input_digest(&obligation_id),
        );
        let bundle = bundle_with(vec![public_obligation]);

        let mut missing_replay =
            native_typed_transport(&obligation_id, TrustMcNativeTypedProofStrength::ChcValidity);
        missing_replay.replay_check_status = None;
        let evidence = adapter.evidence_from_native_typed_chc_pdr_proof_transport(
            &bundle,
            &bundle.obligations[0],
            missing_replay,
        );
        assert_eq!(evidence.status, EvidenceStatus::Unsupported);
        assert!(evidence.artifacts.is_empty());
        assert!(
            evidence
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("lacks an accepted replay/check status"))
        );

        let mut duplicate_role =
            native_typed_transport(&obligation_id, TrustMcNativeTypedProofStrength::ChcValidity);
        duplicate_role.solver_artifacts.push(duplicate_role.solver_artifacts[0].clone());
        let evidence = adapter.evidence_from_native_typed_chc_pdr_proof_transport(
            &bundle,
            &bundle.obligations[0],
            duplicate_role,
        );
        assert_eq!(evidence.status, EvidenceStatus::Unsupported);
        assert!(evidence.artifacts.is_empty());
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("requires exactly one solver transcript artifact")
                && diagnostic.contains("found 2")
        }));

        let mut forged = serde_json::to_value(native_typed_transport(
            &obligation_id,
            TrustMcNativeTypedProofStrength::ChcValidity,
        ))
        .expect("transport serializes");
        forged["check_artifacts"][0]["materialization"]["referenced_artifacts"] =
            serde_json::json!([]);
        forged["response_artifacts"][3]["materialization"]["referenced_artifacts"] =
            serde_json::json!([]);
        let forged = serde_json::from_value(forged).expect("tampered transport deserializes");
        let evidence = adapter.evidence_from_native_typed_chc_pdr_proof_transport(
            &bundle,
            &bundle.obligations[0],
            forged,
        );
        assert_eq!(evidence.status, EvidenceStatus::Unsupported);
        assert!(evidence.artifacts.is_empty());
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("checked proof report references do not match the exact")
        }));
    }

    #[test]
    #[cfg(feature = "trust-mc-native-solver")]
    fn native_typed_transport_preserves_supplemental_response_descriptors() {
        let obligation_id = native_typed_chc_obligation_id(31, 2);
        let mut public_obligation = obligation(ObligationKind::Assertion, &obligation_id);
        add_public_typed_chc_binding_metadata(
            &mut public_obligation,
            &obligation_id,
            &native_typed_normalized_input_digest(&obligation_id),
        );
        let query_bytes = b"supplemental native typed CHC query";
        let query_digest = trust_mc_core::EvidenceHash::sha256_bytes(query_bytes);
        let query_uri = format!("trust-mc://typed-chc/{obligation_id}/problem.json");
        let query: TrustMcNativeTypedProofArtifactRef = serde_json::from_value(serde_json::json!({
            "kind": trust_mc_core::FullVerificationArtifactKind::TypedChcProblem,
            "uri": query_uri,
            "digest": query_digest,
            "byte_len": query_bytes.len(),
        }))
        .expect("supplemental descriptor deserializes");
        let mut transport =
            native_typed_transport(&obligation_id, TrustMcNativeTypedProofStrength::ChcValidity);
        transport.response_artifacts.push(query);

        let bundle = bundle_with(vec![public_obligation.clone()]);
        let artifacts =
            validated_native_typed_transport_artifacts(&bundle, &public_obligation, &transport)
                .expect("trusted transport remains valid with supplemental context");
        let query = artifacts
            .iter()
            .find(|artifact| artifact.kind == EvidenceArtifactKind::SolverQuery)
            .expect("supplemental solver query is preserved");
        assert_eq!(query.uri, query_uri);
        assert_eq!(query.hash.algorithm, "sha256");
        assert_eq!(query.hash.value, query_digest.value);
        assert!(query.materialization.is_none());
    }

    #[test]
    #[cfg(feature = "trust-mc-native-solver")]
    fn native_typed_transport_rejects_duplicate_and_noncanonical_identity_metadata() {
        let obligation_id = native_typed_chc_obligation_id(31, 2);
        let mut duplicate_identity = obligation(ObligationKind::Assertion, &obligation_id);
        add_public_typed_chc_binding_metadata(
            &mut duplicate_identity,
            &obligation_id,
            &native_typed_normalized_input_digest(&obligation_id),
        );
        duplicate_identity.metadata.push(MetadataEntry {
            key: TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY.to_string(),
            value: "31".to_string(),
        });
        assert_eq!(native_trust_ir_expected_trust_mc_obligation_id(&duplicate_identity), None);
        let reason = validate_public_trust_mc_typed_chc_binding_for_native_id(
            &duplicate_identity,
            &obligation_id,
        )
        .expect_err("duplicate native identity metadata must fail closed");
        assert!(reason.contains("incomplete, duplicate, or non-canonical native TrustIr identity"));
        let bundle = bundle_with(vec![duplicate_identity]);
        let evidence = TrustMcVerifierApiAdapter::default()
            .evidence_from_native_typed_chc_pdr_proof_transport(
                &bundle,
                &bundle.obligations[0],
                native_typed_transport(
                    &obligation_id,
                    TrustMcNativeTypedProofStrength::ChcValidity,
                ),
            );
        assert_eq!(evidence.status, EvidenceStatus::Unsupported);
        assert!(evidence.artifacts.is_empty());
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("lacks a unique canonical native TrustIr identity")
        }));

        let mut noncanonical_identity = obligation(ObligationKind::Assertion, &obligation_id);
        add_public_typed_chc_binding_metadata(
            &mut noncanonical_identity,
            &obligation_id,
            &native_typed_normalized_input_digest(&obligation_id),
        );
        noncanonical_identity
            .metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY)
            .expect("request identity metadata")
            .value = "031".to_string();
        assert_eq!(native_trust_ir_expected_trust_mc_obligation_id(&noncanonical_identity), None);
        let reason = validate_public_trust_mc_typed_chc_binding_for_native_id(
            &noncanonical_identity,
            &obligation_id,
        )
        .expect_err("non-canonical numeric identity metadata must fail closed");
        assert!(reason.contains("incomplete, duplicate, or non-canonical native TrustIr identity"));

        let mut duplicate_binding = obligation(ObligationKind::Assertion, &obligation_id);
        add_public_typed_chc_binding_metadata(
            &mut duplicate_binding,
            &obligation_id,
            &native_typed_normalized_input_digest(&obligation_id),
        );
        let duplicate = duplicate_binding
            .metadata
            .iter()
            .find(|entry| entry.key == TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY)
            .expect("typed binding metadata")
            .clone();
        duplicate_binding.metadata.push(duplicate);
        let reason = validate_public_trust_mc_typed_chc_binding_for_native_id(
            &duplicate_binding,
            &obligation_id,
        )
        .expect_err("duplicate binding metadata must fail closed");
        assert!(reason.contains("missing proof-grade typed trust_mc CHC/PDR binding metadata"));
    }

    #[test]
    #[cfg(feature = "trust-mc-native-solver")]
    fn native_typed_chc_pdr_proof_transport_requires_exactly_one_materialized_input() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let obligation_id = native_typed_chc_obligation_id(31, 2);
        let mut public_obligation = obligation(ObligationKind::Assertion, &obligation_id);
        add_public_typed_chc_binding_metadata(
            &mut public_obligation,
            &obligation_id,
            &native_typed_normalized_input_digest(&obligation_id),
        );
        let bundle = bundle_with(vec![public_obligation]);

        let mut missing =
            native_typed_transport(&obligation_id, TrustMcNativeTypedProofStrength::ChcValidity);
        missing.response_artifacts.retain(|artifact| {
            artifact.kind != trust_mc_core::FullVerificationArtifactKind::NormalizedInput
        });
        let missing_evidence = adapter.evidence_from_native_typed_chc_pdr_proof_transport(
            &bundle,
            &bundle.obligations[0],
            missing,
        );
        assert_eq!(missing_evidence.status, EvidenceStatus::Unsupported);
        assert!(missing_evidence.artifacts.is_empty());
        assert!(missing_evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("exactly one materialized normalized input")
                && diagnostic.contains("found 0")
        }));

        let mut duplicate =
            native_typed_transport(&obligation_id, TrustMcNativeTypedProofStrength::ChcValidity);
        let normalized = duplicate
            .response_artifacts
            .iter()
            .find(|artifact| {
                artifact.kind == trust_mc_core::FullVerificationArtifactKind::NormalizedInput
            })
            .expect("normalized input")
            .clone();
        duplicate.response_artifacts.push(normalized);
        let duplicate_evidence = adapter.evidence_from_native_typed_chc_pdr_proof_transport(
            &bundle,
            &bundle.obligations[0],
            duplicate,
        );
        assert_eq!(duplicate_evidence.status, EvidenceStatus::Unsupported);
        assert!(duplicate_evidence.artifacts.is_empty());
        assert!(duplicate_evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("exactly one materialized normalized input")
                && diagnostic.contains("found 2")
        }));
    }

    #[test]
    #[cfg(feature = "trust-mc-native-solver")]
    fn native_typed_chc_pdr_proof_transport_rejects_grouped_identity() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let grouped_obligation_id = "trust_ir-native-trust_mc-request-31";
        let bundle =
            bundle_with(vec![obligation(ObligationKind::Assertion, grouped_obligation_id)]);
        let mut transport = native_typed_transport(
            &native_typed_chc_obligation_id(31, 2),
            TrustMcNativeTypedProofStrength::ChcValidity,
        );
        transport.proof_id = None;
        transport.native_id = grouped_obligation_id.to_string();

        let evidence = adapter.evidence_from_native_typed_chc_pdr_proof_transport(
            &bundle,
            &bundle.obligations[0],
            transport,
        );

        assert_eq!(evidence.status, EvidenceStatus::Unsupported);
        assert_eq!(evidence.proof_strength, None);
        assert!(!evidence.is_unbounded_proof());
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("grouped")
                && diagnostic.contains("single proof_id")
                && diagnostic.contains("individual MIR proof transport")
        }));
    }

    #[test]
    #[cfg(feature = "trust-mc-native-solver")]
    fn native_typed_chc_pdr_proof_transport_rejects_non_proved_status() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let obligation_id = native_typed_chc_obligation_id(34, 5);
        let bundle = bundle_with(vec![obligation(ObligationKind::Assertion, &obligation_id)]);
        let mut transport =
            native_typed_transport(&obligation_id, TrustMcNativeTypedProofStrength::PdrInvariant);
        transport.proof_status = TrustMcNativeTypedProofStatus::Unknown;

        let evidence = adapter.evidence_from_native_typed_chc_pdr_proof_transport(
            &bundle,
            &bundle.obligations[0],
            transport,
        );

        assert_eq!(evidence.status, EvidenceStatus::Unsupported);
        assert_eq!(evidence.proof_strength, None);
        assert!(!evidence.is_unbounded_proof());
        assert!(evidence.artifacts.is_empty());
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("status must be proved") && diagnostic.contains("Unknown")
        }));
    }

    #[test]
    #[cfg(feature = "trust-mc-native-solver")]
    fn native_typed_chc_pdr_proof_transport_rejects_public_id_alias_for_tmir_obligation() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let native_obligation_id = native_typed_chc_obligation_id(52, 8);
        let mut public_obligation =
            obligation(ObligationKind::ArithmeticSafety, "vc:demo:f:arithmetic_safety:8");
        public_obligation.metadata.extend([
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY.to_string(),
                value: "trust-mc".to_string(),
            },
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY.to_string(),
                value: "52".to_string(),
            },
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY.to_string(),
                value: "8".to_string(),
            },
        ]);
        let bundle = bundle_with(vec![public_obligation.clone()]);
        let mut transport = native_typed_transport(
            &native_obligation_id,
            TrustMcNativeTypedProofStrength::ChcValidity,
        );
        transport.native_id = public_obligation.obligation_id.clone();

        let evidence = adapter.evidence_from_native_typed_chc_pdr_proof_transport(
            &bundle,
            &public_obligation,
            transport,
        );

        assert_eq!(evidence.status, EvidenceStatus::Unsupported);
        assert_eq!(evidence.proof_strength, None);
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("does not match obligation")
                && diagnostic.contains(&native_obligation_id)
        }));
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_public_claim_batch_binding_accepts_exact_multi_obligation_inventory() {
        let bundle = compiler_style_mixed_public_bundle();
        let native_bundle = bind_compiler_style_native_bundle_to_public(
            compiler_style_mixed_tmir_bundle(),
            &bundle,
        );

        for index in 0..bundle.obligations.len() {
            validate_compiler_style_public_claim_for_test(&bundle, &native_bundle, index)
                .unwrap_or_else(|reason| {
                    panic!("exact public/native row {index} must bind: {reason}")
                });
        }
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_public_claim_binding_rejects_mutated_embedded_digest() {
        let bundle = compiler_style_safe_public_bundle();
        let mut native_bundle =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        native_bundle.module.proof_obligations[0]
            .source
            .as_mut()
            .and_then(|source| source.public.as_mut())
            .expect("fixture embedded public identity")
            .semantic_digest = trust_ir::ProofDigest::sha256([0x5a; 32]);

        let reason = validate_compiler_style_public_claim_for_test(&bundle, &native_bundle, 0)
            .expect_err("a mutated embedded public digest must fail closed");
        assert!(
            reason.contains("embedded public semantic digest")
                && reason.contains("does not match canonical public claim"),
            "unexpected rejection: {reason}"
        );
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_public_claim_binding_rejects_reminted_source_alias() {
        let mut bundle = compiler_style_safe_public_bundle();
        let mut native_bundle =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        bundle.obligations[0].source.line = Some(19);
        bundle.obligations[0].source.end_line = Some(19);
        // An attacker who can replace the public record and remint only the
        // embedded digest must still reconcile the exact source projection.
        remint_native_public_digest_for_test(&mut native_bundle, &bundle, 0);

        let reason = validate_compiler_style_public_claim_for_test(&bundle, &native_bundle, 0)
            .expect_err("a reminted source alias must fail closed");
        assert!(
            reason.contains("embedded source range")
                && reason.contains("does not exactly match public source"),
            "unexpected rejection: {reason}"
        );
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_public_claim_binding_rejects_reminted_formula_alias() {
        let mut bundle = compiler_style_safe_public_bundle();
        let mut native_bundle =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        bundle.obligations[0].metadata.extend([
            MetadataEntry {
                key: TRUST_VC_FORMULA_SCHEMA_METADATA_KEY.to_string(),
                value: "trust.vc.formula.canonical-json.v1".to_string(),
            },
            MetadataEntry {
                key: TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY.to_string(),
                value: r#"{"assertion":"substituted"}"#.to_string(),
            },
        ]);
        remint_native_public_digest_for_test(&mut native_bundle, &bundle, 0);

        let reason = validate_compiler_style_public_claim_for_test(&bundle, &native_bundle, 0)
            .expect_err("a reminted formula alias must fail closed");
        assert!(
            reason.contains("formula does not exactly match canonical public formula metadata"),
            "unexpected rejection: {reason}"
        );
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_public_claim_binding_rejects_contract_and_marker_semantic_mutations() {
        let (bundle, canonical_id, marker_id) = compiler_style_canonical_public_bundle();
        let native_bundle =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        validate_compiler_style_public_claim_for_test(&bundle, &native_bundle, 0).unwrap_or_else(
            |reason| panic!("canonical contract/marker fixture must bind: {reason}"),
        );

        let mut mutated_contract_bundle = bundle.clone();
        let mut mutated_contract_native = native_bundle.clone();
        let canonical = mutated_contract_bundle
            .contracts
            .iter_mut()
            .find(|contract| contract.contract_id == canonical_id)
            .expect("canonical contract");
        let ContractPredicate::MathIr { value, .. } = &mut canonical.predicate else {
            unreachable!("canonical fixture contract is MathIr")
        };
        value["query"]["target"] = serde_json::json!("entry");
        remint_native_public_digest_for_test(
            &mut mutated_contract_native,
            &mutated_contract_bundle,
            0,
        );
        let reason = validate_compiler_style_public_claim_for_test(
            &mutated_contract_bundle,
            &mutated_contract_native,
            0,
        )
        .expect_err("a reminted canonical-contract mutation must fail closed");
        assert!(
            reason.contains("semantic CHC fields differ from authenticated native marker"),
            "unexpected canonical-contract rejection: {reason}"
        );

        let mut mutated_marker_bundle = bundle;
        let mut mutated_marker_native = native_bundle;
        let marker_index = mutated_marker_bundle
            .contracts
            .iter()
            .position(|contract| contract.contract_id == marker_id)
            .expect("native marker contract");
        let ContractPredicate::MathIr { value, .. } =
            &mut mutated_marker_bundle.contracts[marker_index].predicate
        else {
            unreachable!("native marker fixture contract is MathIr")
        };
        value["query"]["target"] = serde_json::json!("entry");
        let public_id = mutated_marker_bundle.obligations[0].obligation_id.clone();
        refresh_typed_chc_binding_metadata(
            &mut mutated_marker_bundle.contracts[marker_index],
            &public_id,
            &native_typed_chc_obligation_id(7, 0),
        );
        let marker = mutated_marker_bundle.contracts[marker_index].clone();
        replace_public_typed_chc_binding_from_contract(
            &mut mutated_marker_bundle.obligations[0],
            &marker,
        );
        remint_native_public_digest_for_test(&mut mutated_marker_native, &mutated_marker_bundle, 0);
        let reason = validate_compiler_style_public_claim_for_test(
            &mutated_marker_bundle,
            &mutated_marker_native,
            0,
        )
        .expect_err("a reminted authenticated-marker mutation must fail closed");
        assert!(
            reason.contains("semantic CHC fields differ from authenticated native marker"),
            "unexpected marker rejection: {reason}"
        );
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_bundle_exact_e4_e5_evidence_retains_same_solve_live_receipt() {
        let (mut bundle, _canonical_id, _marker_id) = compiler_style_canonical_public_bundle();
        bundle.obligations[0].kind = ObligationKind::LoopInvariant;
        bundle.obligations[0].metadata.retain(|entry| {
            !matches!(
                entry.key.as_str(),
                TRUST_VC_FORMULA_SCHEMA_METADATA_KEY
                    | TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY
                    | TRUST_VC_FORMULA_SORT_METADATA_KEY
            )
        });
        add_typed_body_aware_vc_formula(&mut bundle.obligations[0]);
        bundle.validate().expect("exact E4 native bundle fixture must validate");
        let native_bundle =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );

        let mut outcome = adapter
            .evidence_from_native_trust_ir_bundle_with_deadline_and_fresh_receipts(
                &bundle,
                &bundle.obligations,
                &native_bundle,
                Some(Instant::now() + std::time::Duration::from_secs(10)),
            );
        assert_eq!(outcome.evidence.len(), 1);
        assert_eq!(
            outcome.evidence[0].status,
            EvidenceStatus::Proved,
            "exact E4 direct solve was rejected: {:?}",
            outcome.evidence[0].diagnostics
        );
        let receipt = outcome
            .fresh_exact_direct_receipts
            .remove(&bundle.obligations[0].obligation_id)
            .expect("bundle dispatch must preserve the live receipt from that exact solve");
        assert!(outcome.fresh_exact_direct_receipts.is_empty());
        assert_eq!(
            receipt
                .still_authorizes(&bundle, &bundle.obligations[0])
                .expect("bundle-carried exact receipt rechecks"),
            outcome.evidence[0]
                .proof_strength
                .clone()
                .expect("proved exact evidence has proof strength")
        );
        let mut receipt_map = BTreeMap::new();
        receipt_map.insert(bundle.obligations[0].obligation_id.clone(), receipt);
        let mut demoted = outcome.evidence;
        demoted[0].status = EvidenceStatus::Unknown;
        demoted[0].proof_strength = None;
        let filtered = finalize_native_bundle_evidence_with_fresh_receipts(demoted, receipt_map);
        assert!(
            filtered.fresh_exact_direct_receipts.is_empty(),
            "a later public-row demotion must also discard its live receipt"
        );
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_bundle_evidence_converts_pdr_transport() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let bundle = compiler_style_panic_freedom_public_bundle();
        let native_bundle =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);

        let outcome = adapter
            .evidence_from_native_trust_ir_bundle_with_deadline_and_fresh_receipts(
                &bundle,
                &bundle.obligations,
                &native_bundle,
                None,
            );
        assert!(
            outcome.fresh_exact_direct_receipts.is_empty(),
            "whole-function native transport proofs must never mint exact-row receipts"
        );
        let evidence = outcome.evidence;

        assert_eq!(evidence.len(), 1);
        assert_eq!(
            evidence[0].status,
            EvidenceStatus::Proved,
            "native TrustIr bundle proof was rejected: {:?}",
            evidence[0].diagnostics
        );
        // trust-mc 7b4f23f8d runs the IC3/PDR lanes only on cyclic obligations;
        // this safe acyclic bundle is proved by direct CHC validity. Preserve
        // the proof kind actually certified by the native transport rather
        // than relabeling it from the configured proof mode.
        assert_eq!(
            evidence[0].proof_strength,
            Some(ProofStrength {
                reasoning: ReasoningKind::Chc,
                assurance: AssuranceLevel::SmtBacked,
            })
        );
        assert!(evidence[0].is_unbounded_proof());
        assert!(evidence[0].artifacts.iter().any(|artifact| {
            artifact.kind == EvidenceArtifactKind::SolverTranscript
                && artifact
                    .uri
                    .starts_with("artifact://trust-mc/proof-artifacts/solver-transcript/")
                && artifact.materialization.is_some()
        }));
        assert!(evidence[0].artifacts.iter().any(|artifact| {
            artifact.kind == EvidenceArtifactKind::ReplayLog
                && artifact.uri.starts_with("artifact://trust-mc/proof-artifacts/replay-log/")
                && artifact.materialization.is_some()
        }));
        assert!(evidence[0].artifacts.iter().any(|artifact| {
            artifact.kind == EvidenceArtifactKind::ProofCheckReport
                && artifact
                    .uri
                    .starts_with("artifact://trust-mc/proof-artifacts/proof-check-report/")
                && artifact.materialization.is_some()
        }));
        assert!(evidence[0].artifacts.iter().any(|artifact| {
            artifact.kind == EvidenceArtifactKind::SolverQuery
                && artifact.uri.ends_with("/typed-chc-problem.json")
        }));
        assert!(
            evidence[0]
                .artifacts
                .iter()
                .filter(|artifact| artifact.kind == EvidenceArtifactKind::Model)
                .all(|artifact| artifact.materialization.is_none()),
            "supplemental invariant models must not become proof DAG nodes"
        );
        assert!(
            evidence[0]
                .artifacts
                .iter()
                .all(|artifact| artifact.kind != EvidenceArtifactKind::ProofCertificate),
            "a CHC/PDR artifact inventory must not fabricate a certificate route"
        );
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains(
                "native trust_mc typed CHC/PDR proof accepted from a live opaque native-bundle authority",
            ) && diagnostic.contains("serialized transport remains diagnostic-only")
        }));
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("native trust_mc TrustIr CHC/PDR proof-grade result accepted")
                && diagnostic.contains("request_id=7")
                && diagnostic.contains("proof_ids=[0]")
                && diagnostic.contains("cache_key_sha256=")
                && diagnostic.contains("artifact_directory=")
        }));
        assert!(evidence[0].diagnostics.iter().all(|diagnostic| {
            !diagnostic.contains("accepted with proof-grade public typed-CHC binding")
        }));
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn ordinary_formula_less_assertion_cannot_launder_whole_function_transport_proof() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let bundle = compiler_style_safe_public_bundle();
        assert!(!obligation_is_whole_function_panic_freedom(&bundle, &bundle.obligations[0]));
        let native_bundle =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);

        let evidence = adapter.evidence_from_native_trust_ir_bundle(
            &bundle,
            &bundle.obligations,
            &native_bundle,
        );

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(!evidence[0].is_unbounded_proof());
        assert!(evidence[0].artifacts.is_empty());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains(
                "not the exact compiler-authenticated whole-function panic-freedom aggregate",
            ) && diagnostic.contains("refusing to substitute")
        }));
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn certified_exact_e4_e5_refutation_is_terminal_before_native_transport() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc).with_timeout(10_000),
        );

        // Mutation matrix for the two clause roles that share the exact
        // formula lane. The direct contract is a satisfiable bad-state query
        // (`error` is reachable), while the native TrustIr fixture's function
        // body is independently panic-free and therefore transport-provable.
        // The exact, bound counterexample must become terminal `Failed`; the
        // unrelated whole-function proof must never replace it.
        for kind in [ObligationKind::LoopInvariant, ObligationKind::Termination] {
            let obligation_id = native_typed_chc_obligation_id(7, 0);
            let mut public_obligation = obligation_with_contract(
                kind.clone(),
                &obligation_id,
                "contract-exact-loop-formula",
            );
            public_obligation.source = compiler_style_source(18, 13);
            add_typed_body_aware_vc_formula_value(&mut public_obligation, true);
            let mut bundle = bundle_with(vec![public_obligation]);
            let mut direct_contract =
                typed_chc_contract("contract-exact-loop-formula", &obligation_id, true);
            direct_contract.source = compiler_style_source(18, 13);
            let ContractPredicate::MathIr { value, .. } = &mut direct_contract.predicate else {
                unreachable!("exact E4/E5 fixture uses typed MathIr input")
            };
            value["function_name"] = serde_json::json!("tmir_native_checked_branch");
            value["native_metadata"]["function_id"] = serde_json::json!(0);
            refresh_typed_chc_binding_metadata(
                &mut direct_contract,
                &obligation_id,
                &obligation_id,
            );
            push_typed_chc_contract(&mut bundle, direct_contract);
            let native_bundle = bind_compiler_style_native_bundle_to_public(
                compiler_style_safe_tmir_bundle(),
                &bundle,
            );

            let evidence = adapter.evidence_from_native_trust_ir_bundle(
                &bundle,
                &bundle.obligations,
                &native_bundle,
            );

            assert_eq!(evidence.len(), 1);
            assert_eq!(
                evidence[0].status,
                EvidenceStatus::Failed,
                "a certified satisfiable {kind:?} violation must be terminal before whole-function transport: {:#?}",
                evidence[0].diagnostics,
            );
            assert!(evidence[0].proof_strength.is_none());
            assert!(!evidence[0].is_unbounded_proof());
            assert!(evidence[0].counterexample.is_some());
            assert!(evidence[0].artifacts.iter().any(|artifact| {
                artifact.kind == EvidenceArtifactKind::Counterexample
                    && artifact.uri.ends_with("/counterexample.json")
            }));
            assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("refutation witness validated")
                    && diagnostic.contains("direct-SMT acyclic error-derivation witness model")
            }));
            assert!(evidence[0].diagnostics.iter().all(|diagnostic| {
                !diagnostic.contains("native trust_mc typed CHC/PDR proof transport accepted")
                    && !diagnostic.contains("E4/E5 typed formula was not proved")
            }));
        }

        // A compiler-authenticated formula with no exact direct contract is
        // also terminal. This pins the `Ok(None)` branch: even a separately
        // safe native body cannot be substituted for the missing formula
        // query.
        for kind in [ObligationKind::LoopInvariant, ObligationKind::Termination] {
            let obligation_id = native_typed_chc_obligation_id(7, 0);
            let mut public_obligation = obligation(kind.clone(), &obligation_id);
            public_obligation.source = compiler_style_source(18, 13);
            add_typed_body_aware_vc_formula_value(&mut public_obligation, true);
            set_test_native_trust_ir_identity(&mut public_obligation, &obligation_id);
            let bundle = bundle_with(vec![public_obligation]);
            let native_bundle = bind_compiler_style_native_bundle_to_public(
                compiler_style_safe_tmir_bundle(),
                &bundle,
            );

            let evidence = adapter.evidence_from_native_trust_ir_bundle(
                &bundle,
                &bundle.obligations,
                &native_bundle,
            );

            assert_eq!(evidence.len(), 1);
            assert_eq!(
                evidence[0].status,
                EvidenceStatus::Unsupported,
                "a missing exact {kind:?} query must not inherit a whole-function transport proof: {:#?}",
                evidence[0].diagnostics,
            );
            assert!(evidence[0].proof_strength.is_none());
            assert!(!evidence[0].is_unbounded_proof());
            assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("E4/E5 typed formula has no exact direct CHC input")
                    && diagnostic.contains("refusing to substitute")
            }));
            assert!(evidence[0].diagnostics.iter().all(|diagnostic| {
                !diagnostic.contains("native trust_mc typed CHC/PDR proof transport accepted")
            }));
        }
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_transport_cannot_replace_an_exact_precondition_formula() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc).with_timeout(10_000),
        );
        let obligation_id = native_typed_chc_obligation_id(7, 0);

        // The standalone precondition query has a reachable error state while
        // the separately translated function body is panic-free. A result for
        // the latter proof unit must not replace the exact direct result.
        let mut public_obligation = obligation_with_contract(
            ObligationKind::Precondition,
            &obligation_id,
            "contract-exact-precondition-formula",
        );
        public_obligation.source = compiler_style_source(18, 13);
        add_typed_body_aware_vc_formula_value(&mut public_obligation, true);
        let mut bundle = bundle_with(vec![public_obligation]);
        let mut direct_contract =
            typed_chc_contract("contract-exact-precondition-formula", &obligation_id, true);
        direct_contract.source = compiler_style_source(18, 13);
        let ContractPredicate::MathIr { value, .. } = &mut direct_contract.predicate else {
            unreachable!("exact precondition fixture uses typed MathIr input")
        };
        value["function_name"] = serde_json::json!("tmir_native_checked_branch");
        value["native_metadata"]["function_id"] = serde_json::json!(0);
        refresh_typed_chc_binding_metadata(&mut direct_contract, &obligation_id, &obligation_id);
        push_typed_chc_contract(&mut bundle, direct_contract);
        let native_bundle =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);

        let evidence = adapter.evidence_from_native_trust_ir_bundle(
            &bundle,
            &bundle.obligations,
            &native_bundle,
        );

        assert_eq!(evidence.len(), 1);
        assert_eq!(
            evidence[0].status,
            EvidenceStatus::Failed,
            "the exact precondition query has a validated counterexample and must not inherit the unrelated whole-function transport proof: {:#?}",
            evidence[0].diagnostics,
        );
        assert!(evidence[0].proof_strength.is_none());
        assert!(!evidence[0].is_unbounded_proof());
        assert!(evidence[0].counterexample.is_some());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("refutation witness validated")
                && diagnostic.contains("direct-SMT acyclic error-derivation witness model")
        }));
        assert!(evidence[0].diagnostics.iter().all(|diagnostic| {
            !diagnostic.contains("native trust_mc typed CHC/PDR proof transport accepted")
        }));

        // Formula-bearing public/native/replay metadata without a linked
        // direct contract is also terminal. The transport does not inject or
        // solve that formula, so absence cannot authorize substitution either.
        let mut public_obligation = obligation(ObligationKind::Precondition, &obligation_id);
        public_obligation.source = compiler_style_source(18, 13);
        add_typed_body_aware_vc_formula_value(&mut public_obligation, true);
        set_test_native_trust_ir_identity(&mut public_obligation, &obligation_id);
        let bundle = bundle_with(vec![public_obligation]);
        let native_bundle =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);

        let evidence = adapter.evidence_from_native_trust_ir_bundle(
            &bundle,
            &bundle.obligations,
            &native_bundle,
        );

        assert_eq!(evidence.len(), 1);
        assert_eq!(
            evidence[0].status,
            EvidenceStatus::Unsupported,
            "a missing exact precondition query must not inherit a whole-function transport proof: {:#?}",
            evidence[0].diagnostics,
        );
        assert!(evidence[0].proof_strength.is_none());
        assert!(!evidence[0].is_unbounded_proof());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("standalone formula or semantic claim")
                && diagnostic.contains("refusing to substitute")
        }));
        assert!(evidence[0].diagnostics.iter().all(|diagnostic| {
            !diagnostic.contains("native trust_mc typed CHC/PDR proof transport accepted")
        }));
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_bundle_entrypoint_rejects_unowned_e4_e5_before_direct_typed_solve() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc).with_timeout(10_000),
        );

        // The low-level native-bundle entrypoint is public and can be invoked
        // without the router's `supports` filter.  A supplied, directly
        // provable typed contract must not grant ownership to a bare E4/E5
        // obligation: ownership requires the current compiler VC context and
        // exact Bool formula payload as well as the kind.
        for kind in [ObligationKind::LoopInvariant, ObligationKind::Termination] {
            let native_bundle = compiler_style_safe_tmir_bundle();
            let obligation_id = native_typed_chc_obligation_id(7, 0);
            let public_obligation = obligation_with_contract(
                kind.clone(),
                &obligation_id,
                "contract-unowned-loop-formula",
            );
            let mut bundle = bundle_with(vec![public_obligation]);
            push_typed_chc_contract(
                &mut bundle,
                typed_chc_contract("contract-unowned-loop-formula", &obligation_id, false),
            );

            assert!(
                !is_trust_mc_owned_obligation(&bundle.obligations[0]),
                "a bare {kind:?} plus a supplied typed contract must remain unowned"
            );

            let evidence = adapter.evidence_from_native_trust_ir_bundle(
                &bundle,
                &bundle.obligations,
                &native_bundle,
            );

            assert_eq!(evidence.len(), 1);
            assert_eq!(
                evidence[0].status,
                EvidenceStatus::Unsupported,
                "an unowned {kind:?} must be rejected before its supplied direct contract is solved: {:#?}",
                evidence[0].diagnostics,
            );
            assert!(evidence[0].proof_strength.is_none());
            assert!(!evidence[0].is_unbounded_proof());
            assert!(evidence[0].artifacts.is_empty());
            assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("does not own") && diagnostic.contains(&format!("{kind:?}"))
            }));
            assert!(
                evidence[0].diagnostics.iter().any(|diagnostic| {
                    diagnostic.contains("rejected before direct solving")
                        && diagnostic.contains(&format!("{kind:?}"))
                }),
                "missing explicit pre-solve ownership rejection: {:#?}",
                evidence[0].diagnostics
            );
            assert!(evidence[0].diagnostics.iter().all(|diagnostic| {
                !diagnostic.contains("native trust_mc typed CHC/PDR proof transport accepted")
            }));
        }
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_bundle_rejects_post_solve_typed_request_mutation() {
        let public_bundle = compiler_style_safe_public_bundle();
        let native_bundle = bind_compiler_style_native_bundle_to_public(
            compiler_style_safe_tmir_bundle(),
            &public_bundle,
        );
        let runner = trust_mc_driver::NativeTrustIrChcPdrRunner::with_solve_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(std::time::Duration::from_secs(10)),
        );
        let mut solved = runner
            .solve_bundle_native_proof_grade(&native_bundle)
            .expect("fixture should produce one native bundle proof");
        let [row] = solved.obligations.as_mut_slice() else {
            panic!("fixture should produce exactly one proof row");
        };
        let query_target = row.translated.obligation.query_target().to_string();
        let query_rule = row
            .translated
            .obligation
            .vc
            .rules
            .iter_mut()
            .find(|rule| rule.head.name.as_str() == query_target)
            .expect("fixture should contain a query-target rule");
        let mut constraints = query_rule.body.constraints.iter().cloned().collect::<Vec<_>>();
        constraints.push(Expr::bool_const(false));
        query_rule.body =
            trust_mc_core::RuleBody::new(query_rule.body.relation.clone(), constraints);

        let row = solved.obligations.pop().expect("fixture proof row");
        let reason = NativeTrustIrChcPdrAuthorizedProof::try_from_bundle_evidence(row)
            .expect_err("mutating the typed request after solve must fail closed");
        assert!(
            reason.contains("pre-solve request") || reason.contains("pre-solve typed request"),
            "unexpected request-mutation rejection: {reason}"
        );
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_bundle_surfaces_exact_not_proved_reason() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let bundle = compiler_style_panic_freedom_public_bundle();
        let native_bundle = bind_compiler_style_native_bundle_to_public(
            compiler_style_unsafe_tmir_bundle(),
            &bundle,
        );

        let evidence = adapter.evidence_from_native_trust_ir_bundle(
            &bundle,
            &bundle.obligations,
            &native_bundle,
        );

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(evidence[0].artifacts.is_empty());
        let diagnostic =
            evidence[0].diagnostics.first().expect("not-proved reason is the primary diagnostic");
        let expected_id = native_trust_ir_expected_trust_mc_obligation_id(&bundle.obligations[0])
            .expect("fixture has canonical native identity");
        assert!(
            diagnostic
                .contains(&format!("transport solved obligation `{expected_id}` without a proof:"))
        );
        let diagnostic = diagnostic.to_ascii_lowercase();
        assert!(
            diagnostic.contains("refut")
                || diagnostic.contains("counterexample")
                || diagnostic.contains("not prove"),
            "diagnostic must preserve the producer's honest outcome: {diagnostic}"
        );
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_bundle_with_elapsed_deadline_degrades_to_timeout_not_proved() {
        // Trust: the exact inputs that
        // `native_trust_ir_bundle_evidence_converts_pdr_transport` proves must
        // degrade to Timeout — never Proved — once the per-function wall-clock
        // budget is already spent on entry. This is the soundness guard against
        // the catastrophic false-Proved regression: a budget-exhausted
        // obligation can never be reported Proved.
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let bundle = compiler_style_panic_freedom_public_bundle();
        let native_bundle =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);

        // A deadline one hour in the past is already elapsed on entry, so the
        // expensive in-process CHC/PDR solve is never started.
        let elapsed = std::time::Instant::now() - std::time::Duration::from_secs(3600);
        let evidence = adapter.evidence_from_native_trust_ir_bundle_with_deadline(
            &bundle,
            &bundle.obligations,
            &native_bundle,
            Some(elapsed),
        );
        assert_eq!(evidence.len(), 1);
        assert_eq!(
            evidence[0].status,
            EvidenceStatus::Timeout,
            "budget-exhausted obligation must degrade to Timeout, never Proved"
        );
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].artifacts.is_empty());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("per-function wall-clock budget")
                && diagnostic.contains("degraded to Timeout")
        }));

        // Control: the very same inputs with no budget (None) still prove, so
        // the Timeout above is the budget short-circuit, not an unprovable input.
        let proved = adapter.evidence_from_native_trust_ir_bundle_with_deadline(
            &bundle,
            &bundle.obligations,
            &native_bundle,
            None,
        );
        assert_eq!(proved.len(), 1);
        assert_eq!(
            proved[0].status,
            EvidenceStatus::Proved,
            "without a budget the same obligation must still prove (test is not vacuous)"
        );
    }

    // Trust (T3, per-obligation transport delivery): a bundle where one
    // request proves and a sibling request runs without a proof must retain
    // both rows independently in the producer result. This exercises the
    // producer boundary directly: the high-level dispatcher intentionally
    // admits transport proofs only for the compiler's exact one-per-function
    // panic-freedom aggregate, so a synthetic cross-function public bundle is
    // not a valid way to test producer cardinality.
    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_transport_producer_keeps_proved_and_not_proved_siblings() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let bundle = compiler_style_mixed_public_bundle();
        let native_bundle = bind_compiler_style_native_bundle_to_public(
            compiler_style_mixed_tmir_bundle(),
            &bundle,
        );
        let (transports, not_proved) = adapter
            .native_trust_ir_chc_pdr_proof_transports(&native_bundle, None)
            .expect("mixed bundle must return independent producer rows");
        assert_eq!(transports.len(), 1, "the safe sibling must retain its proof transport");
        assert_eq!(not_proved.len(), 1, "the refutable sibling must retain its own outcome");

        let canonical_safe_id =
            native_trust_ir_expected_trust_mc_obligation_id(&bundle.obligations[0])
                .expect("fixture has canonical safe proof-unit identity");
        assert_eq!(
            native_trust_mc_obligation_lookup_key(
                &transports[0].diagnostic_transport().native_id,
            ),
            native_trust_mc_obligation_lookup_key(&canonical_safe_id),
            "the proof transport must stay attached to the safe sibling",
        );
        let canonical_failing_id =
            native_trust_ir_expected_trust_mc_obligation_id(&bundle.obligations[1])
                .expect("fixture has canonical native proof-unit identity");
        let failing_reason = not_proved
            .get(&native_trust_mc_obligation_lookup_key(&canonical_failing_id))
            .expect("not-proved reason must stay attached to the failing sibling");
        assert!(
            failing_reason.contains("counterexample evidence is not a proof"),
            "failing row's reason must carry the solver's own cause, got: {failing_reason}"
        );
    }

    // Trust (T3 regression pin): a fully proved bundle yields an EMPTY
    // not-proved map, so the dispatch behaves exactly as before the producer
    // landed (every obligation consumes its transport; nothing hits the
    // not-proved branch).
    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_transports_not_proved_map_is_empty_for_fully_proved_bundle() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let bundle = compiler_style_safe_public_bundle();
        let native_bundle =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        let (transports, not_proved) = adapter
            .native_trust_ir_chc_pdr_proof_transports(&native_bundle, None)
            .expect("safe bundle must solve");
        assert_eq!(transports.len(), 1);
        assert!(
            not_proved.is_empty(),
            "fully proved bundle must not report not-proved rows: {not_proved:?}"
        );
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_bundle_rejects_mismatched_trust_mc_admission_contract() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let bundle = compiler_style_safe_public_bundle();
        let mut native_bundle =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        for request in &mut native_bundle.requests {
            if let trust_ir::NativeVerificationRequest::TrustMc(request) = request {
                request.provenance.expected_verifier.version = Some("stale-contract".to_string());
            }
        }
        let evidence = adapter.evidence_from_native_trust_ir_bundle(
            &bundle,
            &bundle.obligations,
            &native_bundle,
        );

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("native trust_mc admission contract rejected")
                && diagnostic.contains("stale-contract")
                && diagnostic.contains(TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION)
        }));
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_bundle_rejects_unsupported_semantics_in_request_provenance() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let bundle = compiler_style_safe_public_bundle();
        let mut native_bundle =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        for request in &mut native_bundle.requests {
            if let trust_ir::NativeVerificationRequest::TrustMc(request) = request {
                request.provenance.replay_context.unsupported_modes.push(
                    trust_ir::NativeUnsupportedMode::new(
                        trust_ir::NativeUnsupportedModeReason::UnsupportedVerifierMode,
                        "pointer provenance semantics are not modeled",
                    ),
                );
            }
        }
        let evidence = adapter.evidence_from_native_trust_ir_bundle(
            &bundle,
            &bundle.obligations,
            &native_bundle,
        );

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("native trust_mc admission contract rejected")
                && diagnostic.contains("unsupported native mode")
                && diagnostic.contains("pointer provenance semantics")
        }));
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_bundle_rejects_transport_marker_when_native_runner_has_no_proof_grade_evidence()
     {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let bundle = compiler_style_safe_public_bundle();
        let mut native_bundle =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        for request in &mut native_bundle.requests {
            if let trust_ir::NativeVerificationRequest::TrustMc(request) = request {
                request.mode = trust_ir::TrustMcVerificationMode::BoundedModelCheck;
            }
        }
        let obligation_id = native_typed_chc_obligation_id(7, 0);
        let mut public_obligation = bundle.obligations[0].clone();
        public_obligation.metadata.push(MetadataEntry {
            key: "trust-mc.native-typed-chc-pdr-proof-transport.v1".to_string(),
            value: serde_json::to_string(&native_typed_transport(
                &obligation_id,
                TrustMcNativeTypedProofStrength::PdrInvariant,
            ))
            .expect("transport marker should serialize"),
        });
        let bundle = TrustContractBundle { obligations: vec![public_obligation], ..bundle };

        let evidence = adapter.evidence_from_native_trust_ir_bundle(
            &bundle,
            &bundle.obligations,
            &native_bundle,
        );

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(!evidence[0].is_unbounded_proof());
        assert!(evidence[0].artifacts.is_empty());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains(
                "native trust_mc TrustIr CHC/PDR bundle did not translate to typed obligations",
            )
        }));
        assert!(
            !evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("proof transport accepted"))
        );
    }

    #[test]
    #[cfg(feature = "trust-mc-native-solver")]
    fn native_typed_chc_pdr_proof_transport_rejects_text_only_artifacts() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let obligation_id = native_typed_chc_obligation_id(32, 3);
        let bundle = bundle_with(vec![obligation(ObligationKind::Assertion, &obligation_id)]);
        let mut transport =
            native_typed_transport(&obligation_id, TrustMcNativeTypedProofStrength::ChcValidity);
        transport.replay_artifacts[0].digest = None;
        transport.check_artifacts[0].digest = None;

        let evidence = adapter.evidence_from_native_typed_chc_pdr_proof_transport(
            &bundle,
            &bundle.obligations[0],
            transport,
        );

        assert_eq!(evidence.status, EvidenceStatus::Unsupported);
        assert_eq!(evidence.proof_strength, None);
        assert!(!evidence.is_unbounded_proof());
        assert!(evidence.artifacts.is_empty());
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("replay log artifact")
                && diagnostic.contains("text-only")
                && diagnostic.contains("digest required")
        }));
    }

    #[test]
    #[cfg(feature = "trust-mc-native-solver")]
    fn serialized_native_typed_chc_pdr_transport_metadata_is_not_proof_evidence() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let obligation_id = native_typed_chc_obligation_id(33, 4);
        let mut bundle = bundle_with(vec![obligation(ObligationKind::Assertion, &obligation_id)]);
        let transport =
            native_typed_transport(&obligation_id, TrustMcNativeTypedProofStrength::ChcValidity);
        bundle.metadata.push(MetadataEntry {
            key: "trust-mc.native-typed-chc-pdr-proof-transport.v1".to_string(),
            value: serde_json::to_string(&transport).expect("transport should serialize"),
        });

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(!evidence[0].is_unbounded_proof());
        assert!(evidence[0].artifacts.is_empty());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("typed-input-required")
                && diagnostic.contains("serialized FullVerificationVerdict metadata")
        }));
    }

    #[test]
    fn proof_grade_native_evidence_is_rejected_for_unowned_obligation_kind() {
        // A bare Termination claim remains trust-wp-owned. Only an E5 row with
        // the compiler's valid typed violation formula enters trust-mc.
        let adapter = TrustMcVerifierApiAdapter::default();
        let obligation_id = native_typed_chc_obligation_id(43, 1);
        let bundle = bundle_with(vec![obligation(ObligationKind::Termination, &obligation_id)]);
        let evidence = adapter.evidence_from_native_full_verifier_evidence(
            &bundle,
            &bundle.obligations[0],
            TrustMcNativeFullVerifierEvidence::ChcPdrProof(Box::new(proof_grade_chc_pdr(
                TrustMcChcPdrProofKind::ChcValidity,
                &obligation_id,
            ))),
        );

        assert_eq!(evidence.status, EvidenceStatus::Unsupported);
        assert_eq!(evidence.proof_strength, None);
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("rejected for unowned Termination obligation")
        }));
    }

    #[test]
    fn raw_native_e5_chc_metadata_never_substitutes_for_opaque_authority() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let obligation_id = native_typed_chc_obligation_id(44, 1);
        let mut public_obligation = obligation(ObligationKind::Termination, &obligation_id);
        add_typed_body_aware_vc_formula(&mut public_obligation);
        add_public_typed_chc_binding_metadata(
            &mut public_obligation,
            &obligation_id,
            &proof_grade_normalized_input_digest(&obligation_id),
        );
        let bundle = bundle_with(vec![public_obligation.clone()]);
        let proof = || {
            TrustMcNativeFullVerifierEvidence::ChcPdrProof(Box::new(proof_grade_chc_pdr(
                TrustMcChcPdrProofKind::ChcValidity,
                &obligation_id,
            )))
        };

        // Even exact-looking public metadata is reconstructible. Only the live
        // opaque native-bundle authority may enter the positive path.
        let exact_looking = adapter.evidence_from_native_full_verifier_evidence(
            &bundle,
            &bundle.obligations[0],
            proof(),
        );
        assert_eq!(exact_looking.status, EvidenceStatus::Unsupported, "{exact_looking:#?}");
        assert!(exact_looking.proof_strength.is_none());
        assert!(!exact_looking.is_unbounded_proof());

        let mut wrong_origin_obligation = public_obligation.clone();
        let context = wrong_origin_obligation
            .metadata
            .iter_mut()
            .find(|entry| entry.key == trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY)
            .expect("typed VC context");
        *context = trust_verifier_api::ObligationContext::new(
            trust_verifier_api::ObligationProducer::CompilerMirExtract,
            trust_verifier_api::ObligationOrigin::Contract {
                contract_id: "forged-loop-marker".to_string(),
                // Public contract transport represents a `decreases` source
                // marker as `Asserts`; it still must never authorize an E5 VC.
                contract_kind: ContractKind::Asserts,
                contract_index: 0,
                predicate_schema: Some(
                    trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
                ),
            },
        )
        .to_metadata_entry()
        .expect("wrong-origin context should serialize");
        let wrong_origin_bundle = bundle_with(vec![wrong_origin_obligation]);
        let rejected_wrong_origin = adapter.evidence_from_native_full_verifier_evidence(
            &wrong_origin_bundle,
            &wrong_origin_bundle.obligations[0],
            proof(),
        );
        assert_eq!(rejected_wrong_origin.status, EvidenceStatus::Unsupported);
        assert!(rejected_wrong_origin.proof_strength.is_none());
        assert!(rejected_wrong_origin.artifacts.is_empty());

        let payload = public_obligation
            .metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
            .expect("typed formula payload");
        payload.value = "{}".to_string();
        let forged_bundle = bundle_with(vec![public_obligation]);
        let rejected = adapter.evidence_from_native_full_verifier_evidence(
            &forged_bundle,
            &forged_bundle.obligations[0],
            proof(),
        );
        assert_eq!(rejected.status, EvidenceStatus::Unsupported);
        assert!(rejected.proof_strength.is_none());
        assert!(rejected.artifacts.is_empty());
        assert!(rejected.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("rejected for unowned Termination obligation")
        }));
    }

    #[test]
    fn trust_mc_core_native_conversion_preserves_candidate_status_and_artifact_identity() {
        let native_metadata = native_typed_chc_metadata(101, 1, "chc");
        let obligation_id = native_metadata.expected_obligation_id();
        let obligation = trust_mc_core::MirDerivedChcPdrObligation::new(
            &obligation_id,
            trust_mc_core::MirObligationKind::ArithmeticSafety,
            "(declare-rel entry ())\n(rule entry)\n(query entry)\n",
        )
        .with_native_metadata(native_metadata);
        let proof = trust_mc_core::ChcPdrProofEvidence::try_proof_grade_from_linked_bytes(
            trust_mc_core::ChcPdrProofKind::ChcValidity,
            obligation,
            trust_mc_core::ChcPdrStats { relation_count: 1, clause_count: 1 },
            ("ay://chc-pdr/proof-metadata.json", b"solver transcript"),
            ("trust-mc://chc-pdr/replay-log.json", b"replay log"),
            ("trust-mc://chc-pdr/checked-proof-report.json", b"checked report"),
        )
        .expect("linked core candidate fixture must be non-empty and bounded");
        let verdict = trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
        };

        let evidence = native_evidence_from_trust_mc_core_verdict(verdict);

        let TrustMcNativeFullVerifierEvidence::ChcPdrProof(proof) = evidence else {
            panic!("validated native trust-mc-core candidate should convert to CHC/PDR evidence");
        };
        assert_eq!(
            proof.metadata.replay_check_status,
            Some(TrustMcProofReplayCheckStatus {
                replay: TrustMcProofReplayStatus::Unknown,
                check: TrustMcProofCheckStatus::Unknown,
            })
        );
        for hash in [
            proof.metadata.normalized_input_hash.as_ref().expect("input hash"),
            &proof.metadata.transcript_hashes[0],
            &proof.metadata.replay_log_hashes[0],
            &proof.metadata.checked_report_hashes[0],
        ] {
            assert!(
                proof.artifacts.iter().any(|artifact| { artifact.digest.as_ref() == Some(hash) })
            );
        }
    }

    #[test]
    fn verify_rejects_bundle_carried_trust_mc_core_chc_pdr_verdict_as_diagnostic_only() {
        for proof_kind in [
            trust_mc_core::ChcPdrProofKind::ChcValidity,
            trust_mc_core::ChcPdrProofKind::PdrInvariant,
        ] {
            let adapter = TrustMcVerifierApiAdapter::default();
            let mut bundle = bundle_with(vec![obligation(
                ObligationKind::ArithmeticSafety,
                "arith-core-verdict",
            )]);
            let verdict = core_proof_grade_verdict(proof_kind, "arith-core-verdict");
            bundle.metadata.push(
                trust_mc_core_full_verification_verdict_metadata_entry(
                    "arith-core-verdict",
                    &verdict,
                )
                .expect("metadata should serialize"),
            );

            let evidence = adapter.verify(&bundle, &bundle.obligations);

            assert_eq!(evidence.len(), 1);
            assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
            assert_eq!(evidence[0].proof_strength, None);
            assert!(evidence[0].artifacts.is_empty());
            assert!(!evidence[0].has_solver_transcript_artifacts());
            assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
                diagnostic.contains(
                    "serialized trust_mc FullVerificationVerdict metadata is diagnostic-only",
                )
            }));
            assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("not native proof-grade")
                    && diagnostic.contains("missing native typed CHC obligation metadata")
            }));

            let result = run_result_for(&adapter, &bundle, evidence[0].clone());
            assert_eq!(result.status, VerificationRunStatus::Inconclusive);
            assert!(!result.is_fully_proved());
        }
    }

    #[test]
    fn verify_rejects_non_proof_grade_trust_mc_core_verdict_metadata() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let mut bundle = bundle_with(vec![obligation(
            ObligationKind::ArithmeticSafety,
            "arith-router-placeholder",
        )]);
        let obligation = trust_mc_core::MirDerivedChcPdrObligation::router_placeholder(
            "arith-router-placeholder",
            trust_mc_core::MirObligationKind::ArithmeticSafety,
            "(declare-rel entry ())\n(rule entry)\n(query entry)\n",
        );
        let stats = trust_mc_core::ChcPdrStats { relation_count: 1, clause_count: 1 };
        let proof = trust_mc_core::ChcPdrProofEvidence::proof_grade_from_bytes(
            trust_mc_core::ChcPdrProofKind::ChcValidity,
            obligation,
            stats,
            ("ay://chc-pdr/proof-metadata.json", b"solver transcript"),
            ("trust-mc://chc-pdr/replay-log.json", b"replay log"),
            ("trust-mc://chc-pdr/checked-proof-report.json", b"checked report"),
        );
        let verdict = trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
        };
        bundle.obligations[0].metadata.push(
            trust_mc_core_full_verification_verdict_metadata_entry(
                "arith-router-placeholder",
                &verdict,
            )
            .expect("metadata should serialize"),
        );

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(evidence[0].artifacts.is_empty());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("not native proof-grade")
                && diagnostic.contains("router placeholder")
        }));
    }

    #[test]
    fn verify_rejects_mismatched_trust_mc_core_verdict_obligation_id() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let mut bundle = bundle_with(vec![obligation(ObligationKind::Assertion, "assertion-real")]);
        let verdict = core_proof_grade_verdict(
            trust_mc_core::ChcPdrProofKind::ChcValidity,
            "assertion-other",
        );
        bundle.metadata.push(
            trust_mc_core_full_verification_verdict_metadata_entry("assertion-real", &verdict)
                .expect("metadata should serialize"),
        );

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("does not match requested obligation")
                && diagnostic.contains("assertion-other")
        }));
    }

    #[test]
    fn chc_pdr_native_evidence_without_proof_grade_metadata_is_rejected() {
        let obligation_id = native_typed_chc_obligation_id(44, 1);
        for (mut proof, expected_diagnostic) in [
            (
                {
                    let mut proof =
                        proof_grade_chc_pdr(TrustMcChcPdrProofKind::ChcValidity, &obligation_id);
                    proof.metadata.normalized_input_hash = None;
                    proof
                },
                "missing normalized SHA-256 input digest",
            ),
            (
                {
                    let mut proof =
                        proof_grade_chc_pdr(TrustMcChcPdrProofKind::PdrInvariant, &obligation_id);
                    proof.metadata.transcript_hashes.clear();
                    proof
                },
                "missing solver transcript digest metadata",
            ),
            (
                {
                    let mut proof =
                        proof_grade_chc_pdr(TrustMcChcPdrProofKind::PdrInvariant, &obligation_id);
                    proof.artifacts = vec![TrustMcFullVerificationArtifact::new(
                        TrustMcFullVerificationArtifactKind::SolverTranscript,
                        "artifact://trust-mc/solver-transcript.smt2",
                    )];
                    proof
                },
                "missing solver transcript artifact matching transcript digest metadata",
            ),
            (
                {
                    let mut proof =
                        proof_grade_chc_pdr(TrustMcChcPdrProofKind::ChcValidity, &obligation_id);
                    proof.native_metadata = None;
                    proof
                },
                "missing native typed CHC obligation metadata",
            ),
            (
                {
                    let mut proof =
                        proof_grade_chc_pdr(TrustMcChcPdrProofKind::ChcValidity, &obligation_id);
                    proof.metadata.replay_check_status = None;
                    proof
                },
                "missing replay/check status metadata",
            ),
            (
                {
                    let mut proof =
                        proof_grade_chc_pdr(TrustMcChcPdrProofKind::ChcValidity, &obligation_id);
                    proof.metadata.replay_check_status = Some(TrustMcProofReplayCheckStatus {
                        replay: TrustMcProofReplayStatus::Failed,
                        check: TrustMcProofCheckStatus::Accepted,
                    });
                    proof
                },
                "replay/check status must be Replayed/Accepted",
            ),
        ] {
            proof.invariant_count += 1;
            let adapter = TrustMcVerifierApiAdapter::default();
            let bundle = bundle_with(vec![obligation(ObligationKind::Invariant, &obligation_id)]);
            let evidence = adapter.evidence_from_native_full_verifier_evidence(
                &bundle,
                &bundle.obligations[0],
                TrustMcNativeFullVerifierEvidence::ChcPdrProof(Box::new(proof)),
            );

            assert_eq!(evidence.status, EvidenceStatus::Unsupported);
            assert_eq!(evidence.proof_strength, None);
            assert!(!evidence.is_unbounded_proof());
            assert!(
                evidence
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.contains(expected_diagnostic))
            );

            let result = run_result_for(&adapter, &bundle, evidence);
            assert_eq!(result.status, VerificationRunStatus::Inconclusive);
            assert_eq!(result.summary.unsupported, 1);
            let manifest = result.to_manifest();
            assert_eq!(manifest.accepted_evidence, Vec::new());
            assert_eq!(manifest.rejected_evidence.len(), 1);
            assert_eq!(
                manifest.rejected_evidence[0].disposition,
                EvidenceDisposition::RejectedStatus
            );
        }
    }

    #[test]
    fn finite_acyclic_bmc_is_not_treated_as_chc_pdr_evidence() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new()
                .with_bmc_depth(12)
                .with_proof_mode(TrustMcProofMode::FiniteAcyclicBmc),
        );
        let bundle = bundle_with(vec![obligation(ObligationKind::Invariant, "invariant-1")]);

        let evidence = adapter.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert_eq!(evidence[0].proof_strength, None);
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("finite acyclic BMC is BMC-shaped evidence")
                && diagnostic.contains("not ChcPdrProofEvidence")
        }));
    }

    #[test]
    fn bmc_adapter_output_is_rejected_in_run_manifest() {
        for (proof_mode, obligation_kind, obligation_id, expected_diagnostic) in [
            (
                TrustMcProofMode::Bmc,
                ObligationKind::ArithmeticSafety,
                "arith-bmc",
                "bounded BMC at depth 8 is diagnostic-only",
            ),
            (
                TrustMcProofMode::FiniteAcyclicBmc,
                ObligationKind::Invariant,
                "invariant-finite-bmc",
                "finite acyclic BMC is BMC-shaped evidence",
            ),
        ] {
            let adapter = TrustMcVerifierApiAdapter::new(
                TrustMcConfig::new().with_bmc_depth(8).with_proof_mode(proof_mode),
            );
            let bundle = bundle_with(vec![obligation(obligation_kind, obligation_id)]);
            let context = VerifierExecutionContext::new(format!("trust-mc-{obligation_id}"));

            let result = adapter.verify_with_context(&bundle, &bundle.obligations, &context);
            let manifest = result.to_manifest();

            assert_eq!(manifest.accepted_evidence, Vec::new());
            assert_eq!(manifest.rejected_evidence.len(), 1);
            assert_eq!(manifest.rejected_evidence[0].obligation_id, obligation_id);
            assert_eq!(manifest.rejected_evidence[0].status, EvidenceStatus::Unsupported);
            assert_eq!(manifest.rejected_evidence[0].proof_strength, None);
            assert_eq!(
                manifest.rejected_evidence[0].disposition,
                EvidenceDisposition::RejectedStatus
            );
            assert_eq!(
                manifest.rejected_evidence[0].reason,
                "evidence status Unsupported is not a proof"
            );
            assert!(
                result.evidence[0]
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.contains(expected_diagnostic))
            );
        }
    }

    #[test]
    fn native_bmc_diagnostic_evidence_is_rejected() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_bmc_depth(8).with_proof_mode(TrustMcProofMode::Bmc),
        );
        let bundle = bundle_with(vec![obligation(ObligationKind::ArithmeticSafety, "arith-bmc")]);
        let diagnostic = TrustMcDiagnosticOnlyEvidence::new(
            TrustMcFullVerificationProblemKind::Bmc,
            "BmcSuccessDemoted: bounded success is diagnostic-only",
        )
        .with_artifact(
            TrustMcFullVerificationArtifact::new(
                TrustMcFullVerificationArtifactKind::DiagnosticTrace,
                "artifact://trust-mc/bmc-diagnostic.log",
            )
            .with_digest(sha256('d')),
        );

        let evidence = adapter.evidence_from_native_full_verifier_evidence(
            &bundle,
            &bundle.obligations[0],
            TrustMcNativeFullVerifierEvidence::DiagnosticOnly(diagnostic),
        );

        assert_eq!(evidence.status, EvidenceStatus::Unsupported);
        assert_eq!(evidence.proof_strength, None);
        assert!(!evidence.is_unbounded_proof());
        assert_eq!(evidence.artifacts.len(), 1);
        assert_eq!(evidence.artifacts[0].kind, EvidenceArtifactKind::Log);
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("diagnostic-only evidence is not a full proof")
                && diagnostic.contains("BMC")
        }));
        assert!(evidence.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("bounded BMC diagnostic evidence is rejected")
        }));

        let result = run_result_for(&adapter, &bundle, evidence);
        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
        let manifest = result.to_manifest();
        assert_eq!(manifest.accepted_evidence, Vec::new());
        assert_eq!(manifest.rejected_evidence.len(), 1);
        assert_eq!(manifest.rejected_evidence[0].proof_strength, None);
        assert_eq!(manifest.rejected_evidence[0].disposition, EvidenceDisposition::RejectedStatus);
    }

    #[test]
    fn chc_pdr_adapter_output_without_typed_input_has_no_manifest_proof_strength() {
        for (proof_mode, obligation_id, expected_proof_kind) in [
            (TrustMcProofMode::Chc, "assertion-chc", "ChcPdrProofKind::ChcValidity"),
            (TrustMcProofMode::PdrIc3, "assertion-pdr", "ChcPdrProofKind::PdrInvariant"),
        ] {
            let adapter =
                TrustMcVerifierApiAdapter::new(TrustMcConfig::new().with_proof_mode(proof_mode));
            let bundle = bundle_with(vec![obligation(ObligationKind::Assertion, obligation_id)]);
            let context = VerifierExecutionContext::new(format!("trust-mc-{obligation_id}"));

            let result = adapter.verify_with_context(&bundle, &bundle.obligations, &context);
            let manifest = result.to_manifest();

            assert_eq!(manifest.accepted_evidence, Vec::new());
            assert_eq!(manifest.rejected_evidence.len(), 1);
            assert_eq!(manifest.rejected_evidence[0].status, EvidenceStatus::Unsupported);
            assert_eq!(manifest.rejected_evidence[0].proof_strength, None);
            assert_eq!(
                manifest.rejected_evidence[0].disposition,
                EvidenceDisposition::RejectedStatus
            );
            assert!(result.evidence[0].proof_strength.is_none());
            assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
                diagnostic.contains(expected_proof_kind)
                    && diagnostic.contains("live opaque native-bundle authority")
            }));
        }
    }

    #[test]
    fn run_result_is_inconclusive_not_proved() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let bundle = bundle_with(vec![
            obligation(ObligationKind::Assertion, "assertion-1"),
            obligation(ObligationKind::Invariant, "invariant-1"),
            obligation(ObligationKind::ArithmeticSafety, "arith-1"),
            obligation(ObligationKind::Protocol, "protocol-1"),
        ]);
        let context = VerifierExecutionContext::new("trust-mc-run");

        let result = adapter.verify_with_context(&bundle, &bundle.obligations, &context);

        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
        assert_eq!(result.summary.unsupported, bundle.obligations.len());
        assert_eq!(result.summary.proved, 0);
        assert_eq!(result.evidence.len(), bundle.obligations.len());
        assert!(result.skipped.is_empty());
        assert!(!result.is_fully_proved());
    }

    #[test]
    fn bitvector_const_accepts_full_u128_bit_pattern() {
        use serde_json::json;
        let bv = super::trust_mc_typed_chc_bitvector_to_i128;
        // u128::MAX bit pattern -> all ones -> i128 -1 (this is the constant the
        // corpus's folded_multiply ArithmeticSafety VC rejected before the fix).
        assert_eq!(bv(&json!("340282366920938463463374607431768211455"), "bv").unwrap(), -1_i128);
        // i128::MAX + 1 == 2^127 -> i128::MIN bit pattern.
        assert_eq!(bv(&json!("170141183460469231731687303715884105728"), "bv").unwrap(), i128::MIN,);
        // Negatives and in-range signed values keep their natural value.
        assert_eq!(bv(&json!("-1"), "bv").unwrap(), -1_i128);
        assert_eq!(bv(&json!(i128::MAX.to_string()), "bv").unwrap(), i128::MAX);
        // Beyond u128::MAX still fails closed.
        assert!(bv(&json!("340282366920938463463374607431768211456"), "bv").is_err());
        // The strict-i128 parse (now the REAL-constant path) stays STRICT:
        // u128::MAX must NOT wrap to -1. The INT path admits it EXACTLY via
        // `trust_mc_typed_chc_int_const_expr` (see the wide-int tests).
        assert!(
            super::trust_mc_typed_chc_integer_to_i128(
                &json!("340282366920938463463374607431768211455"),
                "real",
            )
            .is_err()
        );
    }

    /// Exact evaluator for the Int-literal trees `trust_mc_typed_chc_int_const_expr`
    /// builds (plain literals and base-10^9 Horner compositions). Checked u128
    /// arithmetic is exact here: every Horner intermediate is a decimal prefix
    /// of the final value, so it never exceeds a value that itself fits u128.
    fn eval_exact_uint(expr: &Expr) -> u128 {
        use ay_bindings::ExprValue;
        match expr.value() {
            ExprValue::IntConst(value) => value
                .to_string()
                .parse::<u128>()
                .expect("wide-int tree literal is non-negative and fits u128"),
            ExprValue::IntAdd(lhs, rhs) => eval_exact_uint(lhs)
                .checked_add(eval_exact_uint(rhs))
                .expect("Horner intermediate stays within u128"),
            ExprValue::IntMul(lhs, rhs) => eval_exact_uint(lhs)
                .checked_mul(eval_exact_uint(rhs))
                .expect("Horner intermediate stays within u128"),
            other => panic!("unexpected node in wide-int literal tree: {other:?}"),
        }
    }

    #[test]
    fn int_const_admits_full_u128_range_exactly() {
        use serde_json::json;
        let int = |value: serde_json::Value| {
            super::trust_mc_typed_chc_int_const_expr(&value, "integer constant")
        };

        // Everything within i128 round-trips as a single plain literal
        // (unchanged behavior): i128::MIN, -1, 0, u64::MAX, i128::MAX.
        for narrow in [i128::MIN, -1, 0, i128::from(u64::MAX), i128::MAX] {
            let expr = int(json!(narrow.to_string())).expect("i128-range constant must parse");
            assert_eq!(expr, Expr::int_const(narrow));
            assert_eq!(expr.sort(), &Sort::int());
        }
        // JSON-number forms take the same plain path.
        assert_eq!(int(json!(42)).unwrap(), Expr::int_const(42_i128));
        assert_eq!(int(json!(-7)).unwrap(), Expr::int_const(-7_i128));
        assert_eq!(int(json!(u64::MAX)).unwrap(), Expr::int_const(i128::from(u64::MAX)));

        // The range the strict parse used to reject (i128::MAX+1 ..= u128::MAX,
        // e.g. the Lcg::range_i128 `#[requires]` bound u128::MAX) is now
        // ADMITTED and must re-encode EXACTLY — never wrap or truncate.
        for wide in [u128::try_from(i128::MAX).expect("i128::MAX fits u128") + 1, u128::MAX] {
            let expr = int(json!(wide.to_string())).expect("u128-range constant must parse");
            assert_eq!(expr.sort(), &Sort::int());
            assert_eq!(eval_exact_uint(&expr), wide, "wide constant must re-encode exactly");
        }
    }

    #[test]
    fn int_const_still_fails_closed_outside_supported_range() {
        use serde_json::json;
        let int = |value: serde_json::Value| {
            super::trust_mc_typed_chc_int_const_expr(&value, "integer constant")
        };
        // u128::MAX + 1: beyond every producer integer type — fail closed.
        let above = int(json!("340282366920938463463374607431768211456")).unwrap_err();
        assert!(above.contains("outside the supported mathematical integer constant range"));
        // i128::MIN - 1: no producer emits negatives below i128 — fail closed.
        assert!(int(json!("-170141183460469231731687303715884105729")).is_err());
        // Malformed text, empty strings, and non-integer JSON keep failing
        // closed with the pre-existing error shapes.
        assert!(int(json!("not-a-number")).is_err());
        assert!(int(json!("")).unwrap_err().contains("must not be empty"));
        assert!(int(json!(1.5)).unwrap_err().contains("integer number or decimal string"));
        assert!(int(json!(true)).unwrap_err().contains("integer number or decimal string"));
    }

    #[test]
    fn typed_chc_expr_json_wide_int_constant_lowers_end_to_end() {
        use serde_json::json;
        // The exact wire shape the compiler producer emits for a u128-width
        // `#[requires]` type-range bound: `trust_mc_typed_chc_expr_from_trust_spec`
        // passes the `TrustSpecExprKind::IntLiteral` decimal string through
        // VERBATIM as `{"kind":"int_const","value":"<decimal>"}`.
        let mut var_sorts = BTreeMap::new();
        var_sorts.insert("n".to_string(), Sort::int());
        let input: TrustMcTypedChcExprInput = serde_json::from_value(json!({
            "kind": "binary",
            "op": "le",
            "lhs": { "kind": "var", "name": "n", "sort": { "kind": "int" } },
            "rhs": { "kind": "int_const", "value": "340282366920938463463374607431768211455" },
        }))
        .expect("wide-constant comparison should deserialize");

        let expr = input.to_trust_mc_expr(&var_sorts).expect("wide-constant comparison must lower");
        assert_eq!(expr.sort(), &Sort::bool());
        let ay_bindings::ExprValue::IntLe(_, rhs) = expr.value() else {
            panic!("expected an IntLe root, got {:?}", expr.value());
        };
        assert_eq!(eval_exact_uint(rhs), u128::MAX, "rhs must be the exact u128::MAX value");
    }

    #[test]
    fn int_to_bv_lowers_with_width_and_fails_closed_on_bad_params() {
        let unary = super::trust_mc_typed_chc_unary_expr;
        let int_var = || Expr::var("x".to_string(), Sort::int());
        let op = TrustMcTypedChcUnaryOpInput::IntToBv;
        // Happy path: an Int operand + `width` yields a bitvec-sorted expr.
        let bv = unary(op, int_var(), None, None, None, Some(8), None).unwrap();
        assert_eq!(bv.sort(), &Sort::bitvec(8));
        // Missing width, zero width, and a foreign operator param all fail closed.
        assert!(unary(op, int_var(), None, None, None, None, None).is_err());
        assert!(unary(op, int_var(), None, None, None, Some(0), None).is_err());
        assert!(unary(op, int_var(), None, None, None, Some(8), Some(true)).is_err());
        // Sort mismatch (Bool operand) is an error, not a coercion.
        assert!(
            unary(op, Expr::var("b".to_string(), Sort::bool()), None, None, None, Some(8), None)
                .is_err()
        );
    }

    #[test]
    fn bv_to_int_threads_signedness_and_fails_closed_on_bad_params() {
        let unary = super::trust_mc_typed_chc_unary_expr;
        let bv_var = || Expr::var("x".to_string(), Sort::bitvec(8));
        let op = TrustMcTypedChcUnaryOpInput::BvToInt;
        // Both signedness modes lower to Int-sorted exprs…
        let unsigned = unary(op, bv_var(), None, None, None, None, Some(false)).unwrap();
        let signed = unary(op, bv_var(), None, None, None, None, Some(true)).unwrap();
        assert_eq!(unsigned.sort(), &Sort::int());
        assert_eq!(signed.sort(), &Sort::int());
        // …and the flag is load-bearing: bv2int vs bv2int_signed are distinct
        // (a top-bit-set byte must read 255 unsigned, never -1).
        assert_ne!(unsigned, signed);
        // Missing `signed` and a foreign operator param fail closed.
        assert!(unary(op, bv_var(), None, None, None, None, None).is_err());
        assert!(unary(op, bv_var(), None, None, None, Some(8), Some(true)).is_err());
        // Sort mismatch (Int operand) is an error.
        assert!(
            unary(op, Expr::var("i".to_string(), Sort::int()), None, None, None, None, Some(false))
                .is_err()
        );
    }

    #[test]
    fn parameterless_unary_ops_reject_conversion_params() {
        // The width/signed params are exclusive to int_to_bv/bv_to_int: any other
        // unary op carrying them is a producer bug and must fail closed.
        let unary = super::trust_mc_typed_chc_unary_expr;
        let bool_var = || Expr::var("b".to_string(), Sort::bool());
        assert!(
            unary(TrustMcTypedChcUnaryOpInput::Not, bool_var(), None, None, None, Some(8), None)
                .is_err()
        );
        assert!(
            unary(TrustMcTypedChcUnaryOpInput::Not, bool_var(), None, None, None, None, Some(true))
                .is_err()
        );
    }

    #[test]
    fn typed_chc_expr_json_parses_int_bv_conversions_end_to_end() {
        use serde_json::json;
        // The wire shape the rustc_mir_transform producer emits: internally
        // tagged, snake_case ops, conversion params inline on the unary node.
        let mut var_sorts = BTreeMap::new();
        var_sorts.insert("n".to_string(), Sort::int());
        var_sorts.insert("w".to_string(), Sort::bitvec(8));

        let int_to_bv: TrustMcTypedChcExprInput = serde_json::from_value(json!({
            "kind": "unary",
            "op": "int_to_bv",
            "expr": { "kind": "var", "name": "n", "sort": { "kind": "int" } },
            "width": 8,
        }))
        .unwrap();
        assert_eq!(int_to_bv.to_trust_mc_expr(&var_sorts).unwrap().sort(), &Sort::bitvec(8));

        let bv_to_int: TrustMcTypedChcExprInput = serde_json::from_value(json!({
            "kind": "unary",
            "op": "bv_to_int",
            "expr": { "kind": "var", "name": "w", "sort": { "kind": "bit_vec", "width": 8 } },
            "signed": false,
        }))
        .unwrap();
        assert_eq!(bv_to_int.to_trust_mc_expr(&var_sorts).unwrap().sort(), &Sort::int());

        // A payload missing its conversion param parses (serde defaults) but
        // fails closed at lowering.
        let missing_width: TrustMcTypedChcExprInput = serde_json::from_value(json!({
            "kind": "unary",
            "op": "int_to_bv",
            "expr": { "kind": "var", "name": "n", "sort": { "kind": "int" } },
        }))
        .unwrap();
        assert!(missing_width.to_trust_mc_expr(&var_sorts).is_err());
    }
}
