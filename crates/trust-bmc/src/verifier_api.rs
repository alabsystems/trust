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
    ReasoningKind, SourceLocation, SupportLevel, TrustContract, TrustContractBundle,
    TrustObligation, ValidatedVerificationRequest, VerificationEngine,
};

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
mod kernel_replay_admission;
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
mod native_bundle_stop;
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
use native_bundle_stop::NativeBundleTransportError;

#[cfg(all(test, feature = "trust-mc-native-trust-ir-bundle"))]
mod raw_source_stop_tests;

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

// Producer attestation about the FIDELITY of the submitted typed `ChcVc` to the
// body it claims to encode.
//
// This is the consumer's side of the boundary
// `trust_mc_core::ChcPdrEncodingConcreteness` explicitly declines: that
// attestation covers only the `ChcVc` -> solver-problem lowering trust_mc
// itself performs, and its own SCOPE note says the ChcVc-PRODUCTION stage
// "belongs to the producer of the obligation, and consumers must account for it
// on their own side of the boundary". Nothing accounted for it, so a
// producer-side over-approximation reached the refutation gate wearing a
// perfectly valid trust_mc-stage exactness attestation.
//
// The compiler emits the positive value only for its admitted flat typed-VC
// fragment. It covers that submitted ChcVc, not the separate source-to-native
// TrustIR translation. Absence is "unattested", never "attested exact". A native
// bundle needs its own independently checked source correspondence; this flat
// annotation cannot provide it. Like the lowering-status key this is
// deliberately NOT in
// `TRUST_IR_NATIVE_TRANSPORT_METADATA_KEYS`, so it sits inside the obligation's
// canonical public semantic digest and cannot be detached from the row.
const TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_METADATA_KEY: &str =
    "trust-trust-mc.typed-chc-obligation.encoding_fidelity";
/// Positive producer attestation that the submitted `ChcVc` is exact for the
/// source obligation on the admitted flat typed-VC route. It does not attest
/// source-to-native-TrustIR correspondence.
#[cfg(feature = "trust-mc-native-solver")]
const TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_EXACT: &str = "exact";
/// The compiler fell back to the flattened single-formula typed CHC (one
/// nullary `error` relation, one constraint-only rule) for a body whose CFG has
/// a BACK EDGE. Such a formula has no loop transition relation at all, so the
/// loop-carried locals appear in it as free variables with no defining
/// constraint: it OVER-APPROXIMATES the reachable states.
#[cfg(feature = "trust-mc-native-solver")]
const TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_LOOP_ELIDED: &str = "loop_elided_over_approximation";

/// Whether a solver-level `Refuted` on a typed trust_mc CHC may be credited as
/// a public counterexample, judged on the ONE question
/// `ChcPdrEncodingConcreteness` cannot answer: is the submitted `ChcVc` faithful
/// to the body?
///
/// Direction of soundness, and why this is asymmetric with the proof direction:
/// an over-approximating encoding (extra models) is SOUND FOR PROOFS — UNSAT of
/// a superset implies UNSAT of the real reachable set — and UNSOUND AS EVIDENCE
/// FOR REFUTATIONS, because a model of the superset need not be a real
/// execution. So this gate may only ever move a row FAILED -> Unknown; it is
/// never consulted on the Proved path, and `trust_mc_chc_credit_witness` is
/// deliberately left alone.
#[cfg(feature = "trust-mc-native-solver")]
#[derive(Debug, Clone, PartialEq, Eq)]
enum TrustMcChcRefutationAdmissibility {
    /// No producer fidelity attestation rides on this row.
    Unattested,
    /// The producer explicitly attests the complete source-to-ChcVc edge.
    ProducerAttestedExact,
    /// Flat typed-VC exactness does not establish the native source relation.
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    FlatExactDoesNotCoverNativeSource,
    /// The producer attests the submitted `ChcVc` over-approximates the body.
    /// A refutation of it is a refutation of the ENCODING, not of the program.
    ProducerAttestedOverApproximation { class: String },
}

#[cfg(feature = "trust-mc-native-solver")]
impl TrustMcChcRefutationAdmissibility {
    /// Read the flat typed-VC attestation off one authenticated public obligation.
    ///
    /// Fails closed on an UNRECOGNIZED value: a future producer class this
    /// consumer does not understand is treated as an over-approximation, so a
    /// new encoding family cannot acquire refutation authority merely by being
    /// unknown here.
    ///
    /// Fails closed on AMBIGUITY too, and deliberately does not reuse
    /// `metadata_value`: that helper answers a duplicated key with `None`, which
    /// here would read as "no attestation" and hand a disclaimed encoding its
    /// refutation authority back. Duplicate keys are rejected by bundle
    /// validation — but that runs later, inside the witness validator this gate
    /// is checked BEFORE, so it cannot be relied on here.
    fn for_obligation(obligation: &TrustObligation) -> Self {
        let mut attested = obligation
            .metadata
            .iter()
            .filter(|entry| entry.key == TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_METADATA_KEY)
            .map(|entry| entry.value.as_str())
            .peekable();
        let Some(class) = attested.next() else {
            return Self::Unattested;
        };
        if attested.peek().is_some() {
            return Self::ProducerAttestedOverApproximation {
                class: "<ambiguous: the row carries more than one encoding-fidelity attestation>"
                    .to_string(),
            };
        }
        if class == TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_EXACT {
            Self::ProducerAttestedExact
        } else {
            Self::ProducerAttestedOverApproximation { class: class.to_string() }
        }
    }

    /// The public flat-VC annotation is not a native source-correspondence
    /// capability. No production issuer currently establishes that separate
    /// relation, so even an exact flat row must decline native refutation credit.
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn for_native_obligation(obligation: &TrustObligation) -> Self {
        match Self::for_obligation(obligation) {
            Self::ProducerAttestedExact => Self::FlatExactDoesNotCoverNativeSource,
            other => other,
        }
    }

    /// `Some(reason)` when a `Refuted` verdict on this row must be demoted.
    fn rejection_reason(&self) -> Option<String> {
        match self {
            Self::Unattested => Some(
                "the submitted ChcVc has no positive producer fidelity attestation; fresh solver-level replay proves only the encoded request, not correspondence to the source obligation"
                    .to_string(),
            ),
            Self::ProducerAttestedExact => None,
            #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
            Self::FlatExactDoesNotCoverNativeSource => Some(
                "the exact annotation covers the flat typed ChcVc only; native TrustIR refutation lacks independently checked per-obligation source correspondence, so exact encoded-query replay cannot authorize a Rust counterexample"
                    .to_string(),
            ),
            Self::ProducerAttestedOverApproximation { class }
                if class == TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_LOOP_ELIDED =>
            {
                // The clause "for a body whose CFG has a back edge" used to be
                // stated here as a FACT about the body. It is not one, and it
                // misdescribed the common case. The producer sets this class
                // whenever it cannot establish that the enriched encoding fired
                // — deliberately, because the disclosure only ever REMOVES
                // refutation authority, so over-disclosing costs a
                // counterexample while under-disclosing admits a false
                // refutation against correct code (see the fail-open removal of
                // 2026-08-08 in `trust_verify.rs`). A STRAIGHT-LINE body is
                // disclosed too, and for `double` the disclosure is FALSE — measured
                // 2026-09-26 on
                // `fn double(x: i32) -> i32 requires .. ensures result == x * 3
                // { x * 2 }`, whose MIR is `bb0 -> bb1` with no back edge and whose
                // genuine refutation this class demoted to Unknown. That `_0` really is
                // determined is settled by `r06`, the SAME body with the TRUE clause,
                // which passes `-Ztrust-policy=certify` with "3 proved, 0 unknown,
                // 0 runtime-checked"; a formula leaving `_0` free cannot prove
                // `_0 == x * 2`. The producer-side cause is an aliasing deadlock in
                // `typed_chc_return_depends_on_elided_definition`, and three attempts at
                // repairing it were measured and reverted — see the comment there before
                // trying a fourth.
                //
                // IT CHANGES NOTHING HERE EITHER WAY. A stamped row and an unstamped row
                // both demote: absence reads as `Unattested`, which this same match arm
                // rejects. Only the positive `exact` value admits a refutation, and the
                // compiler is forbidden to emit it (see this type's header). Battery row
                // `r07_rust_contract_refuted_strict`,
                // `docs/issues/2026-09-26-chc-refutation-authority-is-fail-closed-by-design.md`.
                Some(
                    "the compiler attests the submitted ChcVc is an over-approximation: it fell back to the flattened single-formula typed CHC (one nullary `error` relation, one constraint-only rule) rather than establishing that the enriched encoding fired. Where the body's CFG has a back edge the loop carries no transition relation and its loop-carried locals are free variables with no defining constraint; the producer also attests this class when it cannot tell, including for a straight-line body, because the attestation only ever removes refutation authority"
                        .to_string(),
                )
            }
            Self::ProducerAttestedOverApproximation { class } => Some(format!(
                "the compiler attests a non-exact ChcVc encoding class `{class}` this consumer does not recognize; an unrecognized fidelity class fails closed"
            )),
        }
    }
}

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

fn trust_native_debug_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var("TRUST_NATIVE_DEBUG").is_ok())
}

fn trust_seal_elig_trace_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("TRUST_SEAL_ELIG_TRACE").is_some())
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
    if !obligation.obligation_id.ends_with(":assertion:panic-freedom:0") {
        return false;
    }
    let trust_verifier_api::BundleSubject::Function { crate_name, path } = &bundle.subject else {
        return false;
    };
    let debug_enabled = trust_native_debug_enabled();
    if !debug_enabled
        && (obligation.kind != ObligationKind::Assertion
            || obligation.contract_id.is_some()
            || obligation.proof_item_id.is_some()
            || obligation.required_strength.is_some()
            || !obligation.summary_facts.is_empty())
    {
        return false;
    }
    let expected_id = format!(
        "vc:{}:assertion:panic-freedom:0",
        trust_types::canonical_artifact_id_component(path)
    );
    // DIAGNOSTIC (pure, no behavior change): when this obligation LOOKS like the
    // whole-function panic-freedom aggregate but the strict gate below rejects
    // it, name the offending clause + dump metadata keys so the 339-merge drift
    // (allowlist / schema) is identified without guessing.
    if debug_enabled {
        let key_allowed = |k: &str| {
            matches!(
                k,
                trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY
                    | TRUST_MC_PANIC_FREEDOM_OBLIGATION_METADATA_KEY
                    | "trust.vc.kind"
                    | TRUST_SOURCE_DIGEST_METADATA_KEY
                    | TRUST_VC_DIGEST_METADATA_KEY
                    | "trust-trust-mc.typed-chc-obligation.lowering_status"
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
        };
        let all_keys: Vec<&str> = obligation.metadata.iter().map(|e| e.key.as_str()).collect();
        let offending_keys: Vec<&str> =
            all_keys.iter().copied().filter(|k| !key_allowed(k)).collect();
        let ctx_present = metadata_value(
            &obligation.metadata,
            trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY,
        );
        let ctx_parse = ctx_present.and_then(|encoded| {
            trust_types::json_depth::from_str_deep::<trust_verifier_api::ObligationContext>(encoded)
                .ok()
        });
        eprintln!(
            "[PF_GATE_DIAG] id={} id_ok={} kind_ok={} contract_none={} proof_item_none={} strength_none={} summary_empty={} panic_enabled={} vckind_ok={} src_digest_ok={} vc_digest_ok={} no_formula_schema={} no_formula_payload={} ctx_present={} ctx_parses={} has_current_schema={} producer_ok={} function_ok={} origin_ok={} offending_keys={:?} all_keys={:?}",
            obligation.obligation_id,
            obligation.obligation_id == expected_id,
            obligation.kind == ObligationKind::Assertion,
            obligation.contract_id.is_none(),
            obligation.proof_item_id.is_none(),
            obligation.required_strength.is_none(),
            obligation.summary_facts.is_empty(),
            metadata_value(&obligation.metadata, TRUST_MC_PANIC_FREEDOM_OBLIGATION_METADATA_KEY) == Some("enabled"),
            metadata_value(&obligation.metadata, "trust.vc.kind") == Some("panic_freedom"),
            metadata_value(&obligation.metadata, TRUST_SOURCE_DIGEST_METADATA_KEY).is_some_and(is_lowercase_sha256_hex),
            metadata_value(&obligation.metadata, TRUST_VC_DIGEST_METADATA_KEY).is_some_and(is_lowercase_sha256_hex),
            metadata_value(&obligation.metadata, TRUST_VC_FORMULA_SCHEMA_METADATA_KEY).is_none(),
            metadata_value(&obligation.metadata, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY).is_none(),
            ctx_present.is_some(),
            ctx_parse.is_some(),
            ctx_parse.as_ref().map(|c| c.has_current_schema()).unwrap_or(false),
            ctx_parse.as_ref().map(|c| matches!(&c.producer, trust_verifier_api::ObligationProducer::CompilerMirExtract)).unwrap_or(false),
            ctx_parse.as_ref().and_then(|c| c.function.as_ref()).map(|f| f.crate_name == crate_name.as_str() && f.path == path.as_str()).unwrap_or(false),
            ctx_parse.as_ref().map(|c| matches!(&c.origin, trust_verifier_api::ObligationOrigin::VerificationCondition { vc_kind, vc_index: 0, formula_schema: None } if vc_kind == "panic_freedom")).unwrap_or(false),
            offending_keys,
            all_keys,
        );
    }
    if obligation.obligation_id != expected_id
        || obligation.kind != ObligationKind::Assertion
        || obligation.contract_id.is_some()
        || obligation.proof_item_id.is_some()
        || obligation.required_strength.is_some()
        || !obligation.summary_facts.is_empty()
    {
        return false;
    }

    #[derive(Clone, Copy)]
    enum MetaSlot<'a> {
        Absent,
        Unique(&'a str),
        Duplicate,
    }
    impl<'a> MetaSlot<'a> {
        fn record(&mut self, value: &'a str) {
            *self = match *self {
                Self::Absent => Self::Unique(value),
                Self::Unique(_) | Self::Duplicate => Self::Duplicate,
            };
        }
        fn unique(self) -> Option<&'a str> {
            match self {
                Self::Unique(v) => Some(v),
                Self::Absent | Self::Duplicate => None,
            }
        }
    }

    let mut panic_enabled = MetaSlot::Absent;
    let mut vc_kind = MetaSlot::Absent;
    let mut src_digest = MetaSlot::Absent;
    let mut vc_digest = MetaSlot::Absent;
    let mut ctx_encoded = MetaSlot::Absent;
    for entry in &obligation.metadata {
        match entry.key.as_str() {
            trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY => {
                ctx_encoded.record(entry.value.as_str());
            }
            TRUST_MC_PANIC_FREEDOM_OBLIGATION_METADATA_KEY => {
                panic_enabled.record(entry.value.as_str());
            }
            "trust.vc.kind" => {
                vc_kind.record(entry.value.as_str());
            }
            TRUST_SOURCE_DIGEST_METADATA_KEY => {
                src_digest.record(entry.value.as_str());
            }
            TRUST_VC_DIGEST_METADATA_KEY => {
                vc_digest.record(entry.value.as_str());
            }
            TRUST_MC_TYPED_CHC_LOWERING_STATUS_METADATA_KEY
            | TRUST_MC_TYPED_CHC_UNSUPPORTED_REASON_METADATA_KEY
            | TRUST_MC_TYPED_CHC_SYNTHETIC_CONTRACT_METADATA_KEY
            | TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_METADATA_KEY
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
            | "trust.trust_ir.native.artifact_fingerprint" => {}
            _ => return false,
        }
    }
    if panic_enabled.unique() != Some("enabled")
        || vc_kind.unique() != Some("panic_freedom")
        || !src_digest.unique().is_some_and(is_lowercase_sha256_hex)
        || !vc_digest.unique().is_some_and(is_lowercase_sha256_hex)
    {
        return false;
    }

    let Some(encoded) = ctx_encoded.unique() else {
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
    trust_verifier_api::native_routing_identity::PROOF_KEY;
const TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY: &str =
    trust_verifier_api::native_routing_identity::REQUEST_KEY;
const TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY: &str =
    trust_verifier_api::native_routing_identity::SUITE_KEY;
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
const TRUST_VC_FORMULA_SMTLIB_METADATA_KEY: &str = "trust.vc.formula.smtlib2";
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
const TRUST_VC_FORMULA_SORT_METADATA_KEY: &str = "trust.vc.formula.sort";
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
const TRUST_IR_OBLIGATION_SOURCE_FORMULA_SCHEMA: &str = "trust.trust_ir.obligation-source.v1";
// Aliased from the owning vocabulary crate, never re-declared: a local
// spelling could drift from the admitted list and split the hardened lane.
use trust_verifier_api::TRUST_VC_HARDENED_OBLIGATION_NAMESPACE as TRUST_VC_HARDENED_NAMESPACE;
const TRUST_VC_HARDENED_WILDCARD: &str = "*";

/// Recognize the exact typed E4/E5 violation envelope consumed by the native
/// reachability lane. Every E4/E5 row is TrustMC-owned; rows without this
/// envelope decline fail-closed rather than changing owners.
fn is_typed_body_aware_e4_e5_obligation(obligation: &TrustObligation) -> bool {
    matches!(obligation.kind, ObligationKind::LoopInvariant | ObligationKind::Termination)
        && typed_spec_predicate_envelope(obligation).is_some()
}

/// The fresh-exact receipt lane's admission: every current compiler-authenticated
/// standalone formula kind owned by TrustMC, plus only the body-aware
/// POSTCONDITION rows whose NEGATED CLAUSE references the return slot.
///
/// The discriminator is a deliberate scoping decision: a postcondition whose
/// clause never mentions the post-state does not constrain the body — it is
/// a ∀-params statement that belongs to the tautology/kernel lanes, and the E9
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
    let Some(predicate) = seal_eligible_compiler_formula_predicate(obligation) else {
        return false;
    };
    if matches!(obligation.kind, ObligationKind::Postcondition) {
        return typed_spec_terminal_negated_clause_references_return_slot(&predicate.root);
    }
    true
}

/// Classify an obligation into `(exact_e4_e5_formula_lane, exact_standalone_formula_fresh_lane)`
/// with at most one `TrustSpecPredicate` + `ObligationContext` JSON parse.
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
fn classify_direct_formula_lanes(obligation: &TrustObligation) -> (bool, bool) {
    match obligation.kind {
        ObligationKind::LoopInvariant | ObligationKind::Termination => {
            (typed_spec_predicate_envelope(obligation).is_some(), false)
        }
        ObligationKind::Assertion
        | ObligationKind::ArithmeticSafety
        | ObligationKind::Precondition
        | ObligationKind::Postcondition => {
            (false, is_typed_body_aware_exact_direct_obligation(obligation))
        }
        _ => (false, false),
    }
}

/// Whether the compiler-authenticated terminal negated clause references the
/// canonical return slot (`Result`, `_0`, a versioned `_0#<token>`, or a
/// projected `_0.<field>` spelling).
///
/// Compiler formula payloads prepend body definitions along an `And` spine and
/// put the actual negated VC at its terminal/rightmost leaf. Inspecting every
/// `Not` subtree would let a negated body fact smuggle an otherwise result-free
/// postcondition into the receipt lane, so only that terminal `Not(clause)` is
/// authoritative here.
fn typed_spec_terminal_negated_clause_references_return_slot(
    root: &trust_verifier_api::TrustSpecExpr,
) -> bool {
    use trust_verifier_api::TrustSpecExprKind as Kind;
    let mut terminal = root;
    while let Kind::Binary { op: trust_verifier_api::TrustSpecBinaryOp::And, rhs, .. } =
        &terminal.kind
    {
        terminal = rhs;
    }
    let Kind::Unary { op: trust_verifier_api::TrustSpecUnaryOp::Not, expr: clause } =
        &terminal.kind
    else {
        return false;
    };
    typed_spec_expr_references_return_slot(clause)
}

/// Return-slot search scoped to an already authenticated postcondition clause.
fn typed_spec_expr_references_return_slot(expr: &trust_verifier_api::TrustSpecExpr) -> bool {
    use trust_verifier_api::TrustSpecExprKind as Kind;
    let is_return_slot = |name: &str| {
        let base = name.split('#').next().unwrap_or(name);
        base == "_0" || base.starts_with("_0.")
    };
    match &expr.kind {
        Kind::Variable { name } => is_return_slot(name),
        Kind::Result => true,
        Kind::BoolLiteral { .. } | Kind::IntLiteral { .. } | Kind::BitVecLiteral { .. } => false,
        Kind::Unary { expr, .. }
        | Kind::Old { expr }
        | Kind::BvUnary { expr, .. }
        | Kind::BvFromInt { expr, .. }
        | Kind::IntFromBv { expr, .. } => typed_spec_expr_references_return_slot(expr),
        Kind::Binary { lhs, rhs, .. } | Kind::BvBinary { lhs, rhs, .. } => {
            typed_spec_expr_references_return_slot(lhs)
                || typed_spec_expr_references_return_slot(rhs)
        }
        Kind::Field { base, .. } => typed_spec_expr_references_return_slot(base),
        Kind::Index { base, index } => {
            typed_spec_expr_references_return_slot(base)
                || typed_spec_expr_references_return_slot(index)
        }
        Kind::Quantifier { body, .. } => typed_spec_expr_references_return_slot(body),
        Kind::IsVariant { scrutinee, .. } | Kind::VariantField { scrutinee, .. } => {
            typed_spec_expr_references_return_slot(scrutinee)
        }
        // Future vocabulary fails CLOSED out of the postcondition lane.
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

/// Seal-eligible compiler-authenticated formula obligations for the exact
/// per-obligation independent-replay mint.
///
/// This is [`is_typed_body_aware_e4_e5_obligation`] with the obligation-kind
/// set widened to exactly the non-custom VC kinds for which the compiler can
/// emit a direct typed CHC with the identical `¬formula ∧ body_defs` shape.
/// Every non-kind
/// authentication check below is byte-identical to the E4/E5 predicate: the
/// current `TrustSpecPredicate` formula schema, a parseable Bool-sorted
/// predicate that `validate()`s, and a current compiler
/// `VerificationCondition` VC origin (`CompilerMirExtract`). A formula-less
/// obligation of ANY of these kinds still returns `false` here, so it can never
/// reach the mint. Widening this routing label does NOT relax the mint itself:
/// admission still requires the unchanged fresh-exact re-lowering plus
/// `validate_external_invariant_model == Ok(true)` independent replay on the
/// obligation's OWN authenticated CHC. It also never enables whole-function
/// transport substitution — a formula-carrying obligation is `Ok(Some)` on its
/// own direct CHC, or fails closed to `Unsupported` on `Ok(None)`; it is never
/// deferrable to the panic-freedom transport.
fn seal_eligible_compiler_formula_predicate(
    obligation: &TrustObligation,
) -> Option<trust_verifier_api::TrustSpecPredicate> {
    let result = if matches!(
        obligation.kind,
        ObligationKind::LoopInvariant
            | ObligationKind::Termination
            | ObligationKind::Assertion
            | ObligationKind::ArithmeticSafety
            | ObligationKind::Precondition
            | ObligationKind::Postcondition
    ) {
        typed_spec_predicate_envelope(obligation)
    } else {
        None
    };
    // DIAGNOSTIC (TRUST_SEAL_ELIG_TRACE): reads only; for the LCG cluster prints
    // the per-check verdict so the exact ineligibility reason is observable.
    if trust_seal_elig_trace_enabled() && result.is_none() {
        let ctx = metadata_value(
            &obligation.metadata,
            trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY,
        )
        .unwrap_or("");
        let schema = metadata_value(&obligation.metadata, TRUST_VC_FORMULA_SCHEMA_METADATA_KEY)
            .unwrap_or("<none>");
        if matches!(
            obligation.kind,
            ObligationKind::Postcondition
                | ObligationKind::Precondition
                | ObligationKind::Assertion
                | ObligationKind::ArithmeticSafety
        ) {
            let ctx_digest: String = ctx.chars().take(110).collect();
            let kind_ok = matches!(
                obligation.kind,
                ObligationKind::LoopInvariant
                    | ObligationKind::Termination
                    | ObligationKind::Assertion
                    | ObligationKind::ArithmeticSafety
                    | ObligationKind::Precondition
                    | ObligationKind::Postcondition
            );
            let payload =
                metadata_value(&obligation.metadata, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY);
            let parse_ok = payload.is_some_and(|p| {
                trust_types::json_depth::from_str_deep::<trust_verifier_api::TrustSpecPredicate>(p).is_ok()
            });
            let (has_sch, root_bool, valid, origin) = payload
                .and_then(|p| {
                    trust_types::json_depth::from_str_deep::<
                            trust_verifier_api::TrustSpecPredicate,
                        >(p)
                        .ok()
                })
                .map(|pr| {
                    (
                        pr.has_current_schema(),
                        pr.root_sort == trust_verifier_api::TrustSpecSort::Bool
                            && pr.root.sort == trust_verifier_api::TrustSpecSort::Bool,
                        pr.validate().is_ok(),
                        has_current_compiler_vc_origin(obligation),
                    )
                })
                .unwrap_or((false, false, false, false));
            eprintln!(
                "[SEAL_ELIG] ctx={ctx_digest:?} kind={:?} kind_ok={kind_ok} schema={schema:?} schema_ok={} payload={} parse_ok={parse_ok} has_current_schema={has_sch} root_bool={root_bool} validate_ok={valid} vc_origin={origin}",
                obligation.kind,
                schema == trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION,
                payload.is_some(),
            );
        }
    }
    result
}

#[cfg_attr(not(test), allow(dead_code))]
fn is_seal_eligible_compiler_formula_obligation(obligation: &TrustObligation) -> bool {
    seal_eligible_compiler_formula_predicate(obligation).is_some()
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

/// Preserve kind-stable v6/D3 ownership without widening direct proof input.
///
/// Loop/termination rows belong to TrustMC even when malformed or incomplete,
/// but only the compiler's current, validated Bool violation envelope may
/// enter a direct solve. A caller-supplied typed contract cannot replace that
/// public producer-authenticated formula.
fn owned_e4_e5_pre_solve_rejection(obligation: &TrustObligation) -> Option<String> {
    if matches!(obligation.kind, ObligationKind::LoopInvariant | ObligationKind::Termination)
        && !is_typed_body_aware_e4_e5_obligation(obligation)
    {
        Some(format!(
            "trust-mc owns {:?} obligations under v6/D3, but this row is missing one current compiler-authenticated E4/E5 Bool formula envelope; rejected before direct solving and refusing any caller-supplied typed contract",
            obligation.kind
        ))
    } else {
        None
    }
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

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
mod whole_function_receipt;

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
mod native_refutation;
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
pub use whole_function_receipt::{
    FreshWholeFunctionChcPdrBundleSeal, FreshWholeFunctionChcPdrReceipt,
};

/// Public native-bundle evidence and two distinct affine receipt families.
///
/// Whole-function transport rows never appear in `fresh_exact_direct_receipts`:
/// that map contains only standalone exact-formula rows. The separate whole-
/// function map retains exact aggregate membership and source-authorized native
/// body/query authority; it can never stand in for a direct formula proof.
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
#[derive(Debug)]
pub struct NativeTrustIrBundleEvidenceWithFreshReceipts {
    pub evidence: Vec<ObligationEvidence>,
    pub fresh_exact_direct_receipts: BTreeMap<String, FreshExactDirectChcPdrReceipt>,
    pub fresh_whole_function_receipts: BTreeMap<String, FreshWholeFunctionChcPdrReceipt>,
}

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
impl From<Vec<ObligationEvidence>> for NativeTrustIrBundleEvidenceWithFreshReceipts {
    fn from(evidence: Vec<ObligationEvidence>) -> Self {
        Self {
            evidence,
            fresh_exact_direct_receipts: BTreeMap::new(),
            fresh_whole_function_receipts: BTreeMap::new(),
        }
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
    if !fresh_exact_direct_receipts.is_empty() {
        let mut public_row_summaries =
            std::collections::HashMap::<&str, (usize, bool)>::with_capacity(evidence.len());
        for row in &evidence {
            let summary =
                public_row_summaries.entry(row.obligation_id.as_str()).or_insert((0, false));
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
    }
    NativeTrustIrBundleEvidenceWithFreshReceipts {
        evidence,
        fresh_exact_direct_receipts,
        fresh_whole_function_receipts: BTreeMap::new(),
    }
}

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
fn finalize_native_bundle_evidence_with_whole_function_receipts(
    evidence: Vec<ObligationEvidence>,
    direct: BTreeMap<String, FreshExactDirectChcPdrReceipt>,
    mut whole: BTreeMap<String, FreshWholeFunctionChcPdrReceipt>,
) -> NativeTrustIrBundleEvidenceWithFreshReceipts {
    let mut outcome = finalize_native_bundle_evidence_with_fresh_receipts(evidence, direct);
    if !whole.is_empty() {
        let mut exact_rows =
            std::collections::HashMap::<&str, Vec<&ObligationEvidence>>::with_capacity(
                outcome.evidence.len(),
            );
        for row in &outcome.evidence {
            exact_rows.entry(row.obligation_id.as_str()).or_default().push(row);
        }
        whole.retain(|id, receipt| {
            id == receipt.public_obligation_id()
                && exact_rows.get(id.as_str()).is_some_and(
                    |rows| matches!(rows.as_slice(), [row] if receipt.matches_native_evidence(row)),
                )
        });
    }
    outcome.fresh_whole_function_receipts = whole;
    outcome
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
                "fresh exact-direct receipt requires an admitted current compiler-authenticated standalone typed formula"
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
                "fresh exact-direct receipt requires an admitted current compiler-authenticated standalone typed formula"
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
    /// Trust (2026-10-17, gate-rca deadline): the native solve cutoff — no solve STARTS
    /// after it and a running one is clamped to it — while every live receipt stays
    /// bound to the caller's dispatch deadline ([`Self::with_solve_cutoff`]).
    #[cfg_attr(
        not(any(feature = "trust-mc-native-solver", feature = "trust-mc-native-trust-ir-bundle")),
        allow(dead_code)
    )]
    solve_cutoff: Option<std::time::Instant>,
}

#[cfg(test)]
std::thread_local! {
    static TYPED_CHC_INPUT_LOOKUP_COUNT_FOR_TEST: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
}

// How many whole-bundle consumer translations this thread ran, so a test can pin
// that the refuted-row path reuses the pre-solve translation (WS-E step 8d).
#[cfg(all(test, feature = "trust-mc-native-trust-ir-bundle"))]
std::thread_local! {
    static NATIVE_BUNDLE_TRANSLATION_COUNT_FOR_TEST: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
    // Trust (C1, 2026-11-06): how many pre-solve translations and solves this
    // thread ran through trust-mc's `_with_source_reference_facts` entries, so a
    // test can pin that BOTH use the facts whenever the facts exist.
    static NATIVE_BUNDLE_SOURCE_REFERENCE_ENTRIES_FOR_TEST: std::cell::Cell<(usize, usize)> =
        const { std::cell::Cell::new((0, 0)) };
}

/// Trust (C1, 2026-11-06): live source facts for initialized reference pointees,
/// re-exported so the router and the compiler's single issuer reach trust-mc's
/// type through this crate's existing edge (no new dependency). Non-cloneable,
/// non-serializable, borrowed from one exact live bundle and its authority.
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
pub use trust_mc_trust_bmc::{
    SourceReferenceFacts, SourceReferenceFactsError, SourceReferenceLoadFact,
    SourceReferenceParameterFact, SourceReferenceValueFact,
};

/// The live source context of one native-bundle run: the borrowed authority, and
/// the source reference facts bound to the same bundle and authority when the
/// compiler issued any. Facts without an authority are unrepresentable.
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
#[derive(Clone, Copy)]
struct NativeLiveSource<'a> {
    authority: &'a trust_ir::SourceGenerationAuthority,
    reference_facts: Option<&'a SourceReferenceFacts<'a>>,
}

/// The same typed result crosses the authority-only and live-source wrappers.
/// A non-proving row retains its producer's cause until the per-row consumer;
/// the test-only diagnostic adapter explicitly projects its reason afterward.
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
type NativeProofTransports = (
    Vec<NativeTrustIrChcPdrAuthorizedProof>,
    BTreeMap<String, native_bundle_stop::NativeTransportNotProved>,
    BTreeMap<String, trust_mc_driver::NativeTrustIrChcPdrRefuted>,
);

impl TrustMcVerifierApiAdapter {
    /// Create an adapter with an explicit trust_mc configuration.
    #[must_use]
    pub fn new(config: TrustMcConfig) -> Self {
        Self { manifest: trust_mc_manifest(), config, solve_cutoff: None }
    }

    /// Trust (2026-10-17, gate-rca deadline): bound this adapter's SOLVING by `cutoff`
    /// as well as by the dispatch deadline its native-bundle entries take.
    ///
    /// The compiler gives the native lane a share of the per-function clock so that the
    /// certifying lanes after it (the in-process ay bridge, the structural and clean-
    /// kernel promotions, certification and S1) keep the rest. The dispatch deadline is
    /// what every fresh exact-direct and whole-function receipt freezes and what the
    /// router's dispatch seal and the compiler's mint compare it with, so it must stay
    /// the function's own deadline: a receipt carrying the cutoff would be refused at
    /// mint as deadline-mismatched, and a mint after the cutoff as late. So the cutoff
    /// is applied only where a solve is started or its clock is set; receipt
    /// timeliness is still judged against the dispatch deadline. `None` = no cutoff.
    #[must_use]
    pub fn with_solve_cutoff(mut self, cutoff: Option<std::time::Instant>) -> Self {
        self.solve_cutoff = cutoff;
        self
    }

    /// The instant solving stops at for a dispatch with `deadline`: the earlier of the
    /// two. Never a receipt's dispatch deadline.
    #[cfg(any(feature = "trust-mc-native-solver", feature = "trust-mc-native-trust-ir-bundle"))]
    fn solve_deadline(&self, deadline: Option<Instant>) -> Option<Instant> {
        match (deadline, self.solve_cutoff) {
            (Some(deadline), Some(cutoff)) => Some(deadline.min(cutoff)),
            (deadline, cutoff) => deadline.or(cutoff),
        }
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
            "tracked per-function wall-clock budget (-Ztrust-verify-function-budget-ms), or the \
             native lane's share of it (the solve cutoff), exceeded before this trust-mc \
             obligation was solved; degraded to Timeout (sound: never Proved)"
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
            decline: None,
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
                    decline: None,
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
    /// typed solver. This compatibility entry point deliberately carries no
    /// source-generation authority, so source-only semantic shortcuts remain
    /// fail-closed. Exported transport records are never capabilities.
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
        // Public convenience wrapper: not on the live producer chain, so it holds
        // no source-generation authority. MC cannot use `Inst::Assume` as a
        // trusted premise here. An exactly bound raw clause can still decline
        // without an encoding; a fallback must establish its own body semantics.
        self.evidence_from_native_trust_ir_bundle_with_deadline_and_fresh_receipts(
            bundle,
            obligations,
            native_bundle,
            None,
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
        // Live source-generation authority for `native_bundle` (see
        // [`trust_ir::SourceGenerationAuthority`]). `Some` only on the live
        // compiler producer chain; `None` (fail-closed) elsewhere.
        authority: Option<&trust_ir::SourceGenerationAuthority>,
        deadline: Option<Instant>,
    ) -> NativeTrustIrBundleEvidenceWithFreshReceipts {
        self.evidence_from_native_trust_ir_bundle_with_optional_source_authority_and_deadline_and_fresh_receipts(
            bundle,
            obligations,
            native_bundle,
            None,
            deadline,
        )
    }

    /// Run the native-bundle path with live source-generation authority.
    ///
    /// This is the sole TrustBMC adapter entry point that may ask TrustMC to
    /// admit source-only semantic shortcuts. The affine authority remains
    /// borrowed and must authorize this exact native bundle instance; ordinary,
    /// decoded, cloned, and hand-built bundles use the compatibility entry
    /// points above and remain fail-closed.
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    pub fn evidence_from_native_trust_ir_bundle_with_source_authority_and_deadline_and_fresh_receipts(
        &self,
        bundle: &TrustContractBundle,
        obligations: &[TrustObligation],
        native_bundle: &trust_ir::NativeVerificationBundle,
        source_generation_authority: &trust_ir::SourceGenerationAuthority,
        deadline: Option<Instant>,
    ) -> NativeTrustIrBundleEvidenceWithFreshReceipts {
        self.evidence_from_native_trust_ir_bundle_with_optional_source_authority_and_deadline_and_fresh_receipts(
            bundle,
            obligations,
            native_bundle,
            Some(NativeLiveSource { authority: source_generation_authority, reference_facts: None }),
            deadline,
        )
    }

    /// Run the native-bundle path with live source-generation authority AND the
    /// compiler's live source reference facts for that same bundle (trust-mc DQ
    /// 2026-10-30). Both the pre-solve translation, whose CHC identities the
    /// refutation and whole-function receipt checks reuse, and the solve go
    /// through trust-mc's `_with_source_reference_facts` entries, so they cannot
    /// disagree. Facts that do not authorize this exact `(native_bundle,
    /// source_generation_authority)` pair are a caller error: every owned row
    /// fails closed with that diagnostic, and no fact-free solve is substituted.
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    pub fn evidence_from_native_trust_ir_bundle_with_source_reference_facts_and_deadline_and_fresh_receipts(
        &self,
        bundle: &TrustContractBundle,
        obligations: &[TrustObligation],
        native_bundle: &trust_ir::NativeVerificationBundle,
        source_generation_authority: &trust_ir::SourceGenerationAuthority,
        source_reference_facts: &SourceReferenceFacts<'_>,
        deadline: Option<Instant>,
    ) -> NativeTrustIrBundleEvidenceWithFreshReceipts {
        if !source_reference_facts.authorizes_bundle(native_bundle, source_generation_authority) {
            return obligations
                .iter()
                .map(|obligation| {
                    let mut evidence = self.unsupported_evidence(bundle, obligation);
                    evidence.diagnostics.insert(
                        0,
                        "native trust_mc source reference facts do not authorize this exact live native bundle and source authority; refusing rather than solving without them"
                            .to_string(),
                    );
                    evidence
                })
                .collect::<Vec<_>>()
                .into();
        }
        self.evidence_from_native_trust_ir_bundle_with_optional_source_authority_and_deadline_and_fresh_receipts(
            bundle,
            obligations,
            native_bundle,
            Some(NativeLiveSource {
                authority: source_generation_authority,
                reference_facts: Some(source_reference_facts),
            }),
            deadline,
        )
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn evidence_from_native_trust_ir_bundle_with_optional_source_authority_and_deadline_and_fresh_receipts(
        &self,
        bundle: &TrustContractBundle,
        obligations: &[TrustObligation],
        native_bundle: &trust_ir::NativeVerificationBundle,
        live_source: Option<NativeLiveSource<'_>>,
        deadline: Option<Instant>,
    ) -> NativeTrustIrBundleEvidenceWithFreshReceipts {
        let source_generation_authority = live_source.map(|source| source.authority);
        // Trust (2026-10-17, gate-rca deadline): what every solve below is bounded by.
        // `deadline` itself stays the dispatch deadline the fresh exact-direct and
        // whole-function receipts freeze ([`Self::with_solve_cutoff`]).
        let solve_deadline = self.solve_deadline(deadline);
        // Trust: ownership is a property of the authenticated public VC, not
        // of a caller-supplied native bundle or direct contract. Record every
        // unowned row and every owned-but-payloadless E4/E5 row before
        // inspecting either input so an invalid native inventory cannot mask
        // (or bypass) the direct-solve admission rejection.
        let mut any_admissible_for_direct = false;
        let mut direct_by_id = BTreeMap::new();
        for obligation in obligations {
            let rejection = if !is_trust_mc_owned_obligation(obligation) {
                Some(format!(
                    "native trust_mc TrustIr bundle input rejected before direct solving for unowned {:?} obligation",
                    obligation.kind
                ))
            } else {
                owned_e4_e5_pre_solve_rejection(obligation)
            };
            if let Some(rejection) = rejection {
                let mut evidence = self.unsupported_evidence(bundle, obligation);
                evidence.diagnostics.push(rejection);
                direct_by_id.insert(obligation.obligation_id.clone(), evidence);
            } else {
                any_admissible_for_direct = true;
            }
        }
        if !any_admissible_for_direct {
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

        let translated = match self.native_trust_ir_chc_pdr_translated_obligations_in_live_source(
            native_bundle,
            live_source,
            solve_deadline,
        ) {
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
        let mut refused_by_obligation = BTreeMap::new();
        for refused in translated.refused_requests {
            let lookup_key = native_trust_mc_obligation_lookup_key(&refused.native_obligation_id);
            *translated_counts.entry(lookup_key.clone()).or_default() += 1;
            refused_by_obligation.entry(lookup_key).or_insert(refused);
        }
        for translated in translated.obligations {
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
            // router's `supports` filter. Apply the same pre-solve admission
            // gate before inspecting a supplied direct contract: a bare E4/E5
            // row remains TrustMC-owned, but an otherwise valid typed CHC
            // contract cannot manufacture the compiler's missing formula.
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
            let claim = match validate_native_trust_ir_public_claim_binding(
                bundle,
                obligation,
                native_bundle,
                &public_claim_binding_context,
            ) {
                Ok(claim) => claim,
                Err(reason) => {
                    let mut evidence = self.unsupported_evidence(bundle, obligation);
                    evidence.diagnostics.insert(
                        0,
                        format!("native trust_mc public/TrustIr claim binding rejected: {reason}"),
                    );
                    direct_by_id.insert(obligation.obligation_id.clone(), evidence);
                    continue;
                }
            };
            // Trust: stop solving once the per-function budget is spent;
            // the remaining direct-path obligations degrade to Timeout.
            if trust_mc_budget_deadline_exceeded(solve_deadline) {
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
            if let Some(refused) = refused_by_obligation.get(&expected_lookup_key) {
                let mut evidence = self.unsupported_evidence(bundle, obligation);
                let reason =
                    native_bundle_stop::NativeTransportNotProved::from_options_refusal(refused)
                        .map_or_else(|reason| reason, |row| row.reason);
                evidence
                    .diagnostics
                    .insert(0, format!("native trust_mc request options rejected: {reason}"));
                direct_by_id.insert(obligation.obligation_id.clone(), evidence);
                continue;
            }
            if let NativePublicClaimKind::RawPostcondition { admission_stop } = claim {
                let mut evidence = self.unsupported_evidence(bundle, obligation);
                if let Some(stop) = admission_stop {
                    // This is the actual typed admission refusal, after ALL
                    // public/native/replay/CHC identity checks completed. No
                    // submitted diagnostic string can manufacture this cause.
                    // The ordinary deadline check above still wins over it.
                    evidence.diagnostics.insert(
                        0,
                        format!(
                            "native trust_mc raw source admission refused: {}",
                            stop.diagnostic()
                        ),
                    );
                    evidence
                        .diagnostics
                        .push(trust_verifier_api::NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC.into());
                } else if let Some(translated) = translated_by_obligation
                    .get(&expected_lookup_key)
                    .filter(|row| row.diagnostics.iter().any(|diagnostic| {
                        !matches!(diagnostic.reason,
                            trust_mc_trust_bmc::TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary)
                    }))
                {
                    evidence.diagnostics.insert(0,
                        "raw postcondition cannot bypass native body lowering/admission diagnostics".into());
                    evidence.diagnostics.extend(translated.diagnostics.iter().map(|diagnostic| {
                        format!("native body lowering diagnostic: {diagnostic:?}")
                    }));
                } else {
                    // This is a validated original clause, not a body violation
                    // formula or a failed solver result. MC has no encoding for
                    // it, even when its body contains Assume instructions. No
                    // MC proof-authority admission or solve has run. A fallback
                    // must check the same body, without importing assumptions as
                    // trusted premises. Extra replay premises remain terminal.
                    // An unsupported MC direct-call summary is likewise an
                    // encoding limit: WP can compose the actual retained callee.
                    // Every other typed lowering diagnostic remains terminal.
                    evidence.decline = Some(trust_verifier_api::DeclineClass::Capability);
                    evidence.diagnostics.insert(0,
                        "native trust-mc has no encoding for this exactly bound raw source postcondition".into());
                }
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

            // Additive standalone-formula fresh lane: compiler-authenticated
            // formula rows outside E4/E5 ATTEMPT the receipt-bearing fresh
            // dispatch, and take its evidence ONLY when the live receipt was
            // actually delivered. Postconditions still enter only through the
            // result-referencing discriminator above; a post-state-free clause
            // cannot use this branch. On any shortfall — missing canonical
            // public digest, no exact direct input, non-Proved solve, or
            // dispatch error — the row preserves that first bounded outcome;
            // it never starts a second generic solve without the caller's
            // deadline. The E4/E5 terminal Unsupported arms below are
            // deliberately NOT reachable from this lane.
            let (exact_e4_e5_formula_lane, exact_standalone_formula_fresh_lane) =
                classify_direct_formula_lanes(obligation);
            let direct_outcome = if exact_standalone_formula_fresh_lane {
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
                    Some(dispatch) => dispatch.map(|dispatch| {
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
                    }),
                    None => Err(format!(
                        "canonical public semantic digest is missing for fresh exact-direct obligation `{}`",
                        obligation.obligation_id
                    )),
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
                self.direct_typed_chc_pdr_evidence_for_with_contract_index(
                    bundle,
                    obligation,
                    Some(&public_claim_binding_context.contracts),
                )
            };
            if trust_native_debug_enabled() {
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
            if trust_native_debug_enabled()
                && obligation.obligation_id.ends_with(":assertion:panic-freedom:0")
            {
                eprintln!(
                    "[DEFER_MATCH] obl={} outcome={} exact_e4_e5={} semantic_requires={} can_defer={}",
                    obligation.obligation_id,
                    match &direct_outcome {
                        Ok(Some(e)) => format!("Ok(Some status={:?})", e.status),
                        Ok(None) => "Ok(None)".to_string(),
                        Err(r) => format!("Err({r})"),
                    },
                    exact_e4_e5_formula_lane,
                    semantic_claim_requires_exact_direct_input,
                    can_defer_to_whole_function_transport,
                );
            }
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
        if trust_native_debug_enabled() {
            eprintln!(
                "[DEFER_SUM] deferred_ids.len()={} deferred={:?} direct_by_id.len()={}",
                deferred_ids.len(),
                deferred_ids,
                direct_by_id.len(),
            );
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
        if trust_mc_budget_deadline_exceeded(solve_deadline) {
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

        // Only the existing audited compiler entrypoint may retain a source-
        // facing whole-function capability. Ordinary module solves keep their
        // public results, but do not acquire this private family. The content
        // snapshot and the pre-solve `translated_by_obligation` above come from
        // the SAME immutable `native_bundle`; no returned proof supplies either.
        let whole_function_seal = source_generation_authority.and_then(|source| {
            FreshWholeFunctionChcPdrBundleSeal::from_source_authorized_bundles(
                bundle,
                obligations,
                native_bundle,
                source,
            )
            .ok()
        });
        let mut fresh_whole_function_receipts = BTreeMap::new();
        let (transports, transport_not_proved, transport_refuted) = match self
            .native_trust_ir_chc_pdr_proof_transports_in_live_source(
                native_bundle,
                live_source,
                solve_deadline,
            ) {
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
                        if reason.before_solver_dispatch() {
                            evidence.diagnostics.push(
                                trust_verifier_api::NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC
                                    .to_string(),
                            );
                        }
                        // insert(0), not push: `unsupported_diagnostics` has already
                        // prepended the generic "missing `trust.vc.formula.schema`"
                        // direct-lane line, which for a row that never uses the direct
                        // lane is a MISATTRIBUTED root cause. The compiler prints only
                        // the first three diagnostics, so appending here leaves the
                        // misleading line leading and hides the real reason. The sibling
                        // branch below already does this; the other two did not.
                        evidence.diagnostics.insert(
                            0,
                            format!(
                                "native trust_mc TrustIr CHC/PDR bundle runner did not produce proof-grade evidence: {reason}"
                            ),
                        );
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
                    if trust_native_debug_enabled() {
                        eprintln!(
                            "[NATIVE_TRUSTMC_RESULT] obl={} kind={:?} FINAL(direct) status={:?} strength={:?}",
                            obligation.obligation_id, obligation.kind, evidence.status, evidence.proof_strength
                        );
                    }
                    return evidence;
                }
                // Trust: the transport solve can exhaust the budget partway
                // through this obligation set; degrade the remainder to Timeout.
                if trust_mc_budget_deadline_exceeded(solve_deadline) {
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
                    // Witnessed refutation channel (T3): the transport solve
                    // REFUTED this row and attached a machine-checked witness.
                    // Every binding is revalidated consumer-side (the consumer's
                    // own translation, recomputed digests, admissibility) before
                    // a Failed verdict is surfaced; any validation failure
                    // demotes to the historical Unknown.
                    //
                    // The consumer translation is the one retained BEFORE the
                    // solve (`translated_by_obligation`), of this same immutable
                    // `native_bundle`; no solver output supplies it. Translating
                    // the whole bundle again for every refuted row recomputed
                    // that identical value once per row (WS-E step 8d).
                    if let Some(refuted_row) = transport_refuted.get(&expected_lookup_key) {
                        return self.native_trust_ir_refuted_row_evidence_with_deadline(
                            bundle,
                            obligation,
                            &native_trust_ir_retained_rows_for(
                                &translated_by_obligation,
                                &translated_counts,
                                &expected_lookup_key,
                            ),
                            refuted_row,
                            solve_deadline,
                        );
                    }
                    let mut evidence = self.unsupported_evidence(bundle, obligation);
                    if let Some(not_proved) = transport_not_proved.get(&expected_lookup_key) {
                        // Only the live typed Unsafe-to-Unknown branch supplies
                        // this cause. A generic error or copied human reason
                        // never establishes why a completed solve was withheld.
                        if not_proved.refutation_was_demoted() {
                            evidence.diagnostics.push(
                                trust_verifier_api::NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC
                                    .to_string(),
                            );
                        }
                        let reason = &not_proved.reason;
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
                        // insert(0) for the same reason as the sibling arm: the generic
                        // missing-schema line is prepended by `unsupported_diagnostics`
                        // and would otherwise mask this, the actual cause.
                        evidence.diagnostics.insert(
                            0,
                            format!(
                                "native trust_mc TrustIr CHC/PDR bundle returned no proof transport for obligation `{expected_native_id}`"
                            ),
                        );
                    }
                    if trust_native_debug_enabled() {
                        eprintln!(
                            "[NATIVE_TRUSTMC] obl={} kind={:?} expected_native_id={} -> NO TRANSPORT (not_proved_reason={:?}, available keys: {:?})",
                            obligation.obligation_id, obligation.kind, expected_native_id,
                            transport_not_proved.get(&expected_lookup_key),
                            transports_by_obligation.keys().collect::<Vec<_>>()
                        );
                    }
                    return evidence;
                };

                let binding = translated_by_obligation.get(&expected_lookup_key)
                    .ok_or_else(|| "independent pre-solve request configuration is absent".to_string())
                    .and_then(|fresh| validate_native_trust_mc_consumer_request_config(
                        fresh, &transport.evidence.translated));
                if let Err(reason) = binding {
                    let mut evidence = self.unsupported_evidence(bundle, obligation);
                    evidence.diagnostics.insert(0, format!("native trust_mc request configuration binding rejected: {reason}"));
                    return evidence;
                }

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
                if trust_native_debug_enabled() {
                    eprintln!(
                        "[NATIVE_TRUSTMC] obl={} kind={:?} FINAL status={:?} strength={:?} diag=[{}]",
                        obligation.obligation_id, obligation.kind, evidence.status,
                        evidence.proof_strength, evidence.diagnostics.join(" | ")
                    );
                }
                if evidence.status == EvidenceStatus::Proved
                    && obligation_is_whole_function_panic_freedom(bundle, obligation)
                    && let Some(seal) = whole_function_seal.as_ref()
                    && source_generation_authority.is_some_and(|source| source.authorizes_bundle(native_bundle))
                {
                    let receipt = translated_by_obligation.get(&expected_lookup_key)
                        .ok_or_else(|| "independent pre-solve translation is absent".to_string())
                        .and_then(|before_solve| FreshWholeFunctionChcPdrReceipt::try_from_native(
                            seal.clone(), obligation, &evidence, before_solve, transport, deadline,
                        ));
                    match receipt {
                        Ok(receipt) => {
                            fresh_whole_function_receipts.insert(obligation.obligation_id.clone(), receipt);
                        }
                        Err(reason) => {
                            // Public Proved is not an alternative authority when
                            // exact aggregate membership/proof replay fails.
                            let mut rejected = self.unsupported_evidence(bundle, obligation);
                            rejected.diagnostics.insert(0, format!("whole-function live receipt rejected: {reason}"));
                            return rejected;
                        }
                    }
                }
                evidence
            })
            .collect();
        finalize_native_bundle_evidence_with_whole_function_receipts(
            evidence,
            fresh_exact_direct_receipts,
            fresh_whole_function_receipts,
        )
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

    /// Translate Root's zero-is-unbounded convention once. An explicitly
    /// supplied zero Duration at the native solver API remains a zero ceiling.
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_solve_options(&self, deadline: Option<Instant>) -> trust_mc_core::ChcPdrSolveOptions {
        let timeout_ms = self.native_solve_timeout_ms(deadline);
        let mut options = trust_mc_core::ChcPdrSolveOptions::default()
            .with_engine(chc_pdr_engine_from_config(self.config.proof_mode))
            .with_proof_certificate(self.config.produce_proofs);
        options.timeout = (timeout_ms != 0).then(|| std::time::Duration::from_millis(timeout_ms));
        options
    }

    #[cfg(all(feature = "trust-mc-native-trust-ir-bundle", test))]
    #[allow(clippy::type_complexity)] // one typed per-outcome channel per T3 delivery lane
    fn native_trust_ir_chc_pdr_proof_transports(
        &self,
        native_bundle: &trust_ir::NativeVerificationBundle,
        // Live source-generation authority for `native_bundle`; threaded verbatim
        // to `solve_bundle_native_proof_grade` so its `Inst::Assume` gate can
        // admit genuine bridge-emitted Assumes. `None` keeps them fail-closed.
        authority: Option<&trust_ir::SourceGenerationAuthority>,
        deadline: Option<Instant>,
    ) -> Result<
        (
            Vec<NativeTrustIrChcPdrAuthorizedProof>,
            BTreeMap<String, String>,
            BTreeMap<String, trust_mc_driver::NativeTrustIrChcPdrRefuted>,
        ),
        String,
    > {
        self.native_trust_ir_chc_pdr_proof_transports_with_optional_source_authority(
            native_bundle,
            None,
            deadline,
        )
        .map(|(proved, not_proved, refuted)| {
            (proved, not_proved.into_iter().map(|(id, row)| (id, row.reason)).collect(), refuted)
        })
        .map_err(|error| error.to_string())
    }

    // Trust (C1, 2026-11-06): test-only; production calls `_in_live_source`.
    #[cfg(all(feature = "trust-mc-native-trust-ir-bundle", test))]
    fn native_trust_ir_chc_pdr_proof_transports_with_optional_source_authority(
        &self,
        native_bundle: &trust_ir::NativeVerificationBundle,
        source_generation_authority: Option<&trust_ir::SourceGenerationAuthority>,
        deadline: Option<Instant>,
    ) -> Result<NativeProofTransports, NativeBundleTransportError> {
        self.native_trust_ir_chc_pdr_proof_transports_in_live_source(
            native_bundle,
            source_generation_authority
                .map(|authority| NativeLiveSource { authority, reference_facts: None }),
            deadline,
        )
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_chc_pdr_proof_transports_in_live_source(
        &self,
        native_bundle: &trust_ir::NativeVerificationBundle,
        live_source: Option<NativeLiveSource<'_>>,
        deadline: Option<Instant>,
    ) -> Result<NativeProofTransports, NativeBundleTransportError> {
        validate_trust_mc_native_admission_contract(native_bundle)?;
        let runner = trust_mc_driver::NativeTrustIrChcPdrRunner::with_solve_options(
            self.native_solve_options(deadline),
        );
        // Trust (C1, 2026-11-06): with live source reference facts the solve goes
        // through trust-mc's facts entry, a strict superset of the source-authority
        // entry (it re-checks that the facts authorize this bundle and authority).
        let bundle_evidence = match live_source {
            Some(NativeLiveSource { authority, reference_facts: Some(facts) }) => {
                #[cfg(test)]
                NATIVE_BUNDLE_SOURCE_REFERENCE_ENTRIES_FOR_TEST
                    .with(|count| count.set((count.get().0, count.get().1 + 1)));
                runner.solve_bundle_native_proof_grade_with_source_reference_facts(
                    native_bundle,
                    authority,
                    facts,
                )
            }
            Some(NativeLiveSource { authority, reference_facts: None }) => runner
                .solve_bundle_native_proof_grade_with_source_authority(native_bundle, authority),
            None => runner.solve_bundle_native_proof_grade(native_bundle),
        }
        .map_err(NativeBundleTransportError::from_driver)?;
        // Requests whose solve ran but did not produce proof-grade evidence are
        // returned as typed, evidence-free rows. Preserve their exact per-row
        // reason so a failed request cannot be hidden behind a generic missing
        // transport message, while rejecting duplicate/overlapping identities
        // as structural corruption.
        let mut proved_ids =
            std::collections::HashSet::with_capacity(bundle_evidence.obligations.len());
        for row in &bundle_evidence.obligations {
            proved_ids.insert(native_trust_mc_obligation_lookup_key(
                &row.translated.obligation.obligation_id,
            ));
        }
        let mut not_proved = BTreeMap::new();
        for row in bundle_evidence.not_proved {
            let obligation_id = row.translated.obligation.obligation_id.clone();
            let lookup_key = native_trust_mc_obligation_lookup_key(&obligation_id);
            if proved_ids.contains(&lookup_key) {
                return Err(
                    format!(
                        "native trust_mc bundle returned obligation `{obligation_id}` as both proved and not-proved"
                    )
                    .into(),
                );
            }
            if row.reason.is_empty()
                || row.reason.trim() != row.reason
                || row.reason.len() > 16 * 1024
                || row.reason.chars().any(char::is_control)
            {
                return Err(
                    format!(
                        "native trust_mc bundle returned a non-canonical not-proved reason for `{obligation_id}`"
                    )
                    .into(),
                );
            }
            if not_proved
                .insert(lookup_key, native_bundle_stop::NativeTransportNotProved::from_driver(row))
                .is_some()
            {
                return Err(
                    format!(
                        "native trust_mc bundle returned duplicate not-proved rows for `{obligation_id}`"
                    )
                    .into(),
                );
            }
        }
        // An unsupported option is a request-local refusal with no encoded
        // VC or solve. Preserve it in the evidence-free channel, not as a fake
        // translated row, and keep the same disjoint-identity guards.
        for row in bundle_evidence.refused_requests {
            let obligation_id = &row.native_obligation_id;
            let lookup_key = native_trust_mc_obligation_lookup_key(obligation_id);
            if proved_ids.contains(&lookup_key) || not_proved.contains_key(&lookup_key) {
                return Err(format!(
                    "native trust_mc bundle returned obligation `{obligation_id}` as refused and as another outcome"
                ).into());
            }
            let refusal = native_bundle_stop::NativeTransportNotProved::from_options_refusal(&row)?;
            not_proved.insert(lookup_key, refusal);
        }
        // Witnessed refutations are their own typed channel: never proof
        // evidence, never a bare not-proved reason. Identity overlap with the
        // proved or not-proved sets is structural corruption (one request, one
        // outcome), exactly like the duplicate checks above.
        let mut refuted = BTreeMap::new();
        for row in bundle_evidence.refuted {
            let obligation_id = row.translated.obligation.obligation_id.clone();
            let lookup_key = native_trust_mc_obligation_lookup_key(&obligation_id);
            if proved_ids.contains(&lookup_key) || not_proved.contains_key(&lookup_key) {
                return Err(
                    format!(
                        "native trust_mc bundle returned obligation `{obligation_id}` as refuted and as another outcome"
                    )
                    .into(),
                );
            }
            if refuted.insert(lookup_key, row).is_some() {
                return Err(format!(
                    "native trust_mc bundle returned duplicate refuted rows for `{obligation_id}`"
                )
                .into());
            }
        }
        Ok((
            bundle_evidence
                .obligations
                .into_iter()
                .map(NativeTrustIrChcPdrAuthorizedProof::try_from_bundle_evidence)
                .collect::<Result<Vec<_>, _>>()?,
            not_proved,
            refuted,
        ))
    }

    // Trust (C1, 2026-11-06): test-only; production calls `_in_live_source`.
    #[cfg(all(feature = "trust-mc-native-trust-ir-bundle", test))]
    fn native_trust_ir_chc_pdr_translated_obligations(
        &self,
        native_bundle: &trust_ir::NativeVerificationBundle,
        deadline: Option<Instant>,
    ) -> Result<Vec<trust_mc_trust_bmc::NativeTrustMcChcPdrObligation>, String> {
        self.native_trust_ir_chc_pdr_translated_obligations_in_live_source(
            native_bundle,
            None,
            deadline,
        )
        .map(|batch| batch.obligations)
    }

    /// The pre-solve consumer translation. With live source reference facts it is
    /// trust-mc's `translate_configured_obligations_with_source_reference_facts`, the entry
    /// its driver documents for producer pre-solve claim/CHC identities, so the
    /// retained rows are the ones the facts solve translates.
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_chc_pdr_translated_obligations_in_live_source(
        &self,
        native_bundle: &trust_ir::NativeVerificationBundle,
        live_source: Option<NativeLiveSource<'_>>,
        deadline: Option<Instant>,
    ) -> Result<trust_mc_trust_bmc::NativeMcConfiguredChcTranslation, String> {
        #[cfg(test)]
        NATIVE_BUNDLE_TRANSLATION_COUNT_FOR_TEST.with(|count| count.set(count.get() + 1));
        let runner = trust_mc_driver::NativeTrustIrChcPdrRunner::with_solve_options(
            self.native_solve_options(deadline),
        );
        match live_source {
            Some(NativeLiveSource { authority, reference_facts: Some(facts) }) => {
                #[cfg(test)]
                NATIVE_BUNDLE_SOURCE_REFERENCE_ENTRIES_FOR_TEST
                    .with(|count| count.set((count.get().0 + 1, count.get().1)));
                runner.translate_configured_obligations_with_source_reference_facts(
                    native_bundle,
                    authority,
                    facts,
                )
            }
            _ => runner.translate_configured_obligations(native_bundle),
        }
        .map_err(native_typed_chc_pdr_error_reason)
    }

    /// Turn one witnessed native-bundle refutation into public evidence.
    ///
    /// REFUTATION SOUNDNESS GATE (native-bundle lane). The producer's witness
    /// is DATA, not authority: before a `Failed` verdict may surface, this
    /// consumer independently
    /// 1. applies the producer-encoding admissibility gate on the public
    ///    obligation (an attested over-approximate encoding cannot ground a
    ///    refutation, exactly as on the direct lane);
    /// 2. takes its OWN translation of its retained native bundle
    ///    (`consumer_rows`: in production the rows translated before the solve,
    ///    of the same immutable bundle, never a solver-returned row) and
    ///    requires it to be free of fail-closed lowering diagnostics (a
    ///    derivation through an unconditional error rule is an admission
    ///    failure, not a program trap);
    /// 3. recomputes the encoded-formula digest from that consumer translation
    ///    (never trusting the producer-threaded translated obligation);
    /// 4. runs the full witness binding validation
    ///    ([`validate_bound_typed_chc_pdr_refutation_witness`]): obligation
    ///    identity, route/cache-key binding, semantic-configuration digest,
    ///    all-zero exact-encoding concreteness, recognized machine-check kind,
    ///    and the materialized counterexample artifact.
    ///
    /// ANY failure demotes to the historical Unknown — never a proof, never a
    /// bare producer-claimed failure.
    ///
    /// The compiler's positive `exact` annotation describes an admitted flat
    /// typed VC. It is not a source-to-native-TrustIR correspondence premise.
    /// This native route checks that distinct scope before any witness can
    /// publish a counterexample. Native source correspondence has no production
    /// issuer yet; replaying the encoded request cannot substitute for it.
    /// Unsupported source constructs can become `Inst::Undef` or otherwise
    /// over-approximate the source, so a complete positive relation and the full
    /// falsification gate remain required before this route can admit credit.
    ///
    /// `consumer_rows` must hold EVERY row of the consumer's translation whose
    /// obligation id could equal the refuted row's (in production: the rows that
    /// share its lookup key, see [`native_trust_ir_retained_rows_for`]); exactly
    /// one of them must carry the refuted row's exact obligation id.
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    #[cfg(test)]
    fn native_trust_ir_refuted_row_evidence(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        consumer_rows: &[&trust_mc_trust_bmc::NativeTrustMcChcPdrObligation],
        row: &trust_mc_driver::NativeTrustIrChcPdrRefuted,
    ) -> ObligationEvidence {
        self.native_trust_ir_refuted_row_evidence_with_deadline(
            bundle,
            obligation,
            consumer_rows,
            row,
            None,
        )
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_refuted_row_evidence_with_deadline(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        consumer_rows: &[&trust_mc_trust_bmc::NativeTrustMcChcPdrObligation],
        row: &trust_mc_driver::NativeTrustIrChcPdrRefuted,
        deadline: Option<Instant>,
    ) -> ObligationEvidence {
        let native_id = &row.translated.obligation.obligation_id;
        let demote = |reason: String| {
            let mut evidence = self.unsupported_evidence(bundle, obligation);
            evidence.diagnostics.insert(
                0,
                format!(
                    "native trust_mc TrustIr CHC/PDR transport refuted obligation `{native_id}` \
                     but the refutation witness was not admitted: {reason}; refutation demoted \
                     to unknown (counterexample evidence is not a proof)"
                ),
            );
            evidence
        };

        let admissibility = TrustMcChcRefutationAdmissibility::for_native_obligation(obligation);
        if let Some(reason) = admissibility.rejection_reason() {
            return demote(reason);
        }
        match native_refutation::check_with_options(
            bundle,
            obligation,
            consumer_rows,
            row,
            &self.native_solve_options(deadline),
        ) {
            Ok((expected_normalized_input, verification_summary)) => {
                let input_artifact = EvidenceArtifact {
                    kind: EvidenceArtifactKind::EngineInput,
                    uri: format!(
                        "trust-verifier-api://bundle/{}/native-trust-ir/obligation/{}/typed-trust-mc-chc",
                        bundle.bundle_id, obligation.obligation_id
                    ),
                    hash: ArtifactHash {
                        algorithm: "sha256".to_string(),
                        value: expected_normalized_input.normalized_input_hash.value.clone(),
                    },
                    materialization: None,
                };
                self.typed_chc_pdr_solver_outcome_evidence(
                    bundle,
                    obligation,
                    EvidenceStatus::Failed,
                    input_artifact,
                    Vec::new(),
                    non_proof_artifacts_from_trust_mc_core_verdict(&row.verification.verdict),
                    format!(
                        "native trust_mc TrustIr CHC/PDR transport refuted the encoded VC and \
                         its refutation witness validated: obligation identity, \
                         consumer-recomputed encoded-formula digest (the consumer's own \
                         native-bundle translation), consumer-recomputed \
                         semantic-configuration digest, and the exact-encoding concreteness \
                         attestation (zero translation drops / havocs / Undef-diagnostic \
                         havocs) all checked; counterexample verification: \
                         {verification_summary}"
                    ),
                )
            }
            Err(reason) => demote(format!("witness failed validation ({reason})")),
        }
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
            // Trust: 2026-09-21 — the wording is SCOPED to this adapter on purpose.
            // "typed CHC input unavailable (root cause): ..." read as a statement
            // about the OBLIGATION, and it is not: it is this adapter declining to
            // lower, while another engine may (and routinely does) discharge the
            // same row. These lines are dumped for EVERY obligation once a
            // compilation reports any failure, so a reader scanning the evidence
            // trail of a red build meets "root cause" next to rows that are
            // PROVED. Measured 2026-09-21: a postcondition row carrying this exact
            // line is proved 6/7 with `0 unknown` once an unrelated row's budget
            // suffices — the line never moved, the verdict did. It cost a full
            // diagnosis cycle chasing a "missing metadata gap" that was this note.
            // The root-cause surfacing itself is kept: it is what stopped the
            // 574-row cascade the comment above records.
            diagnostics.push(format!(
                "trust-mc has no typed CHC input for this obligation (reason: {root_reason}); \
                 this is this adapter declining to lower it, not a verdict — another engine \
                 may still discharge the row"
            ));
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
        self.direct_typed_chc_pdr_evidence_for_with_contract_index(bundle, obligation, None)
    }

    fn direct_typed_chc_pdr_evidence_for_with_contract_index(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        contract_indices: Option<&ContractChcCache>,
    ) -> Result<Option<ObligationEvidence>, String> {
        let Some(input) = self.typed_chc_pdr_obligation_for_with_contract_index(
            bundle,
            obligation,
            contract_indices,
        )?
        else {
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
        contract_indices: Option<&ContractChcCache>,
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

    #[cfg_attr(not(test), allow(dead_code))]
    fn typed_chc_pdr_obligation_for(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
    ) -> Result<Option<DirectTypedChcPdrInput>, String> {
        self.typed_chc_pdr_obligation_for_with_contract_index(bundle, obligation, None)
    }

    #[cfg(test)]
    fn reset_typed_chc_input_lookup_count_for_current_test_thread() {
        TYPED_CHC_INPUT_LOOKUP_COUNT_FOR_TEST.with(|count| count.set(0));
    }

    #[cfg(test)]
    fn typed_chc_input_lookup_count_for_current_test_thread() -> usize {
        TYPED_CHC_INPUT_LOOKUP_COUNT_FOR_TEST.with(std::cell::Cell::get)
    }

    fn typed_chc_pdr_obligation_for_with_contract_index(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        contract_indices: Option<&ContractChcCache>,
    ) -> Result<Option<DirectTypedChcPdrInput>, String> {
        #[cfg(test)]
        TYPED_CHC_INPUT_LOOKUP_COUNT_FOR_TEST.with(|count| count.set(count.get() + 1));
        if let Some(rejection) = owned_e4_e5_pre_solve_rejection(obligation) {
            return Err(rejection);
        }
        // Compiler-native CHC input is a derived transport contract. It must
        // not replace the canonical public `contract_id` after the TrustIr
        // module has committed the public claim. Validate that diagnostic
        // projection through its unique native marker, but select direct proof
        // input only through the ordinary public semantic contract link.
        let native_contract_id = native_trust_ir_synthetic_trust_mc_contract_id(obligation)?;
        let native_contract = if let Some(native_contract_id) = native_contract_id {
            let (contract, native_idx_opt) = if let Some(contract_indices) = contract_indices {
                let matching = contract_indices.indices(native_contract_id);
                let [index] = matching else {
                    return Err(format!(
                        "obligation `{}` names diagnostic native trust-mc synthetic contract `{native_contract_id}`, but the bundle contains {} matching contracts; expected exactly one",
                        obligation.obligation_id,
                        matching.len()
                    ));
                };
                let contract = bundle.contracts.get(*index).ok_or_else(|| {
                    "prevalidated native trust-mc contract index is out of bounds".to_string()
                })?;
                (contract, Some(*index))
            } else {
                (
                    native_trust_ir_synthetic_trust_mc_contract(
                        bundle,
                        obligation,
                        native_contract_id,
                    )?,
                    None,
                )
            };
            validate_native_trust_ir_synthetic_trust_mc_contract_value(
                contract,
                obligation,
                native_contract_id,
            )?;
            Some((contract, native_idx_opt))
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

        let matching_contracts: Vec<(&TrustContract, Option<usize>)> =
            if let Some(contract_indices) = contract_indices {
                contract_indices
                    .indices(contract_id)
                    .iter()
                    .filter_map(|&index| bundle.contracts.get(index).map(|c| (c, Some(index))))
                    .collect()
            } else {
                bundle
                    .contracts
                    .iter()
                    .filter(|contract| contract.contract_id == contract_id)
                    .map(|c| (c, None))
                    .collect()
            };
        if matching_contracts.is_empty() {
            return Err(format!(
                "obligation {} references contract `{contract_id}`, but the bundle has no matching contract",
                obligation.obligation_id
            ));
        }

        let mut typed_inputs: Vec<(
            &TrustContract,
            Option<usize>,
            std::borrow::Cow<'_, TrustMcTypedChcObligationInput>,
        )> = Vec::new();
        for (contract, idx_opt) in matching_contracts {
            let parsed = if let (Some(cache), Some(idx)) = (contract_indices, idx_opt) {
                cache.parsed_input(idx, contract)?.map(std::borrow::Cow::Borrowed)
            } else {
                trust_mc_typed_chc_input_from_contract(contract)?.map(std::borrow::Cow::Owned)
            };
            if let Some(input) = parsed {
                typed_inputs.push((contract, idx_opt, input));
            }
        }

        match typed_inputs.as_slice() {
            [] => Ok(None),
            [(contract, idx_opt, input)] => {
                let input_ref = input.as_ref();
                let has_contract_binding = contract
                    .metadata
                    .iter()
                    .any(|entry| entry.key == TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY);
                let (input, input_digest) = if has_contract_binding
                    || input_ref.native_metadata.is_some()
                {
                    // Legacy proof-capable typed contracts carry their own
                    // native material and complete binding. If either half is
                    // present, remain on the established admission path so a
                    // missing/malformed other half fails exactly as before.
                    (
                        input_ref.clone(),
                        validate_trust_mc_typed_chc_binding_with_cache(
                            contract,
                            obligation,
                            input_ref,
                            contract_indices.zip(*idx_opt),
                        )?,
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
                        contract, obligation, input_ref,
                    )?;
                    let (native_contract, native_idx_opt) = native_contract.ok_or_else(|| {
                        format!(
                            "compiler canonical typed trust_mc contract `{}` for public obligation `{}` requires one authenticated native synthetic-contract marker",
                            contract.contract_id, obligation.obligation_id
                        )
                    })?;
                    let native_input =
                        if let (Some(cache), Some(nidx)) = (contract_indices, native_idx_opt) {
                            cache
                                .parsed_input(nidx, native_contract)?
                                .map(std::borrow::Cow::Borrowed)
                        } else {
                            trust_mc_typed_chc_input_from_contract(native_contract)?
                                .map(std::borrow::Cow::Owned)
                        }
                        .ok_or_else(|| {
                            format!(
                                "authenticated native trust_mc marker contract `{}` has no typed CHC/PDR input",
                                native_contract.contract_id
                            )
                        })?;
                    validate_trust_mc_typed_chc_binding_with_cache(
                        native_contract,
                        obligation,
                        native_input.as_ref(),
                        contract_indices.zip(native_idx_opt),
                    )?;
                    validate_compiler_canonical_trust_mc_semantic_projection(
                        contract,
                        native_contract,
                    )?;
                    let native_obligation_id =
                        native_input.obligation_id.clone().ok_or_else(|| {
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
                    let mut reconciled = input_ref.clone();
                    reconciled.obligation_id = Some(native_obligation_id);
                    reconciled.native_metadata = Some(native_metadata);
                    let digest = if let (Some(cache), Some(idx)) = (contract_indices, *idx_opt) {
                        cache.input_digest(idx, contract)?
                    } else {
                        trust_mc_typed_chc_contract_input_digest(contract)?
                    };
                    (reconciled, digest)
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

        // Trust (2026-10-17, gate-rca deadline): the solve is started and clocked by the
        // solve deadline (the dispatch deadline or the native solve cutoff, whichever is
        // earlier); its completion and its receipt are judged against `deadline` below.
        let solve_deadline = self.solve_deadline(deadline);
        if solve_deadline.is_some_and(|deadline| Instant::now() >= deadline) {
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
        let effective_timeout = if let Some(deadline) = solve_deadline {
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
        // LoopInvariant, Termination, Assertion, ArithmeticSafety,
        // Precondition, and result-referencing Postcondition formula lanes).
        // Every other caller retains the generic reject-only API; it cannot
        // turn a source-unbound CHC candidate into public evidence.
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
                    &normalized_input_source,
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
        retained_obligation: &trust_mc_core::MirChcPdrObligation,
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
            // a recognized independently replayable direct-SMT
            // counterexample kind (acyclic or exact bounded-unroll). ALL
            // checks pass -> `Failed` with the counterexample surfaced; ANY
            // failure or an absent witness -> the historical `Unknown`
            // demotion.
            //
            // PRODUCER-STAGE GATE (added because the note that used to sit here
            // was wrong). The witness's concreteness attestation covers only the
            // trust-mc encoding stage (submitted ChcVc -> solver problem,
            // exact-or-reject with real accounting). The old note then claimed
            // "the ChcVc-production stage stays fail-closed at its own producer
            // boundary (unsupported shapes never emit a MIR-derived typed CHC
            // input)". That is FALSE for a body with a loop: the compiler emits
            // a perfectly "supported" MIR-derived typed CHC for it, namely the
            // flattened single-formula fallback with one nullary `error`
            // relation and one constraint-only rule. That formula has no loop
            // transition relation, so the loop-carried local occurs in it as a
            // free variable with no defining constraint, and the direct-SMT
            // acyclic route satisfies the query by simply CHOOSING a value the
            // program can never produce. Every downstream check passed
            // truthfully — trust-mc really did lower that ChcVc exactly — and a
            // TRUE postcondition was published as
            // `verified_counterexample = true`. So the producer stage is now
            // gated here, on this side of the boundary, exactly where
            // `ChcPdrEncodingConcreteness`'s SCOPE note says it belongs.
            trust_mc_core::ChcPdrSolveStatus::Refuted { witness } => {
                let admissibility = TrustMcChcRefutationAdmissibility::for_obligation(obligation);
                let witness_validation = match admissibility.rejection_reason() {
                    // Checked BEFORE the witness: a witness that validates
                    // perfectly still certifies nothing about a stage it does
                    // not cover, and the diagnostic must say which stage failed.
                    Some(reason) => Err(TypedChcRefutationRejection::ProducerEncoding(reason)),
                    None => match witness.as_deref() {
                        None => Err(TypedChcRefutationRejection::NoWitness),
                        Some(witness) => validate_bound_typed_chc_pdr_refutation_witness(
                            bundle,
                            witness,
                            obligation,
                            retained_obligation,
                            &solved,
                            &expected_normalized_input,
                            chc_pdr_engine_from_config(self.config.proof_mode),
                        )
                        .map_err(TypedChcRefutationRejection::WitnessRejected),
                    },
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
                            TypedChcRefutationRejection::NoWitness => "native trust_mc typed CHC/PDR solver refuted the encoded VC; refutation demoted to unknown: the solver returns no witness model and the encoding's concreteness (havoc-freedom) cannot be certified, so the refutation may reflect over-approximated (havoc'd) semantics rather than a reachable program failure; counterexample evidence is not a proof".to_string(),
                            TypedChcRefutationRejection::WitnessRejected(reason) => format!(
                                "native trust_mc typed CHC/PDR solver refuted the encoded VC; refutation demoted to unknown: a refutation witness was attached but failed validation ({reason}), so the refutation may reflect over-approximated (havoc'd) semantics or a detached/forged certificate rather than a reachable program failure; counterexample evidence is not a proof"
                            ),
                            TypedChcRefutationRejection::ProducerEncoding(reason) => format!(
                                "native trust_mc typed CHC/PDR solver refuted the encoded VC; refutation demoted to unknown: {reason}. A refutation of an over-approximating encoding is a refutation of the ENCODING, not of the program — a satisfying model may assign a value the program can never produce — so it is not evidence even when its conclusion happens to be true. The obligation is UNPROVED, not disproved, by this lane: the demotion reports a gap in the CHC construction's attested fidelity and says nothing about whether the code is correct; another lane's verdict on the same row stands on that lane's own authority"
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
        // Trust (DEMOTED REFUTATION carried its counterexample): only a `Failed`
        // verdict may carry a `Counterexample` artifact. A refutation the soundness
        // gate DEMOTED reaches here as `Unknown`, and its solver model is a model of
        // the ENCODING — it may assign a value the program can never produce (measured:
        // `_2 = 2` for the discriminant of `T<NoExt>`, whose tag-2 variant is
        // uninhabited). Publishing it under the `Counterexample` kind beside an
        // `Unknown` status presented that model as a witness against the code while the
        // same row's diagnostics said "UNPROVED, not disproved". Withheld, and the
        // withholding is disclosed, so the row reports exactly what this lane knows.
        let mut withheld_counterexamples = 0usize;
        evidence.artifacts.extend(artifacts.into_iter().filter(|artifact| {
            let keep = status == EvidenceStatus::Failed
                || artifact.kind != EvidenceArtifactKind::Counterexample;
            withheld_counterexamples += usize::from(!keep);
            keep
        }));
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
        if withheld_counterexamples > 0 {
            evidence.diagnostics.push(format!(
                "withheld {withheld_counterexamples} solver counterexample artifact(s): the verdict is {}, not failed, so the solver's model is a model of the encoded VC and is not published as a counterexample to the program",
                evidence_status_label(status)
            ));
        }
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
    /// Rust integer division: quotient truncated toward zero.
    TruncDiv,
    /// Rust integer remainder: sign follows the dividend.
    TruncRem,
    /// Legacy v1 spelling.  Deserialized so stale artifacts get a precise
    /// fail-closed diagnostic, but never admitted as proof input: historical
    /// MIR producers used this spelling for Rust truncating division.
    Div,
    /// Legacy v1 spelling.  See [`Self::Div`].
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
    /// Distinct additive v1 value operation; this does not prove definedness.
    BvSrem,
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
        // Rust's signed `/` and `%` truncate toward zero, whereas ay's Int
        // `div`/`mod` are Euclidean.  This is the same construction used by
        // `trust_types::ay_bridge`: the remainder takes the dividend's sign,
        // then division uses the exact identity a = b*q + r.  Keeping these as
        // distinct wire ops prevents a historical typed-CHC artifact that
        // explicitly requested Euclidean `div`/`mod` from silently changing
        // meaning.
        TrustMcTypedChcBinaryOpInput::TruncRem => trust_mc_typed_chc_truncating_remainder(lhs, rhs),
        TrustMcTypedChcBinaryOpInput::TruncDiv => {
            trust_mc_typed_chc_truncating_remainder(lhs.clone(), rhs.clone())
                .and_then(|remainder| lhs.try_int_sub(remainder))
                .and_then(|numerator| numerator.try_int_div(rhs))
        }
        // `div`/`mod` existed in schema v1 before the transport distinguished
        // Rust truncating arithmetic from SMT/ay Euclidean arithmetic.  Every
        // historical proof-grade producer used those spellings for Rust MIR,
        // so interpreting them as Euclidean can reproduce the exact
        // false-PROVE this lane fixes.  The schema version did not change;
        // accept the tags during deserialization only so stale payloads fail
        // here with an actionable diagnostic instead of being trusted under an
        // invented meaning.  Current producers emit `trunc_div`/`trunc_rem`.
        TrustMcTypedChcBinaryOpInput::Div | TrustMcTypedChcBinaryOpInput::Mod => {
            return Err(format!(
                "legacy typed trust_mc CHC/PDR binary {op:?} is semantically ambiguous: schema v1 producers used `div`/`mod` for Rust truncating arithmetic; regenerate the payload with explicit `trunc_div`/`trunc_rem`"
            ));
        }
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
        TrustMcTypedChcBinaryOpInput::BvSrem => lhs.try_bvsrem(rhs),
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

/// Exact Rust signed-remainder identity over mathematical integers.
///
/// ay's `int_mod` is Euclidean.  Negating the dividend before `mod` and the
/// result afterwards is what restores Rust's dividend-signed remainder for a
/// negative dividend.  The branches coincide for every non-negative value, so
/// this is also exact for unsigned source integers represented in `Sort::Int`.
///
/// This helper is deliberately a VALUE relation, not a definedness proof.
/// Rust's `rhs == 0` panic and the signed `MIN / -1` and `MIN % -1` overflow
/// panics are authenticated by separate Level-0 MIR obligations, and a body
/// value definition reaches a postcondition only under the corresponding
/// passed-assert path guards.  The structural CHC lane independently rejects
/// machine `Div`/`Rem` when those guards are absent.  Consequently, callers
/// must never use successful construction of this expression as authority that
/// the source operation returns; it states the returned value only on executions
/// for which the independent safety obligations permit the operation to return.
fn trust_mc_typed_chc_truncating_remainder(
    lhs: Expr,
    rhs: Expr,
) -> Result<Expr, ay_bindings::SortError> {
    let nonnegative = lhs.clone().try_int_ge(Expr::int_const(0))?;
    let positive = lhs.clone().try_int_mod(rhs.clone())?;
    let negative = lhs.try_int_neg()?.try_int_mod(rhs)?.try_int_neg()?;
    Expr::try_ite(nonnegative, positive, negative)
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
    // Trust (T3 L4, C09d): the readers' depth bound, as every contract-predicate reader.
    trust_types::json_depth::from_value_deep(value).map(Some).map_err(|err| {
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

#[derive(Debug)]
struct ContractChcCache {
    by_id: std::collections::HashMap<String, Vec<usize>>,
    parsed_inputs: Vec<std::sync::OnceLock<Result<Option<TrustMcTypedChcObligationInput>, String>>>,
    input_digests: Vec<std::sync::OnceLock<Result<String, String>>>,
}

impl ContractChcCache {
    #[cfg(any(test, feature = "trust-mc-native-trust-ir-bundle"))]
    fn new(contracts: &[TrustContract]) -> Self {
        let mut by_id = std::collections::HashMap::with_capacity(contracts.len());
        for (index, contract) in contracts.iter().enumerate() {
            by_id.entry(contract.contract_id.clone()).or_insert_with(Vec::new).push(index);
        }
        let parsed_inputs = (0..contracts.len()).map(|_| std::sync::OnceLock::new()).collect();
        let input_digests = (0..contracts.len()).map(|_| std::sync::OnceLock::new()).collect();
        Self { by_id, parsed_inputs, input_digests }
    }

    fn indices(&self, contract_id: &str) -> &[usize] {
        self.by_id.get(contract_id).map_or(&[][..], Vec::as_slice)
    }

    fn parsed_input<'a>(
        &'a self,
        index: usize,
        contract: &TrustContract,
    ) -> Result<Option<&'a TrustMcTypedChcObligationInput>, String> {
        let Some(slot) = self.parsed_inputs.get(index) else {
            return Err("prevalidated native trust-mc contract index is out of bounds".to_string());
        };
        let cached = slot.get_or_init(|| trust_mc_typed_chc_input_from_contract(contract));
        match cached {
            Ok(opt) => Ok(opt.as_ref()),
            Err(err) => Err(err.clone()),
        }
    }

    fn input_digest(&self, index: usize, contract: &TrustContract) -> Result<String, String> {
        let Some(slot) = self.input_digests.get(index) else {
            return Err("prevalidated native trust-mc contract index is out of bounds".to_string());
        };
        slot.get_or_init(|| trust_mc_typed_chc_contract_input_digest(contract)).clone()
    }
}

fn semantic_projection_object<'a>(
    contract: &'a TrustContract,
    role: &str,
) -> Result<&'a serde_json::Map<String, serde_json::Value>, String> {
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
    value.as_object().ok_or_else(|| {
        format!(
            "{role} typed trust_mc contract `{}` payload is not an object",
            contract.contract_id
        )
    })
}

fn validate_compiler_canonical_trust_mc_semantic_projection(
    canonical_contract: &TrustContract,
    native_contract: &TrustContract,
) -> Result<(), String> {
    let canonical = semantic_projection_object(canonical_contract, "compiler canonical")?;
    let native = semantic_projection_object(native_contract, "authenticated native marker")?;
    // These are the only request-local fields. Every semantic field,
    // including schema_version, origin, function, query, variables,
    // relations, rules, and any future field, remains in the comparison.
    let is_semantic_key = |k: &str| k != "obligation_id" && k != "native_metadata";
    let canonical_semantic_len = canonical.keys().filter(|k| is_semantic_key(k)).count();
    let native_semantic_len = native.keys().filter(|k| is_semantic_key(k)).count();
    let semantic_equal = canonical_semantic_len == native_semantic_len
        && canonical
            .iter()
            .filter(|(k, _)| is_semantic_key(k))
            .all(|(k, v)| native.get(k) == Some(v));
    if !semantic_equal {
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

fn validate_trust_mc_typed_chc_binding_with_cache(
    contract: &TrustContract,
    obligation: &TrustObligation,
    input: &TrustMcTypedChcObligationInput,
    cached_contract: Option<(&ContractChcCache, usize)>,
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

    let contract_input_digest = if let Some((cache, idx)) = cached_contract {
        cache.input_digest(idx, contract)?
    } else {
        trust_mc_typed_chc_contract_input_digest(contract)?
    };
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
    const DIGEST_PREFIX: &[u8] = b"trust-mc.typed-chc-obligation.digest.v1\0";
    let canonical = trust_types::canonical_json_value(value);
    let mut material = Vec::with_capacity(DIGEST_PREFIX.len() + 512);
    material.extend_from_slice(DIGEST_PREFIX);
    serde_json::to_writer(&mut material, &canonical).map_err(|error| {
        format!("failed to serialize canonical typed trust_mc CHC/PDR input: {error}")
    })?;
    Ok(stable_sha256_hex(&material))
}

fn is_lowercase_sha256_hex(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| matches!(byte, b'0'..=b'9' | b'a'..=b'f'))
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
        // KNOWN FALSE-REFUTATION SEAM, measured 2026-08-06 and deliberately NOT
        // patched here — the obvious patch is wrong, see below.
        //
        // A `Refuted` on this lane is credited as a public counterexample
        // (`verified_counterexample = true`) without anything accounting for how
        // the submitted `ChcVc` was PRODUCED. trust-mc's own attestation is
        // truthful but explicitly scoped: `ChcPdrEncodingConcreteness` says it
        // "cannot and does not attest how the submitted `ChcVc` itself was
        // produced ... that stage belongs to the producer of the obligation, and
        // consumers must account for it on their own side of the boundary."
        // Nothing does.
        //
        // For a function with a loop the producer emits the FLATTENED
        // single-formula CHC (`relations=1, clauses=1`, one nullary `error`
        // relation): no init, no transition, so the loop-carried local is a free
        // variable with no defining constraint. Measured, `ensures(*ret >= 0)`
        // over `{ let mut i=0; while i<n { i=i+1; } i }` — TRUE — and the same
        // body with `ensures(*ret >= 5)` — FALSE — produce byte-identical
        // queries but for the comparand, and BOTH are refuted. A verdict that is
        // the same whether the code is right or wrong is not evidence; the
        // 2026-07-13 seed reported UNKNOWN here.
        //
        // WHY THE FUNCTION-SCOPED FIX IS WRONG. Disclosing "this function has a
        // back edge" and demoting every `Refuted` on it was implemented, reviewed
        // and REVERTED: the defect is PATH-scoped, not function-scoped. A
        // realizable counterexample that never reads a loop-carried value gets
        // demoted too — `fn f(n: i32) -> i32 { let mut i=0; while i<3 { i=i+1; } n }`
        // with `ensures(*ret >= 5)` is genuinely defective at `n = 0` and would
        // stop reporting — and it takes >=16 `tests/trust-falsification/mutant/`
        // fixtures' only counterexample with it, flipping that gate GREEN -> RED.
        // It also stamps `ArithmeticSafety`/`BoundsCheck`/`Precondition` rows,
        // not just postconditions.
        //
        // The correct condition is per-OBLIGATION and reads the formula, not the
        // CFG: disclose only when this obligation's own formula carries a free
        // variable that is neither a function input nor defined by an equality
        // within the formula — i.e. an elided definition. That is decidable at
        // the producer (which knows the parameters) and preserves every exact
        // acyclic refutation, which is this lane's entire bug-detection value.
        // Note it cannot be done consumer-side: `vars` on the wire is
        // `{name, sort}` and every `TrustSpecVariable.origin` is `Inferred`, so
        // trust-bmc cannot tell a free input from a dropped-definition local.
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

/// Why one typed CHC/PDR `Refuted` verdict is not admissible as a public
/// counterexample. Every variant demotes the row to `Unknown`; they exist so the
/// diagnostic names WHICH stage failed, since the three are fixed by completely
/// different work.
#[cfg(feature = "trust-mc-native-solver")]
enum TypedChcRefutationRejection {
    /// The producer attests the submitted `ChcVc` does not faithfully encode
    /// the body. Nothing downstream can repair this; the CHC construction must
    /// emit the missing structure.
    ProducerEncoding(String),
    /// The solver returned no refutation witness at all.
    NoWitness,
    /// A witness was attached and failed consumer revalidation.
    WitnessRejected(String),
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
    retained_obligation: &trust_mc_core::MirChcPdrObligation,
    solved: &trust_mc_driver::TypedChcPdrFullVerification,
    expected_normalized_input: &TrustMcNativeTypedChcPdrNormalizedInput,
    expected_engine: trust_mc_core::ChcPdrEngine,
) -> Result<String, String> {
    validate_bound_typed_chc_pdr_refutation_witness_with_options(
        bundle,
        witness,
        obligation,
        retained_obligation,
        solved,
        expected_normalized_input,
        &trust_mc_core::ChcPdrSolveOptions::default().with_engine(expected_engine),
    )
}

#[cfg(feature = "trust-mc-native-solver")]
fn validate_bound_typed_chc_pdr_refutation_witness_with_options(
    bundle: &TrustContractBundle,
    witness: &trust_mc_core::ChcPdrRefutationWitness,
    obligation: &TrustObligation,
    retained_obligation: &trust_mc_core::MirChcPdrObligation,
    solved: &trust_mc_driver::TypedChcPdrFullVerification,
    expected_normalized_input: &TrustMcNativeTypedChcPdrNormalizedInput,
    expected_options: &trust_mc_core::ChcPdrSolveOptions,
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
    let verification_summary = validate_typed_chc_pdr_refutation_witness_with_options(
        witness,
        obligation,
        &solved.outcome.obligation_id,
        expected_normalized_input,
        expected_options,
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
        trust_mc_core::ChcPdrCexVerification::BoundedUnrollDirectSmtModel { k } => {
            // The declared budget must match the materialized payload, and a
            // concrete model must be present — the payload is the witness, not
            // a detachable flag.
            if counterexample.get("source").and_then(serde_json::Value::as_str)
                != Some("direct-smt-bounded-unroll-error-derivation")
                || counterexample.get("witness_model").is_none_or(serde_json::Value::is_null)
                || counterexample.get("unroll_k").and_then(serde_json::Value::as_u64) != Some(*k)
                || *k == 0
            {
                return Err(
                    "bounded-unroll direct-SMT witness has a missing or mismatched model payload"
                        .to_string(),
                );
            }
        }
        other => {
            return Err(format!(
                "unrecognized counterexample verification kind {other:?}; failing closed"
            ));
        }
    }
    // The classification and digest checks above bind the transport, but do
    // not prove that the serialized model follows a reachable derivation. Ask
    // a fresh consumer to validate/lower the retained request, rebuild the
    // direct or exact-k-unrolled CHC problem, reconstruct the supplied clause
    // path, and SMT-check the total sort-exact assignment. Producer-only AY
    // debug traces and every future class fail closed until they expose an
    // equivalent independent replay surface.
    let fresh_replay_summary =
        trust_mc_driver::independently_replay_typed_chc_pdr_refutation_witness_with_options(
            retained_obligation,
            expected_options,
            witness,
        )
        .map_err(|error| {
            format!(
                "counterexample failed fresh independent trace/model replay: {}",
                native_typed_chc_pdr_error_reason(error)
            )
        })?;

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

    // Trust (#51): the INDEPENDENT REPLAY BINDING. This check and the
    // `retained_obligation` parameter arrived together in 6958cc67a5 ("require
    // fresh replay for CHC refutations"), whose merge — its message still carries
    // the `# Conflicts:` marker — dropped the code BETWEEN them: the parameter was
    // left entirely unused and this summary undefined, so `main` did not compile.
    //
    // Restored as the binding the doc above states and the dropped code plainly
    // intended. The caller performs the fresh replay (it re-translates the native
    // bundle and derives `expected_normalized_input` from its own fresh row); what
    // was missing here is the check that the retained obligation is the one that
    // expectation actually came from. Without it the parameter is decorative and a
    // caller could pass an `expected_normalized_input` derived from a DIFFERENT
    // obligation than the one it claims to have retained.
    //
    // Nothing producer-supplied is consulted: both sides are recomputed consumer-side.
    let independent = trust_mc_driver::normalized_typed_chc_pdr_input(retained_obligation)
        .map_err(|error| {
            format!(
                "retained obligation does not re-normalize consumer-side: {}",
                native_typed_chc_pdr_error_reason(error)
            )
        })?;
    if independent.normalized_input_hash != expected_normalized_input.normalized_input_hash {
        return Err("independent re-normalization of the retained obligation disagrees with the \
             expected normalized input"
            .to_string());
    }
    if independent.obligation_set_hash != expected_normalized_input.obligation_set_hash {
        return Err("independent re-normalization of the retained obligation disagrees with the \
             expected obligation set"
            .to_string());
    }
    let retained_binding_summary = "independent consumer re-normalization of the retained obligation agrees with the \
         expected normalized input and obligation set";

    Ok(format!("{verification_summary}; {fresh_replay_summary}; {retained_binding_summary}"))
}

/// Validate the witness fields that bind a refutation to consumer-recomputed
/// obligation, formula, solver-configuration, and exact-lowering facts.
/// Production admission additionally calls
/// [`validate_bound_typed_chc_pdr_refutation_witness`] to bind the solver route,
/// cache key, payload schema, and materialized verdict artifact.
#[cfg(all(test, feature = "trust-mc-native-solver"))]
fn validate_typed_chc_pdr_refutation_witness(
    witness: &trust_mc_core::ChcPdrRefutationWitness,
    obligation: &TrustObligation,
    solver_obligation_id: &str,
    expected_normalized_input: &TrustMcNativeTypedChcPdrNormalizedInput,
    expected_engine: trust_mc_core::ChcPdrEngine,
) -> Result<String, String> {
    validate_typed_chc_pdr_refutation_witness_with_options(
        witness,
        obligation,
        solver_obligation_id,
        expected_normalized_input,
        &trust_mc_core::ChcPdrSolveOptions::default().with_engine(expected_engine),
    )
}

#[cfg(feature = "trust-mc-native-solver")]
fn validate_typed_chc_pdr_refutation_witness_with_options(
    witness: &trust_mc_core::ChcPdrRefutationWitness,
    obligation: &TrustObligation,
    solver_obligation_id: &str,
    expected_normalized_input: &TrustMcNativeTypedChcPdrNormalizedInput,
    expected_options: &trust_mc_core::ChcPdrSolveOptions,
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

    let expected_semantic_config =
        trust_mc_driver::typed_chc_pdr_semantic_config_sha256_for_options(
            expected_options,
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
        // REFUTATION-ONLY provenance: the k-bounded unroll under-approximates
        // (every unrolled clause is one original clause with predicates
        // renamed per level, so the found derivation projects onto the
        // original problem — the witness is real; the truncated prefix proves
        // nothing). This kind is recognized ONLY here, on the Refuted path;
        // no proof-credit gate consults counterexample verification kinds, so
        // it can never mint proof authority.
        trust_mc_core::ChcPdrCexVerification::BoundedUnrollDirectSmtModel { k } => {
            if *k == 0 {
                return Err("bounded-unroll witness declares a zero back-edge budget".to_string());
            }
            Ok(format!("direct-SMT bounded-unroll (k={k}) error-derivation witness model"))
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

/// The rows of the consumer's PRE-SOLVE translation that can carry a refuted
/// transport row's identity: every retained row whose lookup key is
/// `lookup_key` (an exact obligation id always shares its lookup key).
///
/// `translated_by_obligation` keeps the first row per key and
/// `translated_counts` counts them all, so the set is complete exactly when the
/// count is one. That is the only count a deferred obligation reaches the
/// transport with: a key with two or more rows is refused before solving
/// ("returned duplicate translated obligations"). Any other count yields no
/// row, which the refutation gate demotes to Unknown; it never hands the gate a
/// partial set from which one row could be singled out.
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
fn native_trust_ir_retained_rows_for<'a>(
    translated_by_obligation: &'a BTreeMap<
        String,
        trust_mc_trust_bmc::NativeTrustMcChcPdrObligation,
    >,
    translated_counts: &BTreeMap<String, usize>,
    lookup_key: &str,
) -> Vec<&'a trust_mc_trust_bmc::NativeTrustMcChcPdrObligation> {
    match (translated_counts.get(lookup_key), translated_by_obligation.get(lookup_key)) {
        (Some(1), Some(row)) => vec![row],
        _ => Vec::new(),
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
    use trust_verifier_api::native_routing_identity::{
        NativeRoutingIdentityPolicy, SuiteComparison, parse_native_routing_identity,
    };
    let identity = parse_native_routing_identity(
        obligation,
        NativeRoutingIdentityPolicy {
            canonical_id_fallback: false,
            canonical_metadata_numbers: true,
            suite_comparison: SuiteComparison::VerifierAliases,
        },
    )
    .ok()?;
    if identity.suite.as_deref()? != "trust-mc" {
        return None;
    }
    let request_id = identity.request_id?;
    let proof_id = identity.proof_obligation_id?;
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
    trust_mc_requests: std::collections::HashMap<u32, Vec<usize>>,
    request_proof_occurrences: std::collections::HashMap<(usize, u32), usize>,
    proof_owners: std::collections::HashMap<u32, Vec<u32>>,
    proofs: std::collections::HashMap<u32, Vec<usize>>,
    functions: std::collections::HashMap<u32, Vec<usize>>,
    obligation_sources: std::collections::HashMap<u32, Vec<usize>>,
    monomorphizations: std::collections::HashMap<u32, Vec<usize>>,
    replay_assertions: std::collections::HashMap<(usize, u32), Vec<usize>>,
    contracts: ContractChcCache,
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

        let req_len = native_bundle.requests.len();
        let proof_len = native_bundle.module.proof_obligations.len();
        let mut trust_mc_requests =
            std::collections::HashMap::<u32, Vec<usize>>::with_capacity(req_len);
        let mut request_proof_occurrences =
            std::collections::HashMap::<(usize, u32), usize>::with_capacity(proof_len);
        let mut proof_owners = std::collections::HashMap::<u32, Vec<u32>>::with_capacity(proof_len);
        let mut replay_assertions =
            std::collections::HashMap::<(usize, u32), Vec<usize>>::with_capacity(proof_len);
        for (request_index, request) in native_bundle.requests.iter().enumerate() {
            let trust_ir::NativeVerificationRequest::TrustMc(request) = request else {
                continue;
            };
            trust_mc_requests.entry(request.id.index()).or_default().push(request_index);
            let mut owned_proofs =
                std::collections::HashSet::with_capacity(request.obligations.len());
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

        let mut proofs = std::collections::HashMap::<u32, Vec<usize>>::with_capacity(proof_len);
        for (index, proof) in native_bundle.module.proof_obligations.iter().enumerate() {
            proofs.entry(proof.id.index()).or_default().push(index);
        }
        let mut functions = std::collections::HashMap::<u32, Vec<usize>>::with_capacity(
            native_bundle.module.functions.len(),
        );
        for (index, function) in native_bundle.module.functions.iter().enumerate() {
            functions.entry(function.id.index()).or_default().push(index);
        }
        let mut obligation_sources = std::collections::HashMap::<u32, Vec<usize>>::with_capacity(
            native_bundle.compiler_facts.obligation_sources.len(),
        );
        for (index, source) in native_bundle.compiler_facts.obligation_sources.iter().enumerate() {
            obligation_sources.entry(source.obligation.index()).or_default().push(index);
        }
        let mut monomorphizations = std::collections::HashMap::<u32, Vec<usize>>::with_capacity(
            native_bundle.compiler_facts.monomorphizations.len(),
        );
        for (index, fact) in native_bundle.compiler_facts.monomorphizations.iter().enumerate() {
            monomorphizations.entry(fact.id.index()).or_default().push(index);
        }
        let contracts = ContractChcCache::new(&public_bundle.contracts);

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
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NativePublicClaimKind {
    ExistingMcClaim,
    RawPostcondition { admission_stop: Option<NativeRawPostconditionStop> },
}

/// An extra replay premise is an admission refusal, not an encoding gap.
/// An Assume instruction is part of the submitted program instead; the raw
/// source clause still has no MC encoding, and a fallback must model that body.
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NativeRawPostconditionStop {
    ReplayAssumptions,
}

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
impl NativeRawPostconditionStop {
    fn diagnostic(self) -> &'static str {
        match self {
            Self::ReplayAssumptions => {
                "raw postcondition request carries native replay assumptions"
            }
        }
    }
}

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
fn is_raw_source_postcondition(
    bundle: &TrustContractBundle,
    public: &TrustObligation,
) -> Result<bool, String> {
    let markers: Vec<_> = public
        .metadata
        .iter()
        .filter(|entry| entry.key == "trust.ir.raw-source-postcondition.v1")
        .collect();
    if markers.len() > 1 || markers.first().is_some_and(|entry| entry.value != "query-bound") {
        return Err("raw source postcondition marker is not unique and exact".into());
    }
    if !trust_verifier_api::native_contract_claim::has_raw_source_postcondition_contract(
        bundle, public,
    ) {
        return Ok(false);
    }
    if public.metadata.iter().any(|entry| entry.key.starts_with("trust.vc.")) {
        return Ok(false);
    }
    if let Some(encoded) =
        obligation_metadata_value(public, trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY)
    {
        let context: trust_verifier_api::ObligationContext =
            trust_types::json_depth::from_str_deep(encoded)
                .map_err(|error| format!("invalid raw postcondition context: {error}"))?;
        if matches!(
            context.origin,
            trust_verifier_api::ObligationOrigin::VerificationCondition { .. }
        ) {
            return Ok(false);
        }
    }
    if !public.summary_facts.is_empty() {
        return Err("raw source postcondition carries unadmitted summary assumptions".into());
    }
    Ok(true)
}

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
fn validate_native_trust_ir_public_claim_binding(
    public_bundle: &TrustContractBundle,
    public_obligation: &TrustObligation,
    native_bundle: &trust_ir::NativeVerificationBundle,
    context: &NativeTrustIrPublicClaimBindingContext,
) -> Result<NativePublicClaimKind, String> {
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
    use trust_verifier_api::native_contract_claim::NativePublicIdentityError;
    trust_verifier_api::native_contract_claim::validate_native_public_obligation_identity(
        proof,
        &public_obligation.obligation_id,
        canonical_public_digest,
    )
    .map_err(|error| match error {
        NativePublicIdentityError::ObligationIdMismatch { actual } => format!(
            "native TrustIr proof obligation {} embeds public obligation id {:?}, but the verifier requested {:?}",
            proof_id.index(), actual, public_obligation.obligation_id
        ),
        NativePublicIdentityError::SemanticDigestMismatch { actual } => format!(
            "native TrustIr proof obligation {} embedded public semantic digest {} does not match canonical public claim sha256:{canonical_public_digest}",
            proof_id.index(), actual
        ),
        other => format!(
            "native TrustIr proof obligation {} has an invalid public-obligation identity: {other}",
            proof_id.index()
        ),
    })?;

    trust_verifier_api::native_contract_claim::validate_native_public_source_projection(
        &native_bundle.module,
        proof,
        public_obligation,
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
    let claim = if is_raw_source_postcondition(public_bundle, public_obligation)? {
        trust_verifier_api::native_contract_claim::validate_native_public_contract_claim(
            &native_bundle.module,
            proof,
            public_bundle,
            public_obligation,
        )?;
        let admission_stop = if request
            .provenance
            .replay_context
            .atoms
            .iter()
            .any(|atom| atom.kind == trust_ir::NativeReplayAtomKind::Assumption)
        {
            Some(NativeRawPostconditionStop::ReplayAssumptions)
        } else {
            None
        };
        // This candidate leaves the validator only after the remaining replay
        // assertion and CHC marker checks below. A later identity error must
        // remain an unclassified error, even when the body also has assumptions.
        NativePublicClaimKind::RawPostcondition { admission_stop }
    } else {
        validate_native_trust_ir_public_formula_binding(
            public_obligation,
            proof_id,
            embedded_source,
            formula,
        )?;
        NativePublicClaimKind::ExistingMcClaim
    };
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
    Ok(claim)
}

/// The exact inverse of the compiler's `native_trust_ir_route_for_api_obligation`,
/// restricted to the rows it hands to the trust-mc suite. A pairing this table
/// accepts is one the producer could itself have emitted for this public row —
/// nothing wider.
///
/// Binding is IDENTITY reconciliation, never proof authority: it only decides
/// that a native proof unit is the one minted for this public obligation. Every
/// row admitted here still has to clear
/// `validate_native_trust_ir_public_formula_binding` (a formula-less row must
/// carry the exact source envelope and may not reference contract/proof-item
/// data) and, in the caller, the direct/transport gates — of which
/// `obligation_is_whole_function_panic_freedom` is the only door to the N:1
/// transport proof and admits `Assertion` alone.
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
fn trust_mc_public_native_obligation_kind_matches(
    public: &TrustObligation,
    native: &trust_ir::ObligationKind,
) -> bool {
    match (&public.kind, native) {
        (
            ObligationKind::Assertion | ObligationKind::ArithmeticSafety,
            trust_ir::ObligationKind::PanicFreedom,
        ) => true,
        (
            ObligationKind::Precondition | ObligationKind::Postcondition,
            trust_ir::ObligationKind::PanicFreedom,
        ) => obligation_metadata_value(public, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY).is_some(),
        // v6/D3 (`79558a8f2e`, "retire TrustWP verdict authority") moved the
        // payload-less half of Precondition/Postcondition and the
        // envelope-less half of LoopInvariant/Termination from trust-wp to
        // trust-mc WITHOUT changing the native kinds they project onto. This
        // table was written on 2026-07-14, while those four rows were still
        // trust-wp-owned, and was not extended — so the producer emitted
        // pairings the consumer could not accept and the row died at the
        // identity gate reading `kind Postcondition does not match native
        // proof obligation 0 kind Postcondition`. That is drift, not a
        // decision: `native_trust_ir_obligation_cause_projection` right below
        // already projects these three native kinds, and the sibling trust-vc
        // lane shares ONE mapping function between emission and validation
        // exactly so this cannot happen
        // (`trust_vc_native_trust_ir_kind_for_public_obligation`).
        //
        // The guards are the exact NEGATION of the two arms above, using the
        // same predicates, so each public kind still admits exactly ONE native
        // kind and no pairing outside the producer's own routing becomes
        // bindable. In particular a payload-BEARING precondition/postcondition
        // must still bind to `PanicFreedom`, and an E4/E5 row carrying the
        // typed envelope must still bind to `PanicFreedom`.
        //
        // These rows carry no formula, so nothing downstream can credit them:
        // they reach the `Ok(None)` fallthrough and record Unsupported. What
        // changes is that the refusal now names the real reason.
        (ObligationKind::Precondition, trust_ir::ObligationKind::Precondition)
        | (ObligationKind::Postcondition, trust_ir::ObligationKind::Postcondition) => {
            obligation_metadata_value(public, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY).is_none()
        }
        (
            ObligationKind::LoopInvariant | ObligationKind::Termination,
            trust_ir::ObligationKind::PanicFreedom,
        ) => is_typed_body_aware_e4_e5_obligation(public),
        (ObligationKind::LoopInvariant, trust_ir::ObligationKind::LoopInvariant)
        | (ObligationKind::Termination, trust_ir::ObligationKind::TranslationValidation) => {
            !is_typed_body_aware_e4_e5_obligation(public)
        }
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
                    "public obligation `{}` has no public formula metadata encoding its semantic contract/proof-item goal; source-location identity alone does not encode that goal",
                    public.obligation_id
                ));
            }
            // The source.v1 record is closed to these four fields. Public identity
            // is reconciled separately through the embedded public digest and
            // compiler facts; duplicating it here changes the producer's schema.
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
        let matching_marker_indices = context.contracts.indices(marker_id);
        let [marker_index] = matching_marker_indices else {
            return Err(format!(
                "obligation `{}` names diagnostic native trust-mc synthetic contract `{marker_id}`, but the bundle contains {} matching contracts; expected exactly one",
                obligation.obligation_id,
                matching_marker_indices.len()
            ));
        };
        let marker = bundle.contracts.get(*marker_index).ok_or_else(|| {
            "prevalidated native trust-mc contract index is out of bounds".to_string()
        })?;
        validate_native_trust_ir_synthetic_trust_mc_contract_value(marker, obligation, marker_id)?;
        let marker_input =
            context.contracts.parsed_input(*marker_index, marker)?.ok_or_else(|| {
                format!(
                    "authenticated native trust-mc marker contract `{marker_id}` has no typed CHC input"
                )
            })?;
        validate_trust_mc_typed_chc_binding_with_cache(
            marker,
            obligation,
            marker_input,
            Some((&context.contracts, *marker_index)),
        )?;
        validate_native_trust_ir_typed_chc_function_projection(
            marker,
            marker_input,
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
    let matching_contract_indices = context.contracts.indices(contract_id);
    let [contract_index] = matching_contract_indices else {
        return Err(format!(
            "public obligation `{}` references contract `{contract_id}`, but the bundle contains {} exact matches",
            obligation.obligation_id,
            matching_contract_indices.len()
        ));
    };
    let contract = bundle.contracts.get(*contract_index).ok_or_else(|| {
        "prevalidated native trust-mc contract index is out of bounds".to_string()
    })?;
    let Some(input) = context.contracts.parsed_input(*contract_index, contract)? else {
        return Ok(());
    };
    validate_native_trust_ir_typed_chc_function_projection(
        contract,
        input,
        native_function_name,
        native_function_id,
        request_id,
        proof_id,
        input.native_metadata.is_some(),
    )?;
    let carries_binding =
        contract.metadata.iter().any(|entry| entry.key == TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY);
    if carries_binding || input.native_metadata.is_some() {
        validate_trust_mc_typed_chc_binding_with_cache(
            contract,
            obligation,
            input,
            Some((&context.contracts, *contract_index)),
        )?;
        return Ok(());
    }

    validate_compiler_canonical_trust_mc_typed_chc_contract(contract, obligation, input)?;
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
        validate_native_trust_mc_row_request_config(&evidence.translated)?;
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
fn validate_native_trust_mc_row_request_config(
    row: &trust_mc_trust_bmc::NativeTrustMcChcPdrObligation,
) -> Result<(), String> {
    if row.obligation.native_metadata.as_ref().and_then(|metadata| metadata.request_config.as_ref())
        != Some(row.request_config.binding())
    {
        return Err("native TrustIr pre-solve request configuration differs from its typed obligation binding".into());
    }
    Ok(())
}

#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
fn validate_native_trust_mc_consumer_request_config(
    fresh: &trust_mc_trust_bmc::NativeTrustMcChcPdrObligation,
    solved: &trust_mc_trust_bmc::NativeTrustMcChcPdrObligation,
) -> Result<(), String> {
    validate_native_trust_mc_row_request_config(fresh)?;
    validate_native_trust_mc_row_request_config(solved)?;
    if fresh.request_config != solved.request_config {
        return Err(
            "solved native request configuration differs from the independent pre-solve request"
                .into(),
        );
    }
    Ok(())
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
        ObligationKind::LoopInvariant,
        ObligationKind::Termination,
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
            // (`¬postcond ∧ body_defs`). A
            // Postcondition WITHOUT a typed CHC payload fails closed to Unsupported
            // in `trust_mc_typed_chc_lowering`, so owning the kind never fabricates
            // a proof.
            | ObligationKind::Postcondition
            // Trust (P1.2 precedent, extended to preconditions): the call-site
            // `#[requires]` VC is the same payload shape (`¬precond ∧ body_defs`)
            // and reaches the adapter only when the router's payload-aware route
            // dispatched it; a Precondition without a typed CHC payload stays
            // TrustMC-owned and fails closed identically.
            | ObligationKind::Precondition
            // v6/D3: body-aware loop/termination VCs carry the same typed CHC
            // violation envelope. Payload-less rows remain owned but decline
            // fail-closed in the lowering gate.
            | ObligationKind::LoopInvariant
            | ObligationKind::Termination
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

// ---------------------------------------------------------------------------
// targo-trust doctor smoke bundle
// ---------------------------------------------------------------------------

/// Public obligation id of the targo-trust doctor's canonical in-process
/// trust-mc smoke request (see [`doctor_smoke_bundle`]).
pub const DOCTOR_SMOKE_PUBLIC_OBLIGATION_ID: &str = "vc:targo-trust:doctor:trust-mc:smoke:0";
const DOCTOR_SMOKE_NATIVE_REQUEST_ID: u32 = 1;
const DOCTOR_SMOKE_PROOF_OBLIGATION_ID: u32 = 0;
// Synthetic doctor-smoke provenance digests (64 lowercase hex chars). The
// bundle's subject is a doctor artifact, not a program: these digests bind the
// bundle's own records to each other exactly the way the compiler's real
// source/VC digests would, and never stand for any source or VC outside this
// bundle. The bundle can therefore never be mistaken for (or replayed as)
// compiler output for a real function.
const DOCTOR_SMOKE_SOURCE_DIGEST: &str =
    "ad0cad0cad0cad0cad0cad0cad0cad0cad0cad0cad0cad0cad0cad0cad0cad0c";
const DOCTOR_SMOKE_VC_DIGEST: &str =
    "bd0cbd0cbd0cbd0cbd0cbd0cbd0cbd0cbd0cbd0cbd0cbd0cbd0cbd0cbd0cbd0c";

/// Canonical one-obligation typed-CHC bundle for the targo-trust doctor's
/// in-process trust-mc smoke probe.
///
/// CONSTRUCTION ONLY. This function builds data and routes through no
/// verification path: it mints no evidence, no receipt, and no authority.
/// The doctor verifies the returned request exclusively through the public,
/// validated [`VerificationEngine::verify_with_context`] boundary, so the
/// smoke result carries exactly the authority that public dispatch grants a
/// caller-submitted bundle — today that is a validated NON-definitive
/// candidate (public dispatch never mints `Proved` for typed CHC/PDR without
/// a deliverable live receipt; see
/// `evidence_and_fresh_exact_direct_receipt_from_typed_chc_pdr_obligation`).
///
/// The bundle is the compiler-canonical pre-build-pivot shape (public
/// canonical contract + authenticated native marker contract, cf. the
/// `compiler_canonical_trust_mc_bundle` test fixture): one ArithmeticSafety
/// obligation over a trivially safe typed CHC — `entry(false)` with
/// `error :- entry(ok), ok` — whose `error` query is unreachable, so a
/// compiled-in native solver genuinely solves it in-process.
#[must_use]
pub fn doctor_smoke_bundle() -> (TrustContractBundle, TrustObligation) {
    let native_obligation_id = format!(
        "trust_ir-native-trust_mc-request-{DOCTOR_SMOKE_NATIVE_REQUEST_ID}-proof-{DOCTOR_SMOKE_PROOF_OBLIGATION_ID}"
    );
    let marker_contract_id = format!("contract:trust-mc-typed-chc:{native_obligation_id}");
    let canonical_contract_id =
        format!("contract:trust-mc-typed-chc-public:{DOCTOR_SMOKE_PUBLIC_OBLIGATION_ID}");

    // Trivially safe typed CHC: entry(false); error :- entry(ok), ok.
    let ok_var = serde_json::json!({ "kind": "var", "name": "ok", "sort": { "kind": "bool" } });
    let mut marker_value = serde_json::json!({
        "schema_version": TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION,
        "origin": "mir_derived",
        "obligation_id": native_obligation_id,
        "function_name": "targo_trust_doctor::smoke",
        "query": { "target": "error" },
        "vars": [
            { "name": "ok", "sort": { "kind": "bool" } }
        ],
        "relations": [
            { "name": "entry", "arg_sorts": [{ "kind": "bool" }] },
            { "name": "error" }
        ],
        "rules": [
            {
                "head": {
                    "name": "entry",
                    "args": [ { "kind": "bool_const", "value": false } ]
                },
            },
            {
                "head": { "name": "error" },
                "body": {
                    "relation": { "name": "entry", "args": [ ok_var.clone() ] },
                    "constraints": [ ok_var ]
                },
            }
        ],
    });
    let native_digest = |seed: u8| {
        trust_mc_core::NativeArtifactDigest::new("sha256", format!("{seed:02x}").repeat(32))
    };
    let native_metadata = trust_mc_core::NativeTypedChcObligationMetadata::new(
        "Trust",
        "rust-mir",
        Some(native_digest(0x11)),
        native_digest(0x22),
        trust_mc_core::NativeArtifactDigest::new("trust_ir-stable-v1", "33".repeat(32)),
        DOCTOR_SMOKE_NATIVE_REQUEST_ID,
        "chc",
        9,
        vec![DOCTOR_SMOKE_PROOF_OBLIGATION_ID],
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
            proof_obligation_id: DOCTOR_SMOKE_PROOF_OBLIGATION_ID,
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
            invocation: format!("trust-mc native request {DOCTOR_SMOKE_NATIVE_REQUEST_ID}"),
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
                proof_obligation_id: Some(DOCTOR_SMOKE_PROOF_OBLIGATION_ID),
                assertion_id: Some(7),
                span: Some(trust_mc_core::NativeSourceSpanMetadata { file: 0, line: 10, col: 3 }),
            }],
            unsupported_modes: Vec::new(),
        },
    );
    marker_value["native_metadata"] =
        serde_json::to_value(native_metadata).expect("doctor smoke native metadata serializes");

    let synthetic_digest =
        trust_mc_typed_chc_value_digest(&marker_value).expect("doctor smoke typed CHC digests");
    let binding = serde_json::json!({
        "schema_version": TRUST_MC_TYPED_CHC_BINDING_SCHEMA_VERSION,
        "typed_chc_schema": TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION,
        "public_obligation_id": DOCTOR_SMOKE_PUBLIC_OBLIGATION_ID,
        "native_obligation_id": native_obligation_id,
        "synthetic_contract_id": marker_contract_id,
        "source_digest": { "algorithm": "sha256", "value": DOCTOR_SMOKE_SOURCE_DIGEST },
        "vc_digest": { "algorithm": "sha256", "value": DOCTOR_SMOKE_VC_DIGEST },
        "synthetic_chc_digest": { "algorithm": "sha256", "value": synthetic_digest },
    });
    let binding_json =
        serde_json::to_string(&binding).expect("doctor smoke binding metadata serializes");
    let typed_chc_binding_entries = [
        MetadataEntry {
            key: TRUST_MC_TYPED_CHC_SOURCE_DIGEST_METADATA_KEY.to_string(),
            value: DOCTOR_SMOKE_SOURCE_DIGEST.to_string(),
        },
        MetadataEntry {
            key: TRUST_MC_TYPED_CHC_VC_DIGEST_METADATA_KEY.to_string(),
            value: DOCTOR_SMOKE_VC_DIGEST.to_string(),
        },
        MetadataEntry {
            key: TRUST_MC_TYPED_CHC_SYNTHETIC_DIGEST_METADATA_KEY.to_string(),
            value: synthetic_digest,
        },
        MetadataEntry {
            key: TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY.to_string(),
            value: binding_json,
        },
    ];

    let marker = TrustContract {
        contract_id: marker_contract_id.clone(),
        kind: ContractKind::Asserts,
        predicate: ContractPredicate::MathIr {
            schema: TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA.to_string(),
            value: marker_value.clone(),
        },
        source: SourceLocation::default(),
        metadata: std::iter::once(MetadataEntry {
            key: "trust-mc.typed-chc-obligation.source".to_string(),
            value: "compiler-native-trust-ir-trust-spec-vc".to_string(),
        })
        .chain(typed_chc_binding_entries.iter().cloned())
        .collect(),
    };

    let mut canonical_value = marker_value;
    canonical_value["obligation_id"] = serde_json::json!(DOCTOR_SMOKE_PUBLIC_OBLIGATION_ID);
    canonical_value
        .as_object_mut()
        .expect("doctor smoke typed CHC payload is an object")
        .remove("native_metadata");
    let canonical = TrustContract {
        contract_id: canonical_contract_id.clone(),
        kind: ContractKind::Asserts,
        predicate: ContractPredicate::MathIr {
            schema: TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA.to_string(),
            value: canonical_value,
        },
        source: SourceLocation::default(),
        metadata: vec![MetadataEntry {
            key: "trust-trust-mc.typed-chc-obligation.source".to_string(),
            value: "compiler-public-trust-spec-vc".to_string(),
        }],
    };

    let obligation = TrustObligation {
        obligation_id: DOCTOR_SMOKE_PUBLIC_OBLIGATION_ID.to_string(),
        kind: ObligationKind::ArithmeticSafety,
        contract_id: Some(canonical_contract_id),
        proof_item_id: None,
        source: SourceLocation::default(),
        description: "targo-trust doctor in-process trust-mc canonical typed-CHC smoke".to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: [
            MetadataEntry {
                key: TRUST_SOURCE_DIGEST_METADATA_KEY.to_string(),
                value: DOCTOR_SMOKE_SOURCE_DIGEST.to_string(),
            },
            MetadataEntry {
                key: TRUST_VC_DIGEST_METADATA_KEY.to_string(),
                value: DOCTOR_SMOKE_VC_DIGEST.to_string(),
            },
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY.to_string(),
                value: "trust-mc".to_string(),
            },
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY.to_string(),
                value: DOCTOR_SMOKE_NATIVE_REQUEST_ID.to_string(),
            },
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY.to_string(),
                value: DOCTOR_SMOKE_PROOF_OBLIGATION_ID.to_string(),
            },
            MetadataEntry {
                key: TRUST_MC_TYPED_CHC_SYNTHETIC_CONTRACT_METADATA_KEY.to_string(),
                value: marker_contract_id,
            },
        ]
        .into_iter()
        .chain(typed_chc_binding_entries)
        .collect(),
    };

    let mut bundle = TrustContractBundle::empty(
        "targo-trust-doctor-trust-mc-smoke-bundle",
        BundleSubject::Artifact { name: "trust-mc".to_string(), kind: "doctor-smoke".to_string() },
    );
    bundle.contracts = vec![canonical, marker];
    bundle.obligations = vec![obligation.clone()];
    (bundle, obligation)
}

#[cfg(test)]
mod tests {
    use trust_verifier_api::{
        BundleSubject, ContractKind, EvidenceDisposition, SourceLocation, TrustContract,
        VerificationRunResult, VerificationRunStatus, VerifierExecutionContext,
    };

    use super::*;

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    mod division_domain;

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    mod refutation_scope;

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    mod source_envelope;

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

    /// Test-only flat typed-VC fidelity premise. The compiler now emits `exact`
    /// for its admitted flat fragment; this helper is not a native source
    /// correspondence capability.
    #[cfg(feature = "trust-mc-native-solver")]
    fn attest_synthetic_typed_chc_encoding_exact(obligation: &mut TrustObligation) {
        obligation.metadata.push(MetadataEntry {
            key: TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_METADATA_KEY.to_string(),
            value: TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_EXACT.to_string(),
        });
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
        let predicate = trust_verifier_api::TrustSpecPredicate::new(
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
        let predicate = trust_verifier_api::TrustSpecPredicate::new(
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

    /// The same result-free tautology with the schema-level `Result` node in
    /// only the positive body-definition conjunct. Global `Result` presence
    /// must not bypass the negated-clause discriminator.
    fn add_result_node_only_in_body_definition_formula(obligation: &mut TrustObligation) {
        use trust_verifier_api::{TrustSpecBinaryOp as Op, TrustSpecSort};
        let predicate = trust_verifier_api::TrustSpecPredicate::new(
            trust_verifier_api::TrustSpecExpr::binary(
                Op::And,
                trust_verifier_api::TrustSpecExpr::binary(
                    Op::Eq,
                    trust_verifier_api::TrustSpecExpr::result(TrustSpecSort::Int),
                    spec_var("x"),
                ),
                trust_verifier_api::TrustSpecExpr::unary(
                    trust_verifier_api::TrustSpecUnaryOp::Not,
                    trust_verifier_api::TrustSpecExpr::binary(Op::Ge, spec_var("x"), spec_var("x")),
                ),
            ),
            vec![spec_var_decl("x")],
        );
        predicate.validate().expect("schema-level result-node predicate must validate");
        add_vc_formula_payload(obligation, &predicate, "postcondition");
    }

    /// A negated body fact references `Result`, while the terminal negated VC
    /// remains result-free. Searching every `Not` subtree would admit this
    /// shape even though the actual postcondition clause constrains no
    /// post-state value.
    fn add_negated_result_only_in_body_definition_formula(obligation: &mut TrustObligation) {
        use trust_verifier_api::{TrustSpecBinaryOp as Op, TrustSpecSort, TrustSpecUnaryOp};
        let predicate = trust_verifier_api::TrustSpecPredicate::new(
            trust_verifier_api::TrustSpecExpr::binary(
                Op::And,
                trust_verifier_api::TrustSpecExpr::unary(
                    TrustSpecUnaryOp::Not,
                    trust_verifier_api::TrustSpecExpr::result(TrustSpecSort::Bool),
                ),
                trust_verifier_api::TrustSpecExpr::unary(
                    TrustSpecUnaryOp::Not,
                    trust_verifier_api::TrustSpecExpr::binary(Op::Ge, spec_var("x"), spec_var("x")),
                ),
            ),
            vec![spec_var_decl("x")],
        );
        predicate.validate().expect("negated body-result predicate must validate");
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

    /// The fresh-exact standalone-formula admission and its guardrails:
    /// compiler-authenticated TrustMC-owned kinds enter, postconditions retain
    /// their stricter result-reference discriminator, and unrelated kinds or
    /// formula-less rows stay out.
    #[test]
    fn exact_direct_admission_scopes_to_authenticated_standalone_formulas() {
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

        let mut result_node_bypass =
            obligation(ObligationKind::Postcondition, "obligation:demo::f:post:result-node");
        add_result_node_only_in_body_definition_formula(&mut result_node_bypass);
        assert!(
            !is_typed_body_aware_exact_direct_obligation(&result_node_bypass),
            "a Result node outside the negated clause must not bypass the E9 guard"
        );

        let mut negated_result_node_bypass = obligation(
            ObligationKind::Postcondition,
            "obligation:demo::f:post:negated-result-node",
        );
        add_negated_result_only_in_body_definition_formula(&mut negated_result_node_bypass);
        assert!(
            !is_typed_body_aware_exact_direct_obligation(&negated_result_node_bypass),
            "Not(Result) in a prepended body fact must not masquerade as the terminal negated clause"
        );

        let mut loop_row = obligation(ObligationKind::LoopInvariant, "obligation:demo::f:e4:0");
        add_typed_body_aware_vc_formula(&mut loop_row);
        assert!(is_typed_body_aware_e4_e5_obligation(&loop_row), "E4/E5 admission unchanged");
        assert!(
            is_typed_body_aware_exact_direct_obligation(&loop_row),
            "the widened predicate is a superset of E4/E5"
        );

        for (index, kind) in [
            ObligationKind::ArithmeticSafety,
            ObligationKind::Assertion,
            ObligationKind::Precondition,
        ]
        .into_iter()
        .enumerate()
        {
            let mut standalone = obligation(kind, &format!("obligation:demo::f:formula:{index}"));
            add_typed_body_aware_vc_formula(&mut standalone);
            assert!(
                is_seal_eligible_compiler_formula_obligation(&standalone),
                "current compiler-authenticated standalone formula kind must be seal-eligible: {:?}",
                standalone.kind
            );
            assert!(
                is_typed_body_aware_exact_direct_obligation(&standalone),
                "seal-eligible non-postcondition formula must enter the fresh-exact lane: {:?}",
                standalone.kind
            );
            assert!(!is_typed_body_aware_e4_e5_obligation(&standalone));
        }

        for kind in [ObligationKind::Invariant, ObligationKind::Protocol] {
            let mut producer_inert = obligation(kind, "obligation:demo::f:producer-inert");
            add_typed_body_aware_vc_formula(&mut producer_inert);
            assert!(
                !is_seal_eligible_compiler_formula_obligation(&producer_inert)
                    && !is_typed_body_aware_exact_direct_obligation(&producer_inert),
                "a kind outside the compiler direct-CHC producer set stays out: {:?}",
                producer_inert.kind
            );
        }

        let bare = obligation(ObligationKind::ArithmeticSafety, "obligation:demo::f:bare:0");
        assert!(
            !is_typed_body_aware_exact_direct_obligation(&bare),
            "a formula-less safety row must not request a fresh receipt"
        );

        let mut unrelated = obligation(ObligationKind::MemorySafety, "obligation:demo::f:memory:0");
        add_typed_body_aware_vc_formula(&mut unrelated);
        assert!(
            !is_typed_body_aware_exact_direct_obligation(&unrelated),
            "a kind outside the exact direct TrustMC formula set stays out regardless of payload"
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
    fn compiler_style_source_assume_tmir_bundle() -> trust_ir::NativeVerificationBundle {
        let mut bundle = compiler_style_safe_tmir_bundle();
        let function = bundle
            .module
            .functions
            .iter_mut()
            .find(|function| function.name == "tmir_native_checked_branch")
            .expect("fixture includes requested TrustMC function");
        let entry = function.entry;
        let block = function.block_mut(entry).expect("fixture entry block");
        let condition = block
            .body
            .iter()
            .find_map(|node| {
                matches!(&node.inst, trust_ir::Inst::ICmp { .. })
                    .then(|| node.results.first().copied())
                    .flatten()
            })
            .expect("fixture entry computes its branch condition");
        let terminator = block.body.len().checked_sub(1).expect("fixture entry terminator");
        block.body.insert(
            terminator,
            trust_ir::InstrNode::new(trust_ir::Inst::Assume { cond: condition }),
        );
        bundle
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

        let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
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
            options: trust_ir_bridge::trust_mc_chc_request_options(),
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

    // Trust (bounded-unroll refutation lane): the compiler-style bundle whose
    // requested function is the u8 shift-reduction LOOP mirror
    // (`t += (x << 4)` over 64 iterations, loop state threaded as explicit
    // block arguments) — a genuinely input-dependent overflow that no proof
    // lane can prove and only the k-bounded-unroll escalation can refute with
    // a machine-checked witness. Producer delivery lands on
    // `NativeTrustIrChcPdrBundleEvidence::refuted`.
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn compiler_style_loop_overflow_tmir_bundle() -> trust_ir::NativeVerificationBundle {
        use trust_ir::inst::{BinOp, ICmpOp};
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

        let mut mb = ModuleBuilder::new("native_trust_ir_chc_loop_overflow_bundle");
        let ft = mb.add_func_type(vec![Ty::U8], vec![Ty::U8]);
        {
            let mut fb = mb.function("tmir_native_loop_accumulator", ft);
            let entry = fb.create_block();
            let header = fb.create_block();
            let body = fb.create_block();
            let exit = fb.create_block();

            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let x = fb.add_block_param(entry, Ty::U8);
            let four = fb.iconst(Ty::U8, 4);
            let addend = fb.binop(BinOp::Shl, Ty::U8, x, four);
            let zero_i = fb.iconst(Ty::U64, 0);
            let zero_t = fb.iconst(Ty::U8, 0);
            fb.br(header, vec![zero_i, zero_t]);

            // Loop state travels as explicit block arguments (the shape the
            // CHC translator threads exactly, keeping the encoding grounded).
            let i = fb.add_block_param(header, Ty::U64);
            let t = fb.add_block_param(header, Ty::U8);
            fb.switch_to_block(header);
            let bound = fb.iconst(Ty::U64, 64);
            let in_loop = fb.icmp(ICmpOp::Ult, Ty::U64, i, bound);
            fb.condbr(in_loop, body, vec![i, t], exit, vec![t]);

            let i_body = fb.add_block_param(body, Ty::U64);
            let t_body = fb.add_block_param(body, Ty::U8);
            fb.switch_to_block(body);
            let t_next = fb.add(Ty::U8, t_body, addend);
            let one = fb.iconst(Ty::U64, 1);
            let i_next = fb.add(Ty::U64, i_body, one);
            fb.br(header, vec![i_next, t_next]);

            let t_exit = fb.add_block_param(exit, Ty::U8);
            fb.switch_to_block(exit);
            fb.ret(vec![t_exit]);
            fb.build();
        }

        let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
        module.target_info = Some(compiler_style_proof_grade_target());
        let trust_mc_function = module
            .functions
            .iter()
            .find(|func| func.name == "tmir_native_loop_accumulator")
            .expect("fixture includes requested trust_mc function")
            .id;
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::PanicFreedom,
                ProofStatus::Pending,
                "native TrustIr loop-carried accumulator add does not overflow",
            )
            .with_formula(ProofFormula::smtlib2("tmir_native_loop_accumulator_safe", "Bool")),
        );
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
                source_item:
                    "native_trust_ir_chc_loop_overflow_bundle::tmir_native_loop_accumulator"
                        .to_owned(),
                symbol: "_RNvNtC6native28tmir_native_loop_accumulator".to_owned(),
                generic_args: Vec::new(),
                function: Some(trust_mc_function),
                stable_digest: ProofDigest::sha256([0x63; 32]),
            }],
            obligation_sources: vec![NativeObligationSource {
                obligation: ProofId::new(0),
                public_obligation_id: "vc:trust-bmc:loop-overflow:0".to_string(),
                function: Some(trust_mc_function),
                span: Some(source_span),
                assertion_id: Some(NativeAssertionId::new(0)),
                cause: NativeObligationCause::OverflowCheck,
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
            options: trust_ir_bridge::trust_mc_chc_request_options(),
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
                            ProofFormula::smtlib2(
                                "tmir_native_loop_accumulator_guard",
                                "Bool",
                            ),
                        )
                        .with_obligation(ProofId::new(0))
                        .with_span(source_span),
                    )
                    .with_atom(
                        NativeReplayAtom::assertion(
                            NativeReplayAtomId::new(1),
                            ProofFormula::smtlib2("tmir_native_loop_accumulator_safe", "Bool"),
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

        let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
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
            options: trust_ir_bridge::trust_mc_chc_request_options(),
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
            options: trust_ir_bridge::trust_mc_chc_request_options(),
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

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn whole_function_receipt_survives_the_actual_native_solve() {
        let bundle = compiler_style_panic_freedom_public_bundle();
        let mut native =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        // Unit-only model of the existing audited live compiler issuer. This
        // is not evidence that the real compiler lowering path was executed.
        let source = trust_ir::SourceGenerationAuthority::mint_from_live_lowering(&mut native)
            .expect("valid unit fixture source authority");
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let mut outcome = adapter.evidence_from_native_trust_ir_bundle_with_source_authority_and_deadline_and_fresh_receipts(
            &bundle, &bundle.obligations, &native, &source,
            Some(Instant::now() + std::time::Duration::from_secs(10)),
        );
        assert_eq!(outcome.evidence.len(), 1);
        assert_eq!(outcome.evidence[0].status, EvidenceStatus::Proved, "{outcome:#?}");
        assert!(outcome.fresh_exact_direct_receipts.is_empty(), "not a direct-formula proof");
        let id = &bundle.obligations[0].obligation_id;
        assert!(
            outcome.fresh_whole_function_receipts.remove(id).is_some(),
            "the real whole-module proof must retain its own affine receipt"
        );
        assert!(
            outcome.fresh_whole_function_receipts.remove(id).is_none(),
            "one receipt cannot be consumed twice"
        );
    }

    /// Trust (C1, 2026-11-06): with live source reference facts, the pre-solve
    /// translation AND the solve both go through trust-mc's facts entries. The
    /// whole-function receipt then binds (it compares the pre-solve row with the
    /// solved one), so the two translations agree.
    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn source_reference_facts_reach_both_pre_solve_translation_and_solve() {
        let bundle = compiler_style_panic_freedom_public_bundle();
        let mut native =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        let source = trust_ir::SourceGenerationAuthority::mint_from_live_lowering(&mut native)
            .expect("valid unit fixture source authority");
        // An exact, empty claim set: the entries are selected by the facts'
        // presence, never by how many claims they carry.
        let facts =
            SourceReferenceFacts::from_live_source_lowering(&native, &source, vec![], vec![])
                .expect("an empty claim set binds to the exact live bundle");
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        NATIVE_BUNDLE_SOURCE_REFERENCE_ENTRIES_FOR_TEST.with(|count| count.set((0, 0)));
        let mut outcome = adapter
            .evidence_from_native_trust_ir_bundle_with_source_reference_facts_and_deadline_and_fresh_receipts(
                &bundle,
                &bundle.obligations,
                &native,
                &source,
                &facts,
                Some(Instant::now() + std::time::Duration::from_secs(10)),
            );
        let (translated, solved) =
            NATIVE_BUNDLE_SOURCE_REFERENCE_ENTRIES_FOR_TEST.with(std::cell::Cell::get);
        assert_eq!(translated, 1, "the pre-solve translation must use the facts entry");
        assert_eq!(solved, 1, "the solve must use the facts entry");
        assert_eq!(outcome.evidence[0].status, EvidenceStatus::Proved, "{outcome:#?}");
        let id = &bundle.obligations[0].obligation_id;
        assert!(
            outcome.fresh_whole_function_receipts.remove(id).is_some(),
            "the receipt compares the pre-solve and solved rows; it binds only when both \
             translations used the same facts"
        );

        // The authority-only entry still takes neither facts entry.
        NATIVE_BUNDLE_SOURCE_REFERENCE_ENTRIES_FOR_TEST.with(|count| count.set((0, 0)));
        let _ = adapter
            .evidence_from_native_trust_ir_bundle_with_source_authority_and_deadline_and_fresh_receipts(
                &bundle,
                &bundle.obligations,
                &native,
                &source,
                Some(Instant::now() + std::time::Duration::from_secs(10)),
            );
        assert_eq!(
            NATIVE_BUNDLE_SOURCE_REFERENCE_ENTRIES_FOR_TEST.with(std::cell::Cell::get),
            (0, 0)
        );
    }

    /// Trust (C1, 2026-11-06): facts that do not authorize the exact `(bundle,
    /// authority)` pair are a caller error. Every row fails closed with that
    /// diagnostic, and no fact-free solve is substituted.
    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn source_reference_facts_for_another_bundle_fail_closed_without_a_solve() {
        let bundle = compiler_style_panic_freedom_public_bundle();
        let mut native =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        let source = trust_ir::SourceGenerationAuthority::mint_from_live_lowering(&mut native)
            .expect("valid unit fixture source authority");
        let mut other =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        let other_source = trust_ir::SourceGenerationAuthority::mint_from_live_lowering(&mut other)
            .expect("second fixture authority");
        let foreign_facts =
            SourceReferenceFacts::from_live_source_lowering(&other, &other_source, vec![], vec![])
                .expect("facts bound to the other bundle");
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        NATIVE_BUNDLE_SOURCE_REFERENCE_ENTRIES_FOR_TEST.with(|count| count.set((0, 0)));
        NATIVE_BUNDLE_TRANSLATION_COUNT_FOR_TEST.with(|count| count.set(0));
        let outcome = adapter
            .evidence_from_native_trust_ir_bundle_with_source_reference_facts_and_deadline_and_fresh_receipts(
                &bundle,
                &bundle.obligations,
                &native,
                &source,
                &foreign_facts,
                Some(Instant::now() + std::time::Duration::from_secs(10)),
            );
        assert_ne!(outcome.evidence[0].status, EvidenceStatus::Proved);
        assert!(
            outcome.evidence[0].diagnostics[0].contains("source reference facts do not authorize"),
            "{:?}",
            outcome.evidence[0].diagnostics
        );
        assert!(outcome.fresh_whole_function_receipts.is_empty());
        assert_eq!(NATIVE_BUNDLE_TRANSLATION_COUNT_FOR_TEST.with(std::cell::Cell::get), 0);
        assert_eq!(
            NATIVE_BUNDLE_SOURCE_REFERENCE_ENTRIES_FOR_TEST.with(std::cell::Cell::get),
            (0, 0)
        );
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn whole_function_receipt_is_not_minted_by_ordinary_native_entrypoint() {
        let bundle = compiler_style_panic_freedom_public_bundle();
        let native =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let outcome = adapter
            .evidence_from_native_trust_ir_bundle_with_deadline_and_fresh_receipts(
                &bundle,
                &bundle.obligations,
                &native,
                None,
                Some(Instant::now() + std::time::Duration::from_secs(10)),
            );
        assert_eq!(outcome.evidence[0].status, EvidenceStatus::Proved, "{outcome:#?}");
        assert!(outcome.fresh_whole_function_receipts.is_empty());
        assert!(outcome.fresh_exact_direct_receipts.is_empty());
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn whole_function_receipt_preserves_source_authorized_direct_formula_family() {
        let bundle = compiler_style_exact_formula_public_bundle(
            ObligationKind::Precondition,
            add_typed_body_aware_vc_formula,
        );
        let mut native =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        let source = trust_ir::SourceGenerationAuthority::mint_from_live_lowering(&mut native)
            .expect("synthetic unit source issuer");
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let outcome = adapter.evidence_from_native_trust_ir_bundle_with_source_authority_and_deadline_and_fresh_receipts(
            &bundle, &bundle.obligations, &native, &source,
            Some(Instant::now() + std::time::Duration::from_secs(10)),
        );
        assert_eq!(outcome.evidence[0].status, EvidenceStatus::Proved, "{outcome:#?}");
        assert_eq!(outcome.fresh_exact_direct_receipts.len(), 1, "direct family is preserved");
        assert!(outcome.fresh_whole_function_receipts.is_empty());
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn whole_function_receipt_refuses_stale_public_or_native_source() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        for case in 0..3 {
            let mut bundle = compiler_style_panic_freedom_public_bundle();
            let mut native = bind_compiler_style_native_bundle_to_public(
                compiler_style_safe_tmir_bundle(),
                &bundle,
            );
            match case {
                0 => bundle.obligations[0].source = compiler_style_source(99, 7),
                1 => native.module.functions[0].name = "stale_function".into(),
                _ => bundle.obligations.push(bundle.obligations[0].clone()),
            }
            let outcome = adapter
                .evidence_from_native_trust_ir_bundle_with_deadline_and_fresh_receipts(
                    &bundle,
                    &bundle.obligations,
                    &native,
                    None,
                    Some(Instant::now() + std::time::Duration::from_secs(10)),
                );
            assert!(outcome.fresh_whole_function_receipts.is_empty(), "case {case}");
            assert!(
                outcome.evidence.iter().all(|row| row.status != EvidenceStatus::Proved),
                "case {case}: {outcome:#?}"
            );
        }
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn solved_whole_function_receipt_fixture() -> (
        TrustContractBundle,
        trust_ir::NativeVerificationBundle,
        trust_ir::SourceGenerationAuthority,
        NativeTrustIrBundleEvidenceWithFreshReceipts,
    ) {
        let bundle = compiler_style_panic_freedom_public_bundle();
        let mut native =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        // Synthetic unit fixture only, not a new production source issuer.
        let source = trust_ir::SourceGenerationAuthority::mint_from_live_lowering(&mut native)
            .expect("valid synthetic source fixture");
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let outcome = adapter.evidence_from_native_trust_ir_bundle_with_source_authority_and_deadline_and_fresh_receipts(
            &bundle, &bundle.obligations, &native, &source,
            Some(Instant::now() + std::time::Duration::from_secs(30)),
        );
        assert_eq!(outcome.evidence[0].status, EvidenceStatus::Proved, "{outcome:#?}");
        assert_eq!(outcome.fresh_whole_function_receipts.len(), 1, "{outcome:#?}");
        (bundle, native, source, outcome)
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn whole_function_receipt_exact_rebinding_and_private_mutations() {
        let (bundle, native, source, mut outcome) = solved_whole_function_receipt_fixture();
        let receipt = outcome
            .fresh_whole_function_receipts
            .remove(&bundle.obligations[0].obligation_id)
            .unwrap();
        let strength = receipt.still_authorizes(&bundle, &native, &bundle.obligations[0]).unwrap();
        assert_eq!(strength.assurance, trust_verifier_api::AssuranceLevel::SmtBacked);
        assert!(matches!(
            strength.reasoning,
            trust_verifier_api::ReasoningKind::Chc | trust_verifier_api::ReasoningKind::Pdr
        ));
        let mut wrong_row = bundle.obligations[0].clone();
        wrong_row
            .metadata
            .push(MetadataEntry { key: "changed.transport.metadata".into(), value: "1".into() });
        assert!(receipt.still_authorizes(&bundle, &native, &wrong_row).is_err());
        let mut wrong_public = bundle.clone();
        wrong_public.obligations[0] = wrong_row;
        assert!(
            receipt.still_authorizes(&wrong_public, &native, &wrong_public.obligations[0]).is_err()
        );
        let mut wrong_native = native.clone();
        wrong_native.module.functions[0].name = "different_body_owner".into();
        assert!(receipt.still_authorizes(&bundle, &wrong_native, &bundle.obligations[0]).is_err());
        let cloned_native = native.clone();
        assert!(
            !source.authorizes_bundle(&cloned_native),
            "content equality cannot recreate source authority"
        );
        let (_, _, _, foreign) = solved_whole_function_receipt_fixture();
        let foreign_seal =
            foreign.fresh_whole_function_receipts.values().next().unwrap().bundle_seal();
        assert!(
            receipt
                .still_authorizes_under_exact_bundle_seal(&foreign_seal, &bundle.obligations[0])
                .is_err()
        );
        receipt.assert_private_mutation_controls();
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn whole_function_receipt_final_projection_rejects_demotion_mutation_and_duplicates() {
        for case in 0..3 {
            let (_, _, _, mut outcome) = solved_whole_function_receipt_fixture();
            match case {
                0 => outcome.evidence[0].status = EvidenceStatus::Unknown,
                1 => outcome.evidence[0].diagnostics.push("post-solve replacement".into()),
                _ => outcome.evidence.push(outcome.evidence[0].clone()),
            }
            let final_outcome = finalize_native_bundle_evidence_with_whole_function_receipts(
                outcome.evidence,
                outcome.fresh_exact_direct_receipts,
                outcome.fresh_whole_function_receipts,
            );
            assert!(final_outcome.fresh_whole_function_receipts.is_empty(), "case {case}");
        }
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn whole_function_receipt_rejects_real_alternate_body_proof_with_same_ids() {
        let (bundle, native, _, outcome) = solved_whole_function_receipt_fixture();
        let receipt = outcome.fresh_whole_function_receipts.values().next().unwrap();
        let mut changed = native.clone();
        let constant = changed.module.functions[0]
            .blocks
            .iter_mut()
            .flat_map(|block| block.body.iter_mut())
            .find_map(|node| match &mut node.inst {
                trust_ir::Inst::Const { value: trust_ir::Constant::Int(value), .. } => Some(value),
                _ => None,
            })
            .expect("branch threshold constant");
        *constant += 1; // Both bodies are safe, but the proof belongs to a different body/query.
        let changed_digest = changed.module.stable_digest();
        changed.trust_ir_module_digest = changed_digest;
        for node in &mut changed.lineage.nodes {
            node.target_module = changed_digest;
        }
        changed.validate().expect("different valid same-ID native body");
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let deadline = Some(Instant::now() + std::time::Duration::from_secs(10));
        let before =
            adapter.native_trust_ir_chc_pdr_translated_obligations(&changed, deadline).unwrap();
        let (mut actual_proofs, _, _) =
            adapter.native_trust_ir_chc_pdr_proof_transports(&changed, None, deadline).unwrap();
        assert_eq!(actual_proofs.len(), 1, "alternate body must actually earn its own proof");
        let reason = FreshWholeFunctionChcPdrReceipt::try_from_native(
            receipt.bundle_seal(),
            &bundle.obligations[0],
            &outcome.evidence[0],
            &before[0],
            actual_proofs.pop().unwrap(),
            deadline,
        )
        .expect_err(
            "matching IDs and a real different-body proof cannot authorize the original body",
        );
        assert!(reason.contains("different body/source/compiler-fact/lineage digest"), "{reason}");
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn whole_function_receipt_rejects_foreign_source_identity_and_elapsed_dispatch() {
        let (bundle, native, source, _) = solved_whole_function_receipt_fixture();
        let (_, _, foreign_source, _) = solved_whole_function_receipt_fixture();
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let cloned = native.clone();
        for (body, authority, deadline) in [
            (&native, &foreign_source, Some(Instant::now() + std::time::Duration::from_secs(10))),
            (&cloned, &source, Some(Instant::now() + std::time::Duration::from_secs(10))),
            (&native, &source, Some(Instant::now() - std::time::Duration::from_secs(1))),
        ] {
            let outcome = adapter.evidence_from_native_trust_ir_bundle_with_source_authority_and_deadline_and_fresh_receipts(
                &bundle, &bundle.obligations, body, authority, deadline,
            );
            assert!(outcome.fresh_whole_function_receipts.is_empty(), "{outcome:#?}");
        }
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
                // v41: no clause bindings — an empty table reads as UNBINDABLE, never as a wildcard.
                bindings: Vec::new(),
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
            })
            .to_string(),
            smtlib: None,
            sort: None,
            // v41: no clause bindings — an empty table reads as UNBINDABLE, never as a wildcard.
            bindings: Vec::new(),
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
            let file = native
                .module
                .intern_file(file_name.to_string())
                .expect("Module::intern_file: test fixture");
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
        .map(|_| ())
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
            ObligationKind::LoopInvariant,
            ObligationKind::Termination,
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
    fn e4_e5_ownership_is_stable_while_missing_or_invalid_payloads_fail_closed() {
        let adapter = TrustMcVerifierApiAdapter::default();
        for kind in [ObligationKind::LoopInvariant, ObligationKind::Termination] {
            let bare = obligation(kind.clone(), "bare-e4-e5");
            assert!(
                adapter.supports(&bare).is_supported(),
                "v6/D3 ownership must not depend on payload presence"
            );
            let bare_bundle = bundle_with(vec![bare]);
            let evidence = adapter.verify(&bare_bundle, &bare_bundle.obligations);
            assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
            assert!(evidence[0].proof_strength.is_none());

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

        // Trust (T3 L4, C09d): the public validator's 128-level semantic bound is deleted. A
        // payload past it, within the bound its readers decode
        // (`trust_types::json_depth::MAX_DEEP_NESTING` JSON levels, two a Not link), parses
        // and validates; one past the readers' bound fails closed. The chains are built,
        // serialized, parsed and dropped on a deep stack, as each of those recurses per level.
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(256 * 1024 * 1024)
                .spawn_scoped(scope, typed_e4_payloads_past_the_old_bound_on_a_deep_stack)
                .expect("the deep-fixture thread starts")
                .join()
                .expect("the deep fixture passes");
        });
    }

    fn typed_e4_payloads_past_the_old_bound_on_a_deep_stack() {
        let chain_payload = |links: usize| {
            let mut chain = trust_verifier_api::TrustSpecExpr::bool_literal(false);
            for _ in 0..links {
                chain = trust_verifier_api::TrustSpecExpr::unary(
                    trust_verifier_api::TrustSpecUnaryOp::Not,
                    chain,
                );
            }
            serde_json::to_string(&trust_verifier_api::TrustSpecPredicate::new(chain, Vec::new()))
                .expect("the chain serializes")
        };
        let past_the_old_bound = chain_payload(129);
        let parsed =
            trust_types::json_depth::from_str_deep::<trust_verifier_api::TrustSpecPredicate>(
                &past_the_old_bound,
            )
            .expect("the readers decode a payload past the deleted bound");
        parsed.validate().expect("and the public validator admits it");

        let adapter = TrustMcVerifierApiAdapter::default();
        let over_limit = chain_payload(trust_types::json_depth::MAX_DEEP_NESTING / 2 + 1);
        assert!(
            trust_types::json_depth::json_nesting_depth(&over_limit)
                > trust_types::json_depth::MAX_DEEP_NESTING
        );
        let mut over_limit_obligation = obligation(ObligationKind::LoopInvariant, "over-limit-e4");
        add_typed_body_aware_vc_formula(&mut over_limit_obligation);
        over_limit_obligation
            .metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
            .expect("typed formula payload")
            .value = over_limit;
        assert!(adapter.supports(&over_limit_obligation).is_supported());
        let over_limit_bundle = bundle_with(vec![over_limit_obligation]);
        let evidence = adapter.verify(&over_limit_bundle, &over_limit_bundle.obligations);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
    }

    #[test]
    fn malformed_or_ambiguous_e4_e5_formula_metadata_cannot_acquire_trust_mc_authority() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let assert_canonical_but_declined = |obligation: TrustObligation| {
            assert!(adapter.supports(&obligation).is_supported());
            let bundle = bundle_with(vec![obligation]);
            bundle
                .validate_requested_obligations(&bundle.obligations)
                .expect("semantic refusal fixture must cross the canonical request boundary");
            let evidence = adapter.verify(&bundle, &bundle.obligations);
            assert_eq!(evidence.len(), 1, "canonical fixture must reach the adapter");
            assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
            assert!(evidence[0].proof_strength.is_none());
        };
        let assert_ambiguous_envelope_rejected = |obligation: TrustObligation| {
            assert!(adapter.supports(&obligation).is_supported());
            let bundle = bundle_with(vec![obligation]);
            let rejection = bundle
                .validate_requested_obligations(&bundle.obligations)
                .expect_err("duplicate metadata must fail the canonical request boundary");
            assert!(
                rejection.contains("duplicate metadata key"),
                "unexpected public-boundary rejection: {rejection}"
            );
            assert!(
                adapter.verify(&bundle, &bundle.obligations).is_empty(),
                "an invalid public request must not reach the adapter"
            );
        };
        let mut malformed = obligation(ObligationKind::LoopInvariant, "forged-e4");
        add_typed_body_aware_vc_formula(&mut malformed);
        let payload = malformed
            .metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
            .expect("payload metadata");
        payload.value = "{}".to_string();
        assert_canonical_but_declined(malformed);

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
        assert_canonical_but_declined(structurally_invalid);

        let mut ambiguous = obligation(ObligationKind::Termination, "forged-e5");
        add_typed_body_aware_vc_formula(&mut ambiguous);
        ambiguous.metadata.push(MetadataEntry {
            key: TRUST_VC_FORMULA_SCHEMA_METADATA_KEY.to_string(),
            value: trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
        });
        assert_ambiguous_envelope_rejected(ambiguous);

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
        assert_canonical_but_declined(wrong_origin);

        let mut duplicate_context = obligation(ObligationKind::Termination, "duplicate-context-e5");
        add_typed_body_aware_vc_formula(&mut duplicate_context);
        let duplicate = duplicate_context
            .metadata
            .iter()
            .find(|entry| entry.key == trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY)
            .expect("obligation context metadata")
            .clone();
        duplicate_context.metadata.push(duplicate);
        assert_ambiguous_envelope_rejected(duplicate_context);
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

    /// The PROMOTED doctor smoke constructor (used by `targo trust doctor` for
    /// the in-process trust-mc probe) must stay a valid compiler-canonical
    /// direct typed-CHC request: the bundle validates, the request is
    /// canonical (the bundle carries its one obligation), and the direct lane
    /// constructs proof input from it.
    #[test]
    fn doctor_smoke_bundle_is_canonical_direct_typed_chc_request() {
        let (bundle, obligation) = doctor_smoke_bundle();
        bundle.validate().expect("doctor smoke bundle validates");
        bundle
            .validate_requested_obligations(std::slice::from_ref(&obligation))
            .expect("doctor smoke request is canonical");
        assert_eq!(bundle.obligations.as_slice(), std::slice::from_ref(&obligation));
        assert_eq!(obligation.obligation_id, DOCTOR_SMOKE_PUBLIC_OBLIGATION_ID);

        let adapter = TrustMcVerifierApiAdapter::default();
        assert!(adapter.supports(&obligation).is_supported());
        let input = adapter
            .typed_chc_pdr_obligation_for(&bundle, &obligation)
            .expect("doctor smoke canonical lane must validate")
            .expect("doctor smoke bundle must construct direct proof input");
        assert_eq!(
            input.trust_mc_obligation.obligation_id,
            "trust_ir-native-trust_mc-request-1-proof-0"
        );
    }

    /// End-to-end PUBLIC dispatch of the doctor smoke request. Public
    /// `verify_with_context` deliberately keeps native CHC/PDR candidates
    /// NON-definitive (`Proved` requires a deliverable live receipt from the
    /// fresh-exact-replay dispatch entries), so the doctor probe observes a
    /// valid one-obligation envelope whose evidence is a validated
    /// non-definitive candidate — never `Proved`, never `Failed` (the CHC is
    /// trivially safe), and never the empty envelope the pre-fix probe
    /// produced. If this test ever starts seeing `Proved`, the doctor's
    /// trust-mc smoke gains an honest "available": update the targo-trust
    /// doctor expectations together with this test.
    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn doctor_smoke_bundle_public_dispatch_returns_validated_nondefinitive_candidate() {
        let (bundle, obligation) = doctor_smoke_bundle();
        let adapter = TrustMcVerifierApiAdapter::default();
        let context = VerifierExecutionContext::new("targo-trust-doctor-trust-mc-smoke");

        let result =
            adapter.verify_with_context(&bundle, std::slice::from_ref(&obligation), &context);

        assert_eq!(result.run_id, "targo-trust-doctor-trust-mc-smoke");
        assert_eq!(result.bundle_id, bundle.bundle_id);
        assert_eq!(result.summary.requested_obligations, 1);
        assert_eq!(result.evidence.len(), 1);
        assert_eq!(result.evidence[0].obligation_id, obligation.obligation_id);
        assert_ne!(result.status, VerificationRunStatus::Empty);
        assert_ne!(
            result.evidence[0].status,
            EvidenceStatus::Failed,
            "the trivially safe doctor CHC must never be refuted: {:?}",
            result.evidence[0].diagnostics
        );
        assert_eq!(
            result.evidence[0].status,
            EvidenceStatus::Unknown,
            "unexpected doctor smoke evidence status: {:?}",
            result.evidence[0].diagnostics
        );
        assert!(
            result.evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic.contains("constructed typed trust_mc ChcVc") })
        );
    }

    /// Without the native solver the doctor smoke request must fail closed
    /// with the actionable "solving is disabled" diagnostic — not an invalid
    /// envelope.
    #[cfg(not(feature = "trust-mc-native-solver"))]
    #[test]
    fn doctor_smoke_bundle_without_native_solver_fails_closed_with_actionable_reason() {
        let (bundle, obligation) = doctor_smoke_bundle();
        let adapter = TrustMcVerifierApiAdapter::default();
        let context = VerifierExecutionContext::new("targo-trust-doctor-trust-mc-smoke");

        let result =
            adapter.verify_with_context(&bundle, std::slice::from_ref(&obligation), &context);

        assert_eq!(result.evidence.len(), 1);
        assert_eq!(result.evidence[0].status, EvidenceStatus::Unsupported);
        assert!(
            result.evidence[0].diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("native typed CHC/PDR solving is disabled")
            })
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
        #[cfg(feature = "trust-mc-native-solver")]
        attest_synthetic_typed_chc_encoding_exact(&mut bundle.obligations[0]);
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
        #[cfg(feature = "trust-mc-native-solver")]
        attest_synthetic_typed_chc_encoding_exact(&mut unforged_bundle.obligations[0]);
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
        attest_synthetic_typed_chc_encoding_exact(&mut bundle.obligations[0]);
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
        attest_synthetic_typed_chc_encoding_exact(&mut bundle.obligations[0]);
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
        let solved =
            runner.solve_full_verification(request.clone()).expect("reachable error should solve");
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
            &request,
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
            &request,
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
            &request,
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

    /// Gate-arm adversarial replay: start from one REAL production witness
    /// that reaches `Failed`, then mutate each authority-bearing component.
    /// The public verdict must stay `Unknown` unless fresh lowering plus exact
    /// trace/model replay and artifact binding all succeed.
    #[test]
    #[cfg(feature = "trust-mc-native-solver")]
    fn typed_chc_full_verification_requires_fresh_replay_for_every_failed_verdict() {
        let obligation_id = native_typed_chc_obligation_id(54, 50);
        let mut bundle = bundle_with(vec![obligation_with_contract(
            ObligationKind::ArithmeticSafety,
            &obligation_id,
            "contract-typed-fresh-replay",
        )]);
        attest_synthetic_typed_chc_encoding_exact(&mut bundle.obligations[0]);
        push_typed_chc_contract(
            &mut bundle,
            typed_chc_contract("contract-typed-fresh-replay", &obligation_id, true),
        );
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3),
        );
        let input = adapter
            .typed_chc_pdr_obligation_for(&bundle, &bundle.obligations[0])
            .expect("typed input validates")
            .expect("fixture has typed input");
        let request = input.trust_mc_obligation.clone();
        let expected = trust_mc_driver::normalized_typed_chc_pdr_input(&request)
            .expect("retained request normalizes");
        let runner = trust_mc_driver::NativeTypedChcPdrRunner::with_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(std::time::Duration::from_secs(10)),
        );
        let solved =
            runner.solve_full_verification(request.clone()).expect("reachable fixture solves");

        let evidence_for = |candidate: trust_mc_driver::TypedChcPdrFullVerification| {
            adapter.evidence_from_typed_chc_pdr_full_verification(
                &bundle,
                &bundle.obligations[0],
                input.input_artifact.clone(),
                Vec::new(),
                candidate,
                &request,
                expected.clone(),
                false,
            )
        };
        let assert_unknown =
            |label: &str, candidate: trust_mc_driver::TypedChcPdrFullVerification| {
                let evidence = evidence_for(candidate);
                assert_eq!(
                    evidence.status,
                    EvidenceStatus::Unknown,
                    "{label} mutation must fail closed: {:#?}",
                    evidence.diagnostics
                );
                assert!(
                    evidence.counterexample.is_none(),
                    "{label} mutation must not surface a public counterexample"
                );
                assert!(evidence.diagnostics.iter().any(|diagnostic| {
                    diagnostic.contains("refutation demoted to unknown")
                        && diagnostic.contains("failed validation")
                }));
            };

        let baseline = evidence_for(solved.clone());
        assert_eq!(baseline.status, EvidenceStatus::Failed);
        assert!(baseline.counterexample.is_some());
        assert!(baseline.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("fresh direct-SMT acyclic derivation and exact model replay")
        }));

        let mutate_witness =
            |candidate: &mut trust_mc_driver::TypedChcPdrFullVerification,
             mutate: &dyn Fn(&mut trust_mc_core::ChcPdrRefutationWitness)| {
                let trust_mc_core::ChcPdrSolveStatus::Refuted { witness: Some(witness) } =
                    &mut candidate.outcome.status
                else {
                    panic!("fixture carries a witness");
                };
                mutate(witness);
            };

        // A model-domain mutation is deterministic: exact replay requires a
        // total assignment with no extra bindings.
        let mut mutated = solved.clone();
        mutate_witness(&mut mutated, &|witness| {
            let mut payload: serde_json::Value =
                serde_json::from_str(&witness.counterexample_json).expect("payload JSON");
            payload["witness_model"].as_object_mut().expect("model object").insert(
                "forged_extra_binding".to_string(),
                serde_json::json!({ "kind": "bool", "value": true }),
            );
            witness.counterexample_json = payload.to_string();
        });
        assert_unknown("model", mutated);

        let mut mutated = solved.clone();
        mutate_witness(&mut mutated, &|witness| {
            let mut payload: serde_json::Value =
                serde_json::from_str(&witness.counterexample_json).expect("payload JSON");
            let trace = payload["derivation_clause_indices"].as_array_mut().expect("trace array");
            let repeated = trace.first().expect("nonempty trace").clone();
            trace.push(repeated);
            witness.counterexample_json = payload.to_string();
        });
        assert_unknown("transition trace", mutated);

        let mut mutated = solved.clone();
        mutate_witness(&mut mutated, &|witness| {
            witness.verification =
                trust_mc_core::ChcPdrCexVerification::BoundedUnrollDirectSmtModel { k: 4 };
        });
        assert_unknown("proof class", mutated);

        let mut mutated = solved.clone();
        mutate_witness(&mut mutated, &|witness| {
            witness.verification =
                trust_mc_core::ChcPdrCexVerification::BoundedUnrollDirectSmtModel { k: 2 };
            let mut payload: serde_json::Value =
                serde_json::from_str(&witness.counterexample_json).expect("payload JSON");
            payload["source"] = serde_json::json!("direct-smt-bounded-unroll-error-derivation");
            payload["unroll_k"] = serde_json::json!(2);
            witness.counterexample_json = payload.to_string();
        });
        assert_unknown("unroll budget", mutated);

        let mut mutated = solved.clone();
        mutate_witness(&mut mutated, &|witness| {
            witness.encoded_formula_sha256 =
                trust_mc_core::EvidenceHash::sha256_bytes(b"detached formula").value;
        });
        assert_unknown("formula digest", mutated);

        // Keep the witness untouched but detach the materialized artifact. A
        // replay-valid model is still not authority unless the public Failed
        // artifact contains those exact bytes.
        let mut mutated = solved;
        let trust_mc_core::FullVerificationVerdict::Failed { counterexample_artifacts } =
            &mut mutated.verdict
        else {
            panic!("fixture carries a Failed verdict");
        };
        counterexample_artifacts[0] = trust_mc_core::FullVerificationArtifact::from_bytes(
            trust_mc_core::FullVerificationArtifactKind::CounterexampleTrace,
            "trust_mc://detached/counterexample.json",
            br#"{"detached":true}"#,
        );
        assert_unknown("materialized artifact", mutated);
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
        let (mut bundle, _canonical_id, _marker_id, native_id) =
            compiler_canonical_trust_mc_bundle_with_error_derivation(public_id, 53, 49, true);
        // The production compiler does not yet make this claim. This synthetic
        // premise isolates the split public/native identity check exercised by
        // the test from the independent source-fidelity gate.
        attest_synthetic_typed_chc_encoding_exact(&mut bundle.obligations[0]);
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
        // refutation witness). No public counterexample record is fabricated for
        // a non-Failed status, and the solver's `Counterexample` ARTIFACTS are
        // withheld too (disclosed by a diagnostic): published beside `Unknown`
        // they presented a model of the encoding as a witness against the code.
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
        assert!(
            !evidence
                .artifacts
                .iter()
                .any(|artifact| artifact.kind == EvidenceArtifactKind::Counterexample),
            "a DEMOTED refutation must not publish a Counterexample artifact; artifacts: {:#?}",
            evidence.artifacts
        );
        assert!(
            evidence
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic.contains("refutation demoted to unknown") })
        );
        assert!(
            evidence.diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("withheld 1 solver counterexample artifact(s)")
                    && diagnostic.contains("the verdict is unknown")
            }),
            "the withholding must be disclosed; diagnostics: {:#?}",
            evidence.diagnostics
        );

        // The SAME artifacts under a validated (`Failed`) verdict are kept: the
        // filter is keyed on the status, not on the artifact alone.
        let failed = adapter.typed_chc_pdr_solver_outcome_evidence(
            &bundle,
            &bundle.obligations[0],
            EvidenceStatus::Failed,
            trust_mc_typed_chc_engine_input_artifact(
                &bundle,
                &bundle.obligations[0],
                "contract-refuted",
                &sha256_hex('9'),
            ),
            Vec::new(),
            non_proof_artifacts_from_trust_mc_core_verdict(&verdict),
            "validated refutation".to_string(),
        );
        assert!(failed.artifacts.iter().any(|artifact| {
            artifact.kind == EvidenceArtifactKind::Counterexample
                && artifact.uri.ends_with("/counterexample.json")
        }));
        assert!(!failed.diagnostics.iter().any(|diagnostic| diagnostic.contains("withheld")));
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
    fn fresh_exact_direct_pdr_dispatch_retains_nonserializable_formula_receipt() {
        for (index, kind) in [
            ObligationKind::ArithmeticSafety,
            ObligationKind::Assertion,
            ObligationKind::Precondition,
            ObligationKind::LoopInvariant,
            ObligationKind::Termination,
        ]
        .into_iter()
        .enumerate()
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
                "fresh exact standalone-formula dispatch was rejected: {:?}",
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
                .expect("typed standalone-formula payload")
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

    /// gate-rca deadline (2026-10-17): the solve cutoff clamps the exact-direct solve's
    /// own clock, while the live receipt keeps the DISPATCH deadline, the one the router's
    /// dispatch seal and the compiler's mint compare it with. Negative control: without
    /// a cutoff the same dispatch takes the adapter's configured 10 s clock, so the clamp
    /// observed above it is the cutoff's.
    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn exact_direct_solve_cutoff_clamps_the_solve_and_the_receipt_keeps_the_dispatch_deadline() {
        let public_id = "vc:trust-bmc:solve-cutoff:0";
        let (mut bundle, _canonical_id, _marker_id, _native_id) =
            compiler_canonical_trust_mc_bundle(public_id, 96, 0);
        bundle.obligations[0].kind = ObligationKind::LoopInvariant;
        add_typed_body_aware_vc_formula(&mut bundle.obligations[0]);
        bundle.validate().expect("solve-cutoff fixture must validate");
        let config =
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000);
        let deadline = Instant::now() + std::time::Duration::from_secs(3600);
        let applied = |adapter: &TrustMcVerifierApiAdapter| {
            let dispatch = adapter
                .exact_direct_chc_pdr_evidence_with_fresh_receipt(
                    &bundle,
                    &bundle.obligations[0],
                    Some(deadline),
                )
                .expect("exact input validates")
                .expect("fixture carries exact input");
            let receipt = dispatch.receipt.expect("a timely exact solve retains its receipt");
            assert_eq!(
                receipt.dispatch_deadline(),
                Some(deadline),
                "the receipt is bound to the dispatch deadline, never to the cutoff"
            );
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
            std::time::Duration::new(
                options["timeout"]["secs"].as_u64().expect("timeout seconds"),
                options["timeout"]["nanos"].as_u64().expect("timeout nanos") as u32,
            )
        };
        let cutoff = Instant::now() + std::time::Duration::from_secs(2);
        let clamped = applied(
            &TrustMcVerifierApiAdapter::new(config.clone()).with_solve_cutoff(Some(cutoff)),
        );
        assert!(clamped > std::time::Duration::ZERO);
        assert!(
            clamped <= std::time::Duration::from_secs(2),
            "the solve clock {clamped:?} ran past the cutoff"
        );
        let unclamped = applied(&TrustMcVerifierApiAdapter::new(config));
        assert_eq!(
            unclamped,
            std::time::Duration::from_secs(10),
            "control: with no cutoff the configured clock applies under a far deadline"
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
        attest_synthetic_typed_chc_encoding_exact(&mut bundle.obligations[0]);
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

    /// Build the exact bundle of the test above, optionally stamping one
    /// producer encoding-fidelity attestation on the public obligation.
    ///
    /// The CHC is byte-identical in both arms — same flattened single-formula
    /// shape, same satisfiable constraint, same validated direct-SMT witness —
    /// so the ONLY difference between the two verdicts is the producer's
    /// statement about whether that ChcVc faithfully encodes its body.
    #[cfg(feature = "trust-mc-native-solver")]
    fn compiler_spec_refutation_evidence_with_fidelity(
        native_request_id: u32,
        native_proof_id: u32,
        encoding_fidelity: Option<&str>,
    ) -> ObligationEvidence {
        let obligation_id = native_typed_chc_obligation_id(native_request_id, native_proof_id);
        let mut obligation = obligation_with_contract(
            ObligationKind::ArithmeticSafety,
            &obligation_id,
            "contract-spec",
        );
        if let Some(class) = encoding_fidelity {
            obligation.metadata.push(MetadataEntry {
                key: TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_METADATA_KEY.to_string(),
                value: class.to_string(),
            });
        }
        let mut bundle = bundle_with(vec![obligation]);
        let mut contract = typed_chc_contract("contract-spec", &obligation_id, false);
        if let ContractPredicate::MathIr { value, .. } = &mut contract.predicate {
            apply_compiler_spec_satisfiable_constraint_shape(value);
        }
        refresh_typed_chc_binding_metadata(&mut contract, &obligation_id, &obligation_id);
        push_typed_chc_contract(&mut bundle, contract);

        TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3),
        )
        .verify(&bundle, &bundle.obligations)
        .remove(0)
    }

    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn producer_attested_loop_elided_encoding_demotes_refutation_to_unknown() {
        // The regression this closes: a TRUE postcondition on
        // `fn f(n: i32) -> i32 { let mut i = 0; while i < n { i = i + 1; } i }`
        // (no `requires`) was published as `verified_counterexample = true`.
        // The compiler had fallen back to the flattened single-formula typed
        // CHC, which carries NO loop transition relation, so the loop-carried
        // `i` was a free variable and the direct-SMT route "refuted" the query
        // by choosing i = -1 — a value the program cannot produce. Every
        // downstream check passed truthfully; the gap was the ChcVc-PRODUCTION
        // stage, which nothing on this side of the boundary accounted for.
        let gated = compiler_spec_refutation_evidence_with_fidelity(
            41,
            37,
            Some(TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_LOOP_ELIDED),
        );

        // FAILED -> Unknown is the ONLY movement this gate may cause. It must
        // never manufacture a proof out of an encoding it just called unfaithful.
        assert_eq!(gated.status, EvidenceStatus::Unknown);
        assert_ne!(gated.status, EvidenceStatus::Proved);
        assert_eq!(gated.proof_strength, None);
        // A demoted row publishes no counterexample: the whole point is that the
        // solver's model is not evidence about the program.
        assert!(
            gated.counterexample.is_none(),
            "a refutation of an over-approximating encoding must not surface a public counterexample"
        );
        assert!(
            gated.diagnostics.iter().any(|diagnostic| {
                // 302ba178ce0 reworded the reason: it names the attested
                // over-approximation, no longer the "loop-elided" class.
                diagnostic.contains("refutation demoted to unknown")
                    && diagnostic.contains("attests the submitted ChcVc is an over-approximation")
            }),
            "the demotion must name the producer stage that failed; diagnostics: {:#?}",
            gated.diagnostics
        );
        // The gate must not be able to hide a real bug as "code is fine".
        assert!(
            gated
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("UNPROVED, not disproved")),
            "the demotion must report a capability gap, not innocence; diagnostics: {:#?}",
            gated.diagnostics
        );

        // ABSENCE is not positive fidelity. The exact same encoded request
        // therefore remains Unknown until the producer proves and stamps the
        // complete source-to-ChcVc edge.
        let unattested = compiler_spec_refutation_evidence_with_fidelity(42, 38, None);
        assert_eq!(unattested.status, EvidenceStatus::Unknown);
        assert!(unattested.counterexample.is_none());
        assert!(unattested.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("no positive producer fidelity attestation")
        }));

        // Positive control for the consumer gate. This value is test-authored;
        // the compiler is forbidden to emit it until its lowering fidelity is
        // independently established.
        let exact = compiler_spec_refutation_evidence_with_fidelity(
            45,
            41,
            Some(TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_EXACT),
        );
        assert_eq!(exact.status, EvidenceStatus::Failed);
        assert!(exact.counterexample.is_some());
    }

    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn unrecognized_producer_encoding_fidelity_class_fails_closed() {
        // Fail-closed on arrival: a fidelity class this consumer has never heard
        // of must not acquire refutation authority by being unknown. The
        // compiler emits only negative attestations, so any value here is the
        // producer disclaiming exactness in words we do not parse.
        let evidence = compiler_spec_refutation_evidence_with_fidelity(
            43,
            39,
            Some("some_future_over_approximation_class"),
        );
        assert_eq!(evidence.status, EvidenceStatus::Unknown);
        assert!(evidence.counterexample.is_none());
        assert!(
            evidence.diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("unrecognized fidelity class fails closed")
            }),
            "diagnostics: {:#?}",
            evidence.diagnostics
        );
    }

    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn duplicated_producer_encoding_fidelity_attestation_fails_closed() {
        // A duplicated key must not read as "no attestation". `metadata_value`
        // answers ambiguity with `None`, which on this gate would hand a
        // disclaimed encoding its refutation authority back — so the classifier
        // counts the entries itself rather than reusing that helper.
        let obligation_id = native_typed_chc_obligation_id(45, 41);
        let mut obligation = obligation_with_contract(
            ObligationKind::ArithmeticSafety,
            &obligation_id,
            "contract-spec",
        );
        for _ in 0..2 {
            obligation.metadata.push(MetadataEntry {
                key: TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_METADATA_KEY.to_string(),
                value: TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_LOOP_ELIDED.to_string(),
            });
        }

        assert_eq!(
            TrustMcChcRefutationAdmissibility::for_obligation(&obligation)
                .rejection_reason()
                .is_some(),
            true,
            "an ambiguous fidelity attestation must reject the refutation, not ignore it"
        );
    }

    #[cfg(feature = "trust-mc-native-solver")]
    #[test]
    fn producer_encoding_fidelity_gate_never_touches_the_proof_direction() {
        // The asymmetry is the whole design: an over-approximating encoding is
        // SOUND for proofs (UNSAT of a superset implies UNSAT of the real
        // reachable set) and unsound as evidence for refutations. Control C of
        // the reported regression — the same loop WITH `requires(n >= 0)` —
        // proves 4/4 through exactly such an encoding, and must keep doing so.
        // So a row carrying the attestation must still be provable.
        let obligation_id = native_typed_chc_obligation_id(44, 40);
        let mut obligation = obligation_with_contract(
            ObligationKind::ArithmeticSafety,
            &obligation_id,
            "contract-spec",
        );
        obligation.metadata.push(MetadataEntry {
            key: TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_METADATA_KEY.to_string(),
            value: TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_LOOP_ELIDED.to_string(),
        });
        let mut bundle = bundle_with(vec![obligation]);
        // `derive_error = false`: `error` is derivable only from `entry(ok)`
        // with `ok` true, and the only `entry` fact is `entry(false)`, so the
        // query is genuinely unreachable.
        let contract = typed_chc_contract("contract-spec", &obligation_id, false);
        push_typed_chc_contract(&mut bundle, contract);

        let evidence = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc),
        )
        .verify(&bundle, &bundle.obligations);

        // The gate lives in the `Refuted` arm only: it must not demote, reject,
        // or otherwise perturb a row the solver did not refute.
        assert_ne!(evidence[0].status, EvidenceStatus::Failed);
        // Matched on the reason's current wording (302ba178ce0); the old
        // "loop-elided over-approximation" phrase no longer occurs anywhere, so
        // checking for it here was vacuous.
        assert!(
            !evidence[0].diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("attests the submitted ChcVc is an over-approximation")
            }),
            "the fidelity gate must not speak on a non-refuted row; diagnostics: {:#?}",
            evidence[0].diagnostics
        );
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
        attest_synthetic_typed_chc_encoding_exact(&mut bundle.obligations[0]);
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
        attest_synthetic_typed_chc_encoding_exact(&mut bundle.obligations[0]);
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
        attest_synthetic_typed_chc_encoding_exact(&mut bundle.obligations[0]);
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
        attest_synthetic_typed_chc_encoding_exact(&mut bundle.obligations[0]);
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
    fn native_trust_ir_public_claim_binding_catalog_formula_stays_exact_and_non_authoritative() {
        let mut public = obligation(ObligationKind::Postcondition, "obligation:f:postcondition:1");
        public.contract_id = Some("authored-ensures".to_string());
        add_result_referencing_vc_formula(&mut public);
        replace_formula_context(
            &mut public,
            trust_verifier_api::ObligationContext::new(
                trust_verifier_api::ObligationProducer::CompilerMirExtract,
                trust_verifier_api::ObligationOrigin::Contract {
                    contract_id: "authored-ensures".to_string(),
                    contract_kind: ContractKind::Ensures,
                    contract_index: 1,
                    predicate_schema: Some(
                        trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
                    ),
                },
            ),
        );
        let source = trust_ir::ProofObligationSourceIdentity::new(
            "authored-ensures",
            "trust-assertion:authored-ensures",
        );
        let proof_id = trust_ir::ProofId::new(1);
        let formula = compiler_style_public_formula(&public);
        validate_native_trust_ir_public_formula_binding(&public, proof_id, &source, &formula)
            .expect("an exact body-formula projection binds a retained authored catalog row");
        assert!(
            !is_typed_body_aware_exact_direct_obligation(&public),
            "formula identity must not promote a Contract marker to fresh VC proof authority"
        );
        let mut missing = public.clone();
        missing.metadata.retain(|entry| {
            !matches!(
                entry.key.as_str(),
                TRUST_VC_FORMULA_SCHEMA_METADATA_KEY
                    | TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY
                    | TRUST_VC_FORMULA_SMTLIB_METADATA_KEY
                    | TRUST_VC_FORMULA_SORT_METADATA_KEY
            )
        });
        assert!(
            validate_native_trust_ir_public_formula_binding(&missing, proof_id, &source, &formula)
                .unwrap_err()
                .contains("has no public formula metadata")
        );
        let mut partial = public.clone();
        partial.metadata.retain(|entry| entry.key != TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY);
        assert!(
            validate_native_trust_ir_public_formula_binding(&partial, proof_id, &source, &formula)
                .unwrap_err()
                .contains("partial formula schema/payload pair")
        );
        for field in ["schema", "payload", "smtlib", "sort"] {
            let mut altered = formula.clone();
            match field {
                "schema" => altered.schema.push_str(".foreign"),
                "payload" => altered.payload = "{}".to_string(),
                "smtlib" => altered.smtlib = Some("false".to_string()),
                "sort" => altered.sort = Some("Int".to_string()),
                _ => unreachable!(),
            }
            assert!(
                validate_native_trust_ir_public_formula_binding(
                    &public, proof_id, &source, &altered
                )
                .unwrap_err()
                .contains("does not exactly match canonical public formula metadata"),
                "{field} substitution must fail closed"
            );
        }
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_semantic_formula_is_not_replaced_by_a_safe_body_or_source_envelope() {
        let (bundle, _, _) = compiler_style_canonical_public_bundle();
        assert!(bundle.obligations[0].contract_id.is_some());
        let native =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        validate_compiler_style_public_claim_for_test(&bundle, &native, 0)
            .expect("the exact public formula and native identity must bind");

        // Keep the semantic contract, native body, and exact public/native
        // identities. Only remove the public formula. Rebinding reconstructs
        // the producer's source-location envelope, not a proof of the claim.
        let mut missing = bundle.clone();
        missing.obligations[0].metadata.retain(|entry| {
            !matches!(
                entry.key.as_str(),
                TRUST_VC_FORMULA_SCHEMA_METADATA_KEY
                    | TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY
                    | TRUST_VC_FORMULA_SMTLIB_METADATA_KEY
                    | TRUST_VC_FORMULA_SORT_METADATA_KEY
            )
        });
        let source_only = bind_compiler_style_native_bundle_to_public(
            compiler_style_safe_tmir_bundle(),
            &missing,
        );
        let reason = validate_compiler_style_public_claim_for_test(&missing, &source_only, 0)
            .expect_err("a safe native body cannot replace the absent semantic formula");
        assert!(
            reason.contains(
                "has no public formula metadata encoding its semantic contract/proof-item goal",
            ) && reason.contains("source-location identity alone does not encode that goal"),
            "unexpected missing-formula refusal: {reason}"
        );

        // Supplying only half of the original formula is also not a repair.
        // These cases retain their existing, more specific refusal.
        for missing_key in
            [TRUST_VC_FORMULA_SCHEMA_METADATA_KEY, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY]
        {
            let mut partial = bundle.clone();
            partial.obligations[0].metadata.retain(|entry| entry.key != missing_key);
            let partial_native = bind_compiler_style_native_bundle_to_public(
                compiler_style_safe_tmir_bundle(),
                &partial,
            );
            let reason =
                validate_compiler_style_public_claim_for_test(&partial, &partial_native, 0)
                    .expect_err("a partial formula must not bind");
            assert!(
                reason.contains("partial formula schema/payload pair"),
                "unexpected partial-formula refusal for {missing_key}: {reason}"
            );
        }
    }

    /// Build the compiler-style public/native pair for ONE explicit
    /// public-kind/native-kind pairing, so a kind-binding test states the
    /// pairing under test and nothing else. The compiler-fact cause is taken
    /// from the same kind projection the producer uses
    /// (`trust_ir_bridge::native_request`), so the cause gate never masks the
    /// kind gate.
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn compiler_style_kind_pair_fixture(
        public_kind: ObligationKind,
        native_kind: trust_ir::ObligationKind,
        typed_formula_payload: bool,
    ) -> (TrustContractBundle, trust_ir::NativeVerificationBundle) {
        let mut bundle = compiler_style_safe_public_bundle();
        bundle.obligations[0].kind = public_kind;
        if typed_formula_payload {
            bundle.obligations[0].metadata.extend([
                MetadataEntry {
                    key: TRUST_VC_FORMULA_SCHEMA_METADATA_KEY.to_string(),
                    value: "trust.vc.formula.canonical-json.v1".to_string(),
                },
                MetadataEntry {
                    key: TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY.to_string(),
                    value: r#"{"assertion":"body-aware"}"#.to_string(),
                },
            ]);
        }
        let mut native_bundle =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        let proof_id = canonical_u32_metadata_value(
            obligation_metadata_value(
                &bundle.obligations[0],
                TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
            )
            .expect("kind-pair fixture proof id"),
        )
        .expect("canonical kind-pair fixture proof id");
        let cause = native_trust_ir_obligation_cause_projection(&native_kind);
        native_bundle
            .module
            .proof_obligations
            .iter_mut()
            .find(|proof| proof.id.index() == proof_id)
            .expect("kind-pair fixture proof obligation")
            .kind = native_kind;
        native_bundle
            .compiler_facts
            .obligation_sources
            .iter_mut()
            .find(|source| source.obligation.index() == proof_id)
            .expect("kind-pair fixture compiler-fact source")
            .cause = cause;
        let module_digest = native_bundle.module.stable_digest();
        native_bundle.trust_ir_module_digest = module_digest;
        for node in &mut native_bundle.lineage.nodes {
            node.target_module = module_digest;
        }
        native_bundle
            .validate()
            .unwrap_or_else(|errors| panic!("kind-pair fixture must validate: {errors:#?}"));
        (bundle, native_bundle)
    }

    /// v6/D3 (`79558a8f2e`) re-routed the payload-less halves of
    /// Precondition/Postcondition and the envelope-less halves of
    /// LoopInvariant/Termination from trust-wp to trust-mc, keeping their
    /// native kinds. Every pairing the compiler's
    /// `native_trust_ir_route_for_api_obligation` can hand the trust-mc suite
    /// must reconcile here, or the row dies at the identity gate with a
    /// message that reads like a typo (`kind Postcondition does not match
    /// native proof obligation 0 kind Postcondition`).
    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_public_claim_binding_accepts_payloadless_v6_d3_native_kinds() {
        for (public_kind, native_kind) in [
            (ObligationKind::Precondition, trust_ir::ObligationKind::Precondition),
            (ObligationKind::Postcondition, trust_ir::ObligationKind::Postcondition),
            (ObligationKind::LoopInvariant, trust_ir::ObligationKind::LoopInvariant),
            (ObligationKind::Termination, trust_ir::ObligationKind::TranslationValidation),
        ] {
            let (bundle, native_bundle) =
                compiler_style_kind_pair_fixture(public_kind.clone(), native_kind.clone(), false);
            validate_compiler_style_public_claim_for_test(&bundle, &native_bundle, 0)
                .unwrap_or_else(|reason| {
                    panic!(
                        "the compiler's own {public_kind:?} -> {native_kind:?} trust-mc route must bind: {reason}"
                    )
                });
        }
    }

    /// The compiler maps both public rows onto its whole-function-shaped
    /// `PanicFreedom` native proof unit before attaching the exact direct CHC.
    /// Pin that producer mapping pairwise; `ArithmeticSafety` is a native
    /// vocabulary member, but is not emitted for either public row here.
    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_public_claim_binding_pins_assertion_arithmetic_producer_pairs() {
        for public_kind in [ObligationKind::Assertion, ObligationKind::ArithmeticSafety] {
            let (bundle, native_bundle) = compiler_style_kind_pair_fixture(
                public_kind.clone(),
                trust_ir::ObligationKind::PanicFreedom,
                false,
            );
            validate_compiler_style_public_claim_for_test(&bundle, &native_bundle, 0)
                .unwrap_or_else(|reason| {
                    panic!(
                        "the compiler's {public_kind:?} -> PanicFreedom route must bind: {reason}"
                    )
                });
        }
    }

    /// The identity arms must not turn the table into "accept anything". Each
    /// row below is a pairing the producer CANNOT emit for that public
    /// obligation, and each must still fail closed at the identity gate rather
    /// than reaching the formula/marker checks.
    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_public_claim_binding_still_rejects_mismatched_native_kinds() {
        let cases: Vec<(ObligationKind, trust_ir::ObligationKind, bool)> = vec![
            // A postcondition proof unit may never answer a precondition row,
            // nor the converse: the identity arms are pairwise, not a group.
            (ObligationKind::Precondition, trust_ir::ObligationKind::Postcondition, false),
            (ObligationKind::Postcondition, trust_ir::ObligationKind::Precondition, false),
            // The payload-BEARING half of these kinds is routed to
            // PanicFreedom; the identity pairing belongs to the payload-less
            // half alone, so the guards stay exact complements.
            (ObligationKind::Precondition, trust_ir::ObligationKind::Precondition, true),
            (ObligationKind::Postcondition, trust_ir::ObligationKind::Postcondition, true),
            // ...and symmetrically, a payload-LESS row may not claim the
            // PanicFreedom proof unit that carries the body-aware CHC.
            (ObligationKind::Precondition, trust_ir::ObligationKind::PanicFreedom, false),
            (ObligationKind::Postcondition, trust_ir::ObligationKind::PanicFreedom, false),
            // Termination projects onto TranslationValidation and
            // LoopInvariant onto itself; the two may not be swapped.
            (ObligationKind::Termination, trust_ir::ObligationKind::LoopInvariant, false),
            (ObligationKind::LoopInvariant, trust_ir::ObligationKind::TranslationValidation, false),
            // Despite the matching vocabulary name, the compiler maps both
            // rows above to PanicFreedom; accepting this crossed native kind
            // would make the consumer wider than its producer.
            (ObligationKind::Assertion, trust_ir::ObligationKind::ArithmeticSafety, false),
            (ObligationKind::ArithmeticSafety, trust_ir::ObligationKind::ArithmeticSafety, false),
            // An unrelated native kind, and a public kind trust-mc does not
            // own at all, both remain unbindable.
            (ObligationKind::Assertion, trust_ir::ObligationKind::Postcondition, false),
            (ObligationKind::MemorySafety, trust_ir::ObligationKind::MemorySafety, false),
        ];
        for (public_kind, native_kind, typed_formula_payload) in cases {
            let (bundle, native_bundle) = compiler_style_kind_pair_fixture(
                public_kind.clone(),
                native_kind.clone(),
                typed_formula_payload,
            );
            let reason = validate_compiler_style_public_claim_for_test(&bundle, &native_bundle, 0)
                .expect_err(&format!(
                    "{public_kind:?} -> {native_kind:?} (typed payload {typed_formula_payload}) is not a producer route and must fail closed"
                ));
            assert!(
                reason.contains("does not match native proof obligation"),
                "{public_kind:?} -> {native_kind:?} must be refused by the identity gate, got: {reason}"
            );
        }
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
                None,
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

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn compiler_style_exact_formula_public_bundle(
        kind: ObligationKind,
        attach_formula: fn(&mut TrustObligation),
    ) -> TrustContractBundle {
        let (mut bundle, _canonical_id, _marker_id) = compiler_style_canonical_public_bundle();
        bundle.obligations[0].kind = kind;
        bundle.obligations[0].metadata.retain(|entry| {
            !matches!(
                entry.key.as_str(),
                TRUST_VC_FORMULA_SCHEMA_METADATA_KEY
                    | TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY
                    | TRUST_VC_FORMULA_SORT_METADATA_KEY
                    | trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY
            )
        });
        attach_formula(&mut bundle.obligations[0]);
        bundle.validate().expect("exact formula public fixture must validate");
        bundle
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn replace_formula_context(
        obligation: &mut TrustObligation,
        context: trust_verifier_api::ObligationContext,
    ) {
        let entry = obligation
            .metadata
            .iter_mut()
            .find(|entry| entry.key == trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY)
            .expect("exact formula fixture context");
        *entry = context.to_metadata_entry().expect("replacement context serializes");
    }

    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn assert_live_formula_receipt_refused(bundle: TrustContractBundle, label: &str) {
        let native_bundle =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let outcome = adapter
            .evidence_from_native_trust_ir_bundle_with_deadline_and_fresh_receipts(
                &bundle,
                &bundle.obligations,
                &native_bundle,
                None,
                Some(Instant::now() + std::time::Duration::from_secs(10)),
            );
        assert_eq!(outcome.evidence.len(), 1, "{label}");
        assert!(
            outcome.fresh_exact_direct_receipts.is_empty(),
            "{label} acquired a live exact-direct receipt"
        );
        assert_ne!(
            outcome.evidence[0].status,
            EvidenceStatus::Proved,
            "{label} was proved without an admissible live receipt: {:?}",
            outcome.evidence[0].diagnostics
        );
        assert!(outcome.evidence[0].proof_strength.is_none(), "{label}");
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_bundle_producer_exact_formulas_retain_same_solve_live_receipts() {
        let cases: [(ObligationKind, fn(&mut TrustObligation)); 4] = [
            (ObligationKind::ArithmeticSafety, add_typed_body_aware_vc_formula),
            (ObligationKind::Assertion, add_typed_body_aware_vc_formula),
            (ObligationKind::Precondition, add_typed_body_aware_vc_formula),
            (ObligationKind::Postcondition, add_result_referencing_vc_formula),
        ];
        for (kind, attach_formula) in cases {
            let bundle = compiler_style_exact_formula_public_bundle(kind.clone(), attach_formula);
            let native_bundle = bind_compiler_style_native_bundle_to_public(
                compiler_style_safe_tmir_bundle(),
                &bundle,
            );
            let adapter = TrustMcVerifierApiAdapter::new(
                TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
            );
            let mut outcome = adapter
                .evidence_from_native_trust_ir_bundle_with_deadline_and_fresh_receipts(
                    &bundle,
                    &bundle.obligations,
                    &native_bundle,
                    None,
                    Some(Instant::now() + std::time::Duration::from_secs(10)),
                );
            assert_eq!(outcome.evidence.len(), 1);
            assert_eq!(
                outcome.evidence[0].status,
                EvidenceStatus::Proved,
                "producer-real {kind:?} direct solve was rejected: {:?}",
                outcome.evidence[0].diagnostics
            );
            let receipt = outcome
                .fresh_exact_direct_receipts
                .remove(&bundle.obligations[0].obligation_id)
                .unwrap_or_else(|| panic!("producer-real {kind:?} row lost its live receipt"));
            assert!(outcome.fresh_exact_direct_receipts.is_empty());
            assert_eq!(
                receipt
                    .still_authorizes(&bundle, &bundle.obligations[0])
                    .unwrap_or_else(|reason| panic!("{kind:?} receipt failed recheck: {reason}")),
                outcome.evidence[0]
                    .proof_strength
                    .clone()
                    .expect("proved exact evidence has proof strength")
            );
        }
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_bundle_formula_receipt_admission_fails_closed_at_live_seam() {
        assert_live_formula_receipt_refused(
            compiler_style_exact_formula_public_bundle(
                ObligationKind::Postcondition,
                add_result_free_vc_formula,
            ),
            "result-free _0 postcondition",
        );
        assert_live_formula_receipt_refused(
            compiler_style_exact_formula_public_bundle(
                ObligationKind::Postcondition,
                add_result_node_only_in_body_definition_formula,
            ),
            "positive-body-only Result postcondition",
        );
        assert_live_formula_receipt_refused(
            compiler_style_exact_formula_public_bundle(
                ObligationKind::Postcondition,
                add_negated_result_only_in_body_definition_formula,
            ),
            "negated-body-only Result postcondition",
        );

        let mut definition_entry = compiler_style_exact_formula_public_bundle(
            ObligationKind::Precondition,
            add_typed_body_aware_vc_formula,
        );
        replace_formula_context(
            &mut definition_entry.obligations[0],
            trust_verifier_api::ObligationContext::new(
                trust_verifier_api::ObligationProducer::CompilerMirExtract,
                trust_verifier_api::ObligationOrigin::Contract {
                    contract_id: "definition-entry-requires".to_string(),
                    contract_kind: ContractKind::Requires,
                    contract_index: 0,
                    predicate_schema: Some(
                        trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
                    ),
                },
            ),
        );
        assert_live_formula_receipt_refused(definition_entry, "definition-entry requires");

        let mut non_compiler = compiler_style_exact_formula_public_bundle(
            ObligationKind::Assertion,
            add_typed_body_aware_vc_formula,
        );
        replace_formula_context(
            &mut non_compiler.obligations[0],
            trust_verifier_api::ObligationContext::new(
                trust_verifier_api::ObligationProducer::VcGenerator,
                trust_verifier_api::ObligationOrigin::VerificationCondition {
                    vc_kind: "assertion".to_string(),
                    vc_index: 0,
                    formula_schema: Some(
                        trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
                    ),
                },
            ),
        );
        assert_live_formula_receipt_refused(non_compiler, "non-compiler producer");

        let mut malformed_schema = compiler_style_exact_formula_public_bundle(
            ObligationKind::Assertion,
            add_typed_body_aware_vc_formula,
        );
        malformed_schema.obligations[0]
            .metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_VC_FORMULA_SCHEMA_METADATA_KEY)
            .expect("formula schema")
            .value = "trust.vc.formula.invalid".to_string();
        assert_live_formula_receipt_refused(malformed_schema, "malformed formula schema");

        let mut malformed_payload = compiler_style_exact_formula_public_bundle(
            ObligationKind::Assertion,
            add_typed_body_aware_vc_formula,
        );
        malformed_payload.obligations[0]
            .metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
            .expect("formula payload")
            .value = "{}".to_string();
        assert_live_formula_receipt_refused(malformed_payload, "malformed formula payload");

        let mut missing_payload = compiler_style_exact_formula_public_bundle(
            ObligationKind::Assertion,
            add_typed_body_aware_vc_formula,
        );
        missing_payload.obligations[0]
            .metadata
            .retain(|entry| entry.key != TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY);
        assert_live_formula_receipt_refused(missing_payload, "missing formula payload");
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_bundle_missing_exact_input_does_not_start_a_second_generic_solve() {
        let mut bundle = compiler_style_safe_public_bundle();
        bundle.obligations[0].kind = ObligationKind::ArithmeticSafety;
        add_typed_body_aware_vc_formula(&mut bundle.obligations[0]);
        bundle.validate().expect("formula-only public fixture must validate");
        let native_bundle =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        TrustMcVerifierApiAdapter::reset_typed_chc_input_lookup_count_for_current_test_thread();
        let outcome = adapter
            .evidence_from_native_trust_ir_bundle_with_deadline_and_fresh_receipts(
                &bundle,
                &bundle.obligations,
                &native_bundle,
                None,
                Some(Instant::now() + std::time::Duration::from_secs(10)),
            );
        assert_eq!(
            TrustMcVerifierApiAdapter::typed_chc_input_lookup_count_for_current_test_thread(),
            1,
            "the fresh-dispatch miss must be the only exact-input lookup"
        );
        assert!(outcome.fresh_exact_direct_receipts.is_empty());
        assert_eq!(outcome.evidence.len(), 1);
        assert_ne!(outcome.evidence[0].status, EvidenceStatus::Proved);
        assert!(outcome.evidence[0].proof_strength.is_none());
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
            // The production compiler deliberately cannot mint this premise
            // yet.  This synthetic fixture is testing the consumer's
            // validated-refutation path, so state the positive producer edge
            // explicitly instead of relying on absence as exactness.
            attest_synthetic_typed_chc_encoding_exact(&mut bundle.obligations[0]);
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
        // See `certified_exact_e4_e5_refutation_is_terminal_before_native_transport`:
        // a synthetic positive-control refutation must carry the exact
        // producer-fidelity premise that production currently withholds.
        attest_synthetic_typed_chc_encoding_exact(&mut bundle.obligations[0]);
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
    fn owned_payloadless_e4_e5_rejects_supplied_contract_before_direct_solve() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc).with_timeout(10_000),
        );

        // v6/D3 makes E4/E5 ownership kind-stable, including at the public
        // low-level native-bundle entrypoint. Proof admission is narrower: a
        // directly provable caller-supplied contract cannot replace the
        // compiler's missing current Bool violation envelope.
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
                is_trust_mc_owned_obligation(&bundle.obligations[0])
                    && adapter.supports(&bundle.obligations[0]).is_supported(),
                "a payloadless {kind:?} remains TrustMC-owned under v6/D3"
            );

            let public_evidence = adapter.verify(&bundle, &bundle.obligations);
            let native_evidence = adapter.evidence_from_native_trust_ir_bundle(
                &bundle,
                &bundle.obligations,
                &native_bundle,
            );

            for (entrypoint, evidence) in
                [("ordinary verifier-api", public_evidence), ("native-bundle", native_evidence)]
            {
                assert_eq!(evidence.len(), 1);
                assert_eq!(
                    evidence[0].status,
                    EvidenceStatus::Unsupported,
                    "{entrypoint} must reject payloadless {kind:?} before solving the supplied contract: {:#?}",
                    evidence[0].diagnostics,
                );
                assert!(evidence[0].proof_strength.is_none());
                assert!(!evidence[0].is_unbounded_proof());
                assert!(evidence[0].artifacts.is_empty());
                assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
                    diagnostic.contains("trust-mc owns")
                        && diagnostic.contains(&format!("{kind:?}"))
                        && diagnostic.contains("current compiler-authenticated E4/E5 Bool formula")
                        && diagnostic.contains("rejected before direct solving")
                }));
                assert!(evidence[0].diagnostics.iter().all(|diagnostic| {
                    !diagnostic.contains("typed CHC/PDR proof transport accepted")
                        && !diagnostic.contains("typed CHC/PDR input artifact")
                }));
            }
        }
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn payloadless_e4_pre_rejection_does_not_suppress_valid_native_sibling() {
        let path = "demo::f";
        let panic_freedom_id = format!(
            "vc:{}:assertion:panic-freedom:0",
            trust_types::canonical_artifact_id_component(path)
        );
        let payloadless_id = native_typed_chc_obligation_id(8, 1);
        let mut bundle = compiler_style_public_bundle(&[
            (panic_freedom_id.as_str(), 7, 0, 18, 13, COMPILER_STYLE_SAFE_NORMALIZED_INPUT_DIGEST),
            (payloadless_id.as_str(), 8, 1, 42, 9, COMPILER_STYLE_FAILING_NORMALIZED_INPUT_DIGEST),
        ]);
        let panic_context = trust_verifier_api::ObligationContext::new(
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
            panic_context.to_metadata_entry().expect("panic context serializes"),
            MetadataEntry {
                key: TRUST_MC_PANIC_FREEDOM_OBLIGATION_METADATA_KEY.to_string(),
                value: "enabled".to_string(),
            },
            MetadataEntry { key: "trust.vc.kind".to_string(), value: "panic_freedom".to_string() },
        ]);
        assert!(obligation_is_whole_function_panic_freedom(&bundle, &bundle.obligations[0]));

        bundle.obligations[1].kind = ObligationKind::LoopInvariant;
        bundle.obligations[1].contract_id = Some("contract-payloadless-e4".to_string());
        bundle.obligations[1].metadata.retain(|entry| {
            !matches!(
                entry.key.as_str(),
                TRUST_MC_TYPED_CHC_SOURCE_DIGEST_METADATA_KEY
                    | TRUST_MC_TYPED_CHC_VC_DIGEST_METADATA_KEY
                    | TRUST_MC_TYPED_CHC_SYNTHETIC_DIGEST_METADATA_KEY
                    | TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY
            )
        });
        push_typed_chc_contract(
            &mut bundle,
            typed_chc_contract("contract-payloadless-e4", &payloadless_id, false),
        );
        let native_bundle = bind_compiler_style_native_bundle_to_public(
            compiler_style_mixed_tmir_bundle(),
            &bundle,
        );
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );

        let evidence = adapter.evidence_from_native_trust_ir_bundle(
            &bundle,
            &bundle.obligations,
            &native_bundle,
        );

        assert_eq!(evidence.len(), 2);
        assert_eq!(
            evidence[0].status,
            EvidenceStatus::Proved,
            "the exact safe panic-freedom sibling must still consume its native proof: {:#?}",
            evidence[0].diagnostics,
        );
        assert!(evidence[0].is_unbounded_proof());
        assert_eq!(evidence[1].status, EvidenceStatus::Unsupported);
        assert!(evidence[1].proof_strength.is_none());
        assert!(evidence[1].artifacts.is_empty());
        assert!(evidence[1].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("trust-mc owns LoopInvariant")
                && diagnostic.contains("rejected before direct solving")
        }));
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
        // The translated VC is shared (`Arc<ChcVc>`, trust-mc 5f805b33): copy it on
        // write, so the mutation reaches this row and not the seal's pre-solve copy.
        let query_rule = std::sync::Arc::make_mut(&mut row.translated.obligation.vc)
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
        assert!(
            !evidence[0].diagnostics.iter().any(|diagnostic| diagnostic
                == trust_verifier_api::NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC),
            "an ordinary rejected refutation transport has no source-fidelity stop"
        );
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

    /// The public integration-test failure: a bodyless cross-crate call has
    /// no supported direct-call summary. Solving its conservative error rule
    /// completes, but cannot produce a source-level counterexample.
    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_completed_refutation_keeps_typed_source_fidelity_stop() {
        use trust_ir::ty::Ty;
        use trust_ir_build::ModuleBuilder;

        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let public = compiler_style_panic_freedom_public_bundle();
        let mut native = compiler_style_safe_tmir_bundle();
        let mut builder = ModuleBuilder::new("native_cross_crate_call");
        let signature = builder.add_func_type(vec![Ty::I32], vec![]);
        let external = trust_ir::FuncId::new(1);
        let mut caller = builder.function("tmir_native_checked_branch", signature);
        let entry = caller.create_block();
        caller.switch_to_block(entry);
        caller.set_entry(entry);
        let arg = caller.add_block_param(entry, Ty::I32);
        caller.call_void(external, vec![arg]);
        caller.ret(vec![]);
        caller.build();
        assert_eq!(builder.declare_function("external_fixture::add1", signature), external);
        let module = builder.build().expect("actual native cross-crate call module");
        native.module.functions = module.functions;
        native.module.func_types = module.func_types;
        // Rebind diagnostic fixture identity; no source-generation authority,
        // proof artifact, or counterexample is supplied by this test.
        native = bind_compiler_style_native_bundle_to_public(native, &public);
        let evidence =
            adapter.evidence_from_native_trust_ir_bundle(&public, &public.obligations, &native);
        assert_eq!(evidence.len(), 1);
        let row = &evidence[0];
        assert_eq!(row.status, EvidenceStatus::Unsupported);
        assert!(row.proof_strength.is_none() && row.artifacts.is_empty());
        assert!(row.counterexample.is_none() && row.decline.is_none());
        assert!(
            row.diagnostics.iter().any(|diagnostic| diagnostic
                == trust_verifier_api::NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC),
            "the live per-row cause must survive transport: {:?}",
            row.diagnostics
        );
        assert!(
            !row.diagnostics.iter().any(|diagnostic| diagnostic
                == trust_verifier_api::NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC),
            "a completed query must not claim pre-solve refusal"
        );

        // The compiler's live-source entry must preserve the same actual
        // post-solve cause. Empty reference facts are still bound to this
        // exact live bundle and authority; no fact-free solve may substitute.
        let authority = trust_ir::SourceGenerationAuthority::mint_from_live_lowering(&mut native)
            .expect("live native source authority");
        let facts =
            SourceReferenceFacts::from_live_source_lowering(&native, &authority, vec![], vec![])
                .expect("empty facts bind to this exact live source");
        NATIVE_BUNDLE_SOURCE_REFERENCE_ENTRIES_FOR_TEST.with(|count| count.set((0, 0)));
        let live = adapter
            .evidence_from_native_trust_ir_bundle_with_source_reference_facts_and_deadline_and_fresh_receipts(
                &public,
                &public.obligations,
                &native,
                &authority,
                &facts,
                Some(Instant::now() + std::time::Duration::from_secs(10)),
            );
        assert_eq!(
            NATIVE_BUNDLE_SOURCE_REFERENCE_ENTRIES_FOR_TEST.with(std::cell::Cell::get),
            (1, 1),
            "both the pre-solve translation and solve must use live source facts"
        );
        assert_eq!(live.evidence.len(), 1);
        let row = &live.evidence[0];
        assert_eq!(row.status, EvidenceStatus::Unsupported);
        assert!(row.proof_strength.is_none() && row.artifacts.is_empty());
        assert!(row.counterexample.is_none() && row.decline.is_none());
        assert!(row.diagnostics.iter().any(|diagnostic| diagnostic
            == trust_verifier_api::NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC));
        assert!(!row.diagnostics.iter().any(|diagnostic| diagnostic
            == trust_verifier_api::NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC));
    }

    // The original bounded-unroll candidate still replays independently, but
    // flat exactness cannot authorize its publication as a Rust counterexample.
    // The historical test name is retained; its obsolete public Failed premise
    // is migrated explicitly to candidate replay plus native source refusal.
    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_bundle_surfaces_validated_bounded_unroll_refutation_as_failed() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let mut bundle = compiler_style_panic_freedom_public_bundle();
        attest_synthetic_typed_chc_encoding_exact(&mut bundle.obligations[0]);
        let native_bundle = bind_compiler_style_native_bundle_to_public(
            compiler_style_loop_overflow_tmir_bundle(),
            &bundle,
        );
        let (_, _, refuted) = adapter
            .native_trust_ir_chc_pdr_proof_transports(&native_bundle, None, None)
            .expect("loop fixture solves");
        let row = refuted.values().next().expect("real bounded-unroll witness");
        let rows = adapter
            .native_trust_ir_chc_pdr_translated_obligations(&native_bundle, None)
            .expect("loop fixture translates");
        let (_, summary) = native_refutation::check(
            &bundle,
            &bundle.obligations[0],
            &rows.iter().collect::<Vec<_>>(),
            row,
            chc_pdr_engine_from_config(adapter.config.proof_mode),
        )
        .expect("the original real candidate still passes all independent witness checks");
        assert!(summary.contains("bounded-unroll (k="), "actual replay kind: {summary}");

        let evidence = adapter.evidence_from_native_trust_ir_bundle(
            &bundle,
            &bundle.obligations,
            &native_bundle,
        );
        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].counterexample.is_none());
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].diagnostics.iter().any(|text| {
            text.contains("flat typed ChcVc only") && text.contains("source correspondence")
        }));
    }

    // Trust (bounded-unroll refutation lane, fail-closed halves): a REAL
    // witnessed refutation row must demote to unknown — never Failed, never
    // Proved — when (a) the public row carries a producer over-approximation
    // attestation (a model of an over-approximating encoding is not evidence,
    // even when its conclusion happens to be true), or (b) the witness is
    // replayed against a DIFFERENT public obligation (detached witnesses bind
    // nothing).
    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_refuted_row_demotes_on_attestation_or_detached_binding() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let bundle = compiler_style_panic_freedom_public_bundle();
        let native_bundle = bind_compiler_style_native_bundle_to_public(
            compiler_style_loop_overflow_tmir_bundle(),
            &bundle,
        );
        let (_, _, refuted) = adapter
            .native_trust_ir_chc_pdr_proof_transports(&native_bundle, None, None)
            .expect("loop fixture solves");
        let row = refuted.values().next().expect("loop fixture refutes with a witness");

        // (a) attested over-approximation on the public row → demoted before
        // any witness validation runs.
        let mut attested = bundle.clone();
        attested.obligations[0].metadata.push(MetadataEntry {
            key: TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_METADATA_KEY.to_string(),
            value: TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_LOOP_ELIDED.to_string(),
        });
        let consumer_rows = adapter
            .native_trust_ir_chc_pdr_translated_obligations(&native_bundle, None)
            .expect("loop fixture translates");
        let consumer_rows = consumer_rows.iter().collect::<Vec<_>>();
        let evidence = adapter.native_trust_ir_refuted_row_evidence(
            &attested,
            &attested.obligations[0],
            &consumer_rows,
            row,
        );
        assert_ne!(
            evidence.status,
            EvidenceStatus::Failed,
            "an attested over-approximate row must never ground a refutation"
        );
        assert_ne!(evidence.status, EvidenceStatus::Proved);
        assert!(
            evidence.diagnostics.iter().any(|diagnostic| {
                // 302ba178ce0 reworded the reason: it names the attested
                // over-approximation, no longer the "loop-elided" class.
                diagnostic.contains("refutation witness was not admitted")
                    && diagnostic.contains("attests the submitted ChcVc is an over-approximation")
            }),
            "demotion must say why: {:?}",
            evidence.diagnostics
        );

        // (b) the same witness replayed against a DIFFERENT retained native
        // bundle (same request/proof ids, different function body): the
        // consumer's own translation of that bundle recomputes a different
        // encoded-formula digest, so the detached witness fails binding
        // validation and demotes. This is the forged/detached-witness class:
        // the consumer trusts only digests it recomputes from its OWN bundle.
        let foreign_native =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        let foreign_rows = adapter
            .native_trust_ir_chc_pdr_translated_obligations(&foreign_native, None)
            .expect("safe fixture translates");
        let foreign_rows = foreign_rows.iter().collect::<Vec<_>>();
        let rejection = native_refutation::check(
            &bundle,
            &bundle.obligations[0],
            &foreign_rows,
            row,
            chc_pdr_engine_from_config(adapter.config.proof_mode),
        )
        .expect_err("the original detached witness attack must fail binding validation");
        assert!(
            rejection.contains("detached") || rejection.contains("digest"),
            "binding rejection: {rejection}"
        );
        let evidence = adapter.native_trust_ir_refuted_row_evidence(
            &bundle,
            &bundle.obligations[0],
            &foreign_rows,
            row,
        );
        assert_ne!(
            evidence.status,
            EvidenceStatus::Failed,
            "a detached witness must never ground a refutation"
        );
        assert_ne!(evidence.status, EvidenceStatus::Proved);
        assert!(
            evidence
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic.contains("refutation witness was not admitted") }),
            "demotion must say why: {:?}",
            evidence.diagnostics
        );
    }

    // WS-E step 8d: a witnessed refutation is revalidated against the
    // consumer's PRE-SOLVE translation of the same immutable native bundle,
    // retained by the bundle call, instead of translating the whole bundle
    // again for every refuted row. Two things are pinned:
    //   * cost: one whole-bundle consumer translation per bundle call, however
    //     many rows are refuted (it was 1 + the number of refuted rows);
    //   * identity: the refuted row's public evidence is byte-for-byte the
    //     evidence a post-solve re-translation of the whole bundle yields, and
    //     the retained lookup-key subset admits exactly what the whole
    //     translation admits.
    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_refuted_row_reuses_the_pre_solve_translation() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let mut bundle = compiler_style_panic_freedom_public_bundle();
        attest_synthetic_typed_chc_encoding_exact(&mut bundle.obligations[0]);
        let native_bundle = bind_compiler_style_native_bundle_to_public(
            compiler_style_loop_overflow_tmir_bundle(),
            &bundle,
        );

        NATIVE_BUNDLE_TRANSLATION_COUNT_FOR_TEST.with(|count| count.set(0));
        let evidence = adapter.evidence_from_native_trust_ir_bundle(
            &bundle,
            &bundle.obligations,
            &native_bundle,
        );
        let translations = NATIVE_BUNDLE_TRANSLATION_COUNT_FOR_TEST.with(std::cell::Cell::get);
        assert_eq!(evidence.len(), 1);
        assert_eq!(
            evidence[0].status,
            EvidenceStatus::Unsupported,
            "flat exactness must not publish a native source counterexample: {:?}",
            evidence[0].diagnostics
        );
        assert_eq!(
            translations, 1,
            "the bundle call translates the bundle once, before the solve; the refuted \
             row reuses that translation"
        );

        // The same refutation, revalidated three ways, gives one evidence value.
        let (_, _, refuted) = adapter
            .native_trust_ir_chc_pdr_proof_transports(&native_bundle, None, None)
            .expect("loop fixture solves");
        let [(lookup_key, row)] = refuted.iter().collect::<Vec<_>>()[..] else {
            panic!("loop fixture refutes exactly one row, not {}", refuted.len());
        };
        let after_solve = adapter
            .native_trust_ir_chc_pdr_translated_obligations(&native_bundle, None)
            .expect("loop fixture translates");
        let from_post_solve_translation = adapter.native_trust_ir_refuted_row_evidence(
            &bundle,
            &bundle.obligations[0],
            &after_solve.iter().collect::<Vec<_>>(),
            row,
        );
        let mut translated_by_obligation = BTreeMap::new();
        let mut translated_counts = BTreeMap::<String, usize>::new();
        for translated in adapter
            .native_trust_ir_chc_pdr_translated_obligations(&native_bundle, None)
            .expect("loop fixture translates")
        {
            let key = native_trust_mc_obligation_lookup_key(&translated.obligation.obligation_id);
            *translated_counts.entry(key.clone()).or_default() += 1;
            translated_by_obligation.entry(key).or_insert(translated);
        }
        let retained = native_trust_ir_retained_rows_for(
            &translated_by_obligation,
            &translated_counts,
            lookup_key,
        );
        assert_eq!(retained.len(), 1, "the refuted row's key has exactly one retained row");
        let from_retained_translation = adapter.native_trust_ir_refuted_row_evidence(
            &bundle,
            &bundle.obligations[0],
            &retained,
            row,
        );
        assert_eq!(from_retained_translation.status, EvidenceStatus::Unsupported);
        let check = |rows: &[&trust_mc_trust_bmc::NativeTrustMcChcPdrObligation]| {
            native_refutation::check(
                &bundle,
                &bundle.obligations[0],
                rows,
                row,
                chc_pdr_engine_from_config(adapter.config.proof_mode),
            )
            .map(|(input, summary)| (input.normalized_input_hash.value, summary))
        };
        let post_solve_checked = check(&after_solve.iter().collect::<Vec<_>>())
            .expect("the original candidate must still pass full witness replay");
        assert_eq!(check(&retained).unwrap(), post_solve_checked);
        assert_eq!(
            from_retained_translation, from_post_solve_translation,
            "the retained lookup-key subset must admit exactly what the whole translation admits"
        );
        assert_eq!(
            evidence[0], from_post_solve_translation,
            "the bundle call's refuted-row evidence must equal a post-solve re-translation's"
        );

        // A key the retained translation does not hold exactly once yields no
        // row, and the gate demotes: it never picks one of several rows.
        let mut doubled_counts = translated_counts.clone();
        *doubled_counts.get_mut(lookup_key.as_str()).expect("key is counted") = 2;
        let doubled = native_trust_ir_retained_rows_for(
            &translated_by_obligation,
            &doubled_counts,
            lookup_key,
        );
        assert!(doubled.is_empty());
        assert!(check(&doubled).unwrap_err().contains("yielded 0 rows"));
        let demoted = adapter.native_trust_ir_refuted_row_evidence(
            &bundle,
            &bundle.obligations[0],
            &doubled,
            row,
        );
        assert_ne!(demoted.status, EvidenceStatus::Failed);
        assert_ne!(demoted.status, EvidenceStatus::Proved);
        assert!(
            demoted.diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("refutation witness was not admitted")
                    && diagnostic.contains("source correspondence")
            }),
            "demotion must say why: {:?}",
            demoted.diagnostics
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

    /// gate-rca deadline (2026-10-17): a PASSED solve cutoff degrades the native bundle's
    /// obligation to Timeout while the dispatch deadline is still an hour away: the
    /// cutoff alone stops the native lane, so the certifying lanes after it keep their
    /// share of the clock. Control: the same adapter with no cutoff, under the same live
    /// deadline, proves the obligation.
    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_bundle_with_passed_solve_cutoff_degrades_to_timeout_under_a_live_deadline() {
        let config =
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000);
        let bundle = compiler_style_panic_freedom_public_bundle();
        let native_bundle =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &bundle);
        let live = Some(std::time::Instant::now() + std::time::Duration::from_secs(3600));
        let passed = std::time::Instant::now() - std::time::Duration::from_secs(1);

        let cut = TrustMcVerifierApiAdapter::new(config.clone())
            .with_solve_cutoff(Some(passed))
            .evidence_from_native_trust_ir_bundle_with_deadline(
                &bundle,
                &bundle.obligations,
                &native_bundle,
                live,
            );
        assert_eq!(cut.len(), 1);
        assert_eq!(cut[0].status, EvidenceStatus::Timeout, "a passed cutoff never proves");
        assert!(cut[0].proof_strength.is_none());

        let proved = TrustMcVerifierApiAdapter::new(config)
            .evidence_from_native_trust_ir_bundle_with_deadline(
                &bundle,
                &bundle.obligations,
                &native_bundle,
                live,
            );
        assert_eq!(proved.len(), 1);
        assert_eq!(
            proved[0].status,
            EvidenceStatus::Proved,
            "control: without the cutoff the same live dispatch proves (the test is not vacuous)"
        );
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_request_caller_options_preserve_zero_unbounded_and_finite_deadlines() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(0),
        );
        let unbounded = adapter.native_solve_options(None);
        assert_eq!(unbounded.timeout, None);
        assert_eq!(unbounded.produce_proof_certificate, adapter.config.produce_proofs);
        assert!(unbounded.native_request.is_none());
        let finite =
            adapter.native_solve_options(Some(Instant::now() + std::time::Duration::from_secs(5)));
        let remaining = finite.timeout.expect("a finite deadline caps Root's unbounded setting");
        assert!(remaining > std::time::Duration::ZERO);
        assert!(remaining <= std::time::Duration::from_secs(5));
        let ordinary = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(20_000),
        )
        .native_solve_options(None);
        assert_eq!(ordinary.timeout, Some(std::time::Duration::from_secs(20)));
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_kernel_replay_scheduling_excludes_only_the_unsupported_option_request() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let public = compiler_style_mixed_public_bundle();
        let mut original = bind_compiler_style_native_bundle_to_public(
            compiler_style_mixed_tmir_bundle(),
            &public,
        );
        // Unit-only use of the existing audited live issuer. Admission is
        // scheduling data; even the false sibling needs a real kernel proof
        // before a caller may omit its ordinary native search.
        let source =
            trust_ir::SourceGenerationAuthority::mint_from_live_lowering(&mut original).unwrap();
        let baseline = adapter
            .kernel_replay_admissible_native_obligations(
                &public,
                &public.obligations,
                &original,
                &source,
                None,
                None,
            )
            .unwrap();
        let expected =
            public.obligations.iter().map(|row| row.obligation_id.clone()).collect::<BTreeSet<_>>();
        assert_eq!(
            baseline, expected,
            "both original claims must pass the non-proving admission gate"
        );
        let mut changed = original.clone();
        let request = changed
            .requests
            .iter_mut()
            .find_map(|request| match request {
                trust_ir::NativeVerificationRequest::TrustMc(request)
                    if request.id.index() == 8 =>
                {
                    Some(request)
                }
                _ => None,
            })
            .unwrap();
        request.options.arithmetic_model = trust_ir::TrustMcArithmeticModel::MathematicalIntegers;
        let changed_source =
            trust_ir::SourceGenerationAuthority::mint_from_live_lowering(&mut changed).unwrap();
        let admitted = adapter
            .kernel_replay_admissible_native_obligations(
                &public,
                &public.obligations,
                &changed,
                &changed_source,
                None,
                None,
            )
            .unwrap();
        assert_eq!(admitted, BTreeSet::from([public.obligations[0].obligation_id.clone()]));
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_options_refusal_keeps_the_supported_proof_sibling() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let public = compiler_style_mixed_public_bundle();
        let mut native = bind_compiler_style_native_bundle_to_public(
            compiler_style_mixed_tmir_bundle(),
            &public,
        );
        let refused = native
            .requests
            .iter_mut()
            .find_map(|request| match request {
                trust_ir::NativeVerificationRequest::TrustMc(request)
                    if request.id.index() == 8 =>
                {
                    Some(request)
                }
                _ => None,
            })
            .unwrap();
        refused.options.arithmetic_model = trust_ir::TrustMcArithmeticModel::MathematicalIntegers;
        native.validate().unwrap();
        let configured = adapter
            .native_trust_ir_chc_pdr_translated_obligations_in_live_source(&native, None, None)
            .unwrap();
        assert_eq!(configured.obligations.len(), 1);
        assert_eq!(configured.refused_requests.len(), 1);
        assert_eq!(configured.refused_requests[0].field, "arithmetic_model");
        let expected_reason = configured.refused_requests[0].to_string();
        let (proved, not_proved, refuted) = adapter
            .native_trust_ir_chc_pdr_proof_transports(&native, None, None)
            .expect("one option refusal must not discard its supported sibling");
        assert_eq!(proved.len(), 1);
        assert_eq!(proved[0].request_id, 7);
        assert!(refuted.is_empty());
        assert_eq!(not_proved.len(), 1);
        let refused_id =
            native_trust_ir_expected_trust_mc_obligation_id(&public.obligations[1]).unwrap();
        assert_eq!(
            not_proved[&native_trust_mc_obligation_lookup_key(&refused_id)],
            expected_reason
        );
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_options_refusal_prevents_native_proof_credit() {
        let public = compiler_style_panic_freedom_public_bundle();
        let original =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &public);
        for mode in [TrustMcProofMode::Chc, TrustMcProofMode::PdrIc3] {
            let adapter = TrustMcVerifierApiAdapter::new(
                TrustMcConfig::new().with_proof_mode(mode).with_timeout(10_000),
            );
            let proved = adapter.evidence_from_native_trust_ir_bundle(
                &public,
                &public.obligations,
                &original,
            );
            assert_eq!(proved[0].status, EvidenceStatus::Proved, "{proved:#?}");
            let mut native = original.clone();
            let request = native
                .requests
                .iter_mut()
                .find_map(|request| match request {
                    trust_ir::NativeVerificationRequest::TrustMc(request) => Some(request),
                    _ => None,
                })
                .unwrap();
            request.options.arithmetic_model =
                trust_ir::TrustMcArithmeticModel::MathematicalIntegers;
            native.validate().expect("the unsupported encoding selector is structurally valid");
            let evidence =
                adapter.evidence_from_native_trust_ir_bundle(&public, &public.obligations, &native);
            assert_eq!(evidence.len(), 1);
            let row = &evidence[0];
            assert_eq!(row.status, EvidenceStatus::Unsupported, "{evidence:#?}");
            assert!(
                row.proof_strength.is_none()
                    && row.artifacts.is_empty()
                    && row.counterexample.is_none()
            );
            assert!(row.decline.is_none());
            assert!(row.diagnostics[0].contains("request options rejected"));
            assert!(row.diagnostics[0].contains("arithmetic_model=MathematicalIntegers"));
            assert!(row.diagnostics[0].contains("the native translator implements bitvectors"));

            // Zero frames is rejected earlier by the canonical IR validator,
            // not by the configured per-request unsupported-profile channel.
            let mut zero = original.clone();
            let request = zero
                .requests
                .iter_mut()
                .find_map(|request| match request {
                    trust_ir::NativeVerificationRequest::TrustMc(request) => Some(request),
                    _ => None,
                })
                .unwrap();
            request.options.chc.pdr.max_frames = Some(0);
            let errors = zero.validate().expect_err("zero frames is structurally invalid");
            assert_eq!(errors.len(), 1, "only the original zero-frame option changed");
            assert!(matches!(&errors[0],
                trust_ir::NativeVerificationBundleError::InvalidTrustMcChcOptions { request, field }
                    if request.index() == 7 && *field == "chc.pdr.max_frames"));
            let rejected =
                adapter.evidence_from_native_trust_ir_bundle(&public, &public.obligations, &zero);
            assert_eq!(rejected.len(), 1);
            let row = &rejected[0];
            assert_eq!(row.status, EvidenceStatus::Unsupported, "{rejected:#?}");
            assert!(
                row.proof_strength.is_none()
                    && row.artifacts.is_empty()
                    && row.counterexample.is_none()
            );
            assert!(row.decline.is_none());
            assert!(
                row.diagnostics
                    .iter()
                    .any(|reason| reason.contains("native verification bundle validation failed")),
                "the adapter must retain its original structural validation refusal: {rejected:#?}"
            );
        }
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_proof_rejects_options_only_mutation_and_foreign_live_verification() {
        let public = compiler_style_safe_public_bundle();
        let original =
            bind_compiler_style_native_bundle_to_public(compiler_style_safe_tmir_bundle(), &public);
        let mut changed = original.clone();
        let changed_request = changed
            .requests
            .iter_mut()
            .find_map(|request| match request {
                trust_ir::NativeVerificationRequest::TrustMc(request) => Some(request),
                _ => None,
            })
            .unwrap();
        changed_request.options.chc.pdr.max_frames = Some(1);
        let changed_config =
            trust_mc_trust_bmc::EffectiveNativeMcRequestConfig::from_request(changed_request)
                .unwrap();
        changed.validate().unwrap();
        let runner = trust_mc_driver::NativeTrustIrChcPdrRunner::with_solve_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(std::time::Duration::from_secs(10)),
        );
        let solve = |native: &trust_ir::NativeVerificationBundle| {
            runner.solve_bundle_native_proof_grade(native).unwrap().obligations.pop().unwrap()
        };
        let mut row = solve(&original);
        row.verification.authorized_native_proof().expect("real original proof");
        assert_ne!(row.translated.request_config.request_digest(), changed_config.request_digest());
        row.translated.request_config = changed_config;
        let reason = NativeTrustIrChcPdrAuthorizedProof::try_from_bundle_evidence(row).unwrap_err();
        assert!(reason.contains("request configuration"), "{reason}");

        let mut old_row = solve(&original);
        let mut changed_row = solve(&changed);
        old_row.verification.authorized_native_proof().unwrap();
        changed_row.verification.authorized_native_proof().unwrap();
        validate_native_trust_mc_consumer_request_config(&old_row.translated, &old_row.translated)
            .unwrap();
        assert!(
            validate_native_trust_mc_consumer_request_config(
                &old_row.translated,
                &changed_row.translated
            )
            .is_err(),
            "a coherent foreign profile is not the retained consumer request"
        );
        std::mem::swap(&mut old_row.verification, &mut changed_row.verification);
        std::mem::swap(&mut old_row.transport, &mut changed_row.transport);
        for row in [old_row, changed_row] {
            assert!(
                NativeTrustIrChcPdrAuthorizedProof::try_from_bundle_evidence(row).is_err(),
                "a coherent foreign live verification cannot answer another request profile"
            );
        }
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn native_trust_ir_refutation_uses_the_fresh_consumers_request_configuration() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let mut public = compiler_style_panic_freedom_public_bundle();
        attest_synthetic_typed_chc_encoding_exact(&mut public.obligations[0]);
        let original = bind_compiler_style_native_bundle_to_public(
            compiler_style_loop_overflow_tmir_bundle(),
            &public,
        );
        let (_, _, refuted) =
            adapter.native_trust_ir_chc_pdr_proof_transports(&original, None, None).unwrap();
        let row = refuted.values().next().expect("original real false-loop witness");
        let fresh =
            adapter.native_trust_ir_chc_pdr_translated_obligations(&original, None).unwrap();
        let engine = trust_mc_core::ChcPdrEngine::Pdr;
        native_refutation::check(
            &public,
            &public.obligations[0],
            &fresh.iter().collect::<Vec<_>>(),
            row,
            engine,
        )
        .expect("original witness independently replays under its own request profile");
        let mut changed = original.clone();
        let request = changed
            .requests
            .iter_mut()
            .find_map(|request| match request {
                trust_ir::NativeVerificationRequest::TrustMc(request) => Some(request),
                _ => None,
            })
            .unwrap();
        request.options.chc.pdr.max_frames = Some(1);
        changed.validate().unwrap();
        let changed_rows =
            adapter.native_trust_ir_chc_pdr_translated_obligations(&changed, None).unwrap();
        assert_ne!(
            fresh[0].request_config.effective_config_digest(),
            changed_rows[0].request_config.effective_config_digest()
        );
        let expected =
            trust_mc_driver::normalized_typed_chc_pdr_input(&changed_rows[0].obligation).unwrap();
        let original_normalized =
            trust_mc_driver::normalized_typed_chc_pdr_input(&fresh[0].obligation).unwrap();
        assert_eq!(
            expected.normalized_input, original_normalized.normalized_input,
            "only request configuration changed, not the encoded program"
        );
        let trust_mc_core::ChcPdrSolveStatus::Refuted { witness: Some(witness) } =
            &row.verification.outcome.status
        else {
            panic!("original false loop retains its actual witness");
        };
        let options = changed_rows[0]
            .request_config
            .solve_options(&trust_mc_core::ChcPdrSolveOptions::default().with_engine(engine));
        let reason = validate_typed_chc_pdr_refutation_witness_with_options(
            witness,
            &public.obligations[0],
            &row.verification.outcome.obligation_id,
            &expected,
            &options,
        )
        .unwrap_err();
        assert!(reason.contains("semantic-configuration digest"), "{reason}");
        assert!(
            native_refutation::check(
                &public,
                &public.obligations[0],
                &changed_rows.iter().collect::<Vec<_>>(),
                row,
                engine
            )
            .is_err()
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
        let (transports, not_proved, refuted) = adapter
            .native_trust_ir_chc_pdr_proof_transports(&native_bundle, None, None)
            .expect("mixed bundle must return independent producer rows");
        assert!(refuted.is_empty(), "acyclic rows keep their historical delivery: {refuted:?}");
        assert_eq!(transports.len(), 1, "the safe sibling must retain its proof transport");
        assert_eq!(not_proved.len(), 1, "the refutable sibling must retain its own outcome");

        let canonical_safe_id =
            native_trust_ir_expected_trust_mc_obligation_id(&bundle.obligations[0])
                .expect("fixture has canonical safe proof-unit identity");
        assert_eq!(
            native_trust_mc_obligation_lookup_key(&transports[0].diagnostic_transport().native_id,),
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
        let (transports, not_proved, refuted) = adapter
            .native_trust_ir_chc_pdr_proof_transports(&native_bundle, None, None)
            .expect("safe bundle must solve");
        assert!(refuted.is_empty(), "fully proved bundle must not report refuted rows");
        assert_eq!(transports.len(), 1);
        assert!(
            not_proved.is_empty(),
            "fully proved bundle must not report not-proved rows: {not_proved:?}"
        );
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn root_adapter_threads_only_exact_source_authority_to_trust_mc() {
        let adapter = TrustMcVerifierApiAdapter::new(
            TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
        );
        let public_bundle = compiler_style_safe_public_bundle();
        let mut native_bundle = bind_compiler_style_native_bundle_to_public(
            compiler_style_source_assume_tmir_bundle(),
            &public_bundle,
        );
        assert!(native_bundle.module.functions.iter().any(|function| {
            function.instructions().any(|node| matches!(&node.inst, trust_ir::Inst::Assume { .. }))
        }));

        let ordinary = adapter
            .native_trust_ir_chc_pdr_proof_transports_with_optional_source_authority(
                &native_bundle,
                None,
                None,
            )
            .expect_err("the ordinary root adapter route must default-deny source Assume");
        assert!(
            ordinary.to_string().contains("unauthenticated Assume"),
            "unexpected rejection: {ordinary}"
        );

        let authority =
            trust_ir::SourceGenerationAuthority::mint_from_live_lowering(&mut native_bundle)
                .expect("fresh root adapter fixture must mint source authority");
        adapter
            .native_trust_ir_chc_pdr_proof_transports_with_optional_source_authority(
                &native_bundle,
                Some(&authority),
                None,
            )
            .expect("the explicit root adapter route must admit exact source authority");

        let cloned_bundle = native_bundle.clone();
        let clone_error = adapter
            .native_trust_ir_chc_pdr_proof_transports_with_optional_source_authority(
                &cloned_bundle,
                Some(&authority),
                None,
            )
            .expect_err("a cloned bundle must lose source authority");
        assert!(
            clone_error.to_string().contains("unauthenticated Assume"),
            "unexpected clone rejection: {clone_error}"
        );

        let mut foreign_bundle = bind_compiler_style_native_bundle_to_public(
            compiler_style_source_assume_tmir_bundle(),
            &public_bundle,
        );
        let foreign_authority =
            trust_ir::SourceGenerationAuthority::mint_from_live_lowering(&mut foreign_bundle)
                .expect("independent root adapter fixture must mint its own authority");
        let mismatch = adapter
            .native_trust_ir_chc_pdr_proof_transports_with_optional_source_authority(
                &native_bundle,
                Some(&foreign_authority),
                None,
            )
            .expect_err("cross-bundle source authority must fail closed");
        assert!(
            mismatch.to_string().contains("unauthenticated Assume"),
            "unexpected mismatch rejection: {mismatch}"
        );
    }

    #[test]
    #[cfg(feature = "trust-mc-native-trust-ir-bundle")]
    fn root_source_authority_issuer_is_unique_and_legacy_marker_is_absent() {
        fn count_rust_source_occurrences(
            root: &std::path::Path,
            needle: &str,
            production_only: bool,
        ) -> usize {
            let mut pending = vec![root.to_path_buf()];
            let mut count = 0;
            while let Some(path) = pending.pop() {
                let entries = std::fs::read_dir(&path)
                    .unwrap_or_else(|error| panic!("failed to scan {}: {error}", path.display()));
                for entry in entries {
                    let entry = entry.expect("source-tree directory entry");
                    let path = entry.path();
                    let file_type = entry.file_type().expect("source-tree entry type");
                    if file_type.is_dir() {
                        if !matches!(
                            path.file_name().and_then(|name| name.to_str()),
                            Some("target" | ".git")
                        ) {
                            pending.push(path);
                        }
                    } else if file_type.is_file()
                        && path.extension().and_then(|extension| extension.to_str()) == Some("rs")
                        && !(production_only
                            && path.file_name().and_then(|name| name.to_str()) == Some("tests.rs"))
                    {
                        let source = std::fs::read_to_string(&path).unwrap_or_else(|error| {
                            panic!("failed to read {}: {error}", path.display())
                        });
                        let source = if production_only {
                            source
                                .find("#[cfg(test)]\nmod tests")
                                .map_or(source.as_str(), |test_module| &source[..test_module])
                        } else {
                            source.as_str()
                        };
                        count += source.match_indices(needle).count();
                    }
                }
            }
            count
        }

        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let issuer = ["mint", "_from_live_lowering", "("].concat();
        let legacy_marker = ["mark", "_source_generation_live"].concat();
        let issuer_count = [root.join("compiler"), root.join("crates")]
            .iter()
            .map(|path| count_rust_source_occurrences(path, &issuer, true))
            .sum::<usize>();
        let legacy_count = [root.join("compiler"), root.join("crates")]
            .iter()
            .map(|path| count_rust_source_occurrences(path, &legacy_marker, false))
            .sum::<usize>();

        assert_eq!(issuer_count, 1, "live source authority must have one audited root issuer");
        assert_eq!(legacy_count, 0, "the legacy forgeable marker must remain absent");
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
    fn proof_grade_native_evidence_for_payloadless_termination_fails_closed() {
        // A bare Termination claim is TrustMC-owned, but lacks the compiler's
        // valid typed violation formula and therefore cannot admit proof.
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
        assert!(!evidence.diagnostics.is_empty());
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
        assert!(!rejected.diagnostics.is_empty());
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

    /// Evaluate the small, closed Int/Bool expression fragment emitted by the
    /// truncating division/remainder lowering.  The primitive Int operations
    /// deliberately use Euclidean semantics, matching ay/SMT-LIB; the expected
    /// values in the tests use Rust `/` and `%`.
    fn eval_closed_truncating_arithmetic(expr: &Expr) -> i128 {
        use ay_bindings::ExprValue;

        match expr.value() {
            ExprValue::IntConst(value) => {
                value.to_string().parse::<i128>().expect("test integer fits i128")
            }
            ExprValue::IntSub(lhs, rhs) => {
                eval_closed_truncating_arithmetic(lhs) - eval_closed_truncating_arithmetic(rhs)
            }
            ExprValue::IntDiv(lhs, rhs) => eval_closed_truncating_arithmetic(lhs)
                .div_euclid(eval_closed_truncating_arithmetic(rhs)),
            ExprValue::IntMod(lhs, rhs) => eval_closed_truncating_arithmetic(lhs)
                .rem_euclid(eval_closed_truncating_arithmetic(rhs)),
            ExprValue::IntNeg(inner) => -eval_closed_truncating_arithmetic(inner),
            ExprValue::Ite { cond, then_expr, else_expr } => {
                if eval_closed_truncating_condition(cond) {
                    eval_closed_truncating_arithmetic(then_expr)
                } else {
                    eval_closed_truncating_arithmetic(else_expr)
                }
            }
            other => panic!("unexpected truncating-arithmetic node: {other:?}"),
        }
    }

    fn eval_closed_truncating_condition(expr: &Expr) -> bool {
        use ay_bindings::ExprValue;

        match expr.value() {
            ExprValue::BoolConst(value) => *value,
            ExprValue::IntGe(lhs, rhs) => {
                eval_closed_truncating_arithmetic(lhs) >= eval_closed_truncating_arithmetic(rhs)
            }
            other => panic!("unexpected truncating-arithmetic condition: {other:?}"),
        }
    }

    #[test]
    fn typed_chc_signed_bitvector_remainder_deserializes_without_unsigned_reinterpretation() {
        let source = serde_json::json!({
            "kind": "binary",
            "op": "bv_srem",
            "lhs": { "kind": "var", "name": "x", "sort": { "kind": "bit_vec", "width": 8 } },
            "rhs": { "kind": "bit_vec_const", "value": 2, "width": 8 },
        });
        let input: TrustMcTypedChcExprInput = serde_json::from_value(source.clone()).unwrap();
        let vars = BTreeMap::from([("x".to_string(), Sort::bitvec(8))]);
        let signed = input.to_trust_mc_expr(&vars).expect("new producer operation must lower");
        assert!(matches!(signed.value(), ay_bindings::ExprValue::BvSRem(..)));
        let expected =
            Expr::var("x".to_string(), Sort::bitvec(8)).bvsrem(Expr::bitvec_const(2_i128, 8));
        assert_eq!(signed, expected);
        let mut unsigned = source.clone();
        unsigned["op"] = serde_json::json!("bv_urem");
        let unsigned: TrustMcTypedChcExprInput = serde_json::from_value(unsigned).unwrap();
        let unsigned = unsigned.to_trust_mc_expr(&vars).unwrap();
        assert!(matches!(unsigned.value(), ay_bindings::ExprValue::BvURem(..)));
        assert_ne!(signed, unsigned, "a negative dividend distinguishes these operators");

        for rhs in [
            serde_json::json!({ "kind": "int_const", "value": "2" }),
            serde_json::json!({ "kind": "bool_const", "value": true }),
            serde_json::json!({ "kind": "bit_vec_const", "value": 2, "width": 16 }),
        ] {
            let mut malformed = source.clone();
            malformed["rhs"] = rhs;
            let input: TrustMcTypedChcExprInput = serde_json::from_value(malformed).unwrap();
            assert!(input.to_trust_mc_expr(&vars).is_err(), "sort mismatch must fail closed");
        }
        let mut division = source;
        division["op"] = serde_json::json!("bv_sdiv");
        assert!(serde_json::from_value::<TrustMcTypedChcExprInput>(division).is_err());
    }

    #[test]
    fn typed_chc_truncating_division_and_remainder_match_rust_signed_semantics() {
        let binary = super::trust_mc_typed_chc_binary_expr;

        for dividend in -7_i128..=7 {
            for divisor in -4_i128..=4 {
                if divisor == 0 {
                    continue;
                }

                let remainder = binary(
                    TrustMcTypedChcBinaryOpInput::TruncRem,
                    Expr::int_const(dividend),
                    Expr::int_const(divisor),
                )
                .expect("well-sorted truncating remainder must lower");
                let division = binary(
                    TrustMcTypedChcBinaryOpInput::TruncDiv,
                    Expr::int_const(dividend),
                    Expr::int_const(divisor),
                )
                .expect("well-sorted truncating division must lower");

                assert_eq!(
                    eval_closed_truncating_arithmetic(&remainder),
                    dividend % divisor,
                    "remainder mismatch for {dividend} % {divisor}"
                );
                assert_eq!(
                    eval_closed_truncating_arithmetic(&division),
                    dividend / divisor,
                    "division mismatch for {dividend} / {divisor}"
                );
            }
        }
    }

    #[test]
    fn typed_chc_legacy_division_and_modulus_fail_closed() {
        let binary = super::trust_mc_typed_chc_binary_expr;
        let int = Expr::int_const;

        for (op, wire_op) in
            [(TrustMcTypedChcBinaryOpInput::Div, "div"), (TrustMcTypedChcBinaryOpInput::Mod, "mod")]
        {
            let error = binary(op, int(-3_i128), int(2_i128))
                .expect_err("ambiguous legacy arithmetic must not become proof input");
            assert!(error.contains("semantically ambiguous"), "unexpected error: {error}");
            assert!(error.contains("trunc_div") && error.contains("trunc_rem"));

            // Even where both meanings happen to agree (including the entire
            // unsigned/non-negative source domain), accepting the legacy tag
            // would make admission depend on an unauthenticated range invariant
            // that schema v1 did not carry.
            assert!(binary(op, int(7_i128), int(3_i128)).is_err());

            let stale: TrustMcTypedChcExprInput = serde_json::from_value(serde_json::json!({
                "kind": "binary",
                "op": wire_op,
                "lhs": { "kind": "int_const", "value": "7" },
                "rhs": { "kind": "int_const", "value": "3" },
            }))
            .expect("legacy v1 tag should deserialize for a precise diagnostic");
            let error = stale
                .to_trust_mc_expr(&BTreeMap::new())
                .expect_err("stale v1 payload must fail closed before proof admission");
            assert!(error.contains("semantically ambiguous"), "unexpected error: {error}");
        }
    }

    #[test]
    fn typed_chc_truncating_ops_deserialize_and_fail_closed_on_sort_mismatch() {
        use serde_json::json;

        for op in ["trunc_div", "trunc_rem"] {
            let input: TrustMcTypedChcExprInput = serde_json::from_value(json!({
                "kind": "binary",
                "op": op,
                "lhs": { "kind": "int_const", "value": "-3" },
                "rhs": { "kind": "int_const", "value": "2" },
            }))
            .expect("producer truncating op must deserialize");
            let expr = input
                .to_trust_mc_expr(&BTreeMap::new())
                .expect("producer truncating op must lower");
            assert_eq!(expr.sort(), &Sort::int());
        }

        let bool_expr = || Expr::var("b".to_string(), Sort::bool());
        for op in [TrustMcTypedChcBinaryOpInput::TruncDiv, TrustMcTypedChcBinaryOpInput::TruncRem] {
            assert!(
                super::trust_mc_typed_chc_binary_expr(op, bool_expr(), Expr::int_const(2_i128),)
                    .is_err(),
                "truncating op {op:?} must reject a Bool operand"
            );
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

    #[test]
    fn wave491_semantic_projection_and_digest_and_contract_cache_match_oracle() {
        use serde_json::json;

        let make_contract = |id: &str, value: serde_json::Value| TrustContract {
            contract_id: id.to_string(),
            kind: ContractKind::Asserts,
            predicate: ContractPredicate::MathIr {
                schema: TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION.to_string(),
                value,
            },
            source: SourceLocation::default(),
            metadata: Vec::new(),
        };

        let canonical = make_contract(
            "canon",
            json!({
                "schema_version": TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION,
                "origin": "mir_derived",
                "function_name": "demo::f",
                "query": { "target": "bad" },
                "vars": [{ "name": "x", "sort": { "kind": "int" } }],
                "relations": [{ "name": "bad", "arg_sorts": [] }],
                "rules": [{
                    "head": { "name": "bad", "args": [] },
                    "body": { "constraints": [{ "kind": "bool_const", "value": false }] }
                }]
            }),
        );
        let native_matching = make_contract(
            "marker",
            json!({
                "schema_version": TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION,
                "obligation_id": "trust_ir-native-trust-mc-request-0-proof-0",
                "native_metadata": {
                    "native_request_id": 0,
                    "proof_obligation_ids": [0],
                    "function_id": 0
                },
                "origin": "mir_derived",
                "function_name": "demo::f",
                "query": { "target": "bad" },
                "vars": [{ "name": "x", "sort": { "kind": "int" } }],
                "relations": [{ "name": "bad", "arg_sorts": [] }],
                "rules": [{
                    "head": { "name": "bad", "args": [] },
                    "body": { "constraints": [{ "kind": "bool_const", "value": false }] }
                }]
            }),
        );
        assert!(
            validate_compiler_canonical_trust_mc_semantic_projection(&canonical, &native_matching)
                .is_ok()
        );

        let native_extra_semantic = make_contract(
            "marker-extra",
            json!({
                "schema_version": TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA_VERSION,
                "obligation_id": "trust_ir-native-trust-mc-request-0-proof-0",
                "origin": "mir_derived",
                "function_name": "demo::f",
                "extra_semantic_field": 1,
                "query": { "target": "bad" },
                "vars": [{ "name": "x", "sort": { "kind": "int" } }],
                "relations": [{ "name": "bad", "arg_sorts": [] }],
                "rules": []
            }),
        );
        assert!(
            validate_compiler_canonical_trust_mc_semantic_projection(
                &canonical,
                &native_extra_semantic
            )
            .is_err()
        );

        // Digest streaming matches explicit prefix + to_vec reference bytes.
        let ContractPredicate::MathIr { value, .. } = &native_matching.predicate else {
            panic!("expected MathIr");
        };
        let canonical_json = trust_types::canonical_json_value(value);
        let mut expected_bytes = b"trust-mc.typed-chc-obligation.digest.v1\0".to_vec();
        expected_bytes.extend(serde_json::to_vec(&canonical_json).unwrap());
        let expected_digest = stable_sha256_hex(&expected_bytes);
        assert_eq!(trust_mc_typed_chc_value_digest(value).unwrap(), expected_digest);

        // ContractChcCache returns identical parsed inputs and digests on repeated lookups.
        let contracts = vec![canonical.clone(), native_matching.clone()];
        let cache = ContractChcCache::new(&contracts);
        assert_eq!(cache.indices("canon"), &[0]);
        assert_eq!(cache.indices("marker"), &[1]);
        assert!(cache.indices("missing").is_empty());
        assert_eq!(cache.input_digest(1, &contracts[1]).unwrap(), expected_digest);
        assert_eq!(cache.input_digest(1, &contracts[1]).unwrap(), expected_digest);
        assert!(cache.parsed_input(0, &contracts[0]).unwrap().is_some());
        assert!(cache.parsed_input(99, &contracts[0]).is_err());

        // Lowercase sha256 validator accepts exact 64-char lowercase hex and rejects uppercase/short.
        assert!(is_lowercase_sha256_hex(&expected_digest));
        assert!(!is_lowercase_sha256_hex(&expected_digest.to_ascii_uppercase()));
        assert!(!is_lowercase_sha256_hex(&expected_digest[..63]));
    }
    #[test]
    fn native_routing_identity_preserves_mc_metadata_policy_and_rejects_conflicts() {
        fn legacy(row: &TrustObligation) -> Option<String> {
            let suite =
                obligation_metadata_value(row, TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY)?;
            if suite != "trust-mc" {
                return None;
            }
            let request = canonical_u32_metadata_value(obligation_metadata_value(
                row,
                TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY,
            )?)?;
            let proof = canonical_u32_metadata_value(obligation_metadata_value(
                row,
                TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
            )?)?;
            Some(format!("trust_ir-native-trust-mc-request-{request}-proof-{proof}"))
        }
        for request in ["0", "7", "4294967295", "07", "+7", "-1", "4294967296", ""] {
            for proof in ["0", "2", "02", "bad"] {
                let mut row = obligation(ObligationKind::Assertion, "public");
                row.metadata = [
                    (TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY, "trust-mc"),
                    (TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY, request),
                    (TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY, proof),
                ]
                .into_iter()
                .map(|(key, value)| MetadataEntry { key: key.into(), value: value.into() })
                .collect();
                assert_eq!(native_trust_ir_expected_trust_mc_obligation_id(&row), legacy(&row));
            }
        }
        let mut row =
            obligation(ObligationKind::Assertion, "trust_ir-native-trust-mc-request-7-proof-2");
        row.metadata = [
            (TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY, "trust-mc"),
            (TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY, "7"),
            (TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY, "2"),
        ]
        .into_iter()
        .map(|(key, value)| MetadataEntry { key: key.into(), value: value.into() })
        .collect();
        assert_eq!(native_trust_ir_expected_trust_mc_obligation_id(&row), legacy(&row));
        for key in [
            TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY,
            TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY,
            TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
        ] {
            let mut duplicate = row.clone();
            duplicate
                .metadata
                .push(duplicate.metadata.iter().find(|entry| entry.key == key).unwrap().clone());
            assert!(native_trust_ir_expected_trust_mc_obligation_id(&duplicate).is_none());
            let mut missing = row.clone();
            missing.metadata.retain(|entry| entry.key != key);
            assert!(native_trust_ir_expected_trust_mc_obligation_id(&missing).is_none());
        }
        for id in [
            "trust_ir-native-trust_mc-request-7-proof-2",
            "trust_ir-native-TRUST_MC-request-7-proof-2",
        ] {
            row.obligation_id = id.into();
            assert!(native_trust_ir_expected_trust_mc_obligation_id(&row).is_some());
        }
        for suite in ["TRUST-MC", "trust_mc"] {
            let mut wrong = row.clone();
            wrong
                .metadata
                .iter_mut()
                .find(|entry| entry.key == TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY)
                .unwrap()
                .value = suite.into();
            assert!(native_trust_ir_expected_trust_mc_obligation_id(&wrong).is_none());
        }
        for changed in [
            "trust_ir-native-trust-mc-request-8-proof-2",
            "trust_ir-native-trust-mc-request-7-proof-3",
            "trust_ir-native-trust-vc-request-7-proof-2",
        ] {
            row.obligation_id = changed.into();
            assert!(legacy(&row).is_some(), "old metadata-only reader ignored the conflict");
            assert!(native_trust_ir_expected_trust_mc_obligation_id(&row).is_none(), "{changed}");
        }
    }
}
