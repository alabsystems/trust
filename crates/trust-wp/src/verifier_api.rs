// trust_wp verifier-api adapter
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Fail-closed `trust-verifier-api` adapter for trust_wp.
//!
//! trust_wp owns deductive precondition, postcondition, loop-invariant,
//! refinement, and termination obligations at the full-verification boundary.
//! The proof-strength boundary is trust-wp's aggregate native replay gate added in
//! commit `5ac5fe6c848d491da99b6298cfdd4ef632cfc9d9`: a
//! `TrustWpNativePureReplayV1` proof is not reportable until it has been
//! replayed through trust-wp's `VerifyBundleResult` aggregation.
//!
//! Default builds have not wired that aggregate verifier into the adapter. They
//! may decode typed `TrustWpPureExprV1` predicates for diagnostics and local
//! refutation, but successful local replay is not treated as
//! `ProofStrength::deductive`. With `trust-build`, typed `TrustWpPureExprV1`
//! claims are sent directly to trust-wp's committed `NativeTrustWpBundleVerifier`;
//! only an aggregate `VerifyBundleResult::Verified` with proof-grade
//! `TrustWpNativePureReplayV1` evidence and concrete proof transport artifacts is
//! reportable as proof. If the vendored `first-party/trust-wp` checkout is stale
//! and lacks trust-wp's artifact transport API, trust-build fails closed instead
//! of accepting hash-only/text-only evidence. The adapter never shells out to
//! the compatibility CLI path and never treats source strings, contract
//! presence, metadata, summaries, inferred facts, solver success, or
//! lowered-but-not-aggregate-replayed predicates as proof evidence.

use std::collections::BTreeMap;
use std::fmt::Write;

use serde::{Deserialize, Serialize};
use trust_verifier_api::{
    API_VERSION, ArtifactHash, ContractKind, ContractPredicate, Counterexample, EngineCapability,
    EngineKind, EngineManifest, EvidenceArtifact, EvidenceArtifactKind,
    EvidencePublicationMetadata, EvidenceStatus, ObligationEvidence, ObligationKind, ProofStrength,
    ReasoningKind, SummaryFact, SupportLevel, TRUST_SPEC_PREDICATE_SCHEMA_VERSION, TrustContract,
    TrustContractBundle, TrustObligation, TrustSpecBinaryOp, TrustSpecExpr, TrustSpecExprKind,
    TrustSpecPredicate, TrustSpecSort, TrustSpecUnaryOp, ValidatedVerificationRequest,
    VerificationEngine,
};
#[cfg(feature = "trust-build")]
use trust_verifier_api::{EvidenceArtifactMaterialization, EvidenceArtifactReference};

/// Public trust_wp engine name used in manifests and evidence IDs.
pub const TRUST_WP_ENGINE_NAME: &str = "trust-wp";

/// Fail-closed reason used until native trust_wp bundle lowering and proof exist.
pub const TRUST_WP_NATIVE_NOT_WIRED: &str =
    "trust-wp native TrustContractBundle proof-evidence adapter is not wired";

/// trust_wp commit that introduced aggregate native replay evidence checking.
pub(crate) const TRUST_WP_AGGREGATE_NATIVE_REPLAY_GATE_COMMIT: &str =
    "5ac5fe6c848d491da99b6298cfdd4ef632cfc9d9";

/// Fail-closed reason used while Trust does not call trust-wp's aggregate gate.
#[cfg(not(feature = "trust-build"))]
pub(crate) const TRUST_WP_AGGREGATE_NATIVE_REPLAY_GATE_NOT_WIRED: &str =
    "trust-wp aggregate native replay evidence gate is not wired in Trust";

/// Audit schema label for trust-wp's aggregate native replay gate.
pub(crate) const TRUST_WP_AGGREGATE_NATIVE_REPLAY_GATE_SCHEMA_VERSION: &str =
    "trust_wp.verify-bundle.aggregate-native-replay-gate.v1";

/// trust_wp proof evidence schema required before this adapter can claim proof.
pub(crate) const TRUST_WP_PROOF_EVIDENCE_SCHEMA_VERSION: &str = "trust_wp.proof-evidence.v1";

/// trust_wp replay schema required for the first native pure-predicate fragment.
pub(crate) const TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION: &str =
    "trust_wp.native-pure-replay.v1";

// These are wire-format metadata keys, not Rust identifiers: they must match
// the canonical `trust_wp_core::verify_bundle::TRUST_WP_*_METADATA_KEY`
// constants byte for byte (`trust.trust-wp.*`, with `tmir` naming), or
// metadata attached by trust-router under these keys is invisible to
// trust-wp-core's typed readers and every obligation fails closed.
/// Public metadata key for trust_wp native-origin replay context.
pub const TRUST_TRUST_WP_NATIVE_ORIGIN_METADATA_KEY: &str = "trust.trust-wp.native-origin.v1";
/// Public metadata key for a trust_wp native claim digest.
pub const TRUST_TRUST_WP_CLAIM_DIGEST_METADATA_KEY: &str = "trust.trust-wp.claim-digest.v1";
/// Public metadata key for the trust_wp TrustIr source span.
pub const TRUST_TRUST_WP_TRUST_IR_SOURCE_SPAN_METADATA_KEY: &str =
    "trust.trust-wp.tmir-source-span.v1";
/// Public metadata key for trust_wp native verifier identity.
pub const TRUST_TRUST_WP_NATIVE_VERIFIER_METADATA_KEY: &str = "trust.trust-wp.native-verifier.v1";
/// Public metadata key for trust_wp native replay identity.
pub const TRUST_TRUST_WP_NATIVE_REPLAY_METADATA_KEY: &str = "trust.trust-wp.native-replay.v1";
/// Public metadata key for a trust_wp native solver/prover identity.
pub const TRUST_TRUST_WP_NATIVE_SOLVER_METADATA_KEY: &str = "trust.trust-wp.native-solver.v1";
/// Public metadata key for the trust_wp TrustIr obligation source.
pub const TRUST_TRUST_WP_TRUST_IR_OBLIGATION_SOURCE_METADATA_KEY: &str =
    "trust.trust-wp.tmir-obligation-source.v1";
/// Public metadata key for trust_wp proof-context atoms.
pub const TRUST_TRUST_WP_PROOF_CONTEXT_METADATA_KEY: &str = "trust.trust-wp.proof-context.v1";
/// Public metadata key for trust-wp-native summary facts.
pub const TRUST_TRUST_WP_NATIVE_SUMMARY_FACT_METADATA_KEY: &str = "trust.trust-wp.summary-fact.v1";

/// Required metadata keys for trust_wp native replay evidence over TrustIr requests.
pub const TRUST_TRUST_WP_NATIVE_REPLAY_REQUIRED_METADATA_KEYS: [&str; 6] = [
    TRUST_TRUST_WP_NATIVE_ORIGIN_METADATA_KEY,
    TRUST_TRUST_WP_TRUST_IR_SOURCE_SPAN_METADATA_KEY,
    TRUST_TRUST_WP_NATIVE_VERIFIER_METADATA_KEY,
    TRUST_TRUST_WP_NATIVE_REPLAY_METADATA_KEY,
    TRUST_TRUST_WP_NATIVE_SOLVER_METADATA_KEY,
    TRUST_TRUST_WP_TRUST_IR_OBLIGATION_SOURCE_METADATA_KEY,
];

/// trust_wp aggregate proof manifest schema checked before proof evidence is trusted.
///
/// Wire-format value: must stay byte-identical to trust-wp-core's canonical
/// `TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION` (`trust-wp.` spelling) or
/// every aggregate `checked_by`/format comparison rejects valid core evidence.
#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
pub(crate) const TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION: &str =
    "trust-wp.verify-bundle-aggregate.v1";

/// Diagnostic marker for stale vendored trust_wp checkouts.
#[cfg(all(feature = "trust-build", not(trust_wp_proof_transport_api)))]
pub(crate) const TRUST_WP_PROOF_TRANSPORT_API_MISSING: &str =
    "vendored trust_wp proof transport artifact API is missing";

/// Diagnostic marker for trust_wp checkouts without typed native artifact context.
#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    not(trust_wp_structured_context_api)
))]
pub(crate) const TRUST_WP_STRUCTURED_CONTEXT_API_MISSING: &str =
    "vendored trust_wp typed TrustIr/native artifact context API is missing";

/// Diagnostic marker for trust_wp checkouts without the aggregate replay helper.
#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    trust_wp_structured_context_api,
    not(trust_wp_verify_bundle_replay_helper_api)
))]
pub(crate) const TRUST_WP_REPLAY_HELPER_API_MISSING: &str =
    "vendored trust_wp aggregate proof replay helper API is missing";

/// Typed trust_wp pure-expression claim schema accepted by the replay adapter.
pub(crate) const TRUST_WP_PURE_EXPR_SCHEMA_VERSION: &str = "TrustWpPureExprV1";

/// Structured trust_wp TrustFormulaV1 claim schema accepted only through
/// trust-wp's committed native bundle verifier.
pub(crate) const TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION: &str = "trust_wp.trust-formula.v1";

/// Symbolic `trust-types::Formula` claim schema. Predicates delivered with this
/// schema carry a serde-serialized `trust_types::Formula`; this adapter lowers
/// them into the `trust_wp.trust-formula.v1` envelope before native replay.
pub(crate) const TRUST_TYPES_FORMULA_SCHEMA_VERSION: &str = "trust-types.Formula@1";

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
mod trust_wp_metadata_keys {
    #[cfg(trust_wp_metadata_constants_api)]
    pub(crate) use trust_wp_core::verify_bundle::{
        TRUST_WP_CLAIM_DIGEST_METADATA_KEY, TRUST_WP_NATIVE_ORIGIN_METADATA_KEY,
        TRUST_WP_NATIVE_REPLAY_METADATA_KEY, TRUST_WP_NATIVE_SOLVER_METADATA_KEY,
        TRUST_WP_NATIVE_SUMMARY_FACT_METADATA_KEY, TRUST_WP_NATIVE_VERIFIER_METADATA_KEY,
        TRUST_WP_PROOF_CONTEXT_METADATA_KEY, TRUST_WP_TMIR_OBLIGATION_SOURCE_METADATA_KEY,
        TRUST_WP_TMIR_SOURCE_SPAN_METADATA_KEY,
    };

    // Fallback wire-format keys used only when the vendored trust_wp does not
    // export its metadata key constants; the values must stay byte-identical
    // to trust-wp-core's canonical `trust.trust-wp.*` keys.
    #[cfg(not(trust_wp_metadata_constants_api))]
    /// Optional JSON metadata key carrying typed native trust_wp origin information.
    pub(crate) const TRUST_WP_NATIVE_ORIGIN_METADATA_KEY: &str = "trust.trust-wp.native-origin.v1";
    #[cfg(not(trust_wp_metadata_constants_api))]
    /// Optional JSON metadata key carrying a trust_wp `BundleClaim` digest.
    pub(crate) const TRUST_WP_CLAIM_DIGEST_METADATA_KEY: &str = "trust.trust-wp.claim-digest.v1";
    #[cfg(not(trust_wp_metadata_constants_api))]
    /// JSON metadata key carrying a typed trust_wp tMIR source span.
    pub(crate) const TRUST_WP_TMIR_SOURCE_SPAN_METADATA_KEY: &str =
        "trust.trust-wp.tmir-source-span.v1";
    #[cfg(not(trust_wp_metadata_constants_api))]
    /// JSON metadata key carrying a typed trust_wp native verifier identity.
    pub(crate) const TRUST_WP_NATIVE_VERIFIER_METADATA_KEY: &str =
        "trust.trust-wp.native-verifier.v1";
    #[cfg(not(trust_wp_metadata_constants_api))]
    /// JSON metadata key carrying a typed trust_wp native replay identity.
    pub(crate) const TRUST_WP_NATIVE_REPLAY_METADATA_KEY: &str = "trust.trust-wp.native-replay.v1";
    #[cfg(not(trust_wp_metadata_constants_api))]
    /// JSON metadata key carrying one typed native solver/prover identity.
    pub(crate) const TRUST_WP_NATIVE_SOLVER_METADATA_KEY: &str = "trust.trust-wp.native-solver.v1";
    #[cfg(not(trust_wp_metadata_constants_api))]
    /// JSON metadata key carrying a typed trust_wp tMIR obligation source.
    pub(crate) const TRUST_WP_TMIR_OBLIGATION_SOURCE_METADATA_KEY: &str =
        "trust.trust-wp.tmir-obligation-source.v1";
    #[cfg(not(trust_wp_metadata_constants_api))]
    /// JSON metadata key carrying typed assumption/assertion proof context.
    pub(crate) const TRUST_WP_PROOF_CONTEXT_METADATA_KEY: &str = "trust.trust-wp.proof-context.v1";
    #[cfg(not(trust_wp_metadata_constants_api))]
    /// JSON metadata key carrying one trust-wp-native abstract-interpretation summary fact.
    pub(crate) const TRUST_WP_NATIVE_SUMMARY_FACT_METADATA_KEY: &str =
        "trust.trust-wp.summary-fact.v1";
}

#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    trust_wp_structured_context_api
))]
#[allow(unused_imports)]
pub(crate) use trust_wp_metadata_keys::{
    TRUST_WP_CLAIM_DIGEST_METADATA_KEY, TRUST_WP_NATIVE_ORIGIN_METADATA_KEY,
    TRUST_WP_NATIVE_REPLAY_METADATA_KEY, TRUST_WP_NATIVE_SOLVER_METADATA_KEY,
    TRUST_WP_NATIVE_SUMMARY_FACT_METADATA_KEY, TRUST_WP_NATIVE_VERIFIER_METADATA_KEY,
    TRUST_WP_PROOF_CONTEXT_METADATA_KEY, TRUST_WP_TMIR_OBLIGATION_SOURCE_METADATA_KEY,
    TRUST_WP_TMIR_SOURCE_SPAN_METADATA_KEY,
};

/// Artifact kinds required by trust_wp native pure replay evidence.
pub(crate) const TRUST_WP_NATIVE_PURE_REPLAY_REQUIRED_ARTIFACTS: [&str; 2] =
    ["normalized-obligation", "replay-log"];

/// `trust-verifier-api` engine adapter for trust-wp's native full-verification lane.
#[derive(Debug, Clone)]
pub struct TrustWpVerificationEngine {
    manifest: EngineManifest,
    native_replay_evidence: Vec<ObligationEvidence>,
}

impl TrustWpVerificationEngine {
    /// Create the fail-closed trust_wp adapter.
    #[must_use]
    pub fn new() -> Self {
        let mut manifest = EngineManifest::new(
            TRUST_WP_ENGINE_NAME,
            env!("CARGO_PKG_VERSION"),
            EngineKind::Deductive,
        );
        manifest.repository = Some("trust-wp".to_string());
        manifest.api_version = API_VERSION.to_string();
        manifest.capabilities = trust_wp_owned_obligation_kinds()
            .into_iter()
            .map(|obligation_kind| EngineCapability {
                support: trust_wp_support_for_obligation_kind(&obligation_kind),
                obligation_kind,
            })
            .collect();
        manifest.proof_modes = vec![ReasoningKind::Deductive, ReasoningKind::Inductive];

        Self { manifest, native_replay_evidence: Vec::new() }
    }

    /// Attach native trust_wp replay evidence produced by trust-wp-owned proof replay.
    ///
    /// The adapter still validates every evidence item against the requested
    /// obligation and its typed `TrustWpPureExprV1` predicate before returning
    /// `Proved`.
    #[must_use]
    pub fn with_native_replay_evidence(
        mut self,
        native_replay_evidence: Vec<ObligationEvidence>,
    ) -> Self {
        self.native_replay_evidence = native_replay_evidence;
        self
    }

    /// Build fail-closed trust_wp evidence for a rejected native TrustIr proof input.
    ///
    /// This is used by routers that selected trust_wp through a typed
    /// `NativeVerificationBundle`: public metadata alone is not allowed to fall
    /// through as proof when the native request identity is missing or invalid.
    #[must_use]
    pub fn native_trust_ir_bundle_unsupported_evidence(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        reason: impl Into<String>,
    ) -> ObligationEvidence {
        let mut unsupported = self.unsupported_evidence(bundle, obligation);
        unsupported.evidence_id =
            format!("trust-wp:native-trust-ir-rejected:{}", obligation.obligation_id);
        unsupported.diagnostics.insert(
            0,
            format!("trust-wp native TrustIr bundle evidence rejected: {}", reason.into()),
        );
        unsupported
    }

    /// Verify one public obligation using a matched trust_wp request from a typed
    /// TrustIr native verification bundle.
    ///
    /// Existing public `trust.trust_wp.*` metadata is stripped before trust-wp's
    /// controlled metadata helper regenerates proof-relevant context from the
    /// supplied native bundle. This prevents stale or metadata-only replay
    /// evidence from being accepted as native TrustIr proof.
    #[cfg(feature = "trust-build")]
    #[must_use]
    pub fn verify_obligation_with_native_trust_ir_request(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        native_bundle: &trust_ir::NativeVerificationBundle,
        request: &trust_ir::TrustWpNativeRequest,
        proof_obligation_id: trust_ir::ProofId,
    ) -> ObligationEvidence {
        if let Err(errors) = native_bundle.validate() {
            return self.native_trust_ir_bundle_unsupported_evidence(
                bundle,
                obligation,
                format!(
                    "typed TrustIr NativeVerificationBundle validation failed before trust-wp replay: {}",
                    errors
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join("; ")
                ),
            );
        }
        let bundled_request = native_bundle.requests.iter().find_map(|candidate| {
            let trust_ir::NativeVerificationRequest::TrustWp(candidate) = candidate else {
                return None;
            };
            (candidate.id == request.id).then_some(candidate)
        });
        if bundled_request != Some(request) {
            return self.native_trust_ir_bundle_unsupported_evidence(
                bundle,
                obligation,
                format!(
                    "trust-wp native request {} is not the exact validated request carried by the supplied TrustIr bundle",
                    request.id.index()
                ),
            );
        }
        let claim = match native_trust_ir_claim_for_obligation(
            bundle,
            native_bundle,
            request,
            proof_obligation_id,
            obligation,
        ) {
            Ok(claim) => claim,
            Err(reason) => {
                return self
                    .native_trust_ir_bundle_unsupported_evidence(bundle, obligation, reason);
            }
        };

        let mut native_bundle_view = strip_trust_wp_native_metadata_from_bundle(bundle);
        let mut native_obligation = strip_trust_wp_native_metadata_from_obligation(obligation);
        if let Err(reason) = native_bundle_view
            .validate_requested_obligations(std::slice::from_ref(&native_obligation))
        {
            return self.native_trust_ir_bundle_unsupported_evidence(
                bundle,
                obligation,
                format!(
                    "cannot bind trust-wp native replay to an exact canonical public-obligation record: {reason}"
                ),
            );
        }
        let claim_digest = match native_bundle_view
            .canonical_obligation_semantic_digest_sha256(&native_obligation)
        {
            Ok(digest) => digest,
            Err(reason) => {
                return self.native_trust_ir_bundle_unsupported_evidence(
                    bundle,
                    obligation,
                    format!(
                        "cannot bind trust-wp native replay to the canonical public-obligation semantics: {reason}"
                    ),
                );
            }
        };
        let metadata =
            match trust_wp_native_replay_metadata_entries_from_trust_ir_bundle_with_claim_digest(
                native_bundle,
                request,
                proof_obligation_id,
                Some(ArtifactHash { algorithm: "sha256".to_string(), value: claim_digest }),
            ) {
                Ok(metadata) => metadata,
                Err(error) => {
                    return self.native_trust_ir_bundle_unsupported_evidence(
                        bundle,
                        obligation,
                        error.to_string(),
                    );
                }
            };

        native_obligation.metadata.extend(metadata);
        native_bundle_view.obligations = vec![native_obligation.clone()];

        // Wide-int-tolerant canonical encode (never panics, never spuriously
        // fail-closes). A trust_ir function body that carries a u128/i128
        // constant outside serde_json's i64/u64 number range — e.g. the
        // `i128::MIN`/`i128::MAX` type-range literals in `range_i128` /
        // `range_usize` / `small_rat` / `random_problem` — makes a plain
        // `serde_json::to_value(function)` fail with "number out of range"
        // (serde_json's `Value` cannot represent such an integer). The former
        // code turned that into a fail-closed "not JSON-serializable for pure
        // replay" for the WHOLE obligation, even though the CLAIM itself (proved
        // over the typed predicate + summary facts, never over these function
        // bodies) is fully dischargeable. `canonical_digest_json_value` keeps the
        // fast path BYTE-IDENTICAL to `to_value` for every representable value
        // and only falls back for out-of-range integers, encoding them as the
        // injective, deterministic, LOSSLESS tag
        // `{"$trust.digest.i128"|"$trust.digest.u128": "<exact-decimal>"}`. The
        // pure-replay transport carries these functions as opaque digest-faithful
        // JSON — trust-wp-core's native verifier never decodes them numerically
        // (the proof is over `obligation.claim` + summary facts), so the tagged
        // form is a faithful, injective carrier and cannot alter any verdict. A
        // GENUINELY non-serializable function (non-string map key, an erroring
        // `Serialize` impl) still returns `Err` and still fails closed.
        let mut trust_ir_functions: Vec<serde_json::Value> =
            Vec::with_capacity(native_bundle.module.functions.len());
        for function in &native_bundle.module.functions {
            match trust_types::canonical_digest_json_value(function) {
                Ok(value) => trust_ir_functions.push(value),
                Err(error) => {
                    return self.native_trust_ir_bundle_unsupported_evidence(
                        bundle,
                        obligation,
                        format!(
                            "native TrustIr function `{}` is not JSON-serializable for pure replay (fail-closed): {error}",
                            function.name
                        ),
                    );
                }
            }
        }

        let mut evidence = self.verify_one_with_claim(
            &native_bundle_view,
            &native_obligation,
            &claim,
            Some(trust_ir_functions),
        );
        // `EvidencePublicationMetadata::evidence_bundle_hash` is a run-level
        // identity: every evidence row aggregated into one verifier run must
        // name the same bundle.  The trust-wp proof object still carries its
        // per-obligation digest in the checked artifacts, while this outer
        // publication field binds every row produced from this immutable native
        // carrier to the carrier's common cryptographic digest.  Using the
        // per-obligation replay digest here made any function with two clauses
        // look like a splice of conflicting evidence bundles.
        if evidence.status == EvidenceStatus::Proved
            && evidence.publication.evidence_bundle_hash.is_some()
        {
            evidence.publication.evidence_bundle_hash =
                Some(native_bundle.stable_digest().to_string());
        }
        evidence.diagnostics.push(format!(
            "trust-wp native TrustIr bundle request consumed: request_id={} proof_obligation_id={}",
            request.id.index(),
            proof_obligation_id.index()
        ));
        evidence
    }

    fn unsupported_evidence(
        &self,
        _bundle: &TrustContractBundle,
        obligation: &TrustObligation,
    ) -> ObligationEvidence {
        let mut diagnostics = Vec::new();
        if is_trust_wp_owned_obligation_kind(&obligation.kind) {
            diagnostics.push(trust_wp_owned_fail_closed_diagnostic(&obligation.kind));
        } else {
            diagnostics.push(format!(
                "trust-wp native pure replay owns precondition/postcondition/loop-invariant/refinement/termination obligations, not {:?}",
                obligation.kind
            ));
        }
        diagnostics.push(
            format!(
                "TrustContractBundle lowering into TrustWpPureExprV1 claims plus replayable {} and {} artifacts is required before trust_wp evidence can be Proved",
                TRUST_WP_NATIVE_PURE_REPLAY_REQUIRED_ARTIFACTS[0],
                TRUST_WP_NATIVE_PURE_REPLAY_REQUIRED_ARTIFACTS[1],
            ),
        );
        diagnostics.push(trust_wp_omitted_proof_strength_diagnostic());
        diagnostics.push(
            "symbolic, opaque, or unlowered predicates remain fail-closed until trust_wp can decode and replay them under the native proof-evidence schema"
                .to_string(),
        );
        diagnostics.push(
            "each refinement, termination, and non-contract obligation remains fail-closed until dedicated native trust_wp replay evidence is supplied"
                .to_string(),
        );
        diagnostics.push(
            "contract attributes, metadata, summaries, inferred facts, solver success, and CLI availability are audit inputs only; this adapter never shells out or treats their presence as proof evidence"
                .to_string(),
        );

        ObligationEvidence {
            evidence_id: format!("trust-wp:unsupported:{}", obligation.obligation_id),
            obligation_id: obligation.obligation_id.clone(),
            engine: self.manifest.clone(),
            status: EvidenceStatus::Unsupported,
            proof_strength: None,
            artifacts: Vec::new(),
            counterexample: None::<Counterexample>,
            publication: EvidencePublicationMetadata::default(),
            diagnostics,
        }
    }

    fn verify_one(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
    ) -> ObligationEvidence {
        if let Some(candidate) = self
            .native_replay_evidence
            .iter()
            .find(|evidence| evidence.obligation_id == obligation.obligation_id)
        {
            return match self.validate_native_replay_evidence(bundle, obligation, candidate) {
                Ok(()) => candidate.clone(),
                Err(diagnostic) => {
                    let mut rejected = self.unsupported_evidence(bundle, obligation);
                    rejected.evidence_id =
                        format!("trust-wp:rejected:{}", obligation.obligation_id);
                    rejected.diagnostics.insert(0, diagnostic);
                    rejected.diagnostics.push(format!(
                        "candidate evidence {} was rejected and not treated as a trusted formula or proof",
                        candidate.evidence_id
                    ));
                    rejected
                }
            };
        }

        match self.lower_contract_obligation(bundle, obligation) {
            Ok(evidence) => evidence,
            Err(NativeContractLoweringOutcome::Failed { diagnostic, counterexample }) => {
                self.failed_native_contract_evidence(obligation, diagnostic, counterexample)
            }
            Err(NativeContractLoweringOutcome::Unsupported { diagnostic }) => {
                let mut unsupported = self.unsupported_evidence(bundle, obligation);
                unsupported.diagnostics.insert(0, diagnostic);
                unsupported
            }
        }
    }

    #[cfg_attr(not(feature = "trust-build"), allow(dead_code))]
    fn verify_one_with_claim(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        claim: &NativeTrustWpClaim,
        trust_ir_functions: Option<Vec<serde_json::Value>>,
    ) -> ObligationEvidence {
        // Symmetric decode of the wide-int digest tagging applied when the
        // pure-replay transport was built (see
        // `verify_obligation_with_native_trust_ir_request`). This is the exact
        // inverse of the encode: any representable value round-trips to the very
        // bytes a plain `serde_json::to_value` would have produced, and a
        // genuinely out-of-range magnitude is preserved LOSSLESSLY as its tagged
        // carrier (serde_json cannot hold it as a number). Applying it here keeps
        // replay faithful for any consumer that reads back the transported
        // functions, and can never fabricate a value — it only removes a tag the
        // encode itself introduced.
        let trust_ir_functions = trust_ir_functions.map(|functions| {
            functions.into_iter().map(restore_wide_int_digest_tagged_value).collect()
        });
        match self.lower_typed_claim_obligation(bundle, obligation, claim, trust_ir_functions) {
            Ok(evidence) => evidence,
            Err(NativeContractLoweringOutcome::Failed { diagnostic, counterexample }) => {
                self.failed_native_contract_evidence(obligation, diagnostic, counterexample)
            }
            Err(NativeContractLoweringOutcome::Unsupported { diagnostic }) => {
                let mut unsupported = self.unsupported_evidence(bundle, obligation);
                unsupported.diagnostics.insert(0, diagnostic);
                unsupported
            }
        }
    }

    fn lower_contract_obligation(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
    ) -> Result<ObligationEvidence, NativeContractLoweringOutcome> {
        let contract = contract_for_obligation(bundle, obligation)
            .map_err(|diagnostic| NativeContractLoweringOutcome::Unsupported { diagnostic })?;
        validate_contract_route_eligibility(obligation, Some(contract.kind))
            .map_err(|diagnostic| NativeContractLoweringOutcome::Unsupported { diagnostic })?;
        let claim = typed_trust_wp_claim(bundle, obligation)
            .map_err(|diagnostic| NativeContractLoweringOutcome::Unsupported { diagnostic })?;
        self.lower_typed_claim_obligation(bundle, obligation, &claim, None)
    }

    // `trust_ir_functions` is consumed by direct_trust_wp_native_evidence under
    // `feature = "trust-build"` (line ~454 below). Without that feature
    // the param is genuinely unused, so silence the lint conditionally
    // rather than underscoring the name (which would force callers to
    // know about the feature flag).
    #[cfg_attr(not(feature = "trust-build"), allow(unused_variables))]
    fn lower_typed_claim_obligation(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        claim: &NativeTrustWpClaim,
        trust_ir_functions: Option<Vec<serde_json::Value>>,
    ) -> Result<ObligationEvidence, NativeContractLoweringOutcome> {
        validate_contract_route_eligibility(obligation, None)
            .map_err(|diagnostic| NativeContractLoweringOutcome::Unsupported { diagnostic })?;
        summary_facts_for_obligation(bundle, obligation)
            .map_err(|diagnostic| NativeContractLoweringOutcome::Unsupported { diagnostic })?;
        #[cfg(feature = "trust-build")]
        {
            direct_trust_wp_native_evidence(
                &self.manifest,
                bundle,
                obligation,
                claim,
                trust_ir_functions,
            )
        }

        #[cfg(not(feature = "trust-build"))]
        {
            let NativeTrustWpClaim::TrustWpPureExprV1(predicate) = claim else {
                return Err(NativeContractLoweringOutcome::Unsupported {
                    diagnostic: format!(
                        "typed `{}` payload for obligation `{}` requires trust-wp's in-process NativeTrustWpBundleVerifier; this build is fail-closed without `trust-build`",
                        claim.claim_schema(),
                        obligation.obligation_id,
                    ),
                });
            };
            let replay = match replay_typed_predicate_for_evidence(predicate) {
                Ok(replay) => replay,
                Err(NativeReplayFailure::False { diagnostic }) => {
                    return Err(NativeContractLoweringOutcome::Failed {
                        diagnostic,
                        counterexample: Some(native_replay_counterexample(obligation, predicate)),
                    });
                }
                Err(NativeReplayFailure::Unknown { diagnostic }) => {
                    return Err(NativeContractLoweringOutcome::Unsupported { diagnostic });
                }
            };

            Err(NativeContractLoweringOutcome::Unsupported {
                diagnostic: aggregate_gate_missing_diagnostic(obligation, &replay),
            })
        }
    }

    fn failed_native_contract_evidence(
        &self,
        obligation: &TrustObligation,
        diagnostic: String,
        counterexample: Option<Counterexample>,
    ) -> ObligationEvidence {
        ObligationEvidence {
            evidence_id: format!("trust-wp:failed:{}", obligation.obligation_id),
            obligation_id: obligation.obligation_id.clone(),
            engine: self.manifest.clone(),
            status: EvidenceStatus::Failed,
            proof_strength: None,
            artifacts: Vec::new(),
            counterexample,
            publication: EvidencePublicationMetadata::default(),
            diagnostics: vec![
                diagnostic,
                "native trust_wp contract lowering reached a typed trust_wp predicate, but replay did not prove it; proof strength is intentionally omitted".to_string(),
            ],
        }
    }

    fn validate_native_replay_evidence(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        evidence: &ObligationEvidence,
    ) -> Result<(), String> {
        if !is_trust_wp_owned_obligation_kind(&obligation.kind) {
            return Err(format!(
                "trust-wp native replay does not own {:?} obligations",
                obligation.kind
            ));
        }
        if evidence.engine.name != self.manifest.name {
            return Err(format!(
                "candidate evidence engine `{}` is not trust-wp-owned evidence",
                evidence.engine.name
            ));
        }
        if evidence.status != EvidenceStatus::Proved {
            return Err(format!(
                "candidate trust_wp evidence is diagnostic-only: status {:?} is not Proved",
                evidence.status
            ));
        }
        if evidence.proof_strength.as_ref() != Some(&ProofStrength::deductive()) {
            return Err(format!(
                "candidate trust_wp evidence must carry deductive proof strength after checked native replay, got {:?}",
                evidence.proof_strength
            ));
        }
        if evidence.publication.evidence_bundle_hash.as_ref().is_none_or(String::is_empty) {
            return Err(
                "candidate trust_wp evidence is missing proof evidence digest metadata".to_string()
            );
        }
        let summary_facts = summary_facts_for_obligation(bundle, obligation)?;

        let predicate = typed_trust_wp_pure_predicate(bundle, obligation)?;
        let replay = replay_typed_predicate(&predicate)?;
        let expected = expected_native_replay_metadata(bundle, obligation, &replay, &summary_facts);
        if evidence.evidence_id != expected.evidence_id {
            return Err(
                "candidate trust_wp evidence id does not match deterministic typed replay metadata"
                    .to_string(),
            );
        }
        if evidence.artifacts != expected.artifacts {
            return Err(native_replay_artifact_mismatch_detail(
                &expected.artifacts,
                &evidence.artifacts,
            ));
        }
        if evidence.publication.evidence_bundle_hash != Some(expected.evidence_bundle_hash.clone())
        {
            return Err(
                "candidate trust_wp evidence bundle hash does not match deterministic typed replay metadata"
                    .to_string(),
            );
        }

        validate_aggregate_native_replay_gate(evidence)?;

        Ok(())
    }
}

#[cfg(feature = "trust-build")]
fn strip_trust_wp_native_metadata_from_bundle(bundle: &TrustContractBundle) -> TrustContractBundle {
    let mut stripped = bundle.clone();
    stripped.metadata.retain(|entry| !is_trust_wp_native_metadata_key(&entry.key));
    for contract in &mut stripped.contracts {
        contract.metadata.retain(|entry| !is_trust_wp_native_metadata_key(&entry.key));
    }
    for proof_item in &mut stripped.proof_items {
        proof_item.metadata.retain(|entry| !is_trust_wp_native_metadata_key(&entry.key));
        for contract in &mut proof_item.contracts {
            contract.metadata.retain(|entry| !is_trust_wp_native_metadata_key(&entry.key));
        }
    }
    for obligation in &mut stripped.obligations {
        obligation.metadata.retain(|entry| !is_trust_wp_native_metadata_key(&entry.key));
    }
    stripped
}

#[cfg(feature = "trust-build")]
fn strip_trust_wp_native_metadata_from_obligation(obligation: &TrustObligation) -> TrustObligation {
    let mut stripped = obligation.clone();
    stripped.metadata.retain(|entry| !is_trust_wp_native_metadata_key(&entry.key));
    stripped
}

#[cfg(feature = "trust-build")]
fn is_trust_wp_native_metadata_key(key: &str) -> bool {
    matches!(
        key,
        TRUST_TRUST_WP_NATIVE_ORIGIN_METADATA_KEY
            | TRUST_TRUST_WP_CLAIM_DIGEST_METADATA_KEY
            | TRUST_TRUST_WP_TRUST_IR_SOURCE_SPAN_METADATA_KEY
            | TRUST_TRUST_WP_NATIVE_VERIFIER_METADATA_KEY
            | TRUST_TRUST_WP_NATIVE_REPLAY_METADATA_KEY
            | TRUST_TRUST_WP_NATIVE_SOLVER_METADATA_KEY
            | TRUST_TRUST_WP_TRUST_IR_OBLIGATION_SOURCE_METADATA_KEY
            | TRUST_TRUST_WP_PROOF_CONTEXT_METADATA_KEY
            | TRUST_TRUST_WP_NATIVE_SUMMARY_FACT_METADATA_KEY
    )
}

#[cfg_attr(all(feature = "trust-build", not(trust_wp_proof_transport_api)), allow(dead_code))]
enum NativeContractLoweringOutcome {
    Failed { diagnostic: String, counterexample: Option<Counterexample> },
    Unsupported { diagnostic: String },
}

enum NativeReplayFailure {
    False { diagnostic: String },
    Unknown { diagnostic: String },
}

fn trust_wp_support_for_obligation_kind(kind: &ObligationKind) -> SupportLevel {
    if !is_trust_wp_owned_obligation_kind(kind) {
        return SupportLevel::Unsupported {
            reason: format!(
                "trust-wp native pure replay owns precondition/postcondition/loop-invariant/refinement/termination obligations, not {kind:?}"
            ),
        };
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    {
        if is_auto_lowered_contract_obligation_kind(kind) {
            SupportLevel::Supported
        } else {
            SupportLevel::Experimental {
                reason: format!(
                    "trust-wp owns {kind:?} obligations, but direct TrustContractBundle lowering currently covers precondition, postcondition, and loop-invariant typed pure obligations"
                ),
            }
        }
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        not(trust_wp_structured_context_api)
    ))]
    {
        SupportLevel::Experimental {
            reason: stale_trust_wp_structured_context_diagnostic_for_kind(kind),
        }
    }

    #[cfg(all(feature = "trust-build", not(trust_wp_proof_transport_api)))]
    {
        SupportLevel::Experimental {
            reason: stale_trust_wp_transport_api_diagnostic_for_kind(kind),
        }
    }

    #[cfg(not(feature = "trust-build"))]
    {
        SupportLevel::Experimental {
            reason: TRUST_WP_AGGREGATE_NATIVE_REPLAY_GATE_NOT_WIRED.to_string(),
        }
    }
}

#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    not(trust_wp_structured_context_api)
))]
fn stale_trust_wp_structured_context_diagnostic_for_kind(kind: &ObligationKind) -> String {
    format!(
        "{TRUST_WP_STRUCTURED_CONTEXT_API_MISSING}; trust_wp owns {kind:?} obligations only when `first-party/trust-wp` exposes typed TrustIr source, native verifier/replay/solver, proof-context, and abstract-interpretation summary fact metadata that are committed into `{TRUST_WP_PROOF_EVIDENCE_SCHEMA_VERSION}` / `{TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION}` artifacts"
    )
}

#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    not(trust_wp_structured_context_api)
))]
fn stale_trust_wp_structured_context_diagnostic(obligation: &TrustObligation) -> String {
    format!(
        "{TRUST_WP_STRUCTURED_CONTEXT_API_MISSING} for obligation `{}`; refresh `first-party/trust-wp` before reporting deductive proof strength from native trust_wp evidence",
        obligation.obligation_id
    )
}

#[cfg(all(feature = "trust-build", not(trust_wp_proof_transport_api)))]
fn stale_trust_wp_transport_api_diagnostic_for_kind(kind: &ObligationKind) -> String {
    format!(
        "{TRUST_WP_PROOF_TRANSPORT_API_MISSING}; trust_wp owns {kind:?} obligations only when `first-party/trust-wp` exposes digest-checked proof transport artifacts for request, native replay, summary, and aggregate manifest evidence under `{TRUST_WP_PROOF_EVIDENCE_SCHEMA_VERSION}` / `{TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION}`"
    )
}

#[cfg(all(feature = "trust-build", not(trust_wp_proof_transport_api)))]
fn stale_trust_wp_transport_api_diagnostic(obligation: &TrustObligation) -> String {
    format!(
        "{TRUST_WP_PROOF_TRANSPORT_API_MISSING} for obligation `{}`; refresh `first-party/trust-wp` to a trust_wp revision with `EvidenceArtifact::has_transport` and inline artifact bytes before reporting deductive proof strength",
        obligation.obligation_id
    )
}

fn trust_wp_owned_fail_closed_diagnostic(kind: &ObligationKind) -> String {
    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    {
        format!(
            "trust-wp owns {kind:?} obligations only after they are lowered to TrustWpPureExprV1 and replayed through trust_wp VerifyBundleResult aggregation from `{TRUST_WP_AGGREGATE_NATIVE_REPLAY_GATE_COMMIT}` with proof-grade `{TRUST_WP_PROOF_EVIDENCE_SCHEMA_VERSION}` / `{TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION}` evidence; direct committed trust_wp replay is enabled for precondition/postcondition/loop-invariant typed pure obligations"
        )
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        not(trust_wp_structured_context_api)
    ))]
    {
        stale_trust_wp_structured_context_diagnostic_for_kind(kind)
    }

    #[cfg(all(feature = "trust-build", not(trust_wp_proof_transport_api)))]
    {
        stale_trust_wp_transport_api_diagnostic_for_kind(kind)
    }

    #[cfg(not(feature = "trust-build"))]
    {
        format!(
            "{TRUST_WP_AGGREGATE_NATIVE_REPLAY_GATE_NOT_WIRED}; trust_wp owns {kind:?} obligations only after they are lowered to TrustWpPureExprV1 and replayed through trust_wp VerifyBundleResult aggregation from `{TRUST_WP_AGGREGATE_NATIVE_REPLAY_GATE_COMMIT}` with proof-grade `{TRUST_WP_PROOF_EVIDENCE_SCHEMA_VERSION}` / `{TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION}` evidence"
        )
    }
}

fn trust_wp_omitted_proof_strength_diagnostic() -> String {
    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    {
        "proof_strength is intentionally omitted unless trust-wp's direct aggregate native replay evidence gate returns proof-grade evidence"
            .to_string()
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        not(trust_wp_structured_context_api)
    ))]
    {
        format!(
            "proof_strength is intentionally omitted because {TRUST_WP_STRUCTURED_CONTEXT_API_MISSING}"
        )
    }

    #[cfg(all(feature = "trust-build", not(trust_wp_proof_transport_api)))]
    {
        format!(
            "proof_strength is intentionally omitted because {TRUST_WP_PROOF_TRANSPORT_API_MISSING}"
        )
    }

    #[cfg(not(feature = "trust-build"))]
    {
        "proof_strength is intentionally omitted because Trust has not run the checked trust_wp aggregate native replay evidence gate"
            .to_string()
    }
}

impl Default for TrustWpVerificationEngine {
    fn default() -> Self {
        Self::new()
    }
}

impl VerificationEngine for TrustWpVerificationEngine {
    fn manifest(&self) -> &EngineManifest {
        &self.manifest
    }

    fn supports(&self, obligation: &TrustObligation) -> SupportLevel {
        if is_trust_wp_owned_obligation_kind(&obligation.kind) {
            trust_wp_support_for_obligation_kind(&obligation.kind)
        } else {
            SupportLevel::Unsupported {
                reason: format!(
                    "trust-wp native pure replay owns precondition/postcondition/loop-invariant/refinement/termination obligations, not {:?}",
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
        let mut evidence = obligations
            .iter()
            .map(|obligation| self.verify_one(bundle, obligation))
            .collect::<Vec<_>>();
        bind_trust_wp_evidence_batch_publication(&mut evidence);
        evidence
    }
}

/// Replace individually authenticated trust-wp replay hashes with one
/// deterministic batch identity before the public verifier API aggregates the
/// rows.  Each leaf hash remains represented by the batch preimage and by the
/// row's checked artifacts; conflicting unauthenticated candidates cannot reach
/// this point because `verify_one` validates them first.
fn bind_trust_wp_evidence_batch_publication(evidence: &mut [ObligationEvidence]) {
    let mut leaves = evidence
        .iter()
        .filter_map(|item| {
            item.publication
                .evidence_bundle_hash
                .as_deref()
                .map(|hash| (item.obligation_id.as_str(), item.evidence_id.as_str(), hash))
        })
        .collect::<Vec<_>>();
    if leaves.len() < 2 {
        return;
    }
    leaves.sort_unstable();
    if leaves.windows(2).all(|pair| pair[0].2 == pair[1].2) {
        return;
    }

    let mut material =
        format!("schema=trust-wp.evidence-publication-batch.v1\nleaf-count={}\n", leaves.len());
    for (obligation_id, evidence_id, hash) in leaves {
        let _ = writeln!(
            material,
            "obligation={}:{} evidence={}:{} leaf={}:{}",
            obligation_id.len(),
            obligation_id,
            evidence_id.len(),
            evidence_id,
            hash.len(),
            hash,
        );
    }
    let digest = stable_digest(&material);
    let batch_hash = format!("{}:{}", digest.algorithm, digest.value);
    for item in evidence {
        if item.publication.evidence_bundle_hash.is_some() {
            item.publication.evidence_bundle_hash = Some(batch_hash.clone());
        }
    }
}

/// Build typed `trust.trust_wp.*` replay metadata for a trust_wp request inside a
/// TrustIr native verification bundle.
///
/// This is the compiler/router bridge for trust_wp native evidence. It converts
/// TrustIr request provenance, compiler source facts, and replay context into
/// trust-wp's controlled native replay metadata helper instead of constructing
/// proof-relevant JSON strings by hand.
#[cfg(feature = "trust-build")]
pub fn trust_wp_native_replay_metadata_entries_from_trust_ir_bundle(
    native_bundle: &trust_ir::NativeVerificationBundle,
    request: &trust_ir::TrustWpNativeRequest,
    proof_obligation_id: trust_ir::ProofId,
) -> Result<Vec<trust_verifier_api::MetadataEntry>, crate::error::TrustWpLibError> {
    trust_wp_native_replay_metadata_entries_from_trust_ir_bundle_with_claim_digest(
        native_bundle,
        request,
        proof_obligation_id,
        None,
    )
}

#[cfg(feature = "trust-build")]
fn trust_wp_native_replay_metadata_entries_from_trust_ir_bundle_with_claim_digest(
    native_bundle: &trust_ir::NativeVerificationBundle,
    request: &trust_ir::TrustWpNativeRequest,
    proof_obligation_id: trust_ir::ProofId,
    canonical_public_claim_digest: Option<ArtifactHash>,
) -> Result<Vec<trust_verifier_api::MetadataEntry>, crate::error::TrustWpLibError> {
    #[cfg(all(
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api,
        trust_wp_typed_metadata_helper_api
    ))]
    {
        let input = trust_wp_native_replay_metadata_input_from_trust_ir(
            native_bundle,
            request,
            proof_obligation_id,
            canonical_public_claim_digest,
        )?;
        input
            .to_metadata_entries()
            .map(|entries| {
                entries
                    .into_iter()
                    .map(|entry| trust_verifier_api::MetadataEntry {
                        key: entry.key,
                        value: entry.value,
                    })
                    .collect()
            })
            .map_err(|error| crate::error::TrustWpLibError::ContractError {
                reason: format!("failed to serialize trust_wp native TrustIr metadata: {error}"),
            })
    }

    #[cfg(not(all(
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api,
        trust_wp_typed_metadata_helper_api
    )))]
    {
        let _ = (native_bundle, request, proof_obligation_id, canonical_public_claim_digest);
        Err(crate::error::TrustWpLibError::ContractError {
            reason: "vendored trust_wp does not expose the typed native replay metadata helper API"
                .to_string(),
        })
    }
}

#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    trust_wp_structured_context_api,
    trust_wp_typed_metadata_helper_api
))]
fn trust_wp_native_replay_metadata_input_from_trust_ir(
    native_bundle: &trust_ir::NativeVerificationBundle,
    request: &trust_ir::TrustWpNativeRequest,
    proof_obligation_id: trust_ir::ProofId,
    canonical_public_claim_digest: Option<ArtifactHash>,
) -> Result<
    trust_wp_core::verify_bundle::TrustWpNativeReplayEvidenceInput,
    crate::error::TrustWpLibError,
> {
    use trust_wp_core::verify_bundle::{
        BundleDigest, BundleNativeOrigin, BundleNativeReplayIdentity, BundleNativeVerificationMode,
        BundleTmirSourceSpan, TrustWpNativeReplayEvidenceInput,
    };

    if !request.obligations.contains(&proof_obligation_id) {
        return Err(crate::error::TrustWpLibError::ContractError {
            reason: format!(
                "trust-wp request {} does not contain TrustIr proof obligation {}",
                request.id.index(),
                proof_obligation_id.index()
            ),
        });
    }

    let source = native_bundle.obligation_source(proof_obligation_id).ok_or_else(|| {
        crate::error::TrustWpLibError::ContractError {
            reason: format!(
                "trust-wp proof obligation {} is missing typed TrustIr obligation-source metadata",
                proof_obligation_id.index()
            ),
        }
    })?;
    let span = source.span.ok_or_else(|| crate::error::TrustWpLibError::ContractError {
        reason: format!(
            "trust-wp proof obligation {} is missing typed TrustIr source-span metadata",
            proof_obligation_id.index()
        ),
    })?;
    let replay = request.provenance.replay.as_ref().ok_or_else(|| {
        crate::error::TrustWpLibError::ContractError {
            reason: format!("trust-wp request {} is missing replay identity", request.id.index()),
        }
    })?;
    let transcript_digest =
        replay.transcript_digest.ok_or_else(|| crate::error::TrustWpLibError::ContractError {
            reason: format!(
                "trust-wp request {} is missing replay transcript digest",
                request.id.index()
            ),
        })?;
    if request.provenance.solvers.is_empty() {
        return Err(crate::error::TrustWpLibError::ContractError {
            reason: format!(
                "trust-wp request {} is missing native solver identity",
                request.id.index()
            ),
        });
    }

    let native_origin = BundleNativeOrigin::new(
        // Wire-format schema label: trust-wp-core's strict native-origin
        // validation (placeholder solver rejection, proof-context atom
        // binding checks, lineage/digest requirements) is gated on the
        // canonical `tmir.native-verification-bundle.` prefix. Emitting any
        // other spelling silently disables those fail-closed checks.
        format!("tmir.native-verification-bundle.v{}", native_bundle.schema_version),
        match request.mode {
            trust_ir::TrustWpVerificationMode::WeakestPrecondition => {
                BundleNativeVerificationMode::WeakestPrecondition
            }
            trust_ir::TrustWpVerificationMode::StrongestPostcondition => {
                BundleNativeVerificationMode::StrongestPostcondition
            }
            trust_ir::TrustWpVerificationMode::Abduction => BundleNativeVerificationMode::Abduction,
        },
        request.id.index(),
        request.function.index(),
        proof_obligation_id.index(),
    )
    .with_lineage_roots(request.lineage_roots.iter().map(|root| root.index()))
    .with_tmir_module_digest(trust_wp_digest(native_bundle.trust_ir_module_digest));

    let native_verifier = trust_wp_tool_identity(&request.provenance.expected_verifier);
    let native_replay = BundleNativeReplayIdentity::new(
        replay.engine.clone(),
        replay.invocation.clone(),
        trust_wp_digest(transcript_digest),
    );
    let native_solvers =
        request.provenance.solvers.iter().map(trust_wp_tool_identity).collect::<Vec<_>>();
    let tmir_obligation_source = trust_wp_obligation_source(native_bundle, source);
    let proof_context =
        trust_wp_proof_context(&request.provenance.replay_context, proof_obligation_id).map_err(
            |reason| crate::error::TrustWpLibError::ContractError {
                reason: format!(
                    "trust-wp request {} contains an ineligible proof-context claim: {reason}",
                    request.id.index()
                ),
            },
        )?;
    let mut input = TrustWpNativeReplayEvidenceInput::new(
        native_origin,
        BundleTmirSourceSpan::new(span.file, span.line, span.col),
        native_verifier,
        native_replay,
        native_solvers,
        tmir_obligation_source,
    )
    .with_proof_context(proof_context);
    if let Some(digest) = canonical_public_claim_digest {
        input = input.with_claim_digest(BundleDigest::new(digest.algorithm, digest.value));
    }
    Ok(input)
}

#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    trust_wp_structured_context_api,
    trust_wp_typed_metadata_helper_api
))]
fn trust_wp_tool_identity(
    tool: &trust_ir::NativeToolIdentity,
) -> trust_wp_core::verify_bundle::BundleNativeToolIdentity {
    let mut identity =
        trust_wp_core::verify_bundle::BundleNativeToolIdentity::new(tool.name.clone());
    if let Some(version) = &tool.version {
        identity = identity.with_version(version.clone());
    }
    if let Some(revision) = &tool.revision {
        identity = identity.with_revision(revision.clone());
    }
    if let Some(digest) = tool.digest {
        identity = identity.with_digest(trust_wp_digest(digest));
    }
    identity
}

#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    trust_wp_structured_context_api,
    trust_wp_typed_metadata_helper_api
))]
fn trust_wp_obligation_source(
    native_bundle: &trust_ir::NativeVerificationBundle,
    source: &trust_ir::NativeObligationSource,
) -> trust_wp_core::verify_bundle::BundleTmirObligationSource {
    use trust_wp_core::verify_bundle::{
        BundleTmirCompilerFactRef, BundleTmirObligationCause, BundleTmirObligationSource,
    };

    let mut converted = BundleTmirObligationSource::new(match source.cause {
        trust_ir::NativeObligationCause::Precondition => BundleTmirObligationCause::Precondition,
        trust_ir::NativeObligationCause::Postcondition => BundleTmirObligationCause::Postcondition,
        trust_ir::NativeObligationCause::Assert => BundleTmirObligationCause::Assert,
        trust_ir::NativeObligationCause::BoundsCheck => BundleTmirObligationCause::BoundsCheck,
        trust_ir::NativeObligationCause::OverflowCheck => BundleTmirObligationCause::OverflowCheck,
        trust_ir::NativeObligationCause::LayoutCheck => BundleTmirObligationCause::LayoutCheck,
        trust_ir::NativeObligationCause::CastCheck => BundleTmirObligationCause::CastCheck,
        trust_ir::NativeObligationCause::BorrowCheck => BundleTmirObligationCause::BorrowCheck,
        trust_ir::NativeObligationCause::Translation => BundleTmirObligationCause::Translation,
        trust_ir::NativeObligationCause::Panic => BundleTmirObligationCause::Panic,
        trust_ir::NativeObligationCause::PointerOffset => {
            BundleTmirObligationCause::Other("pointer_offset".to_string())
        }
        trust_ir::NativeObligationCause::Other => {
            BundleTmirObligationCause::Other("other".to_string())
        }
        trust_ir::NativeObligationCause::Temporal => BundleTmirObligationCause::Temporal,
    });
    if let Some(function) = source.function {
        converted = converted.with_function_id(function.index());
    }
    if let Some(assertion_id) = source.assertion_id {
        converted = converted.with_assertion_id(assertion_id.index());
    }
    if let Some(monomorphization) = source.monomorphization {
        converted = converted.with_monomorphization_id(monomorphization.index());
    }
    converted.with_compiler_fact_refs(source.facts.iter().map(|fact| {
        let mut converted = match fact {
            trust_ir::NativeCompilerFactRef::AdtLayout(id) => {
                BundleTmirCompilerFactRef::adt_layout(id.index())
            }
            trust_ir::NativeCompilerFactRef::FatPointer(id) => {
                BundleTmirCompilerFactRef::fat_pointer(id.index())
            }
            trust_ir::NativeCompilerFactRef::Cast(id) => {
                BundleTmirCompilerFactRef::cast(id.index())
            }
            trust_ir::NativeCompilerFactRef::Monomorphization(id) => {
                BundleTmirCompilerFactRef::monomorphization(id.index())
            }
            trust_ir::NativeCompilerFactRef::TraitObjectMetadata(id) => {
                BundleTmirCompilerFactRef::other("trait_object_metadata", id.index())
            }
            trust_ir::NativeCompilerFactRef::PointerOffset(id) => {
                BundleTmirCompilerFactRef::other("pointer_offset", id.index())
            }
        };
        if let Some(digest) = native_compiler_fact_digest(native_bundle, fact) {
            converted = converted.with_digest(trust_wp_digest(digest));
        }
        converted
    }))
}

#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    trust_wp_structured_context_api,
    trust_wp_typed_metadata_helper_api
))]
fn native_compiler_fact_digest(
    native_bundle: &trust_ir::NativeVerificationBundle,
    fact: &trust_ir::NativeCompilerFactRef,
) -> Option<trust_ir::ProofDigest> {
    match fact {
        trust_ir::NativeCompilerFactRef::Monomorphization(id) => native_bundle
            .compiler_facts
            .monomorphizations
            .iter()
            .find(|fact| fact.id == *id)
            .map(|fact| fact.stable_digest),
        trust_ir::NativeCompilerFactRef::AdtLayout(_)
        | trust_ir::NativeCompilerFactRef::FatPointer(_)
        | trust_ir::NativeCompilerFactRef::TraitObjectMetadata(_)
        | trust_ir::NativeCompilerFactRef::PointerOffset(_)
        | trust_ir::NativeCompilerFactRef::Cast(_) => None,
    }
}

#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    trust_wp_structured_context_api,
    trust_wp_typed_metadata_helper_api
))]
fn trust_wp_proof_context(
    context: &trust_ir::NativeReplayContext,
    proof_obligation_id: trust_ir::ProofId,
) -> Result<trust_wp_core::verify_bundle::BundleProofContext, String> {
    use trust_wp_core::verify_bundle::{BundleProofAtomRole, BundleProofContext};

    let mut assumptions = Vec::new();
    let mut assertions = Vec::new();

    let mut next_index = 0;
    for atom in context.atoms.iter().filter(|atom| {
        atom.obligation == Some(proof_obligation_id)
            && atom.kind == trust_ir::NativeReplayAtomKind::Assumption
    }) {
        assumptions.push(trust_wp_proof_atom(atom, next_index, BundleProofAtomRole::Assumption)?);
        next_index += 1;
    }
    for atom in context.atoms.iter().filter(|atom| {
        atom.obligation == Some(proof_obligation_id)
            && atom.kind == trust_ir::NativeReplayAtomKind::Assertion
    }) {
        assertions.push(trust_wp_proof_atom(atom, next_index, BundleProofAtomRole::Assertion)?);
        next_index += 1;
    }
    Ok(BundleProofContext::new(assumptions, assertions))
}

#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    trust_wp_structured_context_api,
    trust_wp_typed_metadata_helper_api
))]
fn trust_wp_proof_atom(
    atom: &trust_ir::NativeReplayAtom,
    index: u32,
    role: trust_wp_core::verify_bundle::BundleProofAtomRole,
) -> Result<trust_wp_core::verify_bundle::BundleProofAtom, String> {
    let mut converted = trust_wp_core::verify_bundle::BundleProofAtom::new(
        index,
        role,
        trust_wp_claim(&atom.formula)?,
    )
    .with_native_replay_atom_id(atom.id.index());
    if let Some(obligation) = atom.obligation {
        converted = converted.with_native_obligation_id(obligation.index());
    }
    if let Some(assertion_id) = atom.assertion_id {
        converted = converted.with_native_assertion_id(assertion_id.index());
    }
    if let Some(span) = atom.span {
        converted = converted.with_native_span(
            trust_wp_core::verify_bundle::BundleTmirSourceSpan::new(span.file, span.line, span.col),
        );
    }
    Ok(converted)
}

#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    trust_wp_structured_context_api,
    trust_wp_typed_metadata_helper_api
))]
fn trust_wp_claim(
    formula: &trust_ir::ProofFormula,
) -> Result<trust_wp_core::verify_bundle::BundleClaim, String> {
    use trust_wp_core::verify_bundle::{BundleClaim, BundleClaimFormat};

    match formula.schema.as_str() {
        "TrustWpPureExprV1"
        | TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION
        | TRUST_TYPES_FORMULA_SCHEMA_VERSION => {
            // Proof-context assumptions are proof inputs too. Decode them
            // through the same choke point as the target claim so arithmetic
            // cannot be smuggled into a sibling request via metadata.
            let claim = typed_trust_wp_claim_from_trust_ir_formula(formula)?;
            let (format, payload) = match claim {
                NativeTrustWpClaim::TrustWpPureExprV1(predicate) => {
                    (BundleClaimFormat::TrustWpPureExprV1, predicate.stable_text())
                }
                NativeTrustWpClaim::TrustFormulaV1(payload) => {
                    (BundleClaimFormat::TrustFormulaV1, payload)
                }
            };
            Ok(BundleClaim::new(format, payload))
        }
        "smtlib2" => Ok(BundleClaim::new(
            BundleClaimFormat::SmtLib2,
            formula.smtlib.as_ref().unwrap_or(&formula.payload).clone(),
        )),
        other => Ok(BundleClaim::new(
            BundleClaimFormat::Other(other.to_string()),
            formula.payload.clone(),
        )),
    }
}

#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    trust_wp_structured_context_api,
    trust_wp_typed_metadata_helper_api
))]
fn trust_wp_digest(digest: trust_ir::ProofDigest) -> trust_wp_core::verify_bundle::BundleDigest {
    trust_wp_core::verify_bundle::BundleDigest::new(
        digest.algorithm.to_string(),
        hex_digest(&digest.bytes),
    )
}

#[cfg(feature = "trust-build")]
fn hex_digest(bytes: &[u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(64);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

/// Minimal typed trust_wp pure-expression payload accepted by this adapter.
///
/// This is not a source-expression parser. Callers must pass a typed JSON value
/// under the `TrustWpPureExprV1` schema.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
pub(crate) enum TrustWpPureExprV1 {
    /// Boolean literal.
    Bool { value: bool },
    /// Integer literal.
    Int { value: i64 },
    /// Unary boolean negation.
    Not { expr: Box<TrustWpPureExprV1> },
    /// Free variable with a declared sort (PHASE 1 of the contract-lowering
    /// plan): local constant-fold replay stays fail-closed (`eval_value` ->
    /// None); first-party replay proves variable-bearing claims via its
    /// assumption-projection rule over the parsed stable text.
    Var { name: String, sort: TrustWpPureSortV1 },
    /// Binary typed expression.
    Binary { op: TrustWpPureBinaryOpV1, lhs: Box<TrustWpPureExprV1>, rhs: Box<TrustWpPureExprV1> },
}

impl TrustWpPureExprV1 {
    fn sort(&self) -> Option<TrustWpPureSortV1> {
        match self {
            Self::Bool { .. } => Some(TrustWpPureSortV1::Bool),
            Self::Int { .. } => Some(TrustWpPureSortV1::Int),
            Self::Not { expr } => {
                (expr.sort()? == TrustWpPureSortV1::Bool).then_some(TrustWpPureSortV1::Bool)
            }
            Self::Var { sort, .. } => Some(*sort),
            Self::Binary { op, lhs, rhs } => match op {
                TrustWpPureBinaryOpV1::Add | TrustWpPureBinaryOpV1::Sub => {
                    (lhs.sort()? == TrustWpPureSortV1::Int && rhs.sort()? == TrustWpPureSortV1::Int)
                        .then_some(TrustWpPureSortV1::Int)
                }
                TrustWpPureBinaryOpV1::Eq | TrustWpPureBinaryOpV1::Ne => {
                    (lhs.sort()? == rhs.sort()?).then_some(TrustWpPureSortV1::Bool)
                }
                TrustWpPureBinaryOpV1::Lt
                | TrustWpPureBinaryOpV1::Le
                | TrustWpPureBinaryOpV1::Gt
                | TrustWpPureBinaryOpV1::Ge => (lhs.sort()? == TrustWpPureSortV1::Int
                    && rhs.sort()? == TrustWpPureSortV1::Int)
                    .then_some(TrustWpPureSortV1::Bool),
                TrustWpPureBinaryOpV1::And
                | TrustWpPureBinaryOpV1::Or
                | TrustWpPureBinaryOpV1::Implies => (lhs.sort()? == TrustWpPureSortV1::Bool
                    && rhs.sort()? == TrustWpPureSortV1::Bool)
                    .then_some(TrustWpPureSortV1::Bool),
            },
        }
    }

    fn stable_text(&self) -> String {
        match self {
            Self::Bool { value } => value.to_string(),
            Self::Int { value } => value.to_string(),
            Self::Not { expr } => format!("(! {})", expr.stable_text()),
            Self::Var { name, .. } => name.clone(),
            Self::Binary { op, lhs, rhs } => {
                // A bare `flag == ready` is parsed as Int equality because the
                // stable-text grammar has no declarations. Anchor both direct
                // Bool variables so the canonical text is idempotent and the
                // public JSON, module formula, and assertion formula decode to
                // the same typed AST.
                if matches!(op, TrustWpPureBinaryOpV1::Eq | TrustWpPureBinaryOpV1::Ne)
                    && let (
                        Self::Var { name: lhs, sort: TrustWpPureSortV1::Bool },
                        Self::Var { name: rhs, sort: TrustWpPureSortV1::Bool },
                    ) = (lhs.as_ref(), rhs.as_ref())
                {
                    return format!("(({lhs} == true) {} ({rhs} == true))", op.as_str());
                }
                format!("({} {} {})", lhs.stable_text(), op.as_str(), rhs.stable_text())
            }
        }
    }

    /// Final sibling-wire spelling. Unlike canonical `stable_text`, this makes
    /// Bool variable sorts explicit because trust-wp-core's text parser has no
    /// declarations and treats a bare name as Unknown. Keeping this separate
    /// preserves public/native diagnostic identity and prevents repeated
    /// serialization from expanding an already-canonical formula.
    #[cfg(feature = "trust-build")]
    fn native_replay_text(&self) -> String {
        match self {
            Self::Bool { value } => value.to_string(),
            Self::Int { value } => value.to_string(),
            Self::Not { expr } => format!("(! {})", expr.native_replay_text()),
            Self::Var { name, sort: TrustWpPureSortV1::Bool } => {
                format!("({name} == true)")
            }
            Self::Var { name, sort: TrustWpPureSortV1::Int } => name.clone(),
            Self::Binary {
                op: op @ (TrustWpPureBinaryOpV1::Eq | TrustWpPureBinaryOpV1::Ne),
                lhs,
                rhs,
            } if matches!(
                (lhs.as_ref(), rhs.as_ref()),
                (Self::Var { sort: TrustWpPureSortV1::Bool, .. }, Self::Bool { .. })
                    | (Self::Bool { .. }, Self::Var { sort: TrustWpPureSortV1::Bool, .. })
            ) =>
            {
                format!("({} {} {})", lhs.stable_text(), op.as_str(), rhs.stable_text())
            }
            Self::Binary { op, lhs, rhs } => format!(
                "({} {} {})",
                lhs.native_replay_text(),
                op.as_str(),
                rhs.native_replay_text()
            ),
        }
    }
}

/// Canonicalize the one typed shape whose sorts cannot be recovered from bare
/// stable text. This fold is deliberately structural and idempotent so it is
/// available at both default and `trust-build` JSON ingress without depending
/// on the feature-gated text parser.
fn canonicalize_trust_wp_pure_expr(expr: TrustWpPureExprV1) -> TrustWpPureExprV1 {
    match expr {
        TrustWpPureExprV1::Not { expr } => {
            TrustWpPureExprV1::Not { expr: Box::new(canonicalize_trust_wp_pure_expr(*expr)) }
        }
        TrustWpPureExprV1::Binary { op, lhs, rhs } => {
            let lhs = canonicalize_trust_wp_pure_expr(*lhs);
            let rhs = canonicalize_trust_wp_pure_expr(*rhs);
            if matches!(op, TrustWpPureBinaryOpV1::Eq | TrustWpPureBinaryOpV1::Ne)
                && matches!(
                    (&lhs, &rhs),
                    (
                        TrustWpPureExprV1::Var { sort: TrustWpPureSortV1::Bool, .. },
                        TrustWpPureExprV1::Var { sort: TrustWpPureSortV1::Bool, .. }
                    )
                )
            {
                let bool_identity = |expr| TrustWpPureExprV1::Binary {
                    op: TrustWpPureBinaryOpV1::Eq,
                    lhs: Box::new(expr),
                    rhs: Box::new(TrustWpPureExprV1::Bool { value: true }),
                };
                TrustWpPureExprV1::Binary {
                    op,
                    lhs: Box::new(bool_identity(lhs)),
                    rhs: Box::new(bool_identity(rhs)),
                }
            } else {
                TrustWpPureExprV1::Binary { op, lhs: Box::new(lhs), rhs: Box::new(rhs) }
            }
        }
        leaf => leaf,
    }
}

/// Binary operators supported by the first native replay adapter fragment.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum TrustWpPureBinaryOpV1 {
    And,
    Or,
    Implies,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Add,
    Sub,
}

impl TrustWpPureBinaryOpV1 {
    fn as_str(self) -> &'static str {
        match self {
            Self::And => "&&",
            Self::Or => "||",
            // "==>" — the spelling first-party contract_parser accepts, so a
            // stable-text round trip through parse_contract survives.
            Self::Implies => "==>",
            Self::Eq => "==",
            Self::Ne => "!=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
            Self::Add => "+",
            Self::Sub => "-",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum TrustWpPureSortV1 {
    Bool,
    Int,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TrustWpNativeReplay {
    normalized_predicate: String,
    steps: Vec<TrustWpNativeReplayStep>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum TrustWpNativeReplayStep {
    DecodeTrustWpPureExprV1,
    Normalize(String),
    ApplyRule(&'static str),
    Verified,
}

impl TrustWpNativeReplayStep {
    fn as_wire_line(&self) -> String {
        match self {
            Self::DecodeTrustWpPureExprV1 => "decode:TrustWpPureExprV1".to_string(),
            Self::Normalize(predicate) => format!("normalize:{predicate}"),
            Self::ApplyRule(rule) => format!("replay-rule:{rule}"),
            Self::Verified => "result:verified".to_string(),
        }
    }
}

enum ReplayTruth {
    True { rule: &'static str },
    False { rule: &'static str },
    Unknown { reason: String },
}

impl ReplayTruth {
    fn from_bool(value: bool, rule: &'static str) -> Self {
        if value { Self::True { rule } } else { Self::False { rule } }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum NativeTrustWpClaim {
    TrustWpPureExprV1(TrustWpPureExprV1),
    TrustFormulaV1(String),
}

impl NativeTrustWpClaim {
    #[cfg_attr(all(feature = "trust-build", not(trust_wp_proof_transport_api)), allow(dead_code))]
    fn claim_schema(&self) -> &'static str {
        match self {
            Self::TrustWpPureExprV1(_) => TRUST_WP_PURE_EXPR_SCHEMA_VERSION,
            Self::TrustFormulaV1(_) => TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
        }
    }

    /// Canonical, domain-separated diagnostic fingerprint shared by the
    /// public-contract and native-TrustIr views of this formula.
    ///
    /// This is deliberately computed only after both wire representations have
    /// been decoded into `NativeTrustWpClaim`: hashing their original JSON/text
    /// encodings would reject harmless representation differences while still
    /// leaving semantic canonicalization split across two parsers.
    /// This formula-only value is never used as proof authority. Controlled
    /// replay metadata uses `canonical_obligation_semantic_digest_sha256`,
    /// which also binds the public obligation and its full referenced context.
    #[cfg(feature = "trust-build")]
    fn diagnostic_digest(&self) -> Result<ArtifactHash, String> {
        use sha2::{Digest as _, Sha256};

        let (schema, payload) = match self {
            Self::TrustWpPureExprV1(predicate) => {
                (TRUST_WP_PURE_EXPR_SCHEMA_VERSION, predicate.stable_text())
            }
            Self::TrustFormulaV1(payload) => {
                (TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION, payload.clone())
            }
        };
        let schema_len = u64::try_from(schema.len())
            .map_err(|_| "trust-wp diagnostic claim schema length exceeds u64".to_string())?;
        let payload_len = u64::try_from(payload.len())
            .map_err(|_| "trust-wp diagnostic claim payload length exceeds u64".to_string())?;
        let mut material = Vec::new();
        material.extend_from_slice(b"trust-wp.public-native-claim.v1");
        material.extend_from_slice(&schema_len.to_be_bytes());
        material.extend_from_slice(schema.as_bytes());
        material.extend_from_slice(&payload_len.to_be_bytes());
        material.extend_from_slice(payload.as_bytes());
        let digest = Sha256::digest(&material);
        Ok(ArtifactHash { algorithm: "sha256".to_string(), value: format!("{digest:x}") })
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    fn counterexample_payload(&self) -> serde_json::Value {
        match self {
            Self::TrustWpPureExprV1(predicate) => serde_json::json!({
                "schema": TRUST_WP_PURE_EXPR_SCHEMA_VERSION,
                "predicate": predicate.stable_text(),
            }),
            Self::TrustFormulaV1(payload) => serde_json::json!({
                "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
                "payload": payload,
            }),
        }
    }
}

/// Symmetric inverse of the wide-int digest tagging that
/// `canonical_digest_json_value` applies when the pure-replay function transport
/// is built. Recursively restores a wide-int digest tag
/// `{"$trust.digest.i128"|"$trust.digest.u128": "<decimal>"}` back to a plain
/// JSON number WHENEVER the decimal is representable in serde_json's i64/u64
/// number range, and preserves a genuinely out-of-range magnitude as its
/// lossless tagged carrier (serde_json's `Value` cannot hold it as a number).
///
/// This is a FAITHFUL round trip: for every value a plain `serde_json::to_value`
/// could represent, decode∘encode is the identity on bytes; for the rest the
/// exact decimal magnitude is preserved with no precision loss. It can only undo
/// a tag the encode itself introduced, so it never fabricates or alters a value.
fn restore_wide_int_digest_tagged_value(value: serde_json::Value) -> serde_json::Value {
    use serde_json::Value;
    match value {
        Value::Array(items) => {
            Value::Array(items.into_iter().map(restore_wide_int_digest_tagged_value).collect())
        }
        Value::Object(map) => {
            // A wide-int digest tag is a single-key object whose sole key is the
            // reserved i128/u128 tag and whose value is the exact decimal text.
            if map.len() == 1 {
                for tag_key in [
                    trust_types::json_digest::WIDE_I128_DIGEST_TAG_KEY,
                    trust_types::json_digest::WIDE_U128_DIGEST_TAG_KEY,
                ] {
                    if let Some(Value::String(decimal)) = map.get(tag_key) {
                        if let Ok(as_i64) = decimal.parse::<i64>() {
                            return Value::Number(as_i64.into());
                        }
                        if let Ok(as_u64) = decimal.parse::<u64>() {
                            return Value::Number(as_u64.into());
                        }
                        // Out of serde_json number range: keep the lossless tag.
                        return Value::Object(map);
                    }
                }
            }
            Value::Object(
                map.into_iter()
                    .map(|(key, val)| (key, restore_wide_int_digest_tagged_value(val)))
                    .collect(),
            )
        }
        other => other,
    }
}

fn typed_trust_wp_claim(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<NativeTrustWpClaim, String> {
    let contract = contract_for_obligation(bundle, obligation)?;
    typed_trust_wp_claim_from_contract(contract)
}

fn contract_for_obligation<'a>(
    bundle: &'a TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<&'a TrustContract, String> {
    let Some(contract_id) = obligation.contract_id.as_ref() else {
        return Err(
            "trust-wp replay requires a contract-linked typed predicate payload".to_string()
        );
    };
    bundle.contracts.iter().find(|contract| &contract.contract_id == contract_id).ok_or_else(|| {
        format!(
            "trust-wp replay could not find contract `{contract_id}` for obligation `{}`",
            obligation.obligation_id
        )
    })
}

fn typed_trust_wp_claim_from_contract(
    contract: &TrustContract,
) -> Result<NativeTrustWpClaim, String> {
    match &contract.predicate {
        ContractPredicate::CanonicalJson { schema, value }
        | ContractPredicate::TrustIr { schema, value }
            if schema == TRUST_WP_PURE_EXPR_SCHEMA_VERSION =>
        {
            let predicate = serde_json::from_value::<TrustWpPureExprV1>(value.clone())
                .map_err(|err| format!("invalid typed TrustWpPureExprV1 predicate: {err}"))?;
            if predicate.sort() != Some(TrustWpPureSortV1::Bool) {
                return Err("typed TrustWpPureExprV1 predicate is not boolean".to_string());
            }
            // Trust (#29): this direct ContractPredicate JSON lane is distinct
            // from the TrustIr proof-formula decoder below. Without the same
            // recursive refusal it can serialize `(x + 1) > x` straight into
            // the sibling's unbounded-Int prover and obtain a false machine
            // proof at `u64::MAX`.
            trust_wp_pure_expr_reject_arithmetic(&predicate)?;
            Ok(NativeTrustWpClaim::TrustWpPureExprV1(canonicalize_trust_wp_pure_expr(predicate)))
        }
        ContractPredicate::CanonicalJson { schema, value }
        | ContractPredicate::TrustIr { schema, value }
            if schema == TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION =>
        {
            Ok(NativeTrustWpClaim::TrustFormulaV1(canonical_trust_formula_payload(value)?))
        }
        ContractPredicate::CanonicalJson { schema, value }
        | ContractPredicate::TrustIr { schema, value }
            if schema == TRUST_TYPES_FORMULA_SCHEMA_VERSION =>
        {
            Ok(NativeTrustWpClaim::TrustFormulaV1(
                trust_types_formula_value_to_trust_formula_payload(value)?,
            ))
        }
        ContractPredicate::CanonicalJson { schema, value }
        | ContractPredicate::TrustIr { schema, value }
            if schema == TRUST_SPEC_PREDICATE_SCHEMA_VERSION =>
        {
            let predicate = serde_json::from_value::<TrustSpecPredicate>(value.clone())
                .map_err(|err| format!("invalid typed TrustSpecPredicate payload: {err}"))?;
            Ok(NativeTrustWpClaim::TrustFormulaV1(trust_spec_predicate_to_trust_formula_payload(
                &predicate,
            )?))
        }
        ContractPredicate::TrustExpr { .. } => Err(
            "source TrustExpr strings are not trusted TrustWpPureExprV1 or TrustFormulaV1 formulas"
                .to_string(),
        ),
        ContractPredicate::Unsupported { reason } => Err(format!(
            "unsupported contract predicate cannot produce trust_wp proof evidence: {reason}"
        )),
        _ => Err(format!(
            "contract predicate is not typed `{TRUST_WP_PURE_EXPR_SCHEMA_VERSION}`, `{TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION}`, or `{TRUST_SPEC_PREDICATE_SCHEMA_VERSION}` replay input"
        )),
    }
}

fn validate_contract_route_eligibility(
    obligation: &TrustObligation,
    contract_kind: Option<ContractKind>,
) -> Result<(), String> {
    if !is_auto_lowered_contract_obligation_kind(&obligation.kind) {
        return Err(format!(
            "trust-wp typed routing is ineligible for {:?} obligation `{}`: currently eligible typed inputs are precondition, postcondition, and loop-invariant pure contract obligations; each refinement, termination, and non-contract obligation remains fail-closed until dedicated native trust_wp replay evidence is supplied",
            obligation.kind, obligation.obligation_id
        ));
    }

    if let Some(contract_kind) = contract_kind
        && !contract_kind_matches_obligation(contract_kind, &obligation.kind)
    {
        return Err(format!(
            "trust-wp typed routing rejected obligation `{}`: public obligation kind {:?} is not backed by matching contract kind {:?}",
            obligation.obligation_id, obligation.kind, contract_kind
        ));
    }

    Ok(())
}

fn contract_kind_matches_obligation(
    contract_kind: ContractKind,
    obligation_kind: &ObligationKind,
) -> bool {
    matches!(
        (contract_kind, obligation_kind),
        (ContractKind::Requires, ObligationKind::Precondition)
            | (ContractKind::Ensures, ObligationKind::Postcondition)
            | (ContractKind::LoopInvariant, ObligationKind::LoopInvariant)
            | (ContractKind::Invariant, ObligationKind::LoopInvariant)
    )
}

#[cfg(feature = "trust-build")]
fn native_trust_ir_typed_claim(
    native_bundle: &trust_ir::NativeVerificationBundle,
    proof_obligation_id: trust_ir::ProofId,
) -> Result<NativeTrustWpClaim, String> {
    let proof_obligation = native_bundle
        .module
        .proof_obligations
        .iter()
        .find(|obligation| obligation.id == proof_obligation_id)
        .ok_or_else(|| {
            format!(
                "trust-wp native TrustIr request references missing proof obligation {}",
                proof_obligation_id.index()
            )
        })?;
    let formula = proof_obligation.formula.as_ref().ok_or_else(|| {
        format!(
            "trust-wp native TrustIr proof obligation {} is missing a typed proof formula payload",
            proof_obligation_id.index()
        )
    })?;
    typed_trust_wp_claim_from_trust_ir_formula(formula).map_err(|reason| {
        format!(
            "trust-wp native TrustIr proof obligation {} has unsupported typed formula payload: {reason}",
            proof_obligation_id.index()
        )
    })
}

#[cfg(feature = "trust-build")]
fn native_trust_ir_claim_for_obligation(
    public_bundle: &TrustContractBundle,
    native_bundle: &trust_ir::NativeVerificationBundle,
    request: &trust_ir::TrustWpNativeRequest,
    proof_obligation_id: trust_ir::ProofId,
    public_obligation: &TrustObligation,
) -> Result<NativeTrustWpClaim, String> {
    let public_contract = contract_for_obligation(public_bundle, public_obligation)?;
    validate_contract_route_eligibility(public_obligation, Some(public_contract.kind))?;
    let public_claim = typed_trust_wp_claim_from_contract(public_contract).map_err(|reason| {
        format!(
            "trust-wp public contract for obligation `{}` is not an eligible canonical typed claim: {reason}",
            public_obligation.obligation_id
        )
    })?;
    let sanitized_public_bundle = strip_trust_wp_native_metadata_from_bundle(public_bundle);
    let sanitized_public_obligation =
        strip_trust_wp_native_metadata_from_obligation(public_obligation);
    sanitized_public_bundle
        .validate_requested_obligations(std::slice::from_ref(&sanitized_public_obligation))
        .map_err(|reason| {
            format!(
                "cannot bind trust-wp native claim to an exact canonical public-obligation record: {reason}"
            )
        })?;
    let canonical_public_digest = sanitized_public_bundle
        .canonical_obligation_semantic_digest_sha256(&sanitized_public_obligation)
        .map_err(|reason| {
            format!(
                "cannot bind trust-wp native claim to the canonical public-obligation semantics: {reason}"
            )
        })?;
    if !request.obligations.contains(&proof_obligation_id) {
        return Err(format!(
            "trust-wp native request {} does not bind TrustIr proof obligation {}",
            request.id.index(),
            proof_obligation_id.index()
        ));
    }
    let proof_obligation = native_bundle
        .module
        .proof_obligations
        .iter()
        .find(|obligation| obligation.id == proof_obligation_id)
        .ok_or_else(|| {
            format!(
                "trust-wp native TrustIr request references missing proof obligation {}",
                proof_obligation_id.index()
            )
        })?;
    let embedded_source = proof_obligation.source.as_ref().ok_or_else(|| {
        format!(
            "trust-wp native TrustIr proof obligation {} is missing its embedded typed source identity",
            proof_obligation_id.index()
        )
    })?;
    let embedded_public = embedded_source.public.as_ref().ok_or_else(|| {
        format!(
            "trust-wp native TrustIr proof obligation {} source is missing its atomic public-obligation identity",
            proof_obligation_id.index()
        )
    })?;
    if embedded_public.obligation_id != public_obligation.obligation_id {
        return Err(format!(
            "trust-wp native TrustIr embedded public obligation id mismatch for proof obligation {}: source binds {:?}, public verifier requested {:?}",
            proof_obligation_id.index(),
            embedded_public.obligation_id,
            public_obligation.obligation_id,
        ));
    }
    if embedded_public.semantic_digest.algorithm != trust_ir::ProofDigestAlgorithm::Sha256
        || hex_digest(&embedded_public.semantic_digest.bytes) != canonical_public_digest
    {
        return Err(format!(
            "trust-wp native TrustIr embedded public semantic digest mismatch for obligation `{}` and proof obligation {}: embedded={} canonical=sha256:{}",
            public_obligation.obligation_id,
            proof_obligation_id.index(),
            embedded_public.semantic_digest,
            canonical_public_digest,
        ));
    }

    let source = native_bundle.obligation_source(proof_obligation_id).ok_or_else(|| {
        format!(
            "trust-wp native TrustIr proof obligation {} is missing its typed compiler-fact source binding",
            proof_obligation_id.index()
        )
    })?;
    if source.public_obligation_id != embedded_public.obligation_id {
        return Err(format!(
            "trust-wp native TrustIr compiler-fact public obligation id mismatch for proof obligation {}: compiler facts bind {:?}, embedded source binds {:?}",
            proof_obligation_id.index(),
            source.public_obligation_id,
            embedded_public.obligation_id,
        ));
    }
    if source.function != proof_obligation.function {
        return Err(format!(
            "trust-wp native TrustIr compiler-fact function projection mismatch for proof obligation {}: compiler facts bind {:?}, embedded obligation binds {:?}",
            proof_obligation_id.index(),
            source.function,
            proof_obligation.function,
        ));
    }
    if source.function != Some(request.function) {
        return Err(format!(
            "trust-wp native TrustIr request {} function {} does not match proof obligation {} source function {:?}",
            request.id.index(),
            request.function.index(),
            proof_obligation_id.index(),
            source.function,
        ));
    }
    let embedded_span = embedded_source.range.map(|range| trust_ir::SourceSpan {
        file: range.file,
        line: range.start_line,
        col: range.start_col,
    });
    if source.span != embedded_span {
        return Err(format!(
            "trust-wp native TrustIr compiler-fact span projection mismatch for proof obligation {}: compiler facts bind {:?}, embedded source projects {:?}",
            proof_obligation_id.index(),
            source.span,
            embedded_span,
        ));
    }
    let embedded_assertion_id = trust_ir::NativeAssertionId::new(trust_types::stable_u32_id(
        embedded_source.assertion_id.as_bytes(),
    ));
    if source.assertion_id != Some(embedded_assertion_id) {
        return Err(format!(
            "trust-wp native TrustIr compiler-fact assertion projection mismatch for proof obligation {}: compiler facts bind {:?}, embedded assertion {:?} projects {}",
            proof_obligation_id.index(),
            source.assertion_id,
            embedded_source.assertion_id,
            embedded_assertion_id.index(),
        ));
    }
    let native_kind = trust_wp_public_obligation_kind_from_trust_ir(&proof_obligation.kind)
        .ok_or_else(|| {
            format!(
                "trust-wp typed routing is ineligible for TrustIr proof obligation {} kind {:?}: eligible native trust_wp inputs are precondition, postcondition, and loop-invariant typed formulas",
                proof_obligation_id.index(),
                proof_obligation.kind
            )
        })?;
    if native_kind != public_obligation.kind {
        return Err(format!(
            "trust-wp native TrustIr proof obligation {} kind {:?} does not match public obligation `{}` kind {:?}",
            proof_obligation_id.index(),
            proof_obligation.kind,
            public_obligation.obligation_id,
            public_obligation.kind
        ));
    }
    let embedded_cause = match proof_obligation.kind {
        trust_ir::ObligationKind::Precondition => trust_ir::NativeObligationCause::Precondition,
        trust_ir::ObligationKind::Postcondition => trust_ir::NativeObligationCause::Postcondition,
        trust_ir::ObligationKind::LoopInvariant => trust_ir::NativeObligationCause::Assert,
        _ => unreachable!("trust-wp kind eligibility was checked above"),
    };
    if source.cause != embedded_cause {
        return Err(format!(
            "trust-wp native TrustIr compiler-fact cause projection mismatch for proof obligation {}: compiler facts bind {:?}, obligation kind {:?} projects {:?}",
            proof_obligation_id.index(),
            source.cause,
            proof_obligation.kind,
            embedded_cause,
        ));
    }
    let native_claim = native_trust_ir_typed_claim(native_bundle, proof_obligation_id)?;
    if native_claim != public_claim {
        let public_digest = public_claim.diagnostic_digest()?;
        let native_digest = native_claim.diagnostic_digest()?;
        return Err(format!(
            "trust-wp public/native claim semantic mismatch for obligation `{}` and TrustIr proof obligation {}: public={}:{} native={}:{}",
            public_obligation.obligation_id,
            proof_obligation_id.index(),
            public_digest.algorithm,
            public_digest.value,
            native_digest.algorithm,
            native_digest.value,
        ));
    }

    let bound_assertions = request
        .provenance
        .replay_context
        .atoms
        .iter()
        .filter(|atom| {
            atom.kind == trust_ir::NativeReplayAtomKind::Assertion
                && atom.obligation == Some(proof_obligation_id)
        })
        .collect::<Vec<_>>();
    if bound_assertions.len() != 1 {
        return Err(format!(
            "trust-wp native request {} must contain exactly one assertion replay atom bound to TrustIr proof obligation {}; found {}",
            request.id.index(),
            proof_obligation_id.index(),
            bound_assertions.len(),
        ));
    }
    if bound_assertions[0].assertion_id != source.assertion_id
        || bound_assertions[0].span != source.span
    {
        return Err(format!(
            "trust-wp native request {} assertion replay atom {} does not exactly project proof obligation {} compiler-fact source: assertion {:?}/{:?}, span {:?}/{:?}",
            request.id.index(),
            bound_assertions[0].id.index(),
            proof_obligation_id.index(),
            bound_assertions[0].assertion_id,
            source.assertion_id,
            bound_assertions[0].span,
            source.span,
        ));
    }
    let replay_claim = typed_trust_wp_claim_from_trust_ir_formula(&bound_assertions[0].formula)
        .map_err(|reason| {
            format!(
                "trust-wp native request {} assertion replay atom {} has unsupported typed formula payload: {reason}",
                request.id.index(),
                bound_assertions[0].id.index(),
            )
        })?;
    if replay_claim != native_claim {
        let public_digest = public_claim.diagnostic_digest()?;
        let native_digest = native_claim.diagnostic_digest()?;
        let replay_digest = replay_claim.diagnostic_digest()?;
        return Err(format!(
            "trust-wp public/module/assertion replay claim semantic mismatch for obligation `{}` and TrustIr proof obligation {}: public={}:{} module={}:{} assertion={}:{}",
            public_obligation.obligation_id,
            proof_obligation_id.index(),
            public_digest.algorithm,
            public_digest.value,
            native_digest.algorithm,
            native_digest.value,
            replay_digest.algorithm,
            replay_digest.value,
        ));
    }

    // Definition-site `#[requires]` echo normalization (applied ONLY after the
    // public/native/module/assertion claims were proven byte-equal above, so the
    // three-way claim binding is preserved on the FAITHFUL predicate). A
    // contract-linked `Precondition` obligation is the function's OWN requires
    // (`ContractKind::Requires` is the only contract kind mapped to
    // `Precondition`; a CALL-SITE precondition VC carries NO contract id and never
    // reaches this contract-bound path — see the `callee` note in
    // `trust_wp_obligation_kind`). The definition site MAY ASSUME its own requires,
    // so its obligation is the reflexive echo `assume(P) ⊢ P`. trust-wp-core
    // discharges that echo only when the claim is the self-implication `P ==> P`
    // (its `assumption-projection` rule, reached via `vc_to_positive_goal`); a
    // BARE variable-bearing comparison such as `shift < 32` is — correctly —
    // unprovable standalone and fails closed as "symbolic or unsupported
    // operands". Normalize a variable-bearing def-site requires into that
    // replayable echo.
    //
    // SOUNDNESS: `P ==> P` is a tautology for ANY predicate `P`, so proving it can
    // ONLY discharge the trivial def-site echo — it never asserts that `P` holds
    // for callers (that is the separate, NON-contract-linked call-site VC, which
    // is never wrapped). Both sides are the IDENTICAL `P` (the `<` — and every
    // operand — is reproduced faithfully, never weakened), so
    // `assumption-projection`'s `left == right` holds by construction. Ground
    // (variable-free) requires are left untouched: they already constant-fold, and
    // wrapping them would needlessly perturb their canonical claim text.
    let native_claim = if public_obligation.kind == ObligationKind::Precondition {
        definition_site_requires_echo(native_claim)
    } else {
        native_claim
    };

    Ok(native_claim)
}

/// Rewrite a variable-bearing def-site `#[requires]` predicate `P` into the
/// reflexive echo `P ==> P` so trust-wp-core's `assumption-projection` rule can
/// discharge the "the body may assume its own precondition" obligation. See the
/// call site for the full soundness argument; in short, `P ==> P` is a tautology
/// and can only discharge the trivial echo, never a caller's proof burden.
///
/// Non-`TrustWpPureExprV1` claims and ground (variable-free) predicates pass
/// through unchanged.
#[cfg(feature = "trust-build")]
fn definition_site_requires_echo(claim: NativeTrustWpClaim) -> NativeTrustWpClaim {
    match claim {
        NativeTrustWpClaim::TrustWpPureExprV1(predicate)
            if trust_wp_pure_expr_contains_var(&predicate) =>
        {
            NativeTrustWpClaim::TrustWpPureExprV1(TrustWpPureExprV1::Binary {
                op: TrustWpPureBinaryOpV1::Implies,
                lhs: Box::new(predicate.clone()),
                rhs: Box::new(predicate),
            })
        }
        other => other,
    }
}

/// Whether a typed pure predicate mentions at least one free variable, i.e. is
/// not a fully ground (constant-foldable) expression.
#[cfg(feature = "trust-build")]
fn trust_wp_pure_expr_contains_var(expr: &TrustWpPureExprV1) -> bool {
    match expr {
        TrustWpPureExprV1::Var { .. } => true,
        TrustWpPureExprV1::Bool { .. } | TrustWpPureExprV1::Int { .. } => false,
        TrustWpPureExprV1::Not { expr } => trust_wp_pure_expr_contains_var(expr),
        TrustWpPureExprV1::Binary { lhs, rhs, .. } => {
            trust_wp_pure_expr_contains_var(lhs) || trust_wp_pure_expr_contains_var(rhs)
        }
    }
}

#[cfg(feature = "trust-build")]
fn trust_wp_public_obligation_kind_from_trust_ir(
    kind: &trust_ir::ObligationKind,
) -> Option<ObligationKind> {
    match kind {
        &trust_ir::ObligationKind::Precondition => Some(ObligationKind::Precondition),
        &trust_ir::ObligationKind::Postcondition => Some(ObligationKind::Postcondition),
        &trust_ir::ObligationKind::LoopInvariant => Some(ObligationKind::LoopInvariant),
        &trust_ir::ObligationKind::TypeInvariant
        | &trust_ir::ObligationKind::RefinementType
        | &trust_ir::ObligationKind::TranslationValidation
        | &trust_ir::ObligationKind::MemorySafety
        | &trust_ir::ObligationKind::PanicFreedom => None,
        &trust_ir::ObligationKind::TemporalSafety | &trust_ir::ObligationKind::Liveness => None,
        // ArithmeticSafety (overflow/div) and BoundsCheck (index OOB) are
        // panic-freedom obligations — like MemorySafety/PanicFreedom they map to no
        // distinct trust-wp public kind. `ObligationKind` is `#[non_exhaustive]`;
        // the wildcard keeps future kinds compiling (default: no trust-wp kind).
        &trust_ir::ObligationKind::ArithmeticSafety | &trust_ir::ObligationKind::BoundsCheck => {
            None
        }
        _ => None,
    }
}

#[cfg(feature = "trust-build")]
fn typed_trust_wp_claim_from_trust_ir_formula(
    formula: &trust_ir::ProofFormula,
) -> Result<NativeTrustWpClaim, String> {
    match formula.schema.as_str() {
        "TrustWpPureExprV1" => {
            let predicate = decode_trust_ir_trust_wp_pure_expr_payload(&formula.payload)?;
            if predicate.sort() != Some(TrustWpPureSortV1::Bool) {
                return Err("TrustWpPureExprV1 proof formula is not boolean".to_string());
            }
            Ok(NativeTrustWpClaim::TrustWpPureExprV1(predicate))
        }
        schema if schema == TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION => {
            trust_types::trust_formula_v1::parse_arithmetic_free_trust_formula_v1_payload(
                &formula.payload,
            )
            .map(NativeTrustWpClaim::TrustFormulaV1)
        }
        schema if schema == TRUST_TYPES_FORMULA_SCHEMA_VERSION => {
            if formula.payload.trim().is_empty() {
                return Err("trust-types.Formula@1 payload is empty".to_string());
            }
            let value = trust_types::trust_formula_v1::parse_unique_proof_json_payload(
                &formula.payload,
            )
            .map_err(|err| format!("invalid trust-types.Formula@1 JSON payload: {err}"))?;
            trust_types_formula_value_to_trust_formula_payload(&value)
                .map(NativeTrustWpClaim::TrustFormulaV1)
        }
        "smtlib2" => Err(
            "SMT-LIB2 text is not an eligible typed trust_wp TrustFormula/native contract bundle payload"
                .to_string(),
        ),
        other => Err(format!(
            "schema `{other}` is not `{TRUST_WP_PURE_EXPR_SCHEMA_VERSION}`, `{TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION}`, or `trust-types.Formula@1`"
        )),
    }
}

#[cfg(feature = "trust-build")]
fn decode_trust_ir_trust_wp_pure_expr_payload(payload: &str) -> Result<TrustWpPureExprV1, String> {
    match payload.trim() {
        "true" => return Ok(TrustWpPureExprV1::Bool { value: true }),
        "false" => return Ok(TrustWpPureExprV1::Bool { value: false }),
        _ => {}
    }

    if payload.trim_start().starts_with('{') {
        let value = trust_types::trust_formula_v1::parse_unique_proof_json_payload(payload)
            .map_err(|err| format!("invalid TrustWpPureExprV1 JSON payload: {err}"))?;
        let expr = serde_json::from_value::<TrustWpPureExprV1>(value)
            .map_err(|err| format!("invalid TrustWpPureExprV1 JSON payload: {err}"))?;
        // Trust (#29): the JSON-encoded sub-path can also carry Add/Sub
        // arithmetic; refuse it for the same amendment-1 reason as the
        // stable-text parser gate below, so no arithmetic bare-Int claim
        // reaches the sibling from either sub-path of this lane.
        trust_wp_pure_expr_reject_arithmetic(&expr)?;
        return Ok(canonicalize_trust_wp_pure_expr(expr));
    }
    // STABLE-TEXT fallback (contract-lowering PHASE 0): trust_ir ProofFormula
    // payloads for contract predicates are the stable text the compiler emits
    // (e.g. "(lo <= hi)") because first-party trust-wp-lib builds its
    // proof-context atoms by parse_contract over that same payload. Parse the
    // pure int/bool fragment; anything outside it fails closed.
    trust_types::trust_formula_v1::reject_trust_wp_pure_expr_v1_text_arithmetic(payload)?;
    parse_pure_expr_text(payload).map_err(|err| {
        format!("payload is neither TrustWpPureExprV1 JSON nor pure stable text: {err}")
    })
}

/// Trust (#29): amendment-1 arithmetic refusal for the bare trust-wp
/// stable-text / JSON `TrustWpPureExprV1` claim lane. Machine-integer
/// predicates lowered as unbounded-Int arithmetic are a confirmed false-proof
/// vector: the sibling's linear-int rule proves free-variable Int tautologies
/// such as `x + 1 > x`, which is FALSE at `u64::MAX` under Rust's wrapping
/// machine semantics. Mirrors the compiler's bare-claim gate
/// (`rustc_mir_transform::trust_verify::trust_spec_expr_to_trust_formula_body`)
/// and the body-bound fragment
/// (`trust_ir_bridge::trust_wp_claim::spec_predicate_to_sibling_json`,
/// blueprint amendment 1).
fn trust_wp_pure_bare_claim_arithmetic_refusal(op: &str) -> String {
    format!(
        "TrustWpPureExprV1 arithmetic operator `{op}` is outside the trust-wp stable-text bare-claim fragment: machine arithmetic modeled over unbounded Int is a false-proof vector (`x + 1 > x` is Int-provable but false at u64::MAX); see 2026-07-17 trust-wp lowering blueprint amendment 1"
    )
}

/// Trust (#29): reject any `Add`/`Sub` arithmetic anywhere in a decoded
/// `TrustWpPureExprV1` so the JSON-deserialize sub-path of
/// `decode_trust_ir_trust_wp_pure_expr_payload` cannot bypass the stable-text
/// parser's arithmetic gate. (`*`/`/`/`%`/unary-neg have no `TrustWpPureExprV1`
/// representation, so `Add`/`Sub` are the only arithmetic operators this fold
/// can encounter.) Fail-closed for the same amendment-1 reason.
fn trust_wp_pure_expr_reject_arithmetic(expr: &TrustWpPureExprV1) -> Result<(), String> {
    fn visit(
        expr: &TrustWpPureExprV1,
        variable_sorts: &mut BTreeMap<String, TrustWpPureSortV1>,
    ) -> Result<(), String> {
        match expr {
            TrustWpPureExprV1::Bool { .. } | TrustWpPureExprV1::Int { .. } => Ok(()),
            TrustWpPureExprV1::Var { name, sort } => {
                if !trust_wp_pure_var_name_lexes_as_identifier(name) {
                    return Err(format!(
                        "TrustWpPureExprV1 variable name `{name}` is outside the unambiguous stable-text identifier fragment"
                    ));
                }
                if let Some(previous) = variable_sorts.insert(name.clone(), *sort)
                    && previous != *sort
                {
                    return Err(format!(
                        "TrustWpPureExprV1 variable `{name}` has conflicting sorts `{previous:?}` and `{sort:?}`; one untyped stable-text name cannot preserve both"
                    ));
                }
                Ok(())
            }
            TrustWpPureExprV1::Not { expr } => visit(expr, variable_sorts),
            TrustWpPureExprV1::Binary { op, lhs, rhs } => {
                let arithmetic = match op {
                    TrustWpPureBinaryOpV1::Add => Some("add"),
                    TrustWpPureBinaryOpV1::Sub => Some("sub"),
                    _ => None,
                };
                if let Some(label) = arithmetic {
                    return Err(trust_wp_pure_bare_claim_arithmetic_refusal(label));
                }
                visit(lhs, variable_sorts)?;
                visit(rhs, variable_sorts)
            }
        }
    }

    visit(expr, &mut BTreeMap::new())
}

/// Exact opaque base-identifier lexeme accepted by the downstream contract
/// parser, excluding all of its reserved keywords. Typed JSON variables are
/// emitted as stable text, so accepting any wider spelling can become postfix
/// syntax, token injection, or a parser keyword at replay time.
fn trust_wp_pure_var_name_lexes_as_identifier(name: &str) -> bool {
    trust_types::trust_formula_v1::trust_wp_pure_expr_v1_opaque_identifier(name)
}

/// Recursive-descent parser for the pure stable-text fragment, mirroring
/// first-party `contract_parser` precedence: `==>` (lowest, right-assoc), `||`,
/// `&&`, comparisons (`==` `!=` `<` `<=` `>` `>=`), additive (`+` `-`), unary
/// (`!` `-`), atoms (int literals, `true`/`false`, opaque ASCII identifiers,
/// parens). Identifier sorts are inferred from demand: boolean
/// context yields `Var{Bool}`, arithmetic/comparison context `Var{Int}`
/// (bare `v == w` defaults Int — the contract fragment's convention). FAIL
/// CLOSED on any token or shape outside the fragment.
#[cfg(feature = "trust-build")]
fn parse_pure_expr_text(text: &str) -> Result<TrustWpPureExprV1, String> {
    struct P<'a> {
        s: &'a [u8],
        i: usize,
    }
    type E = TrustWpPureExprV1;
    impl<'a> P<'a> {
        fn ws(&mut self) {
            while self.i < self.s.len() && (self.s[self.i] as char).is_ascii_whitespace() {
                self.i += 1;
            }
        }
        fn peek(&mut self) -> Option<u8> {
            self.ws();
            self.s.get(self.i).copied()
        }
        fn eat(&mut self, tok: &str) -> bool {
            self.ws();
            if self.s[self.i..].starts_with(tok.as_bytes()) {
                // Longest-match guard: don't eat "<" out of "<=", "=" out of "==>", etc.
                let next = self.s.get(self.i + tok.len()).copied();
                let ambiguous = matches!(tok, "<" | ">" | "=" | "!" | "&" | "|");
                if !(ambiguous && matches!(next, Some(b'=') | Some(b'>') | Some(b'&') | Some(b'|')))
                {
                    self.i += tok.len();
                    return true;
                }
            }
            false
        }
        fn implies(&mut self) -> Result<E, String> {
            let lhs = self.or()?;
            if self.eat("==>") {
                let rhs = self.implies()?; // right-assoc
                return Ok(E::Binary {
                    op: TrustWpPureBinaryOpV1::Implies,
                    lhs: Box::new(coerce_bool(lhs)?),
                    rhs: Box::new(coerce_bool(rhs)?),
                });
            }
            Ok(lhs)
        }
        fn or(&mut self) -> Result<E, String> {
            let mut lhs = self.and()?;
            while self.eat("||") {
                let rhs = self.and()?;
                lhs = E::Binary {
                    op: TrustWpPureBinaryOpV1::Or,
                    lhs: Box::new(coerce_bool(lhs)?),
                    rhs: Box::new(coerce_bool(rhs)?),
                };
            }
            Ok(lhs)
        }
        fn and(&mut self) -> Result<E, String> {
            let mut lhs = self.cmp()?;
            while self.eat("&&") {
                let rhs = self.cmp()?;
                lhs = E::Binary {
                    op: TrustWpPureBinaryOpV1::And,
                    lhs: Box::new(coerce_bool(lhs)?),
                    rhs: Box::new(coerce_bool(rhs)?),
                };
            }
            Ok(lhs)
        }
        fn cmp(&mut self) -> Result<E, String> {
            let lhs = self.add()?;
            for (tok, op) in [
                ("==>", TrustWpPureBinaryOpV1::Implies), // guard: never split here
                ("==", TrustWpPureBinaryOpV1::Eq),
                ("!=", TrustWpPureBinaryOpV1::Ne),
                ("<=", TrustWpPureBinaryOpV1::Le),
                (">=", TrustWpPureBinaryOpV1::Ge),
                ("<", TrustWpPureBinaryOpV1::Lt),
                (">", TrustWpPureBinaryOpV1::Gt),
            ] {
                if tok == "==>" {
                    // handled at the implies level; ensure we do not consume it
                    self.ws();
                    if self.s[self.i..].starts_with(b"==>") {
                        return Ok(lhs);
                    }
                    continue;
                }
                if self.eat(tok) {
                    let rhs = self.add()?;
                    let (l, r) =
                        if matches!(op, TrustWpPureBinaryOpV1::Eq | TrustWpPureBinaryOpV1::Ne)
                            && (lhs.sort() == Some(TrustWpPureSortV1::Bool)
                                || rhs.sort() == Some(TrustWpPureSortV1::Bool))
                        {
                            (coerce_bool(lhs)?, coerce_bool(rhs)?)
                        } else {
                            (coerce_int(lhs)?, coerce_int(rhs)?)
                        };
                    return Ok(E::Binary { op, lhs: Box::new(l), rhs: Box::new(r) });
                }
            }
            Ok(lhs)
        }
        fn add(&mut self) -> Result<E, String> {
            let lhs = self.unary()?;
            // Trust (#29, defense-in-depth): refuse additive machine arithmetic
            // in the bare trust-wp stable-text claim lane. `x + 1 > x` and
            // `x - 1 < x` are Int-provable but FALSE at u64::MAX / 0 under
            // Rust's wrapping semantics; the sibling's linear-int rule would
            // "verify" them as bare unbounded-Int claims. Mirrors the compiler
            // bare-claim gate and the body-bound fragment (blueprint amendment
            // 1). Fail-closed: the caller demotes to Unsupported. (`*`/`/` are
            // already outside this parser's grammar.)
            if self.eat("+") {
                return Err(trust_wp_pure_bare_claim_arithmetic_refusal("add"));
            }
            if self.eat("-") {
                return Err(trust_wp_pure_bare_claim_arithmetic_refusal("sub"));
            }
            Ok(lhs)
        }
        fn unary(&mut self) -> Result<E, String> {
            if self.eat("!") {
                let e = self.unary()?;
                return Ok(E::Not { expr: Box::new(coerce_bool(e)?) });
            }
            if self.peek() == Some(b'-') {
                // A leading `-` is either a negative integer literal (a
                // constant — kept) or unary minus over a sub-expression.
                let start = self.i;
                self.i += 1;
                if self.s.get(self.i).is_some_and(u8::is_ascii_digit) {
                    while self.s.get(self.i).is_some_and(|b| b.is_ascii_digit() || *b == b'_') {
                        self.i += 1;
                    }
                    let lit: String = std::str::from_utf8(&self.s[start..self.i])
                        .map_err(|_| "non-utf8 literal".to_string())?
                        .chars()
                        .filter(|c| *c != '_')
                        .collect();
                    return lit
                        .parse::<i64>()
                        .map(|value| E::Int { value })
                        .map_err(|_| format!("int literal out of i64 range: {lit}"));
                }
                let _ = self.unary()?;
                // Trust (#29): unary minus over a non-literal lowers to `0 - e`
                // (Sub) — machine arithmetic outside the amendment-1 fragment.
                // Refuse it for the same false-proof reason as binary `+`/`-`.
                return Err(trust_wp_pure_bare_claim_arithmetic_refusal("neg"));
            }
            self.atom()
        }
        fn atom(&mut self) -> Result<E, String> {
            match self.peek() {
                Some(b'(') => {
                    self.i += 1;
                    let e = self.implies()?;
                    self.ws();
                    if self.s.get(self.i) != Some(&b')') {
                        return Err("expected `)`".to_string());
                    }
                    self.i += 1;
                    Ok(e)
                }
                Some(c) if c.is_ascii_digit() => {
                    let start = self.i;
                    while self.s.get(self.i).is_some_and(|b| b.is_ascii_digit() || *b == b'_') {
                        self.i += 1;
                    }
                    let lit: String = std::str::from_utf8(&self.s[start..self.i])
                        .map_err(|_| "non-utf8 literal".to_string())?
                        .chars()
                        .filter(|c| *c != '_')
                        .collect();
                    lit.parse::<i64>()
                        .map(|value| E::Int { value })
                        .map_err(|_| format!("int literal out of i64 range: {lit}"))
                }
                Some(c) if c.is_ascii_alphabetic() || c == b'_' => {
                    let start = self.i;
                    while self
                        .s
                        .get(self.i)
                        .is_some_and(|b| b.is_ascii_alphanumeric() || *b == b'_')
                    {
                        self.i += 1;
                    }
                    let name = std::str::from_utf8(&self.s[start..self.i])
                        .map_err(|_| "non-utf8 identifier".to_string())?
                        .to_string();
                    match name.as_str() {
                        "true" => Ok(E::Bool { value: true }),
                        "false" => Ok(E::Bool { value: false }),
                        // Sort provisionally Int; boolean contexts re-coerce.
                        _ if trust_wp_pure_var_name_lexes_as_identifier(&name) => {
                            Ok(E::Var { name, sort: TrustWpPureSortV1::Int })
                        }
                        _ => Err(format!("reserved or non-opaque stable-text identifier `{name}`")),
                    }
                }
                other => Err(format!("unsupported token at byte {}: {other:?}", self.i)),
            }
        }
    }
    /// A bare identifier in boolean position becomes a Bool-sorted var; any
    /// other non-boolean expression fails closed.
    fn coerce_bool(e: TrustWpPureExprV1) -> Result<TrustWpPureExprV1, String> {
        match e {
            TrustWpPureExprV1::Var { name, .. } => {
                Ok(TrustWpPureExprV1::Var { name, sort: TrustWpPureSortV1::Bool })
            }
            other if other.sort() == Some(TrustWpPureSortV1::Bool) => Ok(other),
            other => Err(format!("expected boolean expression, got `{}`", other.stable_text())),
        }
    }
    fn coerce_int(e: TrustWpPureExprV1) -> Result<TrustWpPureExprV1, String> {
        match e {
            TrustWpPureExprV1::Var { name, .. } => {
                Ok(TrustWpPureExprV1::Var { name, sort: TrustWpPureSortV1::Int })
            }
            other if other.sort() == Some(TrustWpPureSortV1::Int) => Ok(other),
            other => Err(format!("expected integer expression, got `{}`", other.stable_text())),
        }
    }

    let mut p = P { s: text.as_bytes(), i: 0 };
    let expr = p.implies()?;
    p.ws();
    if p.i != p.s.len() {
        return Err(format!("trailing input at byte {}", p.i));
    }
    // The whole claim must be a boolean predicate.
    let expr = coerce_bool(expr)?;
    if expr.sort() != Some(TrustWpPureSortV1::Bool) {
        return Err("stable-text claim must be boolean-sorted".to_string());
    }
    trust_wp_pure_expr_reject_arithmetic(&expr)?;
    Ok(expr)
}

fn typed_trust_wp_pure_predicate(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<TrustWpPureExprV1, String> {
    match typed_trust_wp_claim(bundle, obligation)? {
        NativeTrustWpClaim::TrustWpPureExprV1(predicate) => Ok(predicate),
        NativeTrustWpClaim::TrustFormulaV1(_) => Err(format!(
            "candidate replay evidence validation for `{TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION}` requires trust_wp aggregate evidence, not local TrustWpPureExprV1 replay metadata"
        )),
    }
}

/// Lower a serde-serialized `trust_types::Formula` value (schema
/// `trust-types.Formula@1`) into the `trust_wp.trust-formula.v1` claim envelope
/// JSON that trust-wp's native replay decoder accepts.
///
/// Fail-closed: the conversion errors for any formula construct outside
/// trust-wp's native int/bool replay fragment (bitvectors, arrays, conditionals,
/// quantifiers, out-of-`i64` literals, non-int/bool variable sorts). Callers must
/// treat the error as Unsupported and never report a proof from an unlowered
/// predicate.
fn trust_types_formula_value_to_trust_formula_payload(
    value: &serde_json::Value,
) -> Result<String, String> {
    let formula = serde_json::from_value::<trust_types::Formula>(value.clone()).map_err(|err| {
        format!("invalid typed `{TRUST_TYPES_FORMULA_SCHEMA_VERSION}` Formula payload: {err}")
    })?;
    trust_types::trust_formula_v1::formula_to_trust_formula_v1_envelope(&formula)
}

fn canonical_trust_formula_payload(value: &serde_json::Value) -> Result<String, String> {
    trust_types::trust_formula_v1::canonical_arithmetic_free_trust_formula_v1_payload(value)
}

fn trust_spec_predicate_to_trust_formula_payload(
    predicate: &TrustSpecPredicate,
) -> Result<String, String> {
    if !predicate.has_current_schema() {
        return Err(format!(
            "unsupported TrustSpecPredicate schema `{}`, expected `{TRUST_SPEC_PREDICATE_SCHEMA_VERSION}`",
            predicate.schema_version
        ));
    }
    if predicate.root_sort != TrustSpecSort::Bool || predicate.root.sort != TrustSpecSort::Bool {
        return Err("TrustSpecPredicate root must be a typed boolean predicate".to_string());
    }
    predicate.validate()?;
    // TrustFormulaV1 is a scalar replay format. `TrustSpecSort::Array` is a
    // valid public specification sort, but it has no faithful representation in
    // this adapter and must fail closed before any scalar claim is serialized.
    if predicate
        .variables
        .iter()
        .any(|variable| matches!(variable.sort, TrustSpecSort::Array { .. }))
        || trust_spec_expr_mentions_array_sort(&predicate.root)
    {
        return Err(
            "TrustSpecPredicate array sort is outside trust_wp TrustFormulaV1 native int/bool replay fragment"
                .to_string(),
        );
    }
    // Float sorts are likewise valid public specification sorts with no
    // faithful representation here: replaying IEEE-754 comparisons (NaN is
    // unordered, +0.0 == -0.0) over the scalar int/bool fragment would give
    // the terms the wrong semantics, so they must fail closed before any
    // scalar claim is serialized.
    if predicate
        .variables
        .iter()
        .any(|variable| matches!(variable.sort, TrustSpecSort::Float { .. }))
        || trust_spec_expr_mentions_float_sort(&predicate.root)
    {
        return Err(
            "TrustSpecPredicate float sort is outside trust_wp TrustFormulaV1 native int/bool replay fragment"
                .to_string(),
        );
    }
    validate_trust_spec_div_mod_defined(&predicate.root)?;

    let mut result_sort = None;
    let body = trust_spec_expr_to_trust_formula_body(&predicate.root, &mut result_sort)?;
    let mut variables = Vec::with_capacity(predicate.variables.len());
    for variable in &predicate.variables {
        if variable.name.trim().is_empty() {
            return Err("TrustSpecPredicate variable name is empty".to_string());
        }
        variables.push(serde_json::json!({
            "name": variable.name,
            "sort": trust_spec_sort_label(variable.sort),
        }));
    }

    let mut payload = serde_json::Map::new();
    payload.insert("schema".to_string(), serde_json::json!(TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION));
    payload.insert("variables".to_string(), serde_json::Value::Array(variables));
    if let Some(sort) = result_sort {
        payload.insert(
            "result".to_string(),
            serde_json::json!({
                "name": "result",
                "sort": trust_spec_sort_label(sort),
            }),
        );
    }
    payload.insert("body".to_string(), body);

    canonical_trust_formula_payload(&serde_json::Value::Object(payload)).map_err(|err| {
        format!("could not canonicalize TrustSpecPredicate as TrustFormulaV1: {err}")
    })
}

fn trust_spec_expr_to_trust_formula_body(
    expr: &TrustSpecExpr,
    result_sort: &mut Option<TrustSpecSort>,
) -> Result<serde_json::Value, String> {
    match &expr.kind {
        TrustSpecExprKind::BoolLiteral { value } => {
            require_sort(expr, TrustSpecSort::Bool, "bool literal")?;
            Ok(serde_json::json!({ "bool": value }))
        }
        TrustSpecExprKind::IntLiteral { value } => {
            require_sort(expr, TrustSpecSort::Int, "int literal")?;
            let parsed = value.parse::<i64>().map_err(|err| {
                format!("TrustSpecPredicate integer literal `{value}` is outside i64: {err}")
            })?;
            Ok(serde_json::json!({ "int": parsed }))
        }
        TrustSpecExprKind::Variable { name } => {
            if name.trim().is_empty() {
                return Err("TrustSpecPredicate variable reference has an empty name".to_string());
            }
            Ok(serde_json::json!({ "var": name }))
        }
        TrustSpecExprKind::Result => {
            if let Some(existing) = result_sort {
                if *existing != expr.sort {
                    return Err("TrustSpecPredicate uses result with inconsistent sorts".to_string());
                }
            } else {
                *result_sort = Some(expr.sort);
            }
            Ok(serde_json::json!({ "result": true }))
        }
        TrustSpecExprKind::Unary { op, expr: inner } => {
            match op {
                TrustSpecUnaryOp::Not => {
                    require_sort(expr, TrustSpecSort::Bool, "not expression")?;
                    require_sort(inner, TrustSpecSort::Bool, "not operand")?;
                }
                // Trust (#29): `Neg` is arithmetic — refuse it in the
                // bare-claim lane for the same amendment-1 reason as the
                // binary arithmetic refusal below.
                TrustSpecUnaryOp::Neg => {
                    return Err(trust_spec_bare_claim_arithmetic_refusal("neg"));
                }
                _ => {
                    return Err(
                        "TrustSpecPredicate unary operator is outside trust_wp TrustFormulaV1 native int/bool replay fragment"
                            .to_string(),
                    );
                }
            }
            Ok(serde_json::json!({
                "op": trust_spec_unary_op_label(*op)?,
                "expr": trust_spec_expr_to_trust_formula_body(inner, result_sort)?,
            }))
        }
        TrustSpecExprKind::Binary { op, lhs, rhs } => {
            // Trust (#29, defense-in-depth): refuse machine arithmetic in the
            // BARE (non-body-bound) trust-wp claim lane, mirroring the
            // compiler's copy of this lowering
            // (rustc_mir_transform::trust_verify) and the body-bound bridge
            // fragment (`trust_ir_bridge::trust_wp_claim::
            // spec_predicate_to_sibling_json`, blueprint amendment 1).
            // Machine-integer predicates lowered as unbounded-Int arithmetic
            // are a confirmed false-proof vector: the sibling's linear-int
            // rule proves free-variable Int tautologies such as
            // `ensures result + 1 > result`, which is FALSE at `u64::MAX`
            // under Rust's wrapping machine semantics. Fail-closed: this
            // refusal surfaces as "is not an eligible canonical typed claim"
            // and the obligation demotes to Unsupported, never Proved.
            if matches!(
                op,
                TrustSpecBinaryOp::Add
                    | TrustSpecBinaryOp::Sub
                    | TrustSpecBinaryOp::Mul
                    | TrustSpecBinaryOp::Div
                    | TrustSpecBinaryOp::Mod
            ) {
                return Err(trust_spec_bare_claim_arithmetic_refusal(
                    trust_spec_binary_op_label(*op)?,
                ));
            }
            validate_trust_spec_binary(*op, expr, lhs, rhs)?;
            Ok(serde_json::json!({
                "op": trust_spec_binary_op_label(*op)?,
                "lhs": trust_spec_expr_to_trust_formula_body(lhs, result_sort)?,
                "rhs": trust_spec_expr_to_trust_formula_body(rhs, result_sort)?,
            }))
        }
        TrustSpecExprKind::Old { expr: inner } => Ok(serde_json::json!({
            "old": trust_spec_expr_to_trust_formula_body(inner, result_sort)?,
        })),
        TrustSpecExprKind::Field { .. }
        | TrustSpecExprKind::Index { .. }
        | TrustSpecExprKind::Quantifier { .. } => Err(
            "TrustSpecPredicate node is outside trust_wp TrustFormulaV1 native int/bool replay fragment"
                .to_string(),
        ),
        _ => Err(
            "TrustSpecPredicate future node is outside trust_wp TrustFormulaV1 native int/bool replay fragment"
                .to_string(),
        ),
    }
}

fn trust_spec_expr_mentions_array_sort(root: &TrustSpecExpr) -> bool {
    let mut pending = vec![root];
    while let Some(expr) = pending.pop() {
        if matches!(expr.sort, TrustSpecSort::Array { .. }) {
            return true;
        }
        match &expr.kind {
            TrustSpecExprKind::Unary { expr, .. }
            | TrustSpecExprKind::Old { expr }
            | TrustSpecExprKind::BvUnary { expr, .. }
            | TrustSpecExprKind::BvFromInt { expr, .. }
            | TrustSpecExprKind::IntFromBv { expr, .. } => pending.push(expr),
            TrustSpecExprKind::Binary { lhs, rhs, .. }
            | TrustSpecExprKind::BvBinary { lhs, rhs, .. } => {
                pending.push(lhs);
                pending.push(rhs);
            }
            TrustSpecExprKind::Field { base, .. } => pending.push(base),
            TrustSpecExprKind::Index { base, index } => {
                pending.push(base);
                pending.push(index);
            }
            TrustSpecExprKind::Quantifier { variable_sort, body, .. } => {
                if matches!(variable_sort, TrustSpecSort::Array { .. }) {
                    return true;
                }
                pending.push(body);
            }
            TrustSpecExprKind::IsVariant { scrutinee, .. }
            | TrustSpecExprKind::VariantField { scrutinee, .. } => pending.push(scrutinee),
            TrustSpecExprKind::BoolLiteral { .. }
            | TrustSpecExprKind::IntLiteral { .. }
            | TrustSpecExprKind::Variable { .. }
            | TrustSpecExprKind::Result
            | TrustSpecExprKind::BitVecLiteral { .. } => {}
            _ => {}
        }
    }
    false
}

fn trust_spec_expr_mentions_float_sort(root: &TrustSpecExpr) -> bool {
    let mut pending = vec![root];
    while let Some(expr) = pending.pop() {
        if matches!(expr.sort, TrustSpecSort::Float { .. }) {
            return true;
        }
        match &expr.kind {
            TrustSpecExprKind::Unary { expr, .. }
            | TrustSpecExprKind::Old { expr }
            | TrustSpecExprKind::BvUnary { expr, .. }
            | TrustSpecExprKind::BvFromInt { expr, .. }
            | TrustSpecExprKind::IntFromBv { expr, .. } => pending.push(expr),
            TrustSpecExprKind::Binary { lhs, rhs, .. }
            | TrustSpecExprKind::BvBinary { lhs, rhs, .. } => {
                pending.push(lhs);
                pending.push(rhs);
            }
            TrustSpecExprKind::Field { base, .. } => pending.push(base),
            TrustSpecExprKind::Index { base, index } => {
                pending.push(base);
                pending.push(index);
            }
            TrustSpecExprKind::Quantifier { variable_sort, body, .. } => {
                if matches!(variable_sort, TrustSpecSort::Float { .. }) {
                    return true;
                }
                pending.push(body);
            }
            TrustSpecExprKind::IsVariant { scrutinee, .. }
            | TrustSpecExprKind::VariantField { scrutinee, .. } => pending.push(scrutinee),
            TrustSpecExprKind::FloatLiteral { .. } => return true,
            TrustSpecExprKind::BoolLiteral { .. }
            | TrustSpecExprKind::IntLiteral { .. }
            | TrustSpecExprKind::Variable { .. }
            | TrustSpecExprKind::Result
            | TrustSpecExprKind::BitVecLiteral { .. } => {}
            _ => {}
        }
    }
    false
}

// Trust (#29): amendment-1 arithmetic refusal for the bare trust-wp claim
// lane. Kept as a single helper so the walker's unary (`Neg`) and binary
// (`Add`/`Sub`/`Mul`/`Div`/`Mod`) refusals stay message-identical with the
// compiler's copy of this lowering (rustc_mir_transform::trust_verify).
fn trust_spec_bare_claim_arithmetic_refusal(op: &str) -> String {
    format!(
        "TrustSpecPredicate arithmetic operator `{op}` is outside the trust-wp TrustFormulaV1 bare-claim fragment: machine arithmetic modeled over unbounded Int is a false-proof vector (`ensures result + 1 > result` is Int-provable but false at u64::MAX); see 2026-07-17 trust-wp lowering blueprint amendment 1"
    )
}

fn validate_trust_spec_div_mod_defined(expr: &TrustSpecExpr) -> Result<(), String> {
    validate_trust_spec_expr_div_mod_defined(expr, &[])
}

fn validate_trust_spec_expr_div_mod_defined(
    expr: &TrustSpecExpr,
    assumptions: &[TrustSpecExpr],
) -> Result<(), String> {
    match &expr.kind {
        TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::And, lhs, rhs } => {
            let mut scoped = assumptions.to_vec();
            collect_trust_spec_definedness_facts(expr, &mut scoped);
            validate_trust_spec_expr_div_mod_defined(lhs, &scoped)?;
            validate_trust_spec_expr_div_mod_defined(rhs, &scoped)
        }
        TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::Implies, lhs, rhs } => {
            let mut scoped = assumptions.to_vec();
            collect_trust_spec_definedness_facts(lhs, &mut scoped);
            validate_trust_spec_expr_div_mod_defined(lhs, &scoped)?;
            validate_trust_spec_expr_div_mod_defined(rhs, &scoped)
        }
        TrustSpecExprKind::Binary {
            op: op @ (TrustSpecBinaryOp::Div | TrustSpecBinaryOp::Mod),
            lhs,
            rhs,
        } => {
            validate_trust_spec_expr_div_mod_defined(lhs, assumptions)?;
            validate_trust_spec_expr_div_mod_defined(rhs, assumptions)?;
            if trust_spec_expr_known_nonzero(rhs, assumptions) {
                Ok(())
            } else {
                Err(format!(
                    "TrustSpecPredicate {:?} divisor must be syntactically nonzero or guarded by a nonzero assumption for trust_wp TrustFormulaV1 native replay",
                    op
                ))
            }
        }
        TrustSpecExprKind::Binary { lhs, rhs, .. } => {
            validate_trust_spec_expr_div_mod_defined(lhs, assumptions)?;
            validate_trust_spec_expr_div_mod_defined(rhs, assumptions)
        }
        TrustSpecExprKind::Unary { expr: inner, .. } | TrustSpecExprKind::Old { expr: inner } => {
            validate_trust_spec_expr_div_mod_defined(inner, assumptions)
        }
        TrustSpecExprKind::Field { base, .. } => {
            validate_trust_spec_expr_div_mod_defined(base, assumptions)
        }
        TrustSpecExprKind::Index { base, index } => {
            validate_trust_spec_expr_div_mod_defined(base, assumptions)?;
            validate_trust_spec_expr_div_mod_defined(index, assumptions)
        }
        TrustSpecExprKind::Quantifier { body, .. } => {
            validate_trust_spec_expr_div_mod_defined(body, assumptions)
        }
        TrustSpecExprKind::BoolLiteral { .. }
        | TrustSpecExprKind::IntLiteral { .. }
        | TrustSpecExprKind::Variable { .. }
        | TrustSpecExprKind::Result => Ok(()),
        _ => Ok(()),
    }
}

fn collect_trust_spec_definedness_facts(expr: &TrustSpecExpr, facts: &mut Vec<TrustSpecExpr>) {
    match &expr.kind {
        TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::And, lhs, rhs } => {
            collect_trust_spec_definedness_facts(lhs, facts);
            collect_trust_spec_definedness_facts(rhs, facts);
        }
        TrustSpecExprKind::Binary { op, .. }
            if trust_spec_is_definedness_fact_operator(*op)
                && !trust_spec_contains_div_mod(expr) =>
        {
            facts.push(expr.clone());
        }
        _ => {}
    }
}

fn trust_spec_is_definedness_fact_operator(op: TrustSpecBinaryOp) -> bool {
    matches!(
        op,
        TrustSpecBinaryOp::Eq
            | TrustSpecBinaryOp::Ne
            | TrustSpecBinaryOp::Lt
            | TrustSpecBinaryOp::Le
            | TrustSpecBinaryOp::Gt
            | TrustSpecBinaryOp::Ge
    )
}

fn trust_spec_expr_known_nonzero(expr: &TrustSpecExpr, assumptions: &[TrustSpecExpr]) -> bool {
    trust_spec_constant_int(expr).is_some_and(|value| value != 0)
        || assumptions
            .iter()
            .any(|assumption| trust_spec_assumption_proves_nonzero(assumption, expr))
}

fn trust_spec_assumption_proves_nonzero(
    assumption: &TrustSpecExpr,
    target: &TrustSpecExpr,
) -> bool {
    let TrustSpecExprKind::Binary { op, lhs, rhs } = &assumption.kind else {
        return false;
    };
    match op {
        TrustSpecBinaryOp::Ne => {
            (lhs.as_ref() == target && trust_spec_is_int_zero(rhs))
                || (rhs.as_ref() == target && trust_spec_is_int_zero(lhs))
        }
        TrustSpecBinaryOp::Gt | TrustSpecBinaryOp::Lt => {
            (lhs.as_ref() == target && trust_spec_is_int_zero(rhs))
                || (trust_spec_is_int_zero(lhs) && rhs.as_ref() == target)
        }
        _ => false,
    }
}

fn trust_spec_contains_div_mod(expr: &TrustSpecExpr) -> bool {
    match &expr.kind {
        TrustSpecExprKind::Binary {
            op: TrustSpecBinaryOp::Div | TrustSpecBinaryOp::Mod, ..
        } => true,
        TrustSpecExprKind::Binary { lhs, rhs, .. } => {
            trust_spec_contains_div_mod(lhs) || trust_spec_contains_div_mod(rhs)
        }
        TrustSpecExprKind::Unary { expr: inner, .. } | TrustSpecExprKind::Old { expr: inner } => {
            trust_spec_contains_div_mod(inner)
        }
        TrustSpecExprKind::Field { base, .. } => trust_spec_contains_div_mod(base),
        TrustSpecExprKind::Index { base, index } => {
            trust_spec_contains_div_mod(base) || trust_spec_contains_div_mod(index)
        }
        TrustSpecExprKind::Quantifier { body, .. } => trust_spec_contains_div_mod(body),
        TrustSpecExprKind::BoolLiteral { .. }
        | TrustSpecExprKind::IntLiteral { .. }
        | TrustSpecExprKind::Variable { .. }
        | TrustSpecExprKind::Result => false,
        _ => false,
    }
}

fn trust_spec_is_int_zero(expr: &TrustSpecExpr) -> bool {
    trust_spec_constant_int(expr) == Some(0)
}

fn trust_spec_constant_int(expr: &TrustSpecExpr) -> Option<i64> {
    match &expr.kind {
        TrustSpecExprKind::IntLiteral { value } => value.parse::<i64>().ok(),
        _ => None,
    }
}

fn require_sort(
    expr: &TrustSpecExpr,
    expected: TrustSpecSort,
    context: &str,
) -> Result<(), String> {
    if expr.sort == expected {
        Ok(())
    } else {
        Err(format!(
            "TrustSpecPredicate {context} has sort {:?}, expected {:?}",
            expr.sort, expected
        ))
    }
}

fn validate_trust_spec_binary(
    op: TrustSpecBinaryOp,
    expr: &TrustSpecExpr,
    lhs: &TrustSpecExpr,
    rhs: &TrustSpecExpr,
) -> Result<(), String> {
    require_sort(expr, op.result_sort(), "binary expression")?;
    match op {
        TrustSpecBinaryOp::Add
        | TrustSpecBinaryOp::Sub
        | TrustSpecBinaryOp::Mul
        | TrustSpecBinaryOp::Div
        | TrustSpecBinaryOp::Mod => {
            require_sort(lhs, TrustSpecSort::Int, "arithmetic lhs")?;
            require_sort(rhs, TrustSpecSort::Int, "arithmetic rhs")
        }
        TrustSpecBinaryOp::Eq | TrustSpecBinaryOp::Ne => {
            if lhs.sort == rhs.sort {
                require_sort(expr, TrustSpecSort::Bool, "comparison expression")
            } else {
                Err(format!(
                    "TrustSpecPredicate equality compares incompatible sorts {:?} and {:?}",
                    lhs.sort, rhs.sort
                ))
            }
        }
        TrustSpecBinaryOp::Lt
        | TrustSpecBinaryOp::Le
        | TrustSpecBinaryOp::Gt
        | TrustSpecBinaryOp::Ge => {
            require_sort(lhs, TrustSpecSort::Int, "comparison lhs")?;
            require_sort(rhs, TrustSpecSort::Int, "comparison rhs")?;
            require_sort(expr, TrustSpecSort::Bool, "comparison expression")
        }
        TrustSpecBinaryOp::And | TrustSpecBinaryOp::Or | TrustSpecBinaryOp::Implies => {
            require_sort(lhs, TrustSpecSort::Bool, "boolean lhs")?;
            require_sort(rhs, TrustSpecSort::Bool, "boolean rhs")?;
            require_sort(expr, TrustSpecSort::Bool, "boolean expression")
        }
        _ => Err(
            "TrustSpecPredicate future binary operator is outside trust_wp TrustFormulaV1 native int/bool replay fragment"
                .to_string(),
        ),
    }
}

fn trust_spec_sort_label(sort: TrustSpecSort) -> &'static str {
    match sort {
        TrustSpecSort::Bool => "bool",
        TrustSpecSort::Int => "int",
        TrustSpecSort::BitVec { .. } => "bit_vec",
        TrustSpecSort::Array { .. } => "array",
        // Unreachable in the TrustFormulaV1 lane: float-sorted predicates are
        // rejected up front in `trust_spec_predicate_to_trust_formula_payload`
        // (IEEE semantics have no faithful scalar int/bool replay).
        TrustSpecSort::Float { .. } => "float",
    }
}

fn trust_spec_unary_op_label(op: TrustSpecUnaryOp) -> Result<&'static str, String> {
    match op {
        TrustSpecUnaryOp::Not => Ok("not"),
        TrustSpecUnaryOp::Neg => Ok("neg"),
        _ => Err(
            "TrustSpecPredicate future unary operator is outside trust_wp TrustFormulaV1 native int/bool replay fragment"
                .to_string(),
        ),
    }
}

fn trust_spec_binary_op_label(op: TrustSpecBinaryOp) -> Result<&'static str, String> {
    match op {
        TrustSpecBinaryOp::Add => Ok("add"),
        TrustSpecBinaryOp::Sub => Ok("sub"),
        TrustSpecBinaryOp::Mul => Ok("mul"),
        TrustSpecBinaryOp::Div => Ok("div"),
        TrustSpecBinaryOp::Mod => Ok("mod"),
        TrustSpecBinaryOp::Eq => Ok("eq"),
        TrustSpecBinaryOp::Ne => Ok("ne"),
        TrustSpecBinaryOp::Lt => Ok("lt"),
        TrustSpecBinaryOp::Le => Ok("le"),
        TrustSpecBinaryOp::Gt => Ok("gt"),
        TrustSpecBinaryOp::Ge => Ok("ge"),
        TrustSpecBinaryOp::And => Ok("and"),
        TrustSpecBinaryOp::Or => Ok("or"),
        TrustSpecBinaryOp::Implies => Ok("implies"),
        _ => Err(
            "TrustSpecPredicate future binary operator is outside trust_wp TrustFormulaV1 native int/bool replay fragment"
                .to_string(),
        ),
    }
}

#[cfg(feature = "trust-build")]
fn direct_trust_wp_native_evidence(
    manifest: &EngineManifest,
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    claim: &NativeTrustWpClaim,
    trust_ir_functions: Option<Vec<serde_json::Value>>,
) -> Result<ObligationEvidence, NativeContractLoweringOutcome> {
    #[cfg(not(trust_wp_proof_transport_api))]
    {
        let _ = (manifest, bundle, claim, trust_ir_functions);
        return Err(NativeContractLoweringOutcome::Unsupported {
            diagnostic: stale_trust_wp_transport_api_diagnostic(obligation),
        });
    }

    #[cfg(all(trust_wp_proof_transport_api, not(trust_wp_structured_context_api)))]
    {
        let _ = (manifest, bundle, claim, trust_ir_functions);
        return Err(NativeContractLoweringOutcome::Unsupported {
            diagnostic: stale_trust_wp_structured_context_diagnostic(obligation),
        });
    }

    #[cfg(all(trust_wp_proof_transport_api, trust_wp_structured_context_api))]
    {
        let request =
            trust_wp_verify_bundle_request(bundle, obligation, claim, trust_ir_functions)?;
        let result = {
            use trust_wp_core::verify_bundle::VerifyBundleEngine as _;
            trust_wp_core::verify_bundle::NativeTrustWpBundleVerifier.verify_bundle(request.clone())
        };

        let Some(obligation_result) = result.obligation_results.first() else {
            return Err(NativeContractLoweringOutcome::Unsupported {
                diagnostic: format!(
                    "trust-wp native pure verifier returned no result for obligation `{}` with aggregate status `{}`: {}; failing closed",
                    obligation.obligation_id,
                    result.status.as_str(),
                    trust_wp_result_diagnostics(&result),
                ),
            });
        };
        if result.obligation_results.len() != 1
            || obligation_result.obligation_id != obligation.obligation_id
        {
            return Err(NativeContractLoweringOutcome::Unsupported {
                diagnostic: format!(
                    "trust-wp native pure verifier returned mismatched results for obligation `{}` with aggregate status `{}`: {}; failing closed",
                    obligation.obligation_id,
                    result.status.as_str(),
                    trust_wp_result_diagnostics(&result),
                ),
            });
        }

        use trust_wp_core::verify_bundle::{
            BundleObligationStatus as TrustWpObligationStatus,
            VerifyBundleStatus as TrustWpBundleStatus,
        };

        match &obligation_result.status {
            TrustWpObligationStatus::Verified { evidence } => {
                if !matches!(result.status, TrustWpBundleStatus::Verified) {
                    return Err(NativeContractLoweringOutcome::Unsupported {
                        diagnostic: format!(
                            "trust-wp native pure verifier produced local evidence for obligation `{}` but aggregate status was `{}`: {}; failing closed",
                            obligation.obligation_id,
                            result.status.as_str(),
                            trust_wp_result_diagnostics(&result),
                        ),
                    });
                }
                #[cfg(trust_wp_verify_bundle_replay_helper_api)]
                trust_wp_core::verify_bundle::replay_verify_bundle_result_evidence(
                    &request, &result,
                )
                .map_err(|error| NativeContractLoweringOutcome::Unsupported {
                    diagnostic: format!(
                        "trust-wp aggregate VerifyBundleResult replay rejected obligation `{}`: {error}; failing closed",
                        obligation.obligation_id
                    ),
                })?;
                #[cfg(not(trust_wp_verify_bundle_replay_helper_api))]
                return Err(NativeContractLoweringOutcome::Unsupported {
                    diagnostic: format!(
                        "{TRUST_WP_REPLAY_HELPER_API_MISSING} for obligation `{}`; refresh `first-party/trust-wp` before reporting deductive proof strength from native trust_wp evidence",
                        obligation.obligation_id
                    ),
                });
                let aggregate_evidence = result.aggregate_evidence.as_ref().ok_or_else(|| {
                    NativeContractLoweringOutcome::Unsupported {
                        diagnostic: format!(
                            "trust-wp aggregate VerifyBundleResult for obligation `{}` had no aggregate proof manifest evidence after replay; failing closed",
                            obligation.obligation_id
                        ),
                    }
                })?;
                validate_trust_wp_proof_result_metadata(
                    obligation,
                    claim,
                    &obligation_result.metadata,
                    evidence,
                )
                .map_err(|diagnostic| NativeContractLoweringOutcome::Unsupported { diagnostic })?;
                trust_wp_verified_evidence_to_trust(
                    manifest,
                    bundle,
                    obligation,
                    claim,
                    &obligation_result.metadata,
                    evidence,
                    aggregate_evidence,
                )
                .map_err(|diagnostic| NativeContractLoweringOutcome::Unsupported { diagnostic })
            }
            TrustWpObligationStatus::Failed { reason } => {
                Err(NativeContractLoweringOutcome::Failed {
                    diagnostic: format!(
                        "trust-wp native pure verifier refuted obligation `{}`: {reason}",
                        obligation.obligation_id
                    ),
                    counterexample: Some(Counterexample {
                        format: "trust_wp.native-pure-replay.counterexample.v1".to_string(),
                        data: serde_json::json!({
                            "obligation_id": obligation.obligation_id.as_str(),
                            "claim": claim.counterexample_payload(),
                            "reason": reason,
                        }),
                    }),
                })
            }
            TrustWpObligationStatus::Unknown { reason } => {
                Err(NativeContractLoweringOutcome::Unsupported {
                    diagnostic: format!(
                        "trust-wp native pure verifier returned unknown for obligation `{}`: {reason}",
                        obligation.obligation_id
                    ),
                })
            }
            TrustWpObligationStatus::Unsupported { reason } => {
                Err(NativeContractLoweringOutcome::Unsupported {
                    diagnostic: format!(
                        "trust-wp native pure verifier does not support obligation `{}` under the current trust_wp dependency: {reason}; {}",
                        obligation.obligation_id,
                        trust_wp_result_diagnostics(&result),
                    ),
                })
            }
            _ => Err(NativeContractLoweringOutcome::Unsupported {
                diagnostic: format!(
                    "trust-wp native pure verifier returned an unrecognized status for obligation `{}`; failing closed",
                    obligation.obligation_id
                ),
            }),
        }
    }
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn trust_wp_verify_bundle_request(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    claim: &NativeTrustWpClaim,
    trust_ir_functions: Option<Vec<serde_json::Value>>,
) -> Result<trust_wp_core::verify_bundle::VerifyBundleRequest, NativeContractLoweringOutcome> {
    use trust_wp_core::verify_bundle::{
        BundleClaim as TrustWpClaim, BundleClaimFormat as TrustWpClaimFormat,
        BundleObligation as TrustWpObligation, BundleProducer as TrustWpProducer,
        BundleTarget as TrustWpTarget, VerifyBundleRequest as TrustWpRequest,
    };

    // Run raw proof-bearing JSON uniqueness before the typed metadata helper,
    // whose serde decoder would otherwise become the first interpretation of
    // an ambiguous duplicate-key payload.
    validate_unique_trust_wp_proof_context_metadata_json(bundle, obligation)
        .map_err(|diagnostic| NativeContractLoweringOutcome::Unsupported { diagnostic })?;

    let (claim_format, payload) = match claim {
        NativeTrustWpClaim::TrustWpPureExprV1(predicate) => {
            trust_wp_pure_expr_reject_arithmetic(predicate)
                .map_err(|diagnostic| NativeContractLoweringOutcome::Unsupported { diagnostic })?;
            (TrustWpClaimFormat::TrustWpPureExprV1, predicate.native_replay_text())
        }
        NativeTrustWpClaim::TrustFormulaV1(payload) => {
            let payload =
                trust_types::trust_formula_v1::parse_arithmetic_free_trust_formula_v1_payload(
                    payload,
                )
                .map_err(|diagnostic| NativeContractLoweringOutcome::Unsupported { diagnostic })?;
            (TrustWpClaimFormat::TrustFormulaV1, payload)
        }
    };

    let mut trust_wp_claim = TrustWpClaim::new(claim_format, payload);
    #[cfg(trust_wp_typed_metadata_helper_api)]
    if let Some(claim_digest) = trust_wp_native_replay_metadata_input(bundle, obligation)
        .map_err(|diagnostic| NativeContractLoweringOutcome::Unsupported { diagnostic })?
        .claim_digest
    {
        trust_wp_claim = trust_wp_claim.with_digest(claim_digest);
    }
    #[cfg(not(trust_wp_typed_metadata_helper_api))]
    if let Some(claim_digest) = optional_trust_wp_metadata::<
        trust_wp_core::verify_bundle::BundleDigest,
    >(bundle, obligation, TRUST_WP_CLAIM_DIGEST_METADATA_KEY)
    .map_err(|diagnostic| NativeContractLoweringOutcome::Unsupported { diagnostic })?
    {
        trust_wp_claim = trust_wp_claim.with_digest(claim_digest);
    }

    let subject_label = bundle_subject_label(bundle);
    let mut trust_wp_obligation = TrustWpObligation::new(
        obligation.obligation_id.clone(),
        trust_wp_obligation_kind(obligation, &subject_label)?,
        subject_label.clone(),
        trust_wp_claim,
    );
    if let Some(location) = trust_wp_source_span(&obligation.source) {
        trust_wp_obligation = trust_wp_obligation.with_location(location);
    }
    trust_wp_obligation =
        attach_required_trust_wp_artifact_context(trust_wp_obligation, bundle, obligation)
            .map_err(|diagnostic| NativeContractLoweringOutcome::Unsupported { diagnostic })?;
    normalize_and_validate_trust_wp_proof_context_claims(
        &mut trust_wp_obligation.metadata.proof_context,
    )
    .map_err(|diagnostic| NativeContractLoweringOutcome::Unsupported { diagnostic })?;
    for fact in trust_wp_summary_facts_for_obligation(bundle, obligation)
        .map_err(|diagnostic| NativeContractLoweringOutcome::Unsupported { diagnostic })?
    {
        trust_wp_obligation = trust_wp_obligation.with_summary_fact(fact);
    }

    let mut request = TrustWpRequest::new(
        bundle.bundle_id.clone(),
        TrustWpProducer::new("trust-wp").with_version(env!("CARGO_PKG_VERSION")),
        TrustWpTarget::new(bundle_crate_name(bundle)),
    )
    .with_obligation(trust_wp_obligation);

    request.functions = trust_ir_functions;

    Ok(request)
}

/// Validate every attached proof-context claim at the final request boundary.
///
/// Metadata parsing and structural binding checks are not semantic claim
/// validation. Re-run the same arithmetic-free format gates used for the target
/// and then ask trust-wp-core to decode the exact payload it will see. The
/// raw-PureExpr AST is restricted to the bool/int comparison fragment, while a
/// validated TrustFormulaV1 may additionally contain its schema's `old`, `let`,
/// and trigger-free quantifier nodes. Casts, calls, postfix projections, and
/// future parser extensions cannot become proof inputs by reinterpretation.
#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn normalize_and_validate_trust_wp_proof_context_claims(
    context: &mut trust_wp_core::verify_bundle::BundleProofContext,
) -> Result<(), String> {
    for (role, atoms) in [
        ("assumption", context.assumptions.as_mut_slice()),
        ("assertion", context.assertions.as_mut_slice()),
    ] {
        for atom in atoms {
            normalize_and_validate_trust_wp_proof_input_claim(&mut atom.claim).map_err(|reason| {
                format!(
                    "trust-wp proof-context {role} atom {} is outside the arithmetic-free native proof-input fragment: {reason}",
                    atom.index
                )
            })?;
        }
    }
    Ok(())
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn normalize_and_validate_trust_wp_proof_input_claim(
    claim: &mut trust_wp_core::verify_bundle::BundleClaim,
) -> Result<(), String> {
    use trust_wp_core::verify_bundle::{
        BundleClaimFormat, BundleObligation, BundleObligationKind, native_predicate_for_obligation,
    };

    let structured_trust_formula = match &claim.format {
        BundleClaimFormat::TrustWpPureExprV1 => {
            trust_types::trust_formula_v1::reject_trust_wp_pure_expr_v1_text_arithmetic(
                &claim.payload,
            )?;
            let predicate = parse_pure_expr_text(&claim.payload)?;
            trust_wp_pure_expr_reject_arithmetic(&predicate)?;
            if predicate.sort() != Some(TrustWpPureSortV1::Bool) {
                return Err("TrustWpPureExprV1 proof-context claim is not boolean".to_string());
            }
            claim.payload = predicate.native_replay_text();
            false
        }
        BundleClaimFormat::TrustFormulaV1 => {
            claim.payload =
                trust_types::trust_formula_v1::parse_arithmetic_free_trust_formula_v1_payload(
                    &claim.payload,
                )?;
            true
        }
        BundleClaimFormat::SmtLib2 => {
            return Err("SMT-LIB2 is opaque to native proof-context replay".to_string());
        }
        BundleClaimFormat::Other(format) => {
            return Err(format!(
                "opaque claim format `{format}` has no native proof-context decoder"
            ));
        }
        _ => return Err("unrecognized proof-context claim format".to_string()),
    };

    let probe = BundleObligation::new(
        "__trust_wp_proof_context_probe",
        BundleObligationKind::Postcondition,
        "__trust_wp_proof_context_probe",
        claim.clone(),
    );
    let decoded = native_predicate_for_obligation(&probe)
        .map_err(|diagnostic| format!("native predicate decode failed: {diagnostic:?}"))?;
    validate_trust_wp_native_arithmetic_free_expr(&decoded.predicate, structured_trust_formula)
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn validate_trust_wp_native_arithmetic_free_expr(
    expr: &trust_wp_core::formula::PureExpr,
    structured_trust_formula: bool,
) -> Result<(), String> {
    use trust_wp_core::formula::{BinOp, PureExpr, UnOp};

    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Var(_, _) => Ok(()),
        PureExpr::UnOp(UnOp::Not, inner) => {
            validate_trust_wp_native_arithmetic_free_expr(inner, structured_trust_formula)
        }
        PureExpr::BinOp(lhs, op, rhs)
            if matches!(
                op,
                BinOp::Eq
                    | BinOp::Ne
                    | BinOp::Lt
                    | BinOp::Le
                    | BinOp::Gt
                    | BinOp::Ge
                    | BinOp::And
                    | BinOp::Or
                    | BinOp::Implies
            ) =>
        {
            validate_trust_wp_native_arithmetic_free_expr(lhs, structured_trust_formula)?;
            validate_trust_wp_native_arithmetic_free_expr(rhs, structured_trust_formula)
        }
        // These four nodes are part of the shared TrustFormulaV1 schema and
        // have already passed its recursive sort/arithmetic validation. They
        // have no spelling in the raw PureExpr stable-text lane, so keep this
        // allowance strictly format-sensitive.
        PureExpr::Old(inner) if structured_trust_formula => {
            validate_trust_wp_native_arithmetic_free_expr(inner, true)
        }
        PureExpr::Let { value, body, .. } if structured_trust_formula => {
            validate_trust_wp_native_arithmetic_free_expr(value, true)?;
            validate_trust_wp_native_arithmetic_free_expr(body, true)
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. }
            if structured_trust_formula && triggers.is_empty() =>
        {
            validate_trust_wp_native_arithmetic_free_expr(body, true)
        }
        _ => Err(format!(
            "decoded native expression node `{expr:?}` is outside the arithmetic-free proof-input allowlist (Bool/Int/Var/Not/comparison/boolean, plus TrustFormulaV1 Old/Let/trigger-free quantifiers)"
        )),
    }
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn trust_wp_obligation_kind(
    obligation: &TrustObligation,
    subject_label: &str,
) -> Result<trust_wp_core::verify_bundle::BundleObligationKind, NativeContractLoweringOutcome> {
    use trust_wp_core::verify_bundle::BundleObligationKind as TrustWpObligationKind;

    match &obligation.kind {
        ObligationKind::Precondition => Ok(TrustWpObligationKind::Precondition {
            callee: if obligation.contract_id.is_some() {
                // Definition-site `#[requires]` echo. A Precondition obligation
                // carrying a contract id is the function's OWN requires
                // (`ObligationOrigin::Contract` / `ContractKind::Requires`, the
                // only contract mapped to `Precondition`), which the body may
                // ASSUME — the caller establishes it separately at each call
                // site. Encode `callee == function` (the subject label that also
                // becomes the obligation's `function`) so trust-wp-core's native
                // replay recognises the reflexive `assume(P) ⊢ P` echo and
                // discharges it (see `is_definition_site_requires_echo`).
                //
                // A CALL-SITE precondition VC is a `VerificationCondition` with
                // NO contract id (routed to trust-mc, or otherwise the caller's
                // burden to PROVE); it keeps the parsed / `unknown-callee` label
                // so `callee != function` and it is NEVER assumed.
                subject_label.to_string()
            } else {
                obligation
                    .description
                    .strip_prefix("precondition:")
                    .unwrap_or("unknown-callee")
                    .to_string()
            },
        }),
        ObligationKind::Postcondition => Ok(TrustWpObligationKind::Postcondition),
        ObligationKind::LoopInvariant => Ok(TrustWpObligationKind::LoopInvariant),
        other => Err(NativeContractLoweringOutcome::Unsupported {
            diagnostic: format!(
                "trust-wp native pure direct verifier covers precondition, postcondition, and loop-invariant obligations; {other:?} remains fail-closed"
            ),
        }),
    }
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn trust_wp_source_span(
    source: &trust_verifier_api::SourceLocation,
) -> Option<trust_wp_core::verify_bundle::BundleSourceSpan> {
    let file = source.file.as_ref()?;
    let line = source.line?;
    let column = source.column.unwrap_or(0);
    Some(trust_wp_core::verify_bundle::BundleSourceSpan::new(file.clone(), line, column))
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn attach_required_trust_wp_artifact_context(
    mut trust_wp_obligation: trust_wp_core::verify_bundle::BundleObligation,
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<trust_wp_core::verify_bundle::BundleObligation, String> {
    // Defense in depth at the metadata-consumption helper itself. Request
    // construction already runs this before any typed helper, but keeping the
    // bounded duplicate-key scan here prevents a future direct caller from
    // silently changing the first interpretation of proof-bearing context.
    validate_unique_trust_wp_proof_context_metadata_json(bundle, obligation)?;

    #[cfg(trust_wp_typed_metadata_helper_api)]
    {
        let metadata = trust_wp_native_replay_metadata_input(bundle, obligation)?;
        trust_wp_obligation = trust_wp_obligation
            .with_native_origin(metadata.native_origin)
            .with_tmir_source_span(metadata.tmir_source_span)
            .with_native_verifier(metadata.native_verifier)
            .with_native_replay(metadata.native_replay)
            .with_native_solvers(metadata.native_solvers)
            .with_tmir_obligation_source(metadata.tmir_obligation_source);
        if !metadata.proof_context.is_empty() {
            trust_wp_obligation = trust_wp_obligation.with_proof_context(metadata.proof_context);
        }
        Ok(trust_wp_obligation)
    }

    #[cfg(not(trust_wp_typed_metadata_helper_api))]
    {
        use trust_wp_core::verify_bundle::{
            BundleNativeReplayIdentity, BundleNativeToolIdentity, BundleProofContext,
            BundleTmirObligationSource, BundleTmirSourceSpan,
        };

        let native_origin = required_trust_wp_native_origin_from_metadata(bundle, obligation)?;
        let tmir_source_span = required_trust_wp_metadata::<BundleTmirSourceSpan>(
            bundle,
            obligation,
            TRUST_WP_TMIR_SOURCE_SPAN_METADATA_KEY,
        )?;
        let native_verifier = required_trust_wp_metadata::<BundleNativeToolIdentity>(
            bundle,
            obligation,
            TRUST_WP_NATIVE_VERIFIER_METADATA_KEY,
        )?;
        let native_replay = required_trust_wp_metadata::<BundleNativeReplayIdentity>(
            bundle,
            obligation,
            TRUST_WP_NATIVE_REPLAY_METADATA_KEY,
        )?;
        let native_solvers = repeated_trust_wp_metadata::<BundleNativeToolIdentity>(
            bundle,
            obligation,
            TRUST_WP_NATIVE_SOLVER_METADATA_KEY,
        )?;
        if native_solvers.is_empty() {
            return Err(format!(
                "trust-wp proof evidence for obligation `{}` requires at least one typed native solver/prover metadata entry `{TRUST_WP_NATIVE_SOLVER_METADATA_KEY}`; refusing string-only or placeholder evidence",
                obligation.obligation_id
            ));
        }
        let tmir_obligation_source = required_trust_wp_metadata::<BundleTmirObligationSource>(
            bundle,
            obligation,
            TRUST_WP_TMIR_OBLIGATION_SOURCE_METADATA_KEY,
        )?;

        trust_wp_obligation = trust_wp_obligation
            .with_native_origin(native_origin)
            .with_tmir_source_span(tmir_source_span)
            .with_native_verifier(native_verifier)
            .with_native_replay(native_replay)
            .with_tmir_obligation_source(tmir_obligation_source);
        for solver in native_solvers {
            trust_wp_obligation = trust_wp_obligation.with_native_solver(solver);
        }
        if let Some(proof_context) = optional_trust_wp_metadata::<BundleProofContext>(
            bundle,
            obligation,
            TRUST_WP_PROOF_CONTEXT_METADATA_KEY,
        )? {
            if !proof_context.is_empty() {
                trust_wp_obligation = trust_wp_obligation.with_proof_context(proof_context);
            }
        }

        Ok(trust_wp_obligation)
    }
}

#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    trust_wp_structured_context_api,
    not(trust_wp_typed_metadata_helper_api)
))]
fn required_trust_wp_metadata<T>(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    key: &str,
) -> Result<T, String>
where
    T: serde::de::DeserializeOwned,
{
    optional_trust_wp_metadata(bundle, obligation, key)?.ok_or_else(|| {
        format!(
            "trust-wp proof evidence for obligation `{}` requires typed metadata `{key}`; refusing proof strength from text-marker or placeholder evidence",
            obligation.obligation_id
        )
    })
}

#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    trust_wp_structured_context_api,
    not(trust_wp_typed_metadata_helper_api)
))]
fn optional_trust_wp_metadata<T>(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    key: &str,
) -> Result<Option<T>, String>
where
    T: serde::de::DeserializeOwned,
{
    let mut entries = metadata_entries(bundle, obligation).filter(|entry| entry.key == key);
    let Some(entry) = entries.next() else {
        return Ok(None);
    };
    if entries.next().is_some() {
        return Err(format!(
            "trust-wp metadata key `{key}` appeared more than once for obligation `{}`",
            obligation.obligation_id
        ));
    }

    serde_json::from_str(&entry.value).map(Some).map_err(|error| {
        format!(
            "invalid trust_wp typed metadata `{key}` for obligation `{}`: {error}; refusing proof strength from text-marker or placeholder evidence",
            obligation.obligation_id
        )
    })
}

#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    trust_wp_structured_context_api,
    not(trust_wp_typed_metadata_helper_api)
))]
fn repeated_trust_wp_metadata<T>(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    key: &str,
) -> Result<Vec<T>, String>
where
    T: serde::de::DeserializeOwned,
{
    metadata_entries(bundle, obligation)
        .filter(|entry| entry.key == key)
        .map(|entry| {
            serde_json::from_str(&entry.value).map_err(|error| {
                format!(
                    "invalid trust_wp typed metadata `{key}` for obligation `{}`: {error}; refusing proof strength from text-marker or placeholder evidence",
                    obligation.obligation_id
                )
            })
        })
        .collect()
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn metadata_entries<'a>(
    bundle: &'a TrustContractBundle,
    obligation: &'a TrustObligation,
) -> impl Iterator<Item = &'a trust_verifier_api::MetadataEntry> {
    bundle.metadata.iter().chain(obligation.metadata.iter())
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn validate_unique_trust_wp_proof_context_metadata_json(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<(), String> {
    let mut entries = metadata_entries(bundle, obligation)
        .filter(|entry| entry.key == TRUST_WP_PROOF_CONTEXT_METADATA_KEY);
    let Some(entry) = entries.next() else {
        return Ok(());
    };
    if entries.next().is_some() {
        return Err(format!(
            "trust-wp metadata key `{TRUST_WP_PROOF_CONTEXT_METADATA_KEY}` appeared more than once for obligation `{}`",
            obligation.obligation_id
        ));
    }
    trust_types::trust_formula_v1::parse_unique_proof_json_payload(&entry.value)
        .map(|_| ())
        .map_err(|reason| {
            format!(
                "invalid trust-wp proof-context metadata for obligation `{}`: {reason}",
                obligation.obligation_id
            )
        })
}

#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    trust_wp_structured_context_api,
    trust_wp_typed_metadata_helper_api
))]
fn trust_wp_native_replay_metadata_input(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<trust_wp_core::verify_bundle::TrustWpNativeReplayEvidenceInput, String> {
    trust_wp_core::verify_bundle::TrustWpNativeReplayEvidenceInput::from_metadata_pairs(
        metadata_entries(bundle, obligation)
            .map(|entry| (entry.key.as_str(), entry.value.as_str())),
    )
    .map_err(|error| {
        format!(
            "invalid trust_wp native replay metadata for obligation `{}`: {error}; refusing proof strength from metadata-only/string-marker evidence",
            obligation.obligation_id
        )
    })
}

#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    trust_wp_structured_context_api,
    not(trust_wp_typed_metadata_helper_api)
))]
#[derive(Debug, Deserialize)]
struct TrustWpNativeOriginMetadata {
    schema: String,
    mode: TrustWpNativeOriginMode,
    request_id: u32,
    function_id: u32,
    obligation_id: u32,
    #[serde(default)]
    lineage_roots: Vec<u32>,
    // Wire-format field: trust-wp-core's `BundleNativeOrigin` serializes this
    // as `tmir_module_digest`; keep the wire name while using trust_ir naming
    // locally.
    #[serde(default, rename = "tmir_module_digest")]
    trust_ir_module_digest: Option<TrustWpNativeDigestMetadata>,
}

#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    trust_wp_structured_context_api,
    not(trust_wp_typed_metadata_helper_api)
))]
#[derive(Debug, Deserialize)]
#[serde(rename_all = "snake_case")]
enum TrustWpNativeOriginMode {
    WeakestPrecondition,
    StrongestPostcondition,
    Abduction,
}

#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    trust_wp_structured_context_api,
    not(trust_wp_typed_metadata_helper_api)
))]
#[derive(Debug, Deserialize)]
struct TrustWpNativeDigestMetadata {
    algorithm: String,
    value: String,
}

#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    trust_wp_structured_context_api,
    not(trust_wp_typed_metadata_helper_api)
))]
fn trust_wp_native_origin_from_metadata(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<Option<trust_wp_core::verify_bundle::BundleNativeOrigin>, String> {
    let mut entries = metadata_entries(bundle, obligation)
        .filter(|entry| entry.key == TRUST_WP_NATIVE_ORIGIN_METADATA_KEY);
    let Some(entry) = entries.next() else {
        return Ok(None);
    };
    if entries.next().is_some() {
        return Err(format!(
            "trust-wp native origin metadata key `{TRUST_WP_NATIVE_ORIGIN_METADATA_KEY}` appeared more than once for obligation `{}`",
            obligation.obligation_id
        ));
    }

    let metadata: TrustWpNativeOriginMetadata =
        serde_json::from_str(&entry.value).map_err(|error| {
            format!(
                "invalid trust_wp native origin metadata `{TRUST_WP_NATIVE_ORIGIN_METADATA_KEY}` for obligation `{}`: {error}",
                obligation.obligation_id
            )
        })?;
    let mode = match metadata.mode {
        TrustWpNativeOriginMode::WeakestPrecondition => {
            trust_wp_core::verify_bundle::BundleNativeVerificationMode::WeakestPrecondition
        }
        TrustWpNativeOriginMode::StrongestPostcondition => {
            trust_wp_core::verify_bundle::BundleNativeVerificationMode::StrongestPostcondition
        }
        TrustWpNativeOriginMode::Abduction => {
            trust_wp_core::verify_bundle::BundleNativeVerificationMode::Abduction
        }
    };
    let mut origin = trust_wp_core::verify_bundle::BundleNativeOrigin::new(
        metadata.schema,
        mode,
        metadata.request_id,
        metadata.function_id,
        metadata.obligation_id,
    )
    .with_lineage_roots(metadata.lineage_roots);
    if let Some(digest) = metadata.trust_ir_module_digest {
        origin = origin.with_tmir_module_digest(trust_wp_core::verify_bundle::BundleDigest::new(
            digest.algorithm,
            digest.value,
        ));
    }
    Ok(Some(origin))
}

#[cfg(all(
    feature = "trust-build",
    trust_wp_proof_transport_api,
    trust_wp_structured_context_api,
    not(trust_wp_typed_metadata_helper_api)
))]
fn required_trust_wp_native_origin_from_metadata(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<trust_wp_core::verify_bundle::BundleNativeOrigin, String> {
    trust_wp_native_origin_from_metadata(bundle, obligation)?.ok_or_else(|| {
        format!(
            "trust-wp proof evidence for obligation `{}` requires typed native TrustIr origin metadata `{TRUST_WP_NATIVE_ORIGIN_METADATA_KEY}`; refusing proof strength from marker-only evidence",
            obligation.obligation_id
        )
    })
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn trust_wp_native_origin_mode_label(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Option<String> {
    #[cfg(trust_wp_typed_metadata_helper_api)]
    {
        trust_wp_native_replay_metadata_input(bundle, obligation)
            .ok()
            .map(|metadata| metadata.native_origin.mode.as_str().to_string())
    }

    #[cfg(not(trust_wp_typed_metadata_helper_api))]
    {
        trust_wp_native_origin_from_metadata(bundle, obligation)
            .ok()
            .flatten()
            .map(|origin| origin.mode.as_str().to_string())
    }
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn trust_wp_summary_facts_for_obligation(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<Vec<trust_wp_core::verify_bundle::BundleSummaryFact>, String> {
    let trust_summary_facts = summary_facts_for_obligation(bundle, obligation)?;
    let mut trust_wp_summary_facts =
        trust_summary_facts.iter().map(trust_wp_summary_fact).collect::<Vec<_>>();

    #[cfg(trust_wp_typed_metadata_helper_api)]
    trust_wp_summary_facts
        .extend(trust_wp_native_replay_metadata_input(bundle, obligation)?.summary_facts);

    #[cfg(not(trust_wp_typed_metadata_helper_api))]
    trust_wp_summary_facts.extend(repeated_trust_wp_metadata::<
        trust_wp_core::verify_bundle::BundleSummaryFact,
    >(
        bundle, obligation, TRUST_WP_NATIVE_SUMMARY_FACT_METADATA_KEY
    )?);
    Ok(trust_wp_summary_facts)
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn trust_wp_summary_fact(fact: &SummaryFact) -> trust_wp_core::verify_bundle::BundleSummaryFact {
    use trust_wp_core::verify_bundle::{
        BundleDigest as TrustWpDigest, BundleSummaryFact as TrustWpSummaryFact,
        BundleSummaryFactKind as TrustWpSummaryFactKind,
    };

    TrustWpSummaryFact::new(
        fact.id.clone(),
        fact.producer.clone(),
        fact.source_crate.clone(),
        fact.source_item.clone(),
        match &fact.kind {
            trust_verifier_api::SummaryFactKind::PointerProvenanceEq { left, right } => {
                TrustWpSummaryFactKind::PointerProvenanceEq {
                    left: left.clone(),
                    right: right.clone(),
                }
            }
            trust_verifier_api::SummaryFactKind::FatPointerMetadataEq { left, right } => {
                TrustWpSummaryFactKind::FatPointerMetadataEq {
                    left: left.clone(),
                    right: right.clone(),
                }
            }
            trust_verifier_api::SummaryFactKind::Other { schema } => {
                TrustWpSummaryFactKind::Other { schema: schema.clone() }
            }
            _ => TrustWpSummaryFactKind::Other {
                schema: "trust-verifier-api.future-summary-fact".to_string(),
            },
        },
        TrustWpDigest::new(fact.digest.algorithm.clone(), fact.digest.value.clone()),
    )
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn trust_wp_verified_evidence_to_trust(
    manifest: &EngineManifest,
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    claim: &NativeTrustWpClaim,
    metadata: &trust_wp_core::verify_bundle::BundleResultMetadata,
    evidence: &trust_wp_core::verify_bundle::ProofEvidence,
    aggregate_evidence: &trust_wp_core::verify_bundle::ProofEvidence,
) -> Result<ObligationEvidence, String> {
    use trust_wp_core::verify_bundle::{
        ProofEvidenceFormat as TrustWpProofEvidenceFormat, ProofStrength as TrustWpProofStrength,
    };

    if evidence.format != TrustWpProofEvidenceFormat::TrustWpNativePureReplayV1 {
        return Err(format!(
            "trust-wp native pure evidence for obligation `{}` used unsupported evidence format `{}`",
            obligation.obligation_id,
            evidence.format.as_str(),
        ));
    }
    if !evidence.is_proof_grade() {
        return Err(format!(
            "trust-wp native pure evidence for obligation `{}` is not proof-grade checked evidence",
            obligation.obligation_id
        ));
    }
    let proof_strength = match evidence.strength {
        TrustWpProofStrength::Sound => ProofStrength::deductive(),
        TrustWpProofStrength::Certified => ProofStrength::certified(ReasoningKind::Deductive),
        other => {
            return Err(format!(
                "trust-wp native pure evidence for obligation `{}` used non-deductive proof strength `{}`",
                obligation.obligation_id,
                other.as_str(),
            ));
        }
    };
    if evidence.checked_by.as_deref() != Some(TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION) {
        return Err(format!(
            "trust-wp native pure evidence for obligation `{}` was checked by {:?}, expected `{TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION}`",
            obligation.obligation_id,
            evidence.checked_by.as_deref(),
        ));
    }
    if aggregate_evidence.format != TrustWpProofEvidenceFormat::TrustWpVerifyBundleAggregateV1 {
        return Err(format!(
            "trust-wp aggregate evidence for obligation `{}` used unsupported evidence format `{}`, expected `{TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION}`",
            obligation.obligation_id,
            aggregate_evidence.format.as_str(),
        ));
    }
    if !aggregate_evidence.is_proof_grade() {
        return Err(format!(
            "trust-wp aggregate evidence for obligation `{}` is not proof-grade checked evidence",
            obligation.obligation_id
        ));
    }
    if aggregate_evidence.checked_by.as_deref()
        != Some(TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION)
    {
        return Err(format!(
            "trust-wp aggregate evidence for obligation `{}` was checked by {:?}, expected `{TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION}`",
            obligation.obligation_id,
            aggregate_evidence.checked_by.as_deref(),
        ));
    }

    validate_trust_wp_proof_transport_artifacts(
        obligation,
        "native replay",
        &evidence.artifacts,
        required_native_replay_artifacts(bundle, obligation)?.as_slice(),
    )?;
    validate_trust_wp_proof_transport_artifacts(
        obligation,
        "aggregate proof manifest",
        &aggregate_evidence.artifacts,
        &[
            trust_wp_core::verify_bundle::EvidenceArtifactKind::RequestDigest,
            trust_wp_core::verify_bundle::EvidenceArtifactKind::AggregateProofManifest,
        ],
    )?;

    let evidence_id =
        format!("trust-wp:native-pure:{}:{}", bundle.bundle_id, obligation.obligation_id);
    let proof_binding_id = trust_wp_native_transport_binding_id(bundle, obligation)?;
    let artifacts = trust_wp_structured_evidence_artifacts(
        evidence,
        aggregate_evidence,
        &proof_binding_id,
        &obligation.obligation_id,
    )?;
    validate_trust_replay_and_check_artifacts(obligation, &artifacts)?;
    let native_trust_ir_identity = trust_wp_native_trust_ir_identity_material(bundle, obligation)?;

    Ok(ObligationEvidence {
        evidence_id,
        obligation_id: obligation.obligation_id.clone(),
        engine: manifest.clone(),
        status: EvidenceStatus::Proved,
        proof_strength: Some(proof_strength),
        artifacts,
        counterexample: None::<Counterexample>,
        publication: EvidencePublicationMetadata {
            publication_plan_hash: bundle.publication.dpub_plan_hash.clone(),
            trust_engines_lock_hash: bundle.publication.trust_engines_lock_hash.clone(),
            evidence_bundle_hash: evidence
                .digest
                .as_ref()
                .map(|digest| format!("{}:{}", digest.algorithm, digest.value)),
            ..EvidencePublicationMetadata::default()
        },
        diagnostics: trust_wp_verified_evidence_diagnostics(
            bundle,
            obligation,
            claim,
            metadata,
            evidence,
            aggregate_evidence,
            &native_trust_ir_identity,
        ),
    })
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn trust_wp_native_transport_binding_id(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<String, String> {
    #[cfg(trust_wp_typed_metadata_helper_api)]
    let origin = trust_wp_native_replay_metadata_input(bundle, obligation)?.native_origin;

    #[cfg(not(trust_wp_typed_metadata_helper_api))]
    let origin = required_trust_wp_native_origin_from_metadata(bundle, obligation)?;

    Ok(format!(
        "trust_ir-native-trust-wp-request-{}-proof-{}",
        origin.request_id, origin.obligation_id
    ))
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn validate_trust_wp_proof_result_metadata(
    obligation: &TrustObligation,
    claim: &NativeTrustWpClaim,
    metadata: &trust_wp_core::verify_bundle::BundleResultMetadata,
    evidence: &trust_wp_core::verify_bundle::ProofEvidence,
) -> Result<(), String> {
    use trust_wp_core::verify_bundle::ProofEvidenceFormat as TrustWpProofEvidenceFormat;

    let solver = metadata.solver.as_ref().ok_or_else(|| {
        format!(
            "trust-wp native pure result for obligation `{}` is missing solver/replay metadata",
            obligation.obligation_id
        )
    })?;
    if solver.engine != "trust-wp-core.native-pure-replay" {
        return Err(format!(
            "trust-wp native pure result for obligation `{}` used solver engine `{}`, expected `trust-wp-core.native-pure-replay`",
            obligation.obligation_id, solver.engine
        ));
    }
    if solver.checker != TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION {
        return Err(format!(
            "trust-wp native pure result for obligation `{}` used checker `{}`, expected `{TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION}`",
            obligation.obligation_id, solver.checker
        ));
    }
    let expected_claim_format = trust_wp_native_claim_format_label(claim);
    if solver.claim_format != expected_claim_format {
        return Err(format!(
            "trust-wp native pure result for obligation `{}` used claim format `{}`, expected `{expected_claim_format}`",
            obligation.obligation_id, solver.claim_format
        ));
    }
    if solver.replay_steps == 0 {
        return Err(format!(
            "trust-wp native pure result for obligation `{}` reported zero replay steps",
            obligation.obligation_id
        ));
    }

    let evidence_metadata = metadata.evidence.as_ref().ok_or_else(|| {
        format!(
            "trust-wp native pure result for obligation `{}` is missing proof evidence metadata",
            obligation.obligation_id
        )
    })?;
    if evidence_metadata.format != TrustWpProofEvidenceFormat::TrustWpNativePureReplayV1 {
        return Err(format!(
            "trust-wp native pure result for obligation `{}` used evidence format `{}`, expected `{TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION}`",
            obligation.obligation_id,
            evidence_metadata.format.as_str()
        ));
    }
    if evidence_metadata.strength != evidence.strength {
        return Err(format!(
            "trust-wp native pure result for obligation `{}` evidence strength metadata did not match attached evidence",
            obligation.obligation_id
        ));
    }
    if evidence_metadata.digest != evidence.digest {
        return Err(format!(
            "trust-wp native pure result for obligation `{}` evidence digest metadata did not match attached evidence",
            obligation.obligation_id
        ));
    }
    if evidence_metadata.artifact_count != evidence.artifacts.len() {
        return Err(format!(
            "trust-wp native pure result for obligation `{}` evidence artifact count metadata did not match attached evidence",
            obligation.obligation_id
        ));
    }
    if evidence_metadata.checked_by != evidence.checked_by {
        return Err(format!(
            "trust-wp native pure result for obligation `{}` checked-by metadata did not match attached evidence",
            obligation.obligation_id
        ));
    }
    Ok(())
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn trust_wp_native_claim_format_label(claim: &NativeTrustWpClaim) -> &'static str {
    match claim {
        NativeTrustWpClaim::TrustWpPureExprV1(_) => "TrustWpPureExprV1",
        NativeTrustWpClaim::TrustFormulaV1(_) => "TrustFormulaV1",
    }
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn trust_wp_verified_evidence_diagnostics(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    claim: &NativeTrustWpClaim,
    metadata: &trust_wp_core::verify_bundle::BundleResultMetadata,
    evidence: &trust_wp_core::verify_bundle::ProofEvidence,
    aggregate_evidence: &trust_wp_core::verify_bundle::ProofEvidence,
    native_trust_ir_identity: &str,
) -> Vec<String> {
    let mut diagnostics = vec![format!(
        "verified by trust_wp NativeTrustWpBundleVerifier aggregate VerifyBundleResult using typed `{}` claim payload and `{TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION}` checked evidence",
        claim.claim_schema()
    )];
    if let Some(solver) = metadata.solver.as_ref() {
        diagnostics.push(format!(
            "trust-wp proof result metadata: engine={}, checker={}, claim_format={}, replay_steps={}, assumptions={}, assertions={}",
            solver.engine,
            solver.checker,
            solver.claim_format,
            solver.replay_steps,
            solver.assumptions,
            solver.assertions
        ));
    }
    diagnostics.push(format!(
        "trust-wp proof transport artifacts preserved: native_artifacts={}, aggregate_artifacts={}, aggregate_schema={TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION}",
        evidence.artifacts.len(),
        aggregate_evidence.artifacts.len(),
    ));
    diagnostics
        .push(format!("trust-wp native TrustIr identity preserved: {native_trust_ir_identity}"));
    if let Some(mode) = trust_wp_native_origin_mode_label(bundle, obligation) {
        diagnostics.push(format!("trust-wp native origin mode preserved: {mode}"));
    }
    diagnostics
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn validate_trust_wp_proof_transport_artifacts(
    obligation: &TrustObligation,
    evidence_label: &str,
    artifacts: &[trust_wp_core::verify_bundle::EvidenceArtifact],
    required: &[trust_wp_core::verify_bundle::EvidenceArtifactKind],
) -> Result<(), String> {
    for required_kind in required {
        if !artifacts.iter().any(|artifact| &artifact.kind == required_kind) {
            return Err(format!(
                "trust-wp {evidence_label} evidence for obligation `{}` is missing structured `{}` artifact transport",
                obligation.obligation_id,
                required_kind.as_str(),
            ));
        }
    }

    for artifact in artifacts {
        if !artifact.has_transport() {
            return Err(format!(
                "trust-wp {evidence_label} evidence for obligation `{}` includes text-only `{}` artifact `{}` without URI or inline transport bytes; refusing proof strength",
                obligation.obligation_id,
                artifact.kind.as_str(),
                artifact.id,
            ));
        }
        if !artifact.inline_bytes_digest_matches() {
            return Err(format!(
                "trust-wp {evidence_label} evidence for obligation `{}` includes `{}` artifact `{}` whose inline transport bytes do not match digest `{}:{}`",
                obligation.obligation_id,
                artifact.kind.as_str(),
                artifact.id,
                artifact.digest.algorithm,
                artifact.digest.value,
            ));
        }
        if !artifact.has_stable_identity() {
            return Err(format!(
                "trust-wp {evidence_label} evidence for obligation `{}` includes `{}` artifact `{}` without stable proof artifact identity",
                obligation.obligation_id,
                artifact.kind.as_str(),
                artifact.id,
            ));
        }
    }

    Ok(())
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn required_native_replay_artifacts(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<Vec<trust_wp_core::verify_bundle::EvidenceArtifactKind>, String> {
    let mut required = vec![
        trust_wp_core::verify_bundle::EvidenceArtifactKind::RequestDigest,
        trust_wp_core::verify_bundle::EvidenceArtifactKind::NormalizedObligation,
        trust_wp_core::verify_bundle::EvidenceArtifactKind::ReplayLog,
    ];
    if !trust_wp_summary_facts_for_obligation(bundle, obligation)?.is_empty() {
        required.push(trust_wp_core::verify_bundle::EvidenceArtifactKind::SummaryEvidence);
    }
    Ok(required)
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn trust_wp_structured_evidence_artifacts(
    evidence: &trust_wp_core::verify_bundle::ProofEvidence,
    aggregate_evidence: &trust_wp_core::verify_bundle::ProofEvidence,
    proof_binding_id: &str,
    obligation_id: &str,
) -> Result<Vec<EvidenceArtifact>, String> {
    validate_trust_wp_upstream_transcript_relation(evidence)?;
    let input_manifest = trust_wp_structural_input_manifest(
        evidence,
        aggregate_evidence,
        proof_binding_id,
        obligation_id,
    )?;
    let mut artifacts = vec![input_manifest];
    for artifact in evidence.artifacts.iter().chain(aggregate_evidence.artifacts.iter()) {
        let converted = if matches!(
            artifact.kind,
            trust_wp_core::verify_bundle::EvidenceArtifactKind::ReplayLog
                | trust_wp_core::verify_bundle::EvidenceArtifactKind::SolverTranscript
        ) {
            trust_wp_evidence_artifact(artifact, proof_binding_id, obligation_id)?
        } else {
            trust_wp_evidence_artifact_descriptor(artifact)?
        };
        if !artifacts.iter().any(|existing: &EvidenceArtifact| {
            existing.kind == converted.kind && existing.hash == converted.hash
        }) {
            artifacts.push(converted);
        }
    }
    bind_trust_wp_transcript_to_replay(&mut artifacts, obligation_id)?;
    Ok(artifacts)
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn trust_wp_structural_input_manifest(
    evidence: &trust_wp_core::verify_bundle::ProofEvidence,
    aggregate_evidence: &trust_wp_core::verify_bundle::ProofEvidence,
    proof_binding_id: &str,
    obligation_id: &str,
) -> Result<EvidenceArtifact, String> {
    use trust_wp_core::verify_bundle::EvidenceArtifactKind as Kind;

    let mut inputs = evidence
        .artifacts
        .iter()
        .map(|artifact| ("obligation", artifact))
        .chain(aggregate_evidence.artifacts.iter().map(|artifact| ("aggregate", artifact)))
        .filter(|(_, artifact)| !matches!(artifact.kind, Kind::ReplayLog | Kind::SolverTranscript))
        .map(|(lane, artifact)| {
            let bytes = artifact
                .inline_bytes
                .as_ref()
                .ok_or_else(|| {
                    format!("trust-wp structural input `{}` has no exact inline bytes", artifact.id)
                })?
                .decoded_bytes()
                .map_err(|error| {
                    format!(
                        "trust-wp structural input `{}` bytes failed to decode: {error}",
                        artifact.id
                    )
                })?;
            Ok((lane, artifact, bytes))
        })
        .collect::<Result<Vec<_>, String>>()?;
    inputs.sort_by(|left, right| {
        (
            left.0,
            left.1.kind.as_str(),
            left.1.id.as_str(),
            left.1.digest.algorithm.as_str(),
            left.1.digest.value.as_str(),
        )
            .cmp(&(
                right.0,
                right.1.kind.as_str(),
                right.1.id.as_str(),
                right.1.digest.algorithm.as_str(),
                right.1.digest.value.as_str(),
            ))
    });
    if inputs.is_empty() {
        return Err("trust-wp proof has no exact structural input artifacts".to_string());
    }

    const MAGIC: &[u8] = b"trust-wp.public-structural-input-manifest.v1\0";
    let mut payload = Vec::new();
    payload.extend_from_slice(MAGIC);
    payload.extend_from_slice(
        &u32::try_from(inputs.len())
            .map_err(|_| "trust-wp structural input count overflow".to_string())?
            .to_be_bytes(),
    );
    for (lane, artifact, bytes) in inputs {
        push_trust_wp_manifest_field(&mut payload, lane.as_bytes())?;
        push_trust_wp_manifest_field(&mut payload, artifact.kind.as_str().as_bytes())?;
        push_trust_wp_manifest_field(&mut payload, artifact.id.as_bytes())?;
        push_trust_wp_manifest_field(&mut payload, artifact.digest.algorithm.as_bytes())?;
        push_trust_wp_manifest_field(&mut payload, artifact.digest.value.as_bytes())?;
        push_trust_wp_manifest_field(
            &mut payload,
            artifact.uri.as_deref().unwrap_or_default().as_bytes(),
        )?;
        payload.extend_from_slice(
            &u64::try_from(bytes.len())
                .map_err(|_| "trust-wp structural input byte length overflow".to_string())?
                .to_be_bytes(),
        );
        payload.extend_from_slice(&bytes);
    }

    let kind = EvidenceArtifactKind::NormalizedObligation;
    let (materialization, hash) = EvidenceArtifactMaterialization::new_bound(
        kind,
        &payload,
        proof_binding_id,
        obligation_id,
        Vec::new(),
    )
    .ok_or_else(|| {
        "trust-wp combined structural input manifest is empty, oversized, or invalid".to_string()
    })?;
    Ok(EvidenceArtifact {
        kind,
        uri: format!(
            "artifact://trust-wp/proof-artifacts/{}/{}",
            artifact_kind_label(kind),
            hash.value
        ),
        hash,
        materialization: Some(materialization),
    })
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn push_trust_wp_manifest_field(target: &mut Vec<u8>, value: &[u8]) -> Result<(), String> {
    target.extend_from_slice(
        &u32::try_from(value.len())
            .map_err(|_| "trust-wp structural manifest field length overflow".to_string())?
            .to_be_bytes(),
    );
    target.extend_from_slice(value);
    Ok(())
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn validate_trust_wp_upstream_transcript_relation(
    evidence: &trust_wp_core::verify_bundle::ProofEvidence,
) -> Result<(), String> {
    use trust_wp_core::verify_bundle::EvidenceArtifactKind as Kind;
    let replay = evidence
        .artifacts
        .iter()
        .enumerate()
        .filter(|(_, artifact)| artifact.kind == Kind::ReplayLog)
        .collect::<Vec<_>>();
    let check = evidence
        .artifacts
        .iter()
        .filter(|artifact| artifact.kind == Kind::SolverTranscript)
        .collect::<Vec<_>>();
    let ([(replay_index, replay)], [check]) = (replay.as_slice(), check.as_slice()) else {
        return Err("trust-wp upstream proof must contain exactly one replay log and one proof-check transcript".to_string());
    };
    let check_bytes = check
        .inline_bytes
        .as_ref()
        .ok_or_else(|| "trust-wp proof-check transcript has no exact inline bytes".to_string())?
        .decoded_bytes()
        .map_err(|error| format!("trust-wp proof-check transcript bytes are invalid: {error}"))?;
    let check_text = std::str::from_utf8(&check_bytes)
        .map_err(|error| format!("trust-wp proof-check transcript is not UTF-8: {error}"))?;
    let field = |name: &str| format!("artifact.{replay_index}.{name}");
    let declared_binding =
        format!("{}={}:{}", field("declared-digest"), replay.digest.algorithm, replay.digest.value);
    let actual_binding =
        format!("{}={}:{}", field("actual-digest"), replay.digest.algorithm, replay.digest.value);
    let kind_binding = format!("{}={}", field("kind"), Kind::ReplayLog.as_str());
    if !check_text.lines().any(|line| line == kind_binding)
        || !check_text.lines().any(|line| line == declared_binding)
        || !check_text.lines().any(|line| line == actual_binding)
    {
        return Err(
            "trust-wp proof-check transcript does not bind the exact indexed replay-log kind and declared/actual digest".to_string(),
        );
    }
    Ok(())
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn bind_trust_wp_transcript_to_replay(
    artifacts: &mut [EvidenceArtifact],
    obligation_id: &str,
) -> Result<(), String> {
    let input_indices = artifacts
        .iter()
        .enumerate()
        .filter_map(|(index, artifact)| {
            (artifact.kind == EvidenceArtifactKind::NormalizedObligation
                && artifact.materialization.is_some())
            .then_some(index)
        })
        .collect::<Vec<_>>();
    let transcript_indices = artifacts
        .iter()
        .enumerate()
        .filter_map(|(index, artifact)| {
            (artifact.kind == EvidenceArtifactKind::SolverTranscript).then_some(index)
        })
        .collect::<Vec<_>>();
    let check_indices = artifacts
        .iter()
        .enumerate()
        .filter_map(|(index, artifact)| {
            (artifact.kind == EvidenceArtifactKind::ProofCheckReport).then_some(index)
        })
        .collect::<Vec<_>>();
    let ([input_index], [transcript_index], [check_index]) =
        (input_indices.as_slice(), transcript_indices.as_slice(), check_indices.as_slice())
    else {
        return Err(format!(
            "trust-wp proof transport requires exactly one materialized structural input, replay transcript, and proof-check report; inputs={}, transcripts={}, checks={}",
            input_indices.len(),
            transcript_indices.len(),
            check_indices.len()
        ));
    };

    let input_kind = artifacts[*input_index].kind;
    let input_hash = artifacts[*input_index].hash.clone();
    let transcript_kind = artifacts[*transcript_index].kind;
    let transcript_materialization =
        artifacts[*transcript_index].materialization.as_ref().ok_or_else(|| {
            "trust-wp replay transcript did not retain exact inline bytes".to_string()
        })?;
    let transcript_payload = transcript_materialization
        .bound_payload_bytes(transcript_kind, obligation_id)
        .ok_or_else(|| "trust-wp replay transcript binding envelope is invalid".to_string())?;
    let (rebound_transcript, rebound_transcript_hash) = EvidenceArtifactMaterialization::new_bound(
        transcript_kind,
        &transcript_payload,
        transcript_materialization.proof_binding_id(),
        obligation_id,
        vec![EvidenceArtifactReference { kind: input_kind, hash: input_hash }],
    )
    .ok_or_else(|| "trust-wp replay transcript materialization is invalid".to_string())?;
    artifacts[*transcript_index].materialization = Some(rebound_transcript);
    artifacts[*transcript_index].hash = rebound_transcript_hash.clone();
    artifacts[*transcript_index].uri = format!(
        "artifact://trust-wp/proof-artifacts/{}/{}",
        artifact_kind_label(transcript_kind),
        rebound_transcript_hash.value
    );

    let check_kind = artifacts[*check_index].kind;
    let materialization = artifacts[*check_index].materialization.as_ref().ok_or_else(|| {
        "trust-wp proof-check report did not retain exact inline bytes".to_string()
    })?;
    let payload = materialization
        .bound_payload_bytes(check_kind, obligation_id)
        .ok_or_else(|| "trust-wp proof-check binding envelope is invalid".to_string())?;
    let (rebound, rebound_hash) = EvidenceArtifactMaterialization::new_bound(
        check_kind,
        &payload,
        materialization.proof_binding_id(),
        obligation_id,
        vec![EvidenceArtifactReference { kind: transcript_kind, hash: rebound_transcript_hash }],
    )
    .ok_or_else(|| "trust-wp solver transcript materialization is invalid".to_string())?;
    artifacts[*check_index].materialization = Some(rebound);
    artifacts[*check_index].hash = rebound_hash;
    artifacts[*check_index].uri = format!(
        "artifact://trust-wp/proof-artifacts/{}/{}",
        artifact_kind_label(check_kind),
        artifacts[*check_index].hash.value
    );
    Ok(())
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn validate_trust_replay_and_check_artifacts(
    obligation: &TrustObligation,
    artifacts: &[EvidenceArtifact],
) -> Result<(), String> {
    let has_transcript =
        artifacts.iter().any(|artifact| artifact.kind == EvidenceArtifactKind::SolverTranscript);
    let has_check =
        artifacts.iter().any(|artifact| artifact.kind == EvidenceArtifactKind::ProofCheckReport);

    if has_transcript && has_check {
        Ok(())
    } else {
        Err(format!(
            "trust-wp native pure evidence for obligation `{}` must preserve both replay transcript and proof-check artifacts after conversion; transcript_artifact={has_transcript}, check_artifact={has_check}",
            obligation.obligation_id
        ))
    }
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn trust_wp_native_trust_ir_identity_material(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<String, String> {
    #[cfg(trust_wp_typed_metadata_helper_api)]
    {
        let metadata = trust_wp_native_replay_metadata_input(bundle, obligation)?;
        trust_wp_native_trust_ir_identity_from_parts(
            obligation,
            &metadata.native_origin,
            metadata.tmir_source_span,
            &metadata.tmir_obligation_source,
        )
    }

    #[cfg(not(trust_wp_typed_metadata_helper_api))]
    {
        let origin = required_trust_wp_native_origin_from_metadata(bundle, obligation)?;
        let span = required_trust_wp_metadata::<trust_wp_core::verify_bundle::BundleTmirSourceSpan>(
            bundle,
            obligation,
            TRUST_WP_TMIR_SOURCE_SPAN_METADATA_KEY,
        )?;
        let source = required_trust_wp_metadata::<
            trust_wp_core::verify_bundle::BundleTmirObligationSource,
        >(bundle, obligation, TRUST_WP_TMIR_OBLIGATION_SOURCE_METADATA_KEY)?;
        trust_wp_native_trust_ir_identity_from_parts(obligation, &origin, span, &source)
    }
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn trust_wp_native_trust_ir_identity_from_parts(
    obligation: &TrustObligation,
    origin: &trust_wp_core::verify_bundle::BundleNativeOrigin,
    span: trust_wp_core::verify_bundle::BundleTmirSourceSpan,
    source: &trust_wp_core::verify_bundle::BundleTmirObligationSource,
) -> Result<String, String> {
    let module_digest = origin.tmir_module_digest.as_ref().ok_or_else(|| {
        format!(
            "trust-wp proof evidence for obligation `{}` is missing native TrustIr module digest identity",
            obligation.obligation_id
        )
    })?;
    if source.function_id != Some(origin.function_id) {
        return Err(format!(
            "trust-wp proof evidence for obligation `{}` has native TrustIr function identity drift: origin function {}, source function {:?}",
            obligation.obligation_id, origin.function_id, source.function_id
        ));
    }

    let lineage_roots = if origin.lineage_roots.is_empty() {
        "none".to_string()
    } else {
        origin.lineage_roots.iter().map(u32::to_string).collect::<Vec<_>>().join(",")
    };

    Ok(format!(
        "schema={}, mode={}, request_id={}, function_id={}, obligation_id={}, source_function_id={}, source_assertion_id={}, source_monomorphization_id={}, trust_ir_span={}:{}:{}, lineage_roots={}, trust_ir_module_digest={}:{}",
        origin.schema.as_str(),
        origin.mode.as_str(),
        origin.request_id,
        origin.function_id,
        origin.obligation_id,
        source.function_id.map_or_else(|| "none".to_string(), |id| id.to_string()),
        source.assertion_id.map_or_else(|| "none".to_string(), |id| id.to_string()),
        source.monomorphization_id.map_or_else(|| "none".to_string(), |id| id.to_string()),
        span.file_id,
        span.line,
        span.column,
        lineage_roots,
        module_digest.algorithm.as_str(),
        module_digest.value.as_str(),
    ))
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn trust_wp_evidence_artifact(
    artifact: &trust_wp_core::verify_bundle::EvidenceArtifact,
    proof_binding_id: &str,
    obligation_id: &str,
) -> Result<EvidenceArtifact, String> {
    let kind = trust_wp_public_artifact_kind(&artifact.kind);

    let materialization = artifact
        .inline_bytes
        .as_ref()
        .map(|bytes| {
            bytes
                .decoded_bytes()
                .map_err(|error| format!("trust-wp artifact `{}` bytes failed to decode: {error}", artifact.id))
                .and_then(|bytes| {
                    EvidenceArtifactMaterialization::new_bound(
                        kind,
                        &bytes,
                        proof_binding_id,
                        obligation_id,
                        Vec::new(),
                    )
                        .ok_or_else(|| {
                            format!("trust-wp artifact `{}` materialization is empty, oversized, or has invalid proof identity", artifact.id)
                        })
                })
        })
        .transpose()?;
    let (materialization, hash) = materialization.ok_or_else(|| {
        format!("trust-wp proof artifact `{}` has no exact inline materialization", artifact.id)
    })?;
    Ok(EvidenceArtifact {
        kind,
        uri: format!(
            "artifact://trust-wp/proof-artifacts/{}/{}",
            artifact_kind_label(kind),
            hash.value
        ),
        hash,
        materialization: Some(materialization),
    })
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn trust_wp_evidence_artifact_descriptor(
    artifact: &trust_wp_core::verify_bundle::EvidenceArtifact,
) -> Result<EvidenceArtifact, String> {
    if artifact.digest.algorithm != "sha256"
        || artifact.digest.value.len() != 64
        || !artifact
            .digest
            .value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(format!(
            "trust-wp artifact `{}` has a non-canonical SHA-256 digest",
            artifact.id
        ));
    }
    let kind = trust_wp_public_artifact_kind(&artifact.kind);
    let hash = ArtifactHash {
        algorithm: artifact.digest.algorithm.clone(),
        value: artifact.digest.value.clone(),
    };
    Ok(EvidenceArtifact {
        kind,
        uri: format!(
            "artifact://trust-wp/upstream-proof-inputs/{}/{}",
            artifact_kind_label(kind),
            hash.value
        ),
        hash,
        // The exact bytes are committed into the one materialized combined
        // NormalizedObligation consumed by the transcript. Keeping these
        // descriptors unmaterialized avoids inventing separate DAG consumers.
        materialization: None,
    })
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn trust_wp_public_artifact_kind(
    kind: &trust_wp_core::verify_bundle::EvidenceArtifactKind,
) -> EvidenceArtifactKind {
    use trust_wp_core::verify_bundle::EvidenceArtifactKind as TrustWpArtifactKind;

    match kind {
        TrustWpArtifactKind::RequestDigest => EvidenceArtifactKind::EngineInput,
        TrustWpArtifactKind::AggregateProofManifest => EvidenceArtifactKind::BuildManifest,
        TrustWpArtifactKind::NormalizedObligation => EvidenceArtifactKind::NormalizedObligation,
        TrustWpArtifactKind::SummaryEvidence => EvidenceArtifactKind::SummaryEvidence,
        TrustWpArtifactKind::ProofCertificate => EvidenceArtifactKind::ProofCertificate,
        // The native-pure ReplayLog is the proof transcript. The upstream
        // SolverTranscript is actually a proof-check transcript over those
        // replay bytes, so expose their consumer roles honestly.
        TrustWpArtifactKind::SolverTranscript => EvidenceArtifactKind::ProofCheckReport,
        TrustWpArtifactKind::ReplayLog => EvidenceArtifactKind::SolverTranscript,
        TrustWpArtifactKind::Counterexample => EvidenceArtifactKind::Counterexample,
        TrustWpArtifactKind::Model => EvidenceArtifactKind::Model,
        TrustWpArtifactKind::DiagnosticTrace => EvidenceArtifactKind::Report,
        _ => EvidenceArtifactKind::Report,
    }
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn trust_wp_result_diagnostics(
    result: &trust_wp_core::verify_bundle::VerifyBundleResult,
) -> String {
    let mut diagnostics = result
        .diagnostics
        .iter()
        .map(|diagnostic| {
            format!("{}:{}: {}", diagnostic.severity.as_str(), diagnostic.code, diagnostic.message)
        })
        .collect::<Vec<_>>();
    for obligation_result in &result.obligation_results {
        diagnostics.extend(obligation_result.diagnostics.iter().map(|diagnostic| {
            format!("{}:{}: {}", diagnostic.severity.as_str(), diagnostic.code, diagnostic.message)
        }));
    }
    if diagnostics.is_empty() {
        "no trust_wp diagnostics".to_string()
    } else {
        diagnostics.join("; ")
    }
}

#[cfg(all(feature = "trust-build", trust_wp_proof_transport_api, trust_wp_structured_context_api))]
fn bundle_crate_name(bundle: &TrustContractBundle) -> String {
    match &bundle.subject {
        trust_verifier_api::BundleSubject::Crate { name } => name.clone(),
        trust_verifier_api::BundleSubject::Function { crate_name, .. } => crate_name.clone(),
        trust_verifier_api::BundleSubject::Artifact { name, .. } => name.clone(),
        _ => "unknown-crate".to_string(),
    }
}

fn replay_typed_predicate(predicate: &TrustWpPureExprV1) -> Result<TrustWpNativeReplay, String> {
    replay_typed_predicate_for_evidence(predicate).map_err(|failure| match failure {
        NativeReplayFailure::False { diagnostic } | NativeReplayFailure::Unknown { diagnostic } => {
            diagnostic
        }
    })
}

fn replay_typed_predicate_for_evidence(
    predicate: &TrustWpPureExprV1,
) -> Result<TrustWpNativeReplay, NativeReplayFailure> {
    let normalized_predicate = predicate.stable_text();
    match prove_typed_predicate(predicate) {
        ReplayTruth::True { rule } => Ok(TrustWpNativeReplay {
            normalized_predicate: normalized_predicate.clone(),
            steps: vec![
                TrustWpNativeReplayStep::DecodeTrustWpPureExprV1,
                TrustWpNativeReplayStep::Normalize(normalized_predicate),
                TrustWpNativeReplayStep::ApplyRule(rule),
                TrustWpNativeReplayStep::Verified,
            ],
        }),
        ReplayTruth::False { rule } => Err(NativeReplayFailure::False {
            diagnostic: format!("typed predicate is false by native pure replay rule `{rule}`"),
        }),
        ReplayTruth::Unknown { reason } => Err(NativeReplayFailure::Unknown {
            diagnostic: format!("native pure replay cannot prove predicate: {reason}"),
        }),
    }
}

#[cfg(not(feature = "trust-build"))]
fn aggregate_gate_missing_diagnostic(
    obligation: &TrustObligation,
    replay: &TrustWpNativeReplay,
) -> String {
    format!(
        "local typed TrustWpPureExprV1 replay for obligation `{}` normalized `{}` but did not pass through trust_wp VerifyBundleResult aggregate native replay evidence gate `{}` from commit `{}`; proof_strength remains omitted until Trust wires that gate",
        obligation.obligation_id,
        replay.normalized_predicate,
        TRUST_WP_AGGREGATE_NATIVE_REPLAY_GATE_SCHEMA_VERSION,
        TRUST_WP_AGGREGATE_NATIVE_REPLAY_GATE_COMMIT,
    )
}

fn validate_aggregate_native_replay_gate(_evidence: &ObligationEvidence) -> Result<(), String> {
    Err(format!(
        "candidate trust_wp evidence matched local typed replay metadata, but Trust has not called trust_wp VerifyBundleResult aggregate native replay gate `{TRUST_WP_AGGREGATE_NATIVE_REPLAY_GATE_SCHEMA_VERSION}` from commit `{TRUST_WP_AGGREGATE_NATIVE_REPLAY_GATE_COMMIT}`; refusing to report deductive proof strength without that aggregate ProofCheckReport"
    ))
}

fn prove_typed_predicate(predicate: &TrustWpPureExprV1) -> ReplayTruth {
    match eval_value(predicate) {
        Some(TrustWpPureValue::Bool(value)) => ReplayTruth::from_bool(value, "typed-constant-fold"),
        Some(TrustWpPureValue::Int(_)) => {
            ReplayTruth::Unknown { reason: "integer expression is not a predicate".to_string() }
        }
        None => ReplayTruth::Unknown {
            reason: "predicate is outside the native replay fragment".to_string(),
        },
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TrustWpPureValue {
    Bool(bool),
    Int(i64),
}

fn eval_value(expr: &TrustWpPureExprV1) -> Option<TrustWpPureValue> {
    match expr {
        TrustWpPureExprV1::Bool { value } => Some(TrustWpPureValue::Bool(*value)),
        TrustWpPureExprV1::Int { value } => Some(TrustWpPureValue::Int(*value)),
        TrustWpPureExprV1::Not { expr } => match eval_value(expr)? {
            TrustWpPureValue::Bool(value) => Some(TrustWpPureValue::Bool(!value)),
            TrustWpPureValue::Int(_) => None,
        },
        // A free variable has no local value: constant-fold replay stays
        // fail-closed (Unknown), never a guessed valuation.
        TrustWpPureExprV1::Var { .. } => None,
        TrustWpPureExprV1::Binary { op, lhs, rhs } => eval_binary(*op, lhs, rhs),
    }
}

fn eval_binary(
    op: TrustWpPureBinaryOpV1,
    lhs: &TrustWpPureExprV1,
    rhs: &TrustWpPureExprV1,
) -> Option<TrustWpPureValue> {
    let lhs = eval_value(lhs)?;
    let rhs = eval_value(rhs)?;
    match (op, lhs, rhs) {
        (TrustWpPureBinaryOpV1::Add, TrustWpPureValue::Int(lhs), TrustWpPureValue::Int(rhs)) => {
            lhs.checked_add(rhs).map(TrustWpPureValue::Int)
        }
        (TrustWpPureBinaryOpV1::Sub, TrustWpPureValue::Int(lhs), TrustWpPureValue::Int(rhs)) => {
            lhs.checked_sub(rhs).map(TrustWpPureValue::Int)
        }
        (TrustWpPureBinaryOpV1::Eq, lhs, rhs) => Some(TrustWpPureValue::Bool(lhs == rhs)),
        (TrustWpPureBinaryOpV1::Ne, lhs, rhs) => Some(TrustWpPureValue::Bool(lhs != rhs)),
        (TrustWpPureBinaryOpV1::Lt, TrustWpPureValue::Int(lhs), TrustWpPureValue::Int(rhs)) => {
            Some(TrustWpPureValue::Bool(lhs < rhs))
        }
        (TrustWpPureBinaryOpV1::Le, TrustWpPureValue::Int(lhs), TrustWpPureValue::Int(rhs)) => {
            Some(TrustWpPureValue::Bool(lhs <= rhs))
        }
        (TrustWpPureBinaryOpV1::Gt, TrustWpPureValue::Int(lhs), TrustWpPureValue::Int(rhs)) => {
            Some(TrustWpPureValue::Bool(lhs > rhs))
        }
        (TrustWpPureBinaryOpV1::Ge, TrustWpPureValue::Int(lhs), TrustWpPureValue::Int(rhs)) => {
            Some(TrustWpPureValue::Bool(lhs >= rhs))
        }
        (TrustWpPureBinaryOpV1::And, TrustWpPureValue::Bool(lhs), TrustWpPureValue::Bool(rhs)) => {
            Some(TrustWpPureValue::Bool(lhs && rhs))
        }
        (TrustWpPureBinaryOpV1::Or, TrustWpPureValue::Bool(lhs), TrustWpPureValue::Bool(rhs)) => {
            Some(TrustWpPureValue::Bool(lhs || rhs))
        }
        (
            TrustWpPureBinaryOpV1::Implies,
            TrustWpPureValue::Bool(lhs),
            TrustWpPureValue::Bool(rhs),
        ) => Some(TrustWpPureValue::Bool(!lhs || rhs)),
        _ => None,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExpectedNativeReplayMetadata {
    evidence_id: String,
    artifacts: Vec<EvidenceArtifact>,
    evidence_bundle_hash: String,
}

fn expected_native_replay_metadata(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    replay: &TrustWpNativeReplay,
    summary_facts: &[SummaryFact],
) -> ExpectedNativeReplayMetadata {
    let summary_artifact = summary_facts_artifact(summary_facts);
    let summary_digest_line = summary_artifact
        .as_ref()
        .map(|artifact| {
            format!("{}:{}", artifact.hash.algorithm.as_str(), artifact.hash.value.as_str())
        })
        .unwrap_or_else(|| "none".to_string());
    let normalized_material = format!(
        "api={api}\nevidence-schema={evidence_schema}\nreplay-schema={replay_schema}\nbundle={bundle}\nobligation={obligation_id}\nkind={kind}\nfunction={function}\nclaim-format=TrustWpPureExprV1\npredicate={predicate}\nsummary-count={summary_count}\nsummary-digest={summary_digest}\n",
        api = API_VERSION,
        evidence_schema = TRUST_WP_PROOF_EVIDENCE_SCHEMA_VERSION,
        replay_schema = TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
        bundle = bundle.bundle_id.as_str(),
        obligation_id = obligation.obligation_id.as_str(),
        kind = obligation_kind_label(&obligation.kind),
        function = bundle_subject_label(bundle),
        predicate = replay.normalized_predicate.as_str(),
        summary_count = summary_facts.len(),
        summary_digest = summary_digest_line.as_str(),
    );
    let normalized_hash = stable_digest(&normalized_material);
    let replay_material = format!(
        "api={api}\nevidence-schema={evidence_schema}\nreplay-schema={replay_schema}\nnormalized-digest={algorithm}:{value}\nsummary-digest={summary_digest}\nsteps=\n{steps}\n",
        api = API_VERSION,
        evidence_schema = TRUST_WP_PROOF_EVIDENCE_SCHEMA_VERSION,
        replay_schema = TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
        algorithm = normalized_hash.algorithm.as_str(),
        value = normalized_hash.value.as_str(),
        summary_digest = summary_digest_line.as_str(),
        steps = replay
            .steps
            .iter()
            .map(TrustWpNativeReplayStep::as_wire_line)
            .collect::<Vec<_>>()
            .join("\n"),
    );
    let replay_hash = stable_digest(&replay_material);
    let mut artifacts = vec![EvidenceArtifact {
        kind: EvidenceArtifactKind::NormalizedObligation,
        uri: stable_artifact_uri(EvidenceArtifactKind::NormalizedObligation, &normalized_hash),
        hash: normalized_hash,
        materialization: None,
    }];
    if let Some(summary_artifact) = summary_artifact {
        artifacts.push(summary_artifact);
    }
    artifacts.push(EvidenceArtifact {
        kind: EvidenceArtifactKind::ReplayLog,
        uri: stable_artifact_uri(EvidenceArtifactKind::ReplayLog, &replay_hash),
        hash: replay_hash,
        materialization: None,
    });
    let evidence_hash = stable_digest(&evidence_manifest_material(&artifacts));

    ExpectedNativeReplayMetadata {
        evidence_id: format!("trust-wp:replay:{}:{}", bundle.bundle_id, obligation.obligation_id),
        artifacts,
        evidence_bundle_hash: format!("{}:{}", evidence_hash.algorithm, evidence_hash.value),
    }
}

fn evidence_manifest_material(artifacts: &[EvidenceArtifact]) -> String {
    let mut material = format!(
        "api={api}\nevidence-schema={evidence_schema}\nformat={format}\nstrength=sound\nchecker={checker}\nartifact-count={artifact_count}\n",
        api = API_VERSION,
        evidence_schema = TRUST_WP_PROOF_EVIDENCE_SCHEMA_VERSION,
        format = TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
        checker = TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
        artifact_count = artifacts.len(),
    );
    for (index, artifact) in artifacts.iter().enumerate() {
        let _ = writeln!(
            material,
            "artifact.{index}.kind={kind}\nartifact.{index}.digest={algorithm}:{value}",
            kind = artifact_kind_label(artifact.kind),
            algorithm = artifact.hash.algorithm,
            value = artifact.hash.value
        );
    }
    material
}

fn validate_summary_facts(summary_facts: &[SummaryFact]) -> Result<(), String> {
    let mut ids = std::collections::BTreeSet::new();
    for fact in summary_facts {
        if !ids.insert(fact.id.as_str()) {
            return Err(format!("duplicate trust_wp summary fact id `{}`", fact.id));
        }
        if !fact.is_replay_addressable() {
            return Err(format!(
                "trust-wp summary fact `{}` is not replay-addressable under trust.summary-fact.v1",
                fact.id
            ));
        }
    }
    Ok(())
}

fn summary_facts_for_obligation(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<Vec<SummaryFact>, String> {
    let mut summary_facts = obligation.summary_facts.clone();
    for metadata in bundle.metadata.iter().chain(obligation.metadata.iter()) {
        match SummaryFact::from_metadata_entry(metadata) {
            Ok(Some(fact)) => summary_facts.push(fact),
            Ok(None) => {}
            Err(err) => {
                return Err(format!(
                    "invalid trust_wp summary fact metadata `{}`: {err}",
                    metadata.key
                ));
            }
        }
    }
    validate_summary_facts(&summary_facts)?;
    Ok(summary_facts)
}

fn summary_facts_artifact(summary_facts: &[SummaryFact]) -> Option<EvidenceArtifact> {
    (!summary_facts.is_empty()).then(|| {
        let hash = stable_digest(&summary_facts_material(summary_facts));
        EvidenceArtifact {
            kind: EvidenceArtifactKind::SummaryEvidence,
            uri: stable_artifact_uri(EvidenceArtifactKind::SummaryEvidence, &hash),
            hash,
            materialization: None,
        }
    })
}

fn summary_facts_material(summary_facts: &[SummaryFact]) -> String {
    let mut facts = summary_facts.iter().collect::<Vec<_>>();
    facts.sort_by(|left, right| left.id.cmp(&right.id));

    let mut material = format!(
        "api={api}\nevidence-schema={evidence_schema}\nsummary-count={summary_count}\n",
        api = API_VERSION,
        evidence_schema = TRUST_WP_PROOF_EVIDENCE_SCHEMA_VERSION,
        summary_count = facts.len(),
    );
    for (index, fact) in facts.into_iter().enumerate() {
        let _ = writeln!(
            material,
            "summary.{index}.id={id}\nsummary.{index}.producer={producer}\nsummary.{index}.source-crate={source_crate}\nsummary.{index}.source-item={source_item}\nsummary.{index}.kind={kind}\nsummary.{index}.digest={algorithm}:{value}",
            id = fact.id.as_str(),
            producer = fact.producer.as_str(),
            source_crate = fact.source_crate.as_str(),
            source_item = fact.source_item.as_str(),
            kind = fact.kind.as_str(),
            algorithm = fact.digest.algorithm.as_str(),
            value = fact.digest.value.as_str(),
        );
        if let Some((left, right)) = fact.kind.endpoints() {
            let _ =
                writeln!(material, "summary.{index}.left={left}\nsummary.{index}.right={right}");
        }
    }
    material
}

fn stable_digest(material: &str) -> ArtifactHash {
    use sha2::{Digest as _, Sha256};

    let digest = Sha256::digest(material.as_bytes());
    ArtifactHash { algorithm: "sha256".to_string(), value: format!("{digest:x}") }
}

fn stable_artifact_uri(kind: EvidenceArtifactKind, hash: &ArtifactHash) -> String {
    format!("artifact://trust-wp/{}/{}/{}", artifact_kind_label(kind), hash.algorithm, hash.value)
}

fn native_replay_artifact_mismatch_detail(
    expected: &[EvidenceArtifact],
    actual: &[EvidenceArtifact],
) -> String {
    let expected_kinds =
        expected.iter().map(|artifact| artifact.kind).collect::<std::collections::BTreeSet<_>>();
    let actual_kinds =
        actual.iter().map(|artifact| artifact.kind).collect::<std::collections::BTreeSet<_>>();

    let missing = expected_kinds
        .difference(&actual_kinds)
        .copied()
        .map(artifact_kind_label)
        .collect::<Vec<_>>();
    if !missing.is_empty() {
        return format!(
            "candidate trust_wp evidence is missing deterministic native replay artifacts: {}",
            missing.join(", ")
        );
    }

    let unexpected = actual_kinds
        .difference(&expected_kinds)
        .copied()
        .map(artifact_kind_label)
        .collect::<Vec<_>>();
    if !unexpected.is_empty() {
        return format!(
            "candidate trust_wp evidence contains unexpected native replay artifacts: {}",
            unexpected.join(", ")
        );
    }

    let mismatched = expected
        .iter()
        .filter(|expected_artifact| {
            !actual.iter().any(|actual_artifact| actual_artifact == *expected_artifact)
        })
        .map(|artifact| artifact_kind_label(artifact.kind))
        .collect::<Vec<_>>();
    if !mismatched.is_empty() {
        return format!(
            "candidate trust_wp evidence has non-canonical native replay artifact metadata and does not match deterministic typed replay metadata: {}",
            mismatched.join(", ")
        );
    }

    "candidate trust_wp evidence does not match deterministic typed replay metadata".to_string()
}

fn artifact_kind_label(kind: EvidenceArtifactKind) -> &'static str {
    match kind {
        EvidenceArtifactKind::NormalizedObligation => "normalized-obligation",
        EvidenceArtifactKind::ReplayLog => "replay-log",
        EvidenceArtifactKind::ProofCertificate => "proof-certificate",
        EvidenceArtifactKind::ProofReplayTrace => "proof-replay-trace",
        EvidenceArtifactKind::ProofCheckReport => "proof-check-report",
        EvidenceArtifactKind::EngineInput => "engine-input",
        EvidenceArtifactKind::SolverQuery => "solver-query",
        EvidenceArtifactKind::SolverProof => "solver-proof",
        EvidenceArtifactKind::SolverTranscript => "solver-transcript",
        EvidenceArtifactKind::Model => "model",
        EvidenceArtifactKind::Counterexample => "counterexample",
        EvidenceArtifactKind::Log => "log",
        EvidenceArtifactKind::Report => "report",
        EvidenceArtifactKind::DscanAttestation => "dscan-attestation",
        EvidenceArtifactKind::DpubManifest => "dpub-manifest",
        EvidenceArtifactKind::BuildManifest => "build-manifest",
        EvidenceArtifactKind::SummaryEvidence => "summary-evidence",
        _ => "unknown",
    }
}

fn obligation_kind_label(kind: &ObligationKind) -> String {
    match kind {
        ObligationKind::Precondition => "precondition".to_string(),
        ObligationKind::Postcondition => "postcondition".to_string(),
        ObligationKind::LoopInvariant => "loop-invariant".to_string(),
        ObligationKind::Refinement => "refinement".to_string(),
        ObligationKind::Termination => "termination".to_string(),
        other => format!("{other:?}"),
    }
}

fn bundle_subject_label(bundle: &TrustContractBundle) -> String {
    match &bundle.subject {
        trust_verifier_api::BundleSubject::Function { path, .. } => path.clone(),
        trust_verifier_api::BundleSubject::Crate { name } => name.clone(),
        trust_verifier_api::BundleSubject::Artifact { name, kind } => format!("{kind}:{name}"),
        _ => "unknown".to_string(),
    }
}

#[cfg(not(feature = "trust-build"))]
fn native_replay_counterexample(
    obligation: &TrustObligation,
    predicate: &TrustWpPureExprV1,
) -> Counterexample {
    Counterexample {
        format: "trust_wp.native-pure-replay.counterexample.v1".to_string(),
        data: serde_json::json!({
            "obligation_id": obligation.obligation_id.as_str(),
            "predicate": predicate.stable_text(),
            "reason": "typed predicate evaluated to false in the native pure replay fragment",
        }),
    }
}

/// Obligation kinds owned by the current trust_wp native replay adapter.
#[must_use]
pub fn trust_wp_owned_obligation_kinds() -> [ObligationKind; 5] {
    [
        ObligationKind::Precondition,
        ObligationKind::Postcondition,
        ObligationKind::LoopInvariant,
        ObligationKind::Refinement,
        ObligationKind::Termination,
    ]
}

/// Returns true for obligations trust-wp's current replay schema can prove natively.
#[must_use]
pub fn is_trust_wp_owned_obligation_kind(kind: &ObligationKind) -> bool {
    matches!(
        kind,
        ObligationKind::Precondition
            | ObligationKind::Postcondition
            | ObligationKind::LoopInvariant
            | ObligationKind::Refinement
            | ObligationKind::Termination
    )
}

fn is_auto_lowered_contract_obligation_kind(kind: &ObligationKind) -> bool {
    matches!(
        kind,
        ObligationKind::Precondition
            | ObligationKind::Postcondition
            | ObligationKind::LoopInvariant
    )
}

#[cfg(test)]
mod tests {

    #[cfg(feature = "trust-build")]
    #[test]
    fn pure_expr_stable_text_parses_contract_fragment() {
        // The def-site requires shape: variable-bearing comparison.
        let e = parse_pure_expr_text("(lo <= hi)").expect("parse");
        assert_eq!(e.stable_text(), "(lo <= hi)");
        assert_eq!(e.sort(), Some(TrustWpPureSortV1::Bool));
        // Vars stay unevaluable — constant-fold replay fail-closed.
        assert!(eval_value(&e).is_none());

        // Implication claim shape, right-assoc, boolean var coercion.
        let e = parse_pure_expr_text("((lo <= hi) && flag) ==> (lo <= hi)").expect("parse");
        assert_eq!(e.sort(), Some(TrustWpPureSortV1::Bool));
        assert_eq!(e.stable_text(), "(((lo <= hi) && flag) ==> (lo <= hi))");

        // Negative literals + opaque SSA-style identifiers (arithmetic-free;
        // subtraction is refused by the #29 amendment-1 gate — see
        // `pure_expr_stable_text_refuses_arithmetic`).
        let e = parse_pure_expr_text("(x_s0_1 >= -5)").expect("parse");
        assert_eq!(e.sort(), Some(TrustWpPureSortV1::Bool));

        // Ground predicates still constant-fold exactly (arithmetic-free).
        let e = parse_pure_expr_text("3 <= 3").expect("parse");
        assert_eq!(eval_value(&e), Some(TrustWpPureValue::Bool(true)));

        // Implies round-trips through its own stable text (the "==>"
        // spelling first-party parse_contract accepts).
        let e = parse_pure_expr_text("true ==> false").expect("parse");
        let round = parse_pure_expr_text(&e.stable_text()).expect("round-trip");
        assert_eq!(e, round);
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn pure_expr_bool_variable_stable_text_preserves_downstream_sort() {
        let var = |name: &str| TrustWpPureExprV1::Var {
            name: name.to_string(),
            sort: TrustWpPureSortV1::Bool,
        };
        let cases = [
            (var("flag"), "flag", "(flag == true)"),
            (
                TrustWpPureExprV1::Not { expr: Box::new(var("flag")) },
                "(! flag)",
                "(! (flag == true))",
            ),
            (
                TrustWpPureExprV1::Binary {
                    op: TrustWpPureBinaryOpV1::And,
                    lhs: Box::new(var("flag")),
                    rhs: Box::new(var("ready")),
                },
                "(flag && ready)",
                "((flag == true) && (ready == true))",
            ),
            (
                TrustWpPureExprV1::Binary {
                    op: TrustWpPureBinaryOpV1::Eq,
                    lhs: Box::new(var("flag")),
                    rhs: Box::new(TrustWpPureExprV1::Bool { value: true }),
                },
                "(flag == true)",
                "(flag == true)",
            ),
            (
                TrustWpPureExprV1::Binary {
                    op: TrustWpPureBinaryOpV1::Eq,
                    lhs: Box::new(var("flag")),
                    rhs: Box::new(var("ready")),
                },
                "((flag == true) == (ready == true))",
                "((flag == true) == (ready == true))",
            ),
            (
                TrustWpPureExprV1::Binary {
                    op: TrustWpPureBinaryOpV1::Ne,
                    lhs: Box::new(var("flag")),
                    rhs: Box::new(var("ready")),
                },
                "((flag == true) != (ready == true))",
                "((flag == true) != (ready == true))",
            ),
            (
                TrustWpPureExprV1::Not {
                    expr: Box::new(TrustWpPureExprV1::Binary {
                        op: TrustWpPureBinaryOpV1::Eq,
                        lhs: Box::new(var("flag")),
                        rhs: Box::new(var("ready")),
                    }),
                },
                "(! ((flag == true) == (ready == true)))",
                "(! ((flag == true) == (ready == true)))",
            ),
        ];
        for (expr, canonical, wire) in cases {
            assert_eq!(expr.stable_text(), canonical);
            assert_eq!(expr.native_replay_text(), wire);
            let canonical_expr = canonicalize_trust_wp_pure_expr(expr.clone());
            assert_eq!(
                canonicalize_trust_wp_pure_expr(canonical_expr.clone()),
                canonical_expr,
                "typed Bool equality canonicalization must be idempotent"
            );
            let canonical_round = parse_pure_expr_text(canonical).unwrap_or_else(|error| {
                panic!("canonical Bool stable text must reparse: {canonical}: {error}")
            });
            assert_eq!(canonical_round, canonical_expr);
            let expected_digest = NativeTrustWpClaim::TrustWpPureExprV1(canonical_expr.clone())
                .diagnostic_digest()
                .expect("public Bool claim hashes");
            for claim_view in [canonical_round.clone(), parse_pure_expr_text(canonical).unwrap()] {
                assert_eq!(
                    NativeTrustWpClaim::TrustWpPureExprV1(claim_view)
                        .diagnostic_digest()
                        .expect("native/replay Bool claim hashes"),
                    expected_digest,
                    "public, native, and replay canonical identities agree for {canonical}",
                );
            }
            let wire_round = parse_pure_expr_text(wire).unwrap_or_else(|error| {
                panic!("final Bool sibling text must reparse: {wire}: {error}")
            });
            assert_eq!(wire_round.sort(), Some(TrustWpPureSortV1::Bool));

            let probe = trust_wp_core::verify_bundle::BundleObligation::new(
                "bool-wire-round-trip",
                trust_wp_core::verify_bundle::BundleObligationKind::Postcondition,
                "demo::bool_wire_round_trip",
                trust_wp_core::verify_bundle::BundleClaim::new(
                    trust_wp_core::verify_bundle::BundleClaimFormat::TrustWpPureExprV1,
                    wire,
                ),
            );
            trust_wp_core::verify_bundle::native_predicate_for_obligation(&probe)
                .expect("final Bool wire text survives the sibling's exact native decoder");
        }
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn pure_expr_stable_text_fails_closed_outside_fragment() {
        for bad in [
            "x * y",       // multiplication not in the fragment
            "f(x)",        // calls
            "x[0]",        // indexing
            "1 <=",        // truncated
            "(lo <= hi",   // unbalanced
            "42",          // non-boolean top level
            "x ==> 1",     // non-boolean implies rhs
            "x && x >= 0", // one stable-text name cannot have Bool and Int sorts
        ] {
            assert!(parse_pure_expr_text(bad).is_err(), "must fail closed on `{bad}`");
        }
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn pure_expr_stable_text_refuses_arithmetic() {
        // Trust (#29): the additive fragment is a false-proof vector — the
        // sibling's linear-int rule proves free-variable Int tautologies that
        // are false under machine wrapping semantics. Each must fail closed,
        // never lowering to a bare Int claim, and cite the counterexample +
        // blueprint amendment.
        for taut in ["(x + 1) > x", "(x - 1) < x", "x + 1 >= x", "-x < 0"] {
            let err = parse_pure_expr_text(taut).unwrap_err();
            assert!(
                err.contains("u64::MAX") && err.contains("amendment 1"),
                "arithmetic refusal must cite counterexample + blueprint for `{taut}`: {err}"
            );
        }

        // The JSON-deserialize sub-path of the same lane must ALSO refuse an
        // Add-bearing predicate at the decode choke point (it bypasses the
        // stable-text parser gate above).
        let json_add = serde_json::to_string(&TrustWpPureExprV1::Binary {
            op: TrustWpPureBinaryOpV1::Gt,
            lhs: Box::new(TrustWpPureExprV1::Binary {
                op: TrustWpPureBinaryOpV1::Add,
                lhs: Box::new(TrustWpPureExprV1::Var {
                    name: "x".to_string(),
                    sort: TrustWpPureSortV1::Int,
                }),
                rhs: Box::new(TrustWpPureExprV1::Int { value: 1 }),
            }),
            rhs: Box::new(TrustWpPureExprV1::Var {
                name: "x".to_string(),
                sort: TrustWpPureSortV1::Int,
            }),
        })
        .expect("serialize");
        assert!(
            decode_trust_ir_trust_wp_pure_expr_payload(&json_add).is_err(),
            "JSON-encoded arithmetic must be refused at the decode choke point"
        );

        for invalid_name in ["true", "forall", "if", "x.field", "x#s1", "true) || true || (false"] {
            let json = serde_json::to_string(&TrustWpPureExprV1::Binary {
                op: TrustWpPureBinaryOpV1::Eq,
                lhs: Box::new(TrustWpPureExprV1::Var {
                    name: invalid_name.to_string(),
                    sort: TrustWpPureSortV1::Bool,
                }),
                rhs: Box::new(TrustWpPureExprV1::Bool { value: false }),
            })
            .expect("typed expression serializes");
            let error = decode_trust_ir_trust_wp_pure_expr_payload(&json)
                .expect_err("raw TrustIr JSON variables must not change meaning in stable text");
            assert!(error.contains("variable name"), "{invalid_name}: {error}");
        }

        // Regression: non-arithmetic predicates through the same lane are
        // unaffected — a variable-bearing comparison and a negative literal
        // still parse to a boolean claim.
        let ok = parse_pure_expr_text("(x >= y)").expect("non-arithmetic comparison parses");
        assert_eq!(ok.sort(), Some(TrustWpPureSortV1::Bool));
        let neg_lit = parse_pure_expr_text("x >= -5").expect("negative literal parses");
        assert_eq!(neg_lit.sort(), Some(TrustWpPureSortV1::Bool));
        let min = parse_pure_expr_text("x >= -9223372036854775808")
            .expect("the full i64 negative-literal boundary parses without positive overflow");
        assert_eq!(min.sort(), Some(TrustWpPureSortV1::Bool));
        let max = parse_pure_expr_text("x <= 9223372036854775807")
            .expect("the full i64 positive-literal boundary parses");
        assert_eq!(max.sort(), Some(TrustWpPureSortV1::Bool));
        assert!(
            parse_pure_expr_text("x >= -9223372036854775809").is_err(),
            "values below i64::MIN still fail closed"
        );
        assert!(
            parse_pure_expr_text("x <= 9223372036854775808").is_err(),
            "values above i64::MAX still fail closed"
        );

        use trust_wp_core::verify_bundle::{
            BundleClaim, BundleClaimFormat, BundleObligation, BundleObligationKind,
            native_predicate_for_obligation,
        };
        let probe = |payload: &str| {
            BundleObligation::new(
                "signed-boundary",
                BundleObligationKind::Postcondition,
                "demo::signed_boundary",
                BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, payload),
            )
        };
        for payload in ["x >= -9223372036854775808", "x <= 9223372036854775807"] {
            native_predicate_for_obligation(&probe(payload))
                .unwrap_or_else(|error| panic!("sibling must decode {payload}: {error:?}"));
        }
        for payload in ["x >= -9223372036854775809", "x <= 9223372036854775808"] {
            assert!(
                native_predicate_for_obligation(&probe(payload)).is_err(),
                "sibling must reject out-of-i64 literal: {payload}"
            );
        }
    }

    use trust_verifier_api::{
        BundleSubject, ContractKind, ContractPredicate, MetadataEntry, ProofStrength,
        SourceLocation, SummaryFactKind, TrustContract, TrustSpecBinaryOp, TrustSpecExpr,
        TrustSpecPredicate, TrustSpecVariable, TrustSpecVariableOrigin, VerificationRunStatus,
        VerifierExecutionContext,
    };

    use super::*;

    fn obligation(kind: ObligationKind, id: &str) -> TrustObligation {
        TrustObligation {
            obligation_id: id.to_string(),
            kind,
            contract_id: Some(format!("contract-{id}")),
            proof_item_id: None,
            source: SourceLocation::default(),
            description: format!("prove {id}"),
            required_strength: Some(ProofStrength::deductive()),
            summary_facts: Vec::new(),
            metadata: Vec::new(),
        }
    }

    fn bundle_with(obligations: Vec<TrustObligation>) -> TrustContractBundle {
        let mut bundle = TrustContractBundle::empty(
            "bundle-trust-wp",
            BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::deductive".to_string(),
            },
        );
        bundle.contracts.push(TrustContract {
            contract_id: "contract-post".to_string(),
            kind: ContractKind::Ensures,
            predicate: ContractPredicate::TrustExpr { text: "result >= x".to_string() },
            source: SourceLocation::default(),
            metadata: vec![MetadataEntry {
                key: "rust.attr".to_string(),
                value: "#[ensures(result >= x)]".to_string(),
            }],
        });
        bundle.metadata.push(MetadataEntry {
            key: "trust_wp.inferred.summary.present".to_string(),
            value: "true".to_string(),
        });
        bundle.obligations = obligations;
        bundle
    }

    fn typed_expr(value: bool) -> TrustWpPureExprV1 {
        TrustWpPureExprV1::Binary {
            op: TrustWpPureBinaryOpV1::Eq,
            // Trust (#29): keep the generic true/false fixture inside the
            // arithmetic-free direct-contract fragment. Arithmetic refusal is
            // exercised by dedicated counterexample tests below.
            lhs: Box::new(TrustWpPureExprV1::Int { value: 2 }),
            rhs: Box::new(TrustWpPureExprV1::Int { value: if value { 2 } else { 3 } }),
        }
    }

    #[cfg(any(
        not(feature = "trust-build"),
        all(feature = "trust-build", trust_wp_proof_transport_api)
    ))]
    fn trust_formula_value(value: bool) -> serde_json::Value {
        serde_json::json!({
            "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
            "body": {"bool": value},
        })
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    // Trust (#29): this ground-true predicate deliberately contains NO
    // arithmetic — the amendment-1 bare-claim fragment refuses
    // Add/Sub/Mul/Div/Mod/Neg, so the former `(1 + 1) == 2` shape would now
    // fail closed instead of exercising the proof-grade evidence path.
    fn trust_spec_true_predicate() -> TrustSpecPredicate {
        TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Eq,
                TrustSpecExpr::int_literal("2"),
                TrustSpecExpr::int_literal("2"),
            ),
            Vec::new(),
        )
    }

    fn trust_spec_result_predicate() -> TrustSpecPredicate {
        TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Ge,
                TrustSpecExpr::result(trust_verifier_api::TrustSpecSort::Int),
                TrustSpecExpr::variable("x", trust_verifier_api::TrustSpecSort::Int),
            ),
            vec![TrustSpecVariable {
                name: "x".to_string(),
                sort: trust_verifier_api::TrustSpecSort::Int,
                origin: TrustSpecVariableOrigin::Local { index: 0 },
            }],
        )
    }

    // Trust (#29): guarded div/mod USED to lower into the bare TrustFormulaV1
    // claim; the amendment-1 arithmetic refusal now fails it closed like every
    // other arithmetic operator (a nonzero-divisor guard removes the
    // div-by-zero hazard but not the Int-vs-machine-semantics hazard). This
    // test now pins the refusal.
    #[test]
    fn trust_spec_predicate_trust_formula_payload_refuses_guarded_div_and_mod() {
        let int_sort = trust_verifier_api::TrustSpecSort::Int;
        let numerator = TrustSpecExpr::variable("numerator", int_sort);
        let denominator = TrustSpecExpr::variable("denominator", int_sort);
        let divisor_nonzero = TrustSpecExpr::binary(
            TrustSpecBinaryOp::Ne,
            denominator.clone(),
            TrustSpecExpr::int_literal("0"),
        );
        let quotient_matches = TrustSpecExpr::binary(
            TrustSpecBinaryOp::Eq,
            TrustSpecExpr::result(int_sort),
            TrustSpecExpr::binary(TrustSpecBinaryOp::Div, numerator.clone(), denominator.clone()),
        );
        let remainder_nonnegative = TrustSpecExpr::binary(
            TrustSpecBinaryOp::Ge,
            TrustSpecExpr::binary(TrustSpecBinaryOp::Mod, numerator.clone(), denominator.clone()),
            TrustSpecExpr::int_literal("0"),
        );
        let predicate = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::And,
                divisor_nonzero,
                TrustSpecExpr::binary(
                    TrustSpecBinaryOp::And,
                    quotient_matches,
                    remainder_nonnegative,
                ),
            ),
            vec![
                TrustSpecVariable {
                    name: "numerator".to_string(),
                    sort: int_sort,
                    origin: TrustSpecVariableOrigin::Local { index: 0 },
                },
                TrustSpecVariable {
                    name: "denominator".to_string(),
                    sort: int_sort,
                    origin: TrustSpecVariableOrigin::Local { index: 1 },
                },
            ],
        );

        let err = trust_spec_predicate_to_trust_formula_payload(&predicate)
            .expect_err("guarded div/mod arithmetic must fail closed (amendment 1)");

        assert!(err.contains("arithmetic operator"), "{err}");
        assert!(err.contains("false at u64::MAX"), "{err}");
    }

    #[test]
    fn trust_spec_predicate_trust_formula_payload_rejects_unguarded_div_and_mod() {
        let int_sort = trust_verifier_api::TrustSpecSort::Int;
        let numerator = TrustSpecExpr::variable("numerator", int_sort);
        let denominator = TrustSpecExpr::variable("denominator", int_sort);
        let predicate = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Eq,
                TrustSpecExpr::result(int_sort),
                TrustSpecExpr::binary(TrustSpecBinaryOp::Mod, numerator, denominator),
            ),
            vec![
                TrustSpecVariable {
                    name: "numerator".to_string(),
                    sort: int_sort,
                    origin: TrustSpecVariableOrigin::Local { index: 0 },
                },
                TrustSpecVariable {
                    name: "denominator".to_string(),
                    sort: int_sort,
                    origin: TrustSpecVariableOrigin::Local { index: 1 },
                },
            ],
        );

        let err = trust_spec_predicate_to_trust_formula_payload(&predicate)
            .expect_err("unguarded modulo must fail closed before native replay");

        assert!(err.contains("divisor must"), "{err}");
    }

    #[test]
    fn trust_spec_predicate_trust_formula_payload_rejects_arrays_before_scalar_emission() {
        let array_sort = trust_verifier_api::TrustSpecSort::Array {
            element: trust_verifier_api::TrustSpecScalarSort::Int,
        };
        let predicate = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Eq,
                TrustSpecExpr::index(
                    TrustSpecExpr::variable("items", array_sort),
                    TrustSpecExpr::int_literal("0"),
                    trust_verifier_api::TrustSpecSort::Int,
                ),
                TrustSpecExpr::int_literal("7"),
            ),
            vec![TrustSpecVariable {
                name: "items".to_string(),
                sort: array_sort,
                origin: TrustSpecVariableOrigin::Local { index: 0 },
            }],
        );

        predicate.validate().expect("read-only array predicate is valid public TrustSpec IR");
        let err = trust_spec_predicate_to_trust_formula_payload(&predicate)
            .expect_err("arrays must not be flattened into scalar TrustFormulaV1 claims");

        assert!(err.contains("array sort is outside"), "{err}");
    }

    #[test]
    fn trust_spec_predicate_trust_formula_payload_rejects_floats_before_scalar_emission() {
        // IEEE-754 comparisons (NaN is unordered, +0.0 == -0.0) have no
        // faithful replay in the scalar int/bool fragment; a float-sorted
        // predicate must fail closed before any TrustFormulaV1 claim is
        // serialized, exactly like the array rejection above.
        let f64_sort = trust_verifier_api::TrustSpecSort::Float { eb: 11, sb: 53 };
        let predicate = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Ge,
                TrustSpecExpr::variable("x", f64_sort),
                TrustSpecExpr::float_literal((-1.0e30_f64).to_bits(), 11, 53),
            ),
            vec![TrustSpecVariable {
                name: "x".to_string(),
                sort: f64_sort,
                origin: TrustSpecVariableOrigin::Local { index: 1 },
            }],
        );

        predicate.validate().expect("float comparison predicate is valid public TrustSpec IR");
        let err = trust_spec_predicate_to_trust_formula_payload(&predicate)
            .expect_err("floats must not be replayed through scalar TrustFormulaV1 claims");

        assert!(err.contains("float sort is outside"), "{err}");
    }

    // Trust (#29, falsification): the confirmed false-proof shapes —
    // free-variable machine-arithmetic Int tautologies — must REFUSE in the
    // bare-claim lowering. `result + 1 > result` and `result - 1 < result`
    // are provable over unbounded Int (the sibling's linear-int rule accepts
    // them) but false at `u64::MAX` / `0u64` under wrapping machine
    // semantics; before this gate the native trust-wp lane reported them
    // "verified". Blueprint amendment 1.
    #[test]
    fn trust_spec_predicate_trust_formula_payload_refuses_arithmetic_int_tautologies() {
        let int_sort = trust_verifier_api::TrustSpecSort::Int;
        let shapes = [
            (
                "add",
                TrustSpecExpr::binary(
                    TrustSpecBinaryOp::Gt,
                    TrustSpecExpr::binary(
                        TrustSpecBinaryOp::Add,
                        TrustSpecExpr::result(int_sort),
                        TrustSpecExpr::int_literal("1"),
                    ),
                    TrustSpecExpr::result(int_sort),
                ),
            ),
            (
                "sub",
                TrustSpecExpr::binary(
                    TrustSpecBinaryOp::Lt,
                    TrustSpecExpr::binary(
                        TrustSpecBinaryOp::Sub,
                        TrustSpecExpr::result(int_sort),
                        TrustSpecExpr::int_literal("1"),
                    ),
                    TrustSpecExpr::result(int_sort),
                ),
            ),
        ];
        for (op, root) in shapes {
            let predicate = TrustSpecPredicate::new(root, Vec::new());
            let err = trust_spec_predicate_to_trust_formula_payload(&predicate)
                .expect_err("machine-arithmetic Int tautology must fail closed (amendment 1)");
            assert!(err.contains(&format!("arithmetic operator `{op}`")), "{op}: {err}");
            assert!(err.contains("false at u64::MAX"), "{op}: {err}");
        }
    }

    // Trust (#29, falsification): unary negation is arithmetic too.
    #[test]
    fn trust_spec_predicate_trust_formula_payload_refuses_unary_neg() {
        let int_sort = trust_verifier_api::TrustSpecSort::Int;
        let predicate = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Le,
                TrustSpecExpr::unary(TrustSpecUnaryOp::Neg, TrustSpecExpr::result(int_sort)),
                TrustSpecExpr::result(int_sort),
            ),
            Vec::new(),
        );
        let err = trust_spec_predicate_to_trust_formula_payload(&predicate)
            .expect_err("unary negation must fail closed (amendment 1)");
        assert!(err.contains("arithmetic operator `neg`"), "{err}");
    }

    fn summary_fact(id: &str, digest: &str) -> SummaryFact {
        SummaryFact::new(
            id,
            "TrustIr",
            "dep_crate",
            "dep_crate::callee",
            SummaryFactKind::PointerProvenanceEq { left: "p".to_string(), right: "q".to_string() },
            ArtifactHash { algorithm: "sha256".to_string(), value: digest.to_string() },
        )
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    fn native_artifact_metadata(kind: &ObligationKind, mode: &str) -> Vec<MetadataEntry> {
        use trust_wp_core::verify_bundle::{
            BundleDigest, BundleNativeReplayIdentity, BundleNativeToolIdentity,
            BundleTmirObligationCause, BundleTmirObligationSource, BundleTmirSourceSpan,
        };

        fn entry<T: serde::Serialize>(key: &str, value: &T) -> MetadataEntry {
            MetadataEntry {
                key: key.to_string(),
                value: serde_json::to_string(value).expect("test metadata serializes"),
            }
        }

        let cause = match kind {
            ObligationKind::Precondition => BundleTmirObligationCause::Precondition,
            ObligationKind::Postcondition => BundleTmirObligationCause::Postcondition,
            ObligationKind::LoopInvariant => BundleTmirObligationCause::Other("loop".to_string()),
            _ => BundleTmirObligationCause::Other("native-test".to_string()),
        };

        vec![
            MetadataEntry {
                key: TRUST_WP_NATIVE_ORIGIN_METADATA_KEY.to_string(),
                value: serde_json::json!({
                    // Canonical `tmir.` prefix: trust-wp-core only applies its
                    // strict native-origin validation under this spelling.
                    "schema": "tmir.native-verification-bundle.v2",
                    "mode": mode,
                    "request_id": 7,
                    "function_id": 11,
                    "obligation_id": 13,
                    "lineage_roots": [3],
                    // Wire field name pinned to trust-wp-core's canonical
                    // `BundleNativeOrigin` serde layout (`tmir_module_digest`).
                    "tmir_module_digest": {
                        "algorithm": "sha256",
                        "value": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                    }
                })
                .to_string(),
            },
            entry(TRUST_WP_TMIR_SOURCE_SPAN_METADATA_KEY, &BundleTmirSourceSpan::new(4, 29, 7)),
            entry(
                TRUST_WP_NATIVE_VERIFIER_METADATA_KEY,
                &BundleNativeToolIdentity::new("trust-wp")
                    .with_version("native-schema-v2")
                    .with_revision("6dfb614"),
            ),
            entry(
                TRUST_WP_NATIVE_REPLAY_METADATA_KEY,
                &BundleNativeReplayIdentity::new(
                    "trust-wp-core.native-pure-replay",
                    "trust-wp-test",
                    BundleDigest::new(
                        "sha256",
                        "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
                    ),
                ),
            ),
            entry(
                TRUST_WP_NATIVE_SOLVER_METADATA_KEY,
                &BundleNativeToolIdentity::new("ay").with_version("0.9.0"),
            ),
            entry(
                TRUST_WP_TMIR_OBLIGATION_SOURCE_METADATA_KEY,
                &BundleTmirObligationSource::new(cause).with_function_id(11),
            ),
        ]
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    fn with_native_artifact_metadata(
        mut obligation: TrustObligation,
        mode: &str,
    ) -> TrustObligation {
        obligation.metadata.extend(native_artifact_metadata(&obligation.kind, mode));
        obligation
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api,
        trust_wp_typed_metadata_helper_api
    ))]
    #[test]
    fn trust_ir_trust_wp_request_produces_structured_native_replay_metadata() {
        fn metadata_json(entries: &[MetadataEntry], key: &str) -> serde_json::Value {
            let entry = entries.iter().find(|entry| entry.key == key).unwrap_or_else(|| {
                panic!("metadata entry `{key}` should be emitted through trust_wp helper")
            });
            serde_json::from_str(&entry.value).expect("metadata value is typed JSON")
        }

        let proof_id = trust_ir::ProofId::new(2);
        let function_id = trust_ir::FuncId::new(0);
        let root = trust_ir::ProofLineageId::new(0);
        let source_digest = trust_ir::ProofDigest::sha256([0x11; 32]);
        let trust_ir_digest = trust_ir::ProofDigest::sha256([0xaa; 32]);
        let transcript_digest = trust_ir::ProofDigest::sha256([0xbb; 32]);
        let span = trust_ir::SourceSpan { file: 4, line: 29, col: 7 };
        let formula = trust_ir::ProofFormula::new("TrustWpPureExprV1", "true");

        let mut module = trust_ir::Module::new("trust-wp-native-metadata-test");
        let func_ty = module.add_func_type(trust_ir::FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
        });
        module.add_function(trust_ir::Function::new(
            function_id,
            "demo::postcondition",
            func_ty,
            trust_ir::BlockId::new(0),
        ));
        module.proof_obligations.push(
            trust_ir::ProofObligation::new(
                proof_id,
                trust_ir::ObligationKind::Postcondition,
                trust_ir::ProofStatus::Pending,
                "prove structured trust_wp metadata",
            )
            .with_formula(formula.clone()),
        );

        let mut lineage_node = trust_ir::ProofLineageNode::new(
            root,
            trust_ir::ProofTransform::new(
                trust_ir::ProofTransformStage::Frontend,
                "rustc-mir-to-trust_ir",
                "Trust",
                "native-request-schema-v1",
            ),
            source_digest,
            trust_ir_digest,
        );
        lineage_node.obligations.push(proof_id);
        let lineage = trust_ir::ProofLineageManifest {
            schema_version: trust_ir::ProofLineageManifest::SCHEMA_VERSION,
            nodes: vec![lineage_node],
            roots: vec![root],
        };
        let mut native_bundle = trust_ir::NativeVerificationBundle::new(
            trust_ir::NativeBundleProducer::TRust,
            trust_ir::NativeAdapterInput::RustMir { body_digest: source_digest },
            trust_ir_digest,
            module,
            lineage,
        );
        native_bundle.compiler_facts.obligation_sources.push(trust_ir::NativeObligationSource {
            obligation: proof_id,
            public_obligation_id: "vc:trust-wp:structured-metadata:0".to_string(),
            function: Some(function_id),
            span: Some(span),
            assertion_id: Some(trust_ir::NativeAssertionId::new(42)),
            cause: trust_ir::NativeObligationCause::Postcondition,
            monomorphization: None,
            facts: Vec::new(),
        });

        let request = trust_ir::TrustWpNativeRequest {
            id: trust_ir::NativeRequestId::new(7),
            mode: trust_ir::TrustWpVerificationMode::WeakestPrecondition,
            function: function_id,
            obligations: vec![proof_id],
            lineage_roots: vec![root],
            options: trust_ir::TrustWpRequestOptions::default(),
            diagnostics: trust_ir::NativeDiagnosticsPolicy::default(),
            provenance: trust_ir::NativeRequestProvenance::trust_wp(
                trust_ir::NativeToolIdentity::new("trust-wp")
                    .with_version("native-schema-v2")
                    .with_revision("test-rev"),
            )
            .with_solver(trust_ir::NativeToolIdentity::new("ay").with_version("0.10.0"))
            .with_replay(
                trust_ir::ProofReplayIdentity::new(
                    "trust-wp-core.native-pure-replay",
                    "trust-wp-core native-bundle --wp",
                )
                .with_transcript_digest(transcript_digest),
            )
            .with_replay_context(
                trust_ir::NativeReplayContext::default()
                    .with_atom(
                        trust_ir::NativeReplayAtom::assumption(
                            trust_ir::NativeReplayAtomId::new(2),
                            trust_ir::ProofFormula::new("TrustWpPureExprV1", "true"),
                        )
                        .with_obligation(proof_id)
                        .with_span(span),
                    )
                    .with_atom(
                        trust_ir::NativeReplayAtom::assertion(
                            trust_ir::NativeReplayAtomId::new(3),
                            formula,
                        )
                        .with_obligation(proof_id)
                        .with_assertion_id(trust_ir::NativeAssertionId::new(42))
                        .with_span(span),
                    ),
            ),
        };

        let metadata = trust_wp_native_replay_metadata_entries_from_trust_ir_bundle(
            &native_bundle,
            &request,
            proof_id,
        )
        .expect("trust-wp helper serializes typed native replay metadata");

        for key in TRUST_TRUST_WP_NATIVE_REPLAY_REQUIRED_METADATA_KEYS {
            assert!(
                metadata.iter().any(|entry| entry.key == key),
                "required trust_wp metadata key `{key}` should be present"
            );
        }
        assert!(
            metadata.iter().any(|entry| entry.key == TRUST_TRUST_WP_PROOF_CONTEXT_METADATA_KEY),
            "non-empty replay context should be serialized as structured trust_wp metadata"
        );
        assert_eq!(
            metadata
                .iter()
                .filter(|entry| entry.key == TRUST_TRUST_WP_NATIVE_SOLVER_METADATA_KEY)
                .count(),
            1
        );

        let origin = metadata_json(&metadata, TRUST_TRUST_WP_NATIVE_ORIGIN_METADATA_KEY);
        // Pins the canonical `tmir.native-verification-bundle.` schema prefix:
        // trust-wp-core's strict native-origin validation (placeholder solver
        // and proof-context binding rejection) only fires under this spelling.
        assert_eq!(
            origin["schema"],
            format!(
                "tmir.native-verification-bundle.v{}",
                trust_ir::NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION
            )
        );
        assert_eq!(origin["mode"], "weakest_precondition");
        assert_eq!(origin["request_id"], 7);
        assert_eq!(origin["function_id"], 0);
        assert_eq!(origin["obligation_id"], 2);
        assert_eq!(origin["lineage_roots"], serde_json::json!([0]));
        // Pins the canonical trust-wp-core wire field name for the module
        // digest (`tmir_module_digest`, from `BundleNativeOrigin`'s serde
        // layout), which downstream readers key on.
        assert_eq!(origin["tmir_module_digest"]["algorithm"], "sha256");
        assert_eq!(origin["tmir_module_digest"]["value"], "aa".repeat(32));

        let source_span =
            metadata_json(&metadata, TRUST_TRUST_WP_TRUST_IR_SOURCE_SPAN_METADATA_KEY);
        assert_eq!(source_span["file_id"], 4);
        assert_eq!(source_span["line"], 29);
        assert_eq!(source_span["column"], 7);

        let replay = metadata_json(&metadata, TRUST_TRUST_WP_NATIVE_REPLAY_METADATA_KEY);
        assert_eq!(replay["engine"], "trust-wp-core.native-pure-replay");
        assert_eq!(replay["transcript_digest"]["algorithm"], "sha256");
        assert_eq!(replay["transcript_digest"]["value"], "bb".repeat(32));

        let source =
            metadata_json(&metadata, TRUST_TRUST_WP_TRUST_IR_OBLIGATION_SOURCE_METADATA_KEY);
        assert_eq!(source["cause"], "postcondition");
        assert_eq!(source["function_id"], 0);
        assert_eq!(source["assertion_id"], 42);

        let proof_context = metadata_json(&metadata, TRUST_TRUST_WP_PROOF_CONTEXT_METADATA_KEY);
        assert_eq!(proof_context["assumptions"].as_array().map(Vec::len), Some(1));
        let assumption = &proof_context["assumptions"][0];
        assert_eq!(assumption["index"], 0);
        assert_eq!(assumption["role"], "assumption");
        assert_eq!(assumption["claim"]["format"], "trust_wp_pure_expr_v1");
        assert_eq!(assumption["claim"]["payload"], "true");
        assert_eq!(assumption["native_replay_atom_id"], 2);
        assert_eq!(assumption["native_obligation_id"], 2);
        assert_eq!(assumption["native_span"]["file_id"], 4);
        assert_eq!(assumption["native_span"]["line"], 29);
        assert_eq!(assumption["native_span"]["column"], 7);
        assert_eq!(proof_context["assertions"].as_array().map(Vec::len), Some(1));
        let assertion = &proof_context["assertions"][0];
        assert_eq!(assertion["index"], 1);
        assert_eq!(assertion["role"], "assertion");
        assert_eq!(assertion["claim"]["format"], "trust_wp_pure_expr_v1");
        assert_eq!(assertion["claim"]["payload"], "true");
        assert_eq!(assertion["native_replay_atom_id"], 3);
        assert_eq!(assertion["native_obligation_id"], 2);
        assert_eq!(assertion["native_assertion_id"], 42);
        assert_eq!(assertion["native_span"]["file_id"], 4);
        assert_eq!(assertion["native_span"]["line"], 29);
        assert_eq!(assertion["native_span"]["column"], 7);
    }

    fn typed_bundle(
        obligation: TrustObligation,
        predicate: TrustWpPureExprV1,
    ) -> TrustContractBundle {
        let mut bundle = TrustContractBundle::empty(
            "bundle-trust-wp-typed",
            BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::deductive".to_string(),
            },
        );
        let contract_id = obligation.contract_id.clone().expect("test obligation has contract");
        bundle.contracts.push(TrustContract {
            contract_id,
            kind: match &obligation.kind {
                ObligationKind::Precondition => ContractKind::Requires,
                ObligationKind::LoopInvariant => ContractKind::LoopInvariant,
                ObligationKind::Refinement => ContractKind::Refinement,
                ObligationKind::Termination => ContractKind::Ensures,
                _ => ContractKind::Ensures,
            },
            predicate: ContractPredicate::CanonicalJson {
                schema: TRUST_WP_PURE_EXPR_SCHEMA_VERSION.to_string(),
                value: serde_json::to_value(predicate).expect("typed expr serializes"),
            },
            source: SourceLocation::default(),
            metadata: Vec::new(),
        });
        bundle.obligations = vec![obligation];
        bundle
    }

    fn typed_bundle_with_obligations(
        obligations: Vec<TrustObligation>,
        predicate: TrustWpPureExprV1,
    ) -> TrustContractBundle {
        let mut bundle = TrustContractBundle::empty(
            "bundle-trust-wp-typed-multi",
            BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::deductive".to_string(),
            },
        );
        for obligation in &obligations {
            let contract_id = obligation.contract_id.clone().expect("test obligation has contract");
            bundle.contracts.push(TrustContract {
                contract_id,
                kind: match &obligation.kind {
                    ObligationKind::Precondition => ContractKind::Requires,
                    ObligationKind::LoopInvariant => ContractKind::LoopInvariant,
                    ObligationKind::Refinement => ContractKind::Refinement,
                    ObligationKind::Termination => ContractKind::Ensures,
                    _ => ContractKind::Ensures,
                },
                predicate: ContractPredicate::CanonicalJson {
                    schema: TRUST_WP_PURE_EXPR_SCHEMA_VERSION.to_string(),
                    value: serde_json::to_value(predicate.clone()).expect("typed expr serializes"),
                },
                source: SourceLocation::default(),
                metadata: Vec::new(),
            });
        }
        bundle.obligations = obligations;
        bundle
    }

    #[test]
    fn direct_typed_contract_json_refuses_machine_add_and_sub() {
        let var = || TrustWpPureExprV1::Var { name: "x".to_string(), sort: TrustWpPureSortV1::Int };
        for (op, label) in
            [(TrustWpPureBinaryOpV1::Add, "add"), (TrustWpPureBinaryOpV1::Sub, "sub")]
        {
            let predicate = TrustWpPureExprV1::Binary {
                op: if op == TrustWpPureBinaryOpV1::Add {
                    TrustWpPureBinaryOpV1::Gt
                } else {
                    TrustWpPureBinaryOpV1::Lt
                },
                lhs: Box::new(TrustWpPureExprV1::Binary {
                    op,
                    lhs: Box::new(var()),
                    rhs: Box::new(TrustWpPureExprV1::Int { value: 1 }),
                }),
                rhs: Box::new(var()),
            };
            let contract = TrustContract {
                contract_id: format!("contract-direct-{label}"),
                kind: ContractKind::Ensures,
                predicate: ContractPredicate::CanonicalJson {
                    schema: TRUST_WP_PURE_EXPR_SCHEMA_VERSION.to_string(),
                    value: serde_json::to_value(predicate).expect("typed predicate serializes"),
                },
                source: SourceLocation::default(),
                metadata: Vec::new(),
            };
            let err = typed_trust_wp_claim_from_contract(&contract)
                .expect_err("direct typed ContractPredicate arithmetic must fail closed");
            assert!(err.contains(&format!("arithmetic operator `{label}`")), "{err}");
            assert!(err.contains("u64::MAX"), "{err}");
        }
    }

    #[test]
    fn direct_typed_contract_json_rejects_unknown_fields_and_formula_arithmetic() {
        let unknown_field_contract = TrustContract {
            contract_id: "contract-direct-unknown-field".to_string(),
            kind: ContractKind::Ensures,
            predicate: ContractPredicate::CanonicalJson {
                schema: TRUST_WP_PURE_EXPR_SCHEMA_VERSION.to_string(),
                value: serde_json::json!({
                    "kind": "not",
                    "expr": {"kind": "bool", "value": false, "ignored": true},
                }),
            },
            source: SourceLocation::default(),
            metadata: Vec::new(),
        };
        let error = typed_trust_wp_claim_from_contract(&unknown_field_contract)
            .expect_err("typed PureExpr nodes must reject unknown nested fields");
        assert!(error.contains("unknown field `ignored`"), "{error}");

        for invalid_name in ["true", "forall", "if", "x.field", "x#s1", "true) || true || (false"] {
            let contract = TrustContract {
                contract_id: "contract-direct-ambiguous-variable".to_string(),
                kind: ContractKind::Ensures,
                predicate: ContractPredicate::CanonicalJson {
                    schema: TRUST_WP_PURE_EXPR_SCHEMA_VERSION.to_string(),
                    value: serde_json::to_value(TrustWpPureExprV1::Binary {
                        op: TrustWpPureBinaryOpV1::Eq,
                        lhs: Box::new(TrustWpPureExprV1::Var {
                            name: invalid_name.to_string(),
                            sort: TrustWpPureSortV1::Bool,
                        }),
                        rhs: Box::new(TrustWpPureExprV1::Bool { value: false }),
                    })
                    .expect("typed predicate serializes"),
                },
                source: SourceLocation::default(),
                metadata: Vec::new(),
            };
            let error = typed_trust_wp_claim_from_contract(&contract)
                .expect_err("typed variable names must have one stable-text interpretation");
            assert!(error.contains("variable name"), "{invalid_name}: {error}");
        }
        assert_eq!(
            trust_wp_pure_expr_reject_arithmetic(&TrustWpPureExprV1::Var {
                name: "_x_0_s1".to_string(),
                sort: TrustWpPureSortV1::Int,
            }),
            Ok(()),
            "an opaque SSA-style identifier remains accepted",
        );

        let bool_var =
            || TrustWpPureExprV1::Var { name: "flag".to_string(), sort: TrustWpPureSortV1::Bool };
        let bool_ordering_contract = TrustContract {
            contract_id: "contract-direct-bool-ordering".to_string(),
            kind: ContractKind::Ensures,
            predicate: ContractPredicate::CanonicalJson {
                schema: TRUST_WP_PURE_EXPR_SCHEMA_VERSION.to_string(),
                value: serde_json::to_value(TrustWpPureExprV1::Binary {
                    op: TrustWpPureBinaryOpV1::Lt,
                    lhs: Box::new(bool_var()),
                    rhs: Box::new(bool_var()),
                })
                .expect("typed predicate serializes"),
            },
            source: SourceLocation::default(),
            metadata: Vec::new(),
        };
        let error = typed_trust_wp_claim_from_contract(&bool_ordering_contract)
            .expect_err("Bool ordering is outside the typed PureExpr grammar");
        assert!(error.contains("not boolean"), "{error}");

        let mixed_sort_predicate = TrustWpPureExprV1::Binary {
            op: TrustWpPureBinaryOpV1::And,
            lhs: Box::new(TrustWpPureExprV1::Var {
                name: "x".to_string(),
                sort: TrustWpPureSortV1::Bool,
            }),
            rhs: Box::new(TrustWpPureExprV1::Binary {
                op: TrustWpPureBinaryOpV1::Ge,
                lhs: Box::new(TrustWpPureExprV1::Var {
                    name: "x".to_string(),
                    sort: TrustWpPureSortV1::Int,
                }),
                rhs: Box::new(TrustWpPureExprV1::Int { value: 0 }),
            }),
        };
        let mixed_sort_contract = TrustContract {
            contract_id: "contract-direct-conflicting-variable-sort".to_string(),
            kind: ContractKind::Ensures,
            predicate: ContractPredicate::CanonicalJson {
                schema: TRUST_WP_PURE_EXPR_SCHEMA_VERSION.to_string(),
                value: serde_json::to_value(mixed_sort_predicate.clone())
                    .expect("typed predicate serializes"),
            },
            source: SourceLocation::default(),
            metadata: Vec::new(),
        };
        let error = typed_trust_wp_claim_from_contract(&mixed_sort_contract)
            .expect_err("one typed variable name cannot carry conflicting sorts");
        assert!(error.contains("conflicting sorts"), "{error}");

        #[cfg(feature = "trust-build")]
        {
            let formula = trust_ir::ProofFormula::new(
                TRUST_WP_PURE_EXPR_SCHEMA_VERSION,
                serde_json::to_string(&mixed_sort_predicate)
                    .expect("typed ProofFormula JSON serializes"),
            );
            let error = typed_trust_wp_claim_from_trust_ir_formula(&formula)
                .expect_err("ProofFormula JSON must reject conflicting variable sorts");
            assert!(error.contains("conflicting sorts"), "{error}");

            let bool_ordering = trust_ir::ProofFormula::new(
                TRUST_WP_PURE_EXPR_SCHEMA_VERSION,
                serde_json::to_string(&TrustWpPureExprV1::Binary {
                    op: TrustWpPureBinaryOpV1::Lt,
                    lhs: Box::new(bool_var()),
                    rhs: Box::new(bool_var()),
                })
                .expect("typed ProofFormula JSON serializes"),
            );
            let error = typed_trust_wp_claim_from_trust_ir_formula(&bool_ordering)
                .expect_err("ProofFormula JSON must reject Bool ordering");
            assert!(error.contains("not boolean"), "{error}");
        }

        let arithmetic_envelope = serde_json::json!({
            "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
            "variables": [{"name": "x", "sort": "int"}],
            "body": {
                "op": "gt",
                "lhs": {
                    "op": "add",
                    "lhs": {"var": "x"},
                    "rhs": {"int": 1},
                },
                "rhs": {"var": "x"},
            },
        });
        let canonical_contract = TrustContract {
            contract_id: "contract-direct-trust-formula-arithmetic".to_string(),
            kind: ContractKind::Ensures,
            predicate: ContractPredicate::CanonicalJson {
                schema: TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION.to_string(),
                value: arithmetic_envelope,
            },
            source: SourceLocation::default(),
            metadata: Vec::new(),
        };
        let error = typed_trust_wp_claim_from_contract(&canonical_contract)
            .expect_err("canonical TrustFormulaV1 arithmetic must fail at contract ingress");
        assert!(error.contains("arithmetic operator `add`"), "{error}");

        let x = || trust_types::Formula::Var("x".to_string(), trust_types::Sort::Int);
        let formula = trust_types::Formula::Gt(
            Box::new(trust_types::Formula::Add(
                Box::new(x()),
                Box::new(trust_types::Formula::Int(1)),
            )),
            Box::new(x()),
        );
        let formula_contract = TrustContract {
            contract_id: "contract-direct-formula-at-1-arithmetic".to_string(),
            kind: ContractKind::Ensures,
            predicate: ContractPredicate::CanonicalJson {
                schema: TRUST_TYPES_FORMULA_SCHEMA_VERSION.to_string(),
                value: serde_json::to_value(formula).expect("Formula@1 serializes"),
            },
            source: SourceLocation::default(),
            metadata: Vec::new(),
        };
        let error = typed_trust_wp_claim_from_contract(&formula_contract)
            .expect_err("Formula@1 arithmetic must fail at contract ingress");
        assert!(error.contains("arithmetic operator `add`"), "{error}");
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api,
        trust_wp_typed_metadata_helper_api
    ))]
    #[test]
    fn proof_context_claim_constructor_rejects_arithmetic_and_duplicate_envelopes() {
        for payload in [
            "(x + 1) > x",
            "(x - 1) < x",
            "(x * 2) > x",
            "(x / 2) <= x",
            "(x % 2) == 0",
            "(x << 1) > x",
            "(x >> 1) <= x",
            "(x & 1) == 0",
            "(x | 1) >= x",
            "(x ^ 1) != x",
            "(~x) < 0",
            "-x < 0",
        ] {
            let formula = trust_ir::ProofFormula::new(TRUST_WP_PURE_EXPR_SCHEMA_VERSION, payload);
            let err = trust_wp_claim(&formula)
                .expect_err("arithmetic proof-context PureExpr must fail before sibling request");
            assert!(err.contains("arithmetic operator"), "{payload}: {err}");
        }

        for payload in [
            "x as u8 == x",
            "(x: u8) == x",
            "f(x) == f(x)",
            "x.field == x.field",
            "old(x) == old(x)",
            "x[0] == x[0]",
            "x && x >= 0",
        ] {
            let formula = trust_ir::ProofFormula::new(TRUST_WP_PURE_EXPR_SCHEMA_VERSION, payload);
            let err = trust_wp_claim(&formula)
                .expect_err("reinterpretable proof-context PureExpr must fail before request");
            assert!(
                err.contains("arithmetic-free")
                    || err.contains("stable text")
                    || (payload == "x && x >= 0" && err.contains("conflicting sorts")),
                "{payload}: {err}"
            );
        }

        let arithmetic_envelope = serde_json::json!({
            "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
            "variables": [{"name": "x", "sort": "int"}],
            "body": {
                "op": "gt",
                "lhs": {
                    "op": "add",
                    "lhs": {"var": "x"},
                    "rhs": {"int": 1},
                },
                "rhs": {"var": "x"},
            },
        });
        let formula = trust_ir::ProofFormula::new(
            TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
            arithmetic_envelope.to_string(),
        );
        assert!(trust_wp_claim(&formula).is_err());

        let duplicate = format!(
            r#"{{"schema":"{TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION}","body":{{"bool":true}},"body":{{"bool":false}}}}"#
        );
        let formula = trust_ir::ProofFormula::new(TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION, duplicate);
        let err = trust_wp_claim(&formula).expect_err("duplicate proof envelope must fail closed");
        assert!(err.contains("duplicate JSON object key `body`"), "{err}");

        let duplicate_nested_op = r#"{
            "kind":"binary",
            "op":"and",
            "lhs":{
                "kind":"binary",
                "op":"add",
                "op":"eq",
                "lhs":{"kind":"int","value":1},
                "rhs":{"kind":"int","value":1}
            },
            "rhs":{"kind":"bool","value":true}
        }"#;
        let formula =
            trust_ir::ProofFormula::new(TRUST_WP_PURE_EXPR_SCHEMA_VERSION, duplicate_nested_op);
        let err = trust_wp_claim(&formula)
            .expect_err("nested duplicate PureExpr operators must fail closed");
        assert!(err.contains("duplicate JSON object key `op`"), "{err}");

        let x = || trust_types::Formula::Var("x".to_string(), trust_types::Sort::Int);
        let raw_formula = trust_types::Formula::Gt(
            Box::new(trust_types::Formula::Add(
                Box::new(x()),
                Box::new(trust_types::Formula::Int(1)),
            )),
            Box::new(x()),
        );
        let formula = trust_ir::ProofFormula::new(
            TRUST_TYPES_FORMULA_SCHEMA_VERSION,
            serde_json::to_string(&raw_formula).expect("Formula@1 serializes"),
        );
        assert!(
            trust_wp_claim(&formula).is_err(),
            "Formula@1 proof-context arithmetic must use the same refusal"
        );
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    #[test]
    fn verify_bundle_request_revalidates_manually_constructed_claims() {
        let obligation = obligation(ObligationKind::Postcondition, "request-choke-point");
        let bundle = typed_bundle(obligation, TrustWpPureExprV1::Bool { value: true });
        let var = || TrustWpPureExprV1::Var { name: "x".to_string(), sort: TrustWpPureSortV1::Int };
        let pure_claim = NativeTrustWpClaim::TrustWpPureExprV1(TrustWpPureExprV1::Binary {
            op: TrustWpPureBinaryOpV1::Gt,
            lhs: Box::new(TrustWpPureExprV1::Binary {
                op: TrustWpPureBinaryOpV1::Add,
                lhs: Box::new(var()),
                rhs: Box::new(TrustWpPureExprV1::Int { value: 1 }),
            }),
            rhs: Box::new(var()),
        });
        let error =
            trust_wp_verify_bundle_request(&bundle, &bundle.obligations[0], &pure_claim, None);
        let Err(NativeContractLoweringOutcome::Unsupported { diagnostic }) = error else {
            panic!(
                "final request construction must refuse manually constructed PureExpr arithmetic"
            );
        };
        assert!(diagnostic.contains("arithmetic operator `add`"), "{diagnostic}");

        let injected_name_claim =
            NativeTrustWpClaim::TrustWpPureExprV1(TrustWpPureExprV1::Binary {
                op: TrustWpPureBinaryOpV1::Eq,
                lhs: Box::new(TrustWpPureExprV1::Var {
                    name: "true) || true || (false".to_string(),
                    sort: TrustWpPureSortV1::Bool,
                }),
                rhs: Box::new(TrustWpPureExprV1::Bool { value: false }),
            });
        let error = trust_wp_verify_bundle_request(
            &bundle,
            &bundle.obligations[0],
            &injected_name_claim,
            None,
        );
        let Err(NativeContractLoweringOutcome::Unsupported { diagnostic }) = error else {
            panic!("final request construction must refuse stable-text variable injection");
        };
        assert!(diagnostic.contains("variable name"), "{diagnostic}");

        let formula_claim = NativeTrustWpClaim::TrustFormulaV1(
            serde_json::json!({
                "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
                "variables": [{"name": "x", "sort": "int"}],
                "body": {
                    "op": "gt",
                    "lhs": {
                        "op": "add",
                        "lhs": {"var": "x"},
                        "rhs": {"int": 1},
                    },
                    "rhs": {"var": "x"},
                },
            })
            .to_string(),
        );
        let error =
            trust_wp_verify_bundle_request(&bundle, &bundle.obligations[0], &formula_claim, None);
        let Err(NativeContractLoweringOutcome::Unsupported { diagnostic }) = error else {
            panic!(
                "final request construction must refuse manually constructed TrustFormula arithmetic"
            );
        };
        assert!(diagnostic.contains("arithmetic operator `add`"), "{diagnostic}");
    }

    #[cfg(feature = "trust-build")]
    fn native_bundle_with_trust_wp_formula(
        kind: trust_ir::ObligationKind,
        formula: Option<trust_ir::ProofFormula>,
        public_bundle: &TrustContractBundle,
        public_obligation: &TrustObligation,
    ) -> trust_ir::NativeVerificationBundle {
        let proof_id = trust_ir::ProofId::new(2);
        let function_id = trust_ir::FuncId::new(0);
        let root = trust_ir::ProofLineageId::new(0);
        let source_digest = trust_ir::ProofDigest::sha256([0x11; 32]);

        let sanitized_public_bundle = strip_trust_wp_native_metadata_from_bundle(public_bundle);
        let sanitized_public_obligation =
            strip_trust_wp_native_metadata_from_obligation(public_obligation);
        let public_semantic_digest = sanitized_public_bundle
            .canonical_obligation_semantic_digest_sha256(&sanitized_public_obligation)
            .expect("native claim fixture has canonical public semantics");
        let public_semantic_digest = sha256_proof_digest(&public_semantic_digest);

        let mut module = trust_ir::Module::new("trust-wp-native-claim-test");
        let source_file =
            module.intern_file(public_obligation.source.file.as_deref().unwrap_or("src/lib.rs"));
        let source_range = trust_ir::ProofObligationSourceRange {
            file: source_file,
            start_line: public_obligation.source.line.unwrap_or(1),
            start_col: public_obligation.source.column.unwrap_or(1),
            end_line: public_obligation.source.end_line.unwrap_or(1),
            end_col: public_obligation.source.end_column.unwrap_or(1),
        };
        let source_id = public_obligation
            .contract_id
            .as_deref()
            .or(public_obligation.proof_item_id.as_deref())
            .unwrap_or(&public_obligation.obligation_id)
            .to_string();
        let assertion_text_id = format!("trust-assertion:{source_id}");
        let native_assertion_id = trust_ir::NativeAssertionId::new(trust_types::stable_u32_id(
            assertion_text_id.as_bytes(),
        ));
        let func_ty = module.add_func_type(trust_ir::FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
        });
        module.add_function(trust_ir::Function::new(
            function_id,
            "demo::postcondition",
            func_ty,
            trust_ir::BlockId::new(0),
        ));
        let replay_formula = formula
            .clone()
            .unwrap_or_else(|| trust_ir::ProofFormula::new("TrustWpPureExprV1", "true"));
        let mut proof_obligation = trust_ir::ProofObligation::new(
            proof_id,
            kind.clone(),
            trust_ir::ProofStatus::Pending,
            "prove native formula",
        );
        if let Some(formula) = formula {
            proof_obligation = proof_obligation.with_formula(formula);
        }
        module.proof_obligations.push(
            proof_obligation.with_function(function_id).with_source(
                trust_ir::ProofObligationSourceIdentity::new(source_id, assertion_text_id)
                    .with_range(source_range)
                    .with_public(trust_ir::PublicObligationIdentity {
                        obligation_id: public_obligation.obligation_id.clone(),
                        semantic_digest: public_semantic_digest,
                    }),
            ),
        );
        let trust_ir_digest = module.stable_digest();

        let mut lineage_node = trust_ir::ProofLineageNode::new(
            root,
            trust_ir::ProofTransform::new(
                trust_ir::ProofTransformStage::Frontend,
                "rustc-mir-to-trust_ir",
                "Trust",
                "native-request-schema-v1",
            ),
            source_digest,
            trust_ir_digest,
        );
        lineage_node.obligations.push(proof_id);
        let lineage = trust_ir::ProofLineageManifest {
            schema_version: trust_ir::ProofLineageManifest::SCHEMA_VERSION,
            nodes: vec![lineage_node],
            roots: vec![root],
        };

        let mut native_bundle = trust_ir::NativeVerificationBundle::new(
            trust_ir::NativeBundleProducer::TRust,
            trust_ir::NativeAdapterInput::RustMir { body_digest: source_digest },
            trust_ir_digest,
            module,
            lineage,
        );
        let source_span = trust_ir::SourceSpan {
            file: source_range.file,
            line: source_range.start_line,
            col: source_range.start_col,
        };
        native_bundle.compiler_facts.obligation_sources.push(trust_ir::NativeObligationSource {
            obligation: proof_id,
            public_obligation_id: public_obligation.obligation_id.clone(),
            function: Some(function_id),
            span: Some(source_span),
            assertion_id: Some(native_assertion_id),
            cause: match kind {
                trust_ir::ObligationKind::Precondition => {
                    trust_ir::NativeObligationCause::Precondition
                }
                trust_ir::ObligationKind::Postcondition => {
                    trust_ir::NativeObligationCause::Postcondition
                }
                trust_ir::ObligationKind::LoopInvariant => trust_ir::NativeObligationCause::Assert,
                _ => trust_ir::NativeObligationCause::Panic,
            },
            monomorphization: None,
            facts: Vec::new(),
        });
        native_bundle.requests.push(trust_ir::NativeVerificationRequest::TrustWp(
            trust_ir::TrustWpNativeRequest {
                id: trust_ir::NativeRequestId::new(0),
                mode: trust_ir::TrustWpVerificationMode::WeakestPrecondition,
                function: function_id,
                obligations: vec![proof_id],
                lineage_roots: vec![root],
                options: trust_ir::TrustWpRequestOptions::default(),
                diagnostics: trust_ir::NativeDiagnosticsPolicy::default(),
                provenance: trust_ir::NativeRequestProvenance::trust_wp(
                    trust_ir::NativeToolIdentity::new("trust-wp"),
                )
                .with_solver(trust_ir::NativeToolIdentity::new("ay"))
                .with_replay(
                    trust_ir::ProofReplayIdentity::new("trust-wp", "unit-test")
                        .with_transcript_digest(trust_ir::ProofDigest::sha256([0x22; 32])),
                )
                .with_replay_context(
                    trust_ir::NativeReplayContext::default().with_atom(
                        trust_ir::NativeReplayAtom::assertion(
                            trust_ir::NativeReplayAtomId::new(0),
                            replay_formula,
                        )
                        .with_obligation(proof_id)
                        .with_assertion_id(native_assertion_id)
                        .with_span(source_span),
                    ),
                ),
            },
        ));
        native_bundle
    }

    #[cfg(feature = "trust-build")]
    fn sha256_proof_digest(value: &str) -> trust_ir::ProofDigest {
        assert_eq!(value.len(), 64, "fixture SHA-256 digest is fixed width");
        let mut bytes = [0_u8; 32];
        for (index, pair) in value.as_bytes().chunks_exact(2).enumerate() {
            let nibble = |byte| match byte {
                b'0'..=b'9' => byte - b'0',
                b'a'..=b'f' => byte - b'a' + 10,
                _ => panic!("fixture SHA-256 digest must use canonical lowercase hex"),
            };
            bytes[index] = (nibble(pair[0]) << 4) | nibble(pair[1]);
        }
        trust_ir::ProofDigest::sha256(bytes)
    }

    #[cfg(feature = "trust-build")]
    fn native_trust_wp_request(
        native_bundle: &trust_ir::NativeVerificationBundle,
    ) -> &trust_ir::TrustWpNativeRequest {
        let Some(trust_ir::NativeVerificationRequest::TrustWp(request)) =
            native_bundle.requests.first()
        else {
            panic!("fixture contains one trust-wp native request");
        };
        request
    }

    #[cfg(feature = "trust-build")]
    fn native_trust_wp_request_mut(
        native_bundle: &mut trust_ir::NativeVerificationBundle,
    ) -> &mut trust_ir::TrustWpNativeRequest {
        let Some(trust_ir::NativeVerificationRequest::TrustWp(request)) =
            native_bundle.requests.first_mut()
        else {
            panic!("fixture contains one trust-wp native request");
        };
        request
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_claim_accepts_exact_matching_public_and_native_claims() {
        let public_obligation = obligation(ObligationKind::Postcondition, "native-post");
        let public_bundle = typed_bundle_with_obligations(
            vec![public_obligation.clone()],
            TrustWpPureExprV1::Bool { value: true },
        );
        let native_bundle = native_bundle_with_trust_wp_formula(
            trust_ir::ObligationKind::Postcondition,
            Some(trust_ir::ProofFormula::new("TrustWpPureExprV1", "true")),
            &public_bundle,
            &public_obligation,
        );

        let claim = native_trust_ir_claim_for_obligation(
            &public_bundle,
            &native_bundle,
            native_trust_wp_request(&native_bundle),
            trust_ir::ProofId::new(2),
            &public_obligation,
        )
        .expect("native TrustIr formula is an eligible trust_wp claim");

        assert_eq!(
            claim,
            NativeTrustWpClaim::TrustWpPureExprV1(TrustWpPureExprV1::Bool { value: true })
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_bool_equality_claims_have_exact_public_module_assertion_ast_parity() {
        let var = |name: &str| TrustWpPureExprV1::Var {
            name: name.to_string(),
            sort: TrustWpPureSortV1::Bool,
        };
        let eq = || TrustWpPureExprV1::Binary {
            op: TrustWpPureBinaryOpV1::Eq,
            lhs: Box::new(var("flag")),
            rhs: Box::new(var("ready")),
        };
        let cases = [
            ("eq", eq()),
            (
                "ne",
                TrustWpPureExprV1::Binary {
                    op: TrustWpPureBinaryOpV1::Ne,
                    lhs: Box::new(var("flag")),
                    rhs: Box::new(var("ready")),
                },
            ),
            ("nested", TrustWpPureExprV1::Not { expr: Box::new(eq()) }),
        ];

        for (case, source_expr) in cases {
            let public_obligation =
                obligation(ObligationKind::Postcondition, &format!("native-bool-{case}"));
            let public_bundle =
                typed_bundle_with_obligations(vec![public_obligation.clone()], source_expr.clone());
            let canonical_text = source_expr.stable_text();
            let formula = trust_ir::ProofFormula::new(
                TRUST_WP_PURE_EXPR_SCHEMA_VERSION,
                canonical_text.clone(),
            );
            let native_bundle = native_bundle_with_trust_wp_formula(
                trust_ir::ObligationKind::Postcondition,
                Some(formula),
                &public_bundle,
                &public_obligation,
            );

            let public_claim = typed_trust_wp_claim_from_contract(&public_bundle.contracts[0])
                .expect("public typed Bool claim canonicalizes");
            let module_claim =
                native_trust_ir_typed_claim(&native_bundle, trust_ir::ProofId::new(2))
                    .expect("module Bool claim canonicalizes");
            let assertion_formula =
                &native_trust_wp_request(&native_bundle).provenance.replay_context.atoms[0].formula;
            let assertion_claim = typed_trust_wp_claim_from_trust_ir_formula(assertion_formula)
                .expect("assertion Bool claim canonicalizes");
            let expected =
                NativeTrustWpClaim::TrustWpPureExprV1(canonicalize_trust_wp_pure_expr(source_expr));

            assert_eq!(public_claim, expected, "{case}: public raw AST");
            assert_eq!(module_claim, expected, "{case}: module raw AST");
            assert_eq!(assertion_claim, expected, "{case}: assertion raw AST");
            assert_eq!(public_claim, module_claim, "{case}: public/module raw AST parity");
            assert_eq!(module_claim, assertion_claim, "{case}: module/assertion raw AST parity");
            assert_eq!(
                expected,
                NativeTrustWpClaim::TrustWpPureExprV1(
                    parse_pure_expr_text(&canonical_text)
                        .expect("canonical Bool stable text reparses exactly"),
                ),
                "{case}: canonical typed/text AST parity",
            );

            let bound = native_trust_ir_claim_for_obligation(
                &public_bundle,
                &native_bundle,
                native_trust_wp_request(&native_bundle),
                trust_ir::ProofId::new(2),
                &public_obligation,
            )
            .expect("three-way Bool claim binding succeeds");
            assert_eq!(bound, expected, "{case}: bound raw AST");
        }
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_claim_rejects_embedded_public_id_substitution_without_formula_drift() {
        let public_obligation =
            obligation(ObligationKind::Postcondition, "native-embedded-public-id-substitution");
        let public_bundle = typed_bundle_with_obligations(
            vec![public_obligation.clone()],
            TrustWpPureExprV1::Bool { value: true },
        );
        let mut native_bundle = native_bundle_with_trust_wp_formula(
            trust_ir::ObligationKind::Postcondition,
            Some(trust_ir::ProofFormula::new("TrustWpPureExprV1", "true")),
            &public_bundle,
            &public_obligation,
        );
        let original_formula = native_bundle.module.proof_obligations[0].formula.clone();
        native_bundle.module.proof_obligations[0]
            .source
            .as_mut()
            .expect("fixture embeds source identity")
            .public
            .as_mut()
            .expect("fixture embeds public identity")
            .obligation_id = "native-embedded-public-id-alias".to_string();

        let error = native_trust_ir_claim_for_obligation(
            &public_bundle,
            &native_bundle,
            native_trust_wp_request(&native_bundle),
            trust_ir::ProofId::new(2),
            &public_obligation,
        )
        .expect_err("an embedded public id substitution must fail closed");

        assert!(error.contains("embedded public obligation id mismatch"), "{error}");
        assert_eq!(
            native_bundle.module.proof_obligations[0].formula, original_formula,
            "the substitution test must not rely on formula drift"
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_claim_rejects_embedded_public_digest_substitution_without_formula_drift() {
        let public_obligation =
            obligation(ObligationKind::Postcondition, "native-embedded-public-digest-substitution");
        let public_bundle = typed_bundle_with_obligations(
            vec![public_obligation.clone()],
            TrustWpPureExprV1::Bool { value: true },
        );
        let mut native_bundle = native_bundle_with_trust_wp_formula(
            trust_ir::ObligationKind::Postcondition,
            Some(trust_ir::ProofFormula::new("TrustWpPureExprV1", "true")),
            &public_bundle,
            &public_obligation,
        );
        let original_formula = native_bundle.module.proof_obligations[0].formula.clone();
        native_bundle.module.proof_obligations[0]
            .source
            .as_mut()
            .expect("fixture embeds source identity")
            .public
            .as_mut()
            .expect("fixture embeds public identity")
            .semantic_digest
            .bytes[0] ^= 1;

        let error = native_trust_ir_claim_for_obligation(
            &public_bundle,
            &native_bundle,
            native_trust_wp_request(&native_bundle),
            trust_ir::ProofId::new(2),
            &public_obligation,
        )
        .expect_err("an embedded public semantic digest substitution must fail closed");

        assert!(error.contains("embedded public semantic digest mismatch"), "{error}");
        assert_eq!(
            native_bundle.module.proof_obligations[0].formula, original_formula,
            "the substitution test must not rely on formula drift"
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_claim_rejects_compiler_fact_source_projection_substitutions() {
        let public_obligation =
            obligation(ObligationKind::Postcondition, "native-compiler-source-projection");
        let public_bundle = typed_bundle_with_obligations(
            vec![public_obligation.clone()],
            TrustWpPureExprV1::Bool { value: true },
        );
        let native_bundle = native_bundle_with_trust_wp_formula(
            trust_ir::ObligationKind::Postcondition,
            Some(trust_ir::ProofFormula::new("TrustWpPureExprV1", "true")),
            &public_bundle,
            &public_obligation,
        );
        let original_formula = native_bundle.module.proof_obligations[0].formula.clone();
        type SourceMutation = fn(&mut trust_ir::NativeVerificationBundle);
        let mutations: &[(&str, SourceMutation)] = &[
            ("function projection mismatch", |bundle| {
                bundle.compiler_facts.obligation_sources[0].function = None;
            }),
            ("span projection mismatch", |bundle| {
                bundle.compiler_facts.obligation_sources[0]
                    .span
                    .as_mut()
                    .expect("fixture compiler source has a span")
                    .line += 1;
            }),
            ("assertion projection mismatch", |bundle| {
                bundle.compiler_facts.obligation_sources[0].assertion_id =
                    Some(trust_ir::NativeAssertionId::new(17));
            }),
            ("cause projection mismatch", |bundle| {
                bundle.compiler_facts.obligation_sources[0].cause =
                    trust_ir::NativeObligationCause::Assert;
            }),
        ];

        for (expected_error, mutate) in mutations {
            let mut substituted = native_bundle.clone();
            mutate(&mut substituted);
            let error = native_trust_ir_claim_for_obligation(
                &public_bundle,
                &substituted,
                native_trust_wp_request(&substituted),
                trust_ir::ProofId::new(2),
                &public_obligation,
            )
            .expect_err("a compiler-fact source projection substitution must fail closed");

            assert!(error.contains(expected_error), "{expected_error}: {error}");
            assert_eq!(
                substituted.module.proof_obligations[0].formula, original_formula,
                "source projection substitution must not rely on formula drift"
            );
        }
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_claim_rejects_public_native_predicate_substitution() {
        let public_obligation = obligation(ObligationKind::Postcondition, "native-post");
        let public_bundle = typed_bundle_with_obligations(
            vec![public_obligation.clone()],
            TrustWpPureExprV1::Bool { value: false },
        );
        let native_bundle = native_bundle_with_trust_wp_formula(
            trust_ir::ObligationKind::Postcondition,
            Some(trust_ir::ProofFormula::new("TrustWpPureExprV1", "true")),
            &public_bundle,
            &public_obligation,
        );

        let error = native_trust_ir_claim_for_obligation(
            &public_bundle,
            &native_bundle,
            native_trust_wp_request(&native_bundle),
            trust_ir::ProofId::new(2),
            &public_obligation,
        )
        .expect_err("a native `true` formula must not prove a public `false` contract");

        assert!(
            error.contains("public/native claim semantic mismatch")
                && error.contains("public=sha256:")
                && error.contains("native=sha256:"),
            "{error}"
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_claim_rejects_result_and_old_substitutions() {
        let int_sort = trust_verifier_api::TrustSpecSort::Int;
        let variable = TrustSpecVariable {
            name: "x".to_string(),
            sort: int_sort,
            origin: TrustSpecVariableOrigin::Local { index: 0 },
        };
        let public_predicate = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Eq,
                TrustSpecExpr::result(int_sort),
                TrustSpecExpr::old(TrustSpecExpr::variable("x", int_sort)),
            ),
            vec![variable.clone()],
        );
        let substituted_native_predicates = [
            (
                "result-for-old",
                TrustSpecPredicate::new(
                    TrustSpecExpr::binary(
                        TrustSpecBinaryOp::Eq,
                        TrustSpecExpr::old(TrustSpecExpr::variable("x", int_sort)),
                        TrustSpecExpr::old(TrustSpecExpr::variable("x", int_sort)),
                    ),
                    vec![variable.clone()],
                ),
            ),
            (
                "old-for-result",
                TrustSpecPredicate::new(
                    TrustSpecExpr::binary(
                        TrustSpecBinaryOp::Eq,
                        TrustSpecExpr::result(int_sort),
                        TrustSpecExpr::result(int_sort),
                    ),
                    vec![variable],
                ),
            ),
        ];

        for (case, substituted_native_predicate) in substituted_native_predicates {
            let obligation_id = format!("native-result-old-{case}");
            let native_formula =
                trust_spec_predicate_to_trust_formula_payload(&substituted_native_predicate)
                    .expect("substituted native predicate lowers to TrustFormulaV1");
            let public_obligation = obligation(ObligationKind::Postcondition, &obligation_id);
            let mut public_bundle = TrustContractBundle::empty(
                format!("bundle-trust-wp-result-old-{case}"),
                BundleSubject::Function {
                    crate_name: "demo".to_string(),
                    path: format!("demo::result_old::{case}"),
                },
            );
            public_bundle.contracts.push(TrustContract {
                contract_id: public_obligation.contract_id.clone().expect("contract id"),
                kind: ContractKind::Ensures,
                predicate: ContractPredicate::CanonicalJson {
                    schema: TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
                    value: serde_json::to_value(public_predicate.clone())
                        .expect("TrustSpecPredicate serializes"),
                },
                source: SourceLocation::default(),
                metadata: Vec::new(),
            });
            public_bundle.obligations = vec![public_obligation.clone()];
            let native_bundle = native_bundle_with_trust_wp_formula(
                trust_ir::ObligationKind::Postcondition,
                Some(trust_ir::ProofFormula::new(
                    TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
                    native_formula,
                )),
                &public_bundle,
                &public_obligation,
            );

            let error = native_trust_ir_claim_for_obligation(
                &public_bundle,
                &native_bundle,
                native_trust_wp_request(&native_bundle),
                trust_ir::ProofId::new(2),
                &public_obligation,
            )
            .expect_err("result/old substitution must not preserve proof authority");

            assert!(error.contains("public/native claim semantic mismatch"), "{case}: {error}");
        }
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_claim_rejects_public_obligation_source_id_alias() {
        let native_public_obligation = obligation(ObligationKind::Postcondition, "native-original");
        let native_public_bundle = typed_bundle_with_obligations(
            vec![native_public_obligation.clone()],
            TrustWpPureExprV1::Bool { value: true },
        );
        let native_bundle = native_bundle_with_trust_wp_formula(
            trust_ir::ObligationKind::Postcondition,
            Some(trust_ir::ProofFormula::new("TrustWpPureExprV1", "true")),
            &native_public_bundle,
            &native_public_obligation,
        );
        let public_obligation = obligation(ObligationKind::Postcondition, "native-alias");
        let public_bundle = typed_bundle_with_obligations(
            vec![public_obligation.clone()],
            TrustWpPureExprV1::Bool { value: true },
        );

        let error = native_trust_ir_claim_for_obligation(
            &public_bundle,
            &native_bundle,
            native_trust_wp_request(&native_bundle),
            trust_ir::ProofId::new(2),
            &public_obligation,
        )
        .expect_err("a native source id alias must not bind the public obligation");

        assert!(
            error.contains("public obligation id mismatch")
                && error.contains("native-original")
                && error.contains("native-alias"),
            "{error}"
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_claim_rejects_assertion_replay_claim_drift() {
        let public_obligation = obligation(ObligationKind::Postcondition, "native-assertion-drift");
        let public_bundle = typed_bundle_with_obligations(
            vec![public_obligation.clone()],
            TrustWpPureExprV1::Bool { value: true },
        );
        let mut native_bundle = native_bundle_with_trust_wp_formula(
            trust_ir::ObligationKind::Postcondition,
            Some(trust_ir::ProofFormula::new("TrustWpPureExprV1", "true")),
            &public_bundle,
            &public_obligation,
        );
        let assertion = native_trust_wp_request_mut(&mut native_bundle)
            .provenance
            .replay_context
            .atoms
            .first_mut()
            .expect("fixture assertion replay atom");
        assertion.formula = trust_ir::ProofFormula::new("TrustWpPureExprV1", "false");
        assertion.payload_digest = assertion.expected_payload_digest();
        let error = native_trust_ir_claim_for_obligation(
            &public_bundle,
            &native_bundle,
            native_trust_wp_request(&native_bundle),
            trust_ir::ProofId::new(2),
            &public_obligation,
        )
        .expect_err("assertion replay drift must not retain native claim authority");

        assert!(
            error.contains("public/module/assertion replay claim semantic mismatch")
                && error.contains("assertion=sha256:"),
            "{error}"
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_claim_rejects_missing_bound_assertion_replay_atom() {
        let public_obligation =
            obligation(ObligationKind::Postcondition, "native-missing-assertion");
        let public_bundle = typed_bundle_with_obligations(
            vec![public_obligation.clone()],
            TrustWpPureExprV1::Bool { value: true },
        );
        let mut native_bundle = native_bundle_with_trust_wp_formula(
            trust_ir::ObligationKind::Postcondition,
            Some(trust_ir::ProofFormula::new("TrustWpPureExprV1", "true")),
            &public_bundle,
            &public_obligation,
        );
        native_trust_wp_request_mut(&mut native_bundle).provenance.replay_context.atoms.clear();

        let error = native_trust_ir_claim_for_obligation(
            &public_bundle,
            &native_bundle,
            native_trust_wp_request(&native_bundle),
            trust_ir::ProofId::new(2),
            &public_obligation,
        )
        .expect_err("missing assertion replay claim must fail closed");

        assert!(
            error.contains("exactly one assertion replay atom") && error.contains("found 0"),
            "{error}"
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_claim_rejects_duplicate_bound_assertion_replay_atoms() {
        let public_obligation =
            obligation(ObligationKind::Postcondition, "native-duplicate-assertion");
        let public_bundle = typed_bundle_with_obligations(
            vec![public_obligation.clone()],
            TrustWpPureExprV1::Bool { value: true },
        );
        let mut native_bundle = native_bundle_with_trust_wp_formula(
            trust_ir::ObligationKind::Postcondition,
            Some(trust_ir::ProofFormula::new("TrustWpPureExprV1", "true")),
            &public_bundle,
            &public_obligation,
        );
        let request = native_trust_wp_request_mut(&mut native_bundle);
        let mut duplicate = request.provenance.replay_context.atoms[0].clone();
        duplicate.id = trust_ir::NativeReplayAtomId::new(1);
        duplicate.payload_digest = duplicate.expected_payload_digest();
        request.provenance.replay_context.atoms.push(duplicate);

        let error = native_trust_ir_claim_for_obligation(
            &public_bundle,
            &native_bundle,
            native_trust_wp_request(&native_bundle),
            trust_ir::ProofId::new(2),
            &public_obligation,
        )
        .expect_err("duplicate assertion replay claims must not be selected by ordering");

        assert!(
            error.contains("exactly one assertion replay atom") && error.contains("found 2"),
            "{error}"
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_adapter_validates_replay_atom_payload_digest_before_admission() {
        let public_obligation =
            obligation(ObligationKind::Postcondition, "native-invalid-atom-digest");
        let public_bundle = typed_bundle_with_obligations(
            vec![public_obligation.clone()],
            TrustWpPureExprV1::Bool { value: true },
        );
        let mut native_bundle = native_bundle_with_trust_wp_formula(
            trust_ir::ObligationKind::Postcondition,
            Some(trust_ir::ProofFormula::new("TrustWpPureExprV1", "true")),
            &public_bundle,
            &public_obligation,
        );
        native_trust_wp_request_mut(&mut native_bundle).provenance.replay_context.atoms[0]
            .formula = trust_ir::ProofFormula::new("TrustWpPureExprV1", "false");
        let evidence = TrustWpVerificationEngine::new()
            .verify_obligation_with_native_trust_ir_request(
                &public_bundle,
                &public_obligation,
                &native_bundle,
                native_trust_wp_request(&native_bundle),
                trust_ir::ProofId::new(2),
            );

        assert_eq!(evidence.status, EvidenceStatus::Unsupported);
        assert!(evidence.proof_strength.is_none());
        assert!(evidence.artifacts.is_empty());
        assert!(
            evidence.diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("NativeVerificationBundle validation failed")
                    && diagnostic.contains("replay atom")
                    && diagnostic.contains("digest")
            }),
            "{evidence:#?}"
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_adapter_rejects_substituted_public_obligation_record() {
        let canonical_obligation =
            obligation(ObligationKind::Postcondition, "native-substituted-record");
        let public_bundle = typed_bundle_with_obligations(
            vec![canonical_obligation.clone()],
            TrustWpPureExprV1::Bool { value: true },
        );
        let native_bundle = native_bundle_with_trust_wp_formula(
            trust_ir::ObligationKind::Postcondition,
            Some(trust_ir::ProofFormula::new("TrustWpPureExprV1", "true")),
            &public_bundle,
            &canonical_obligation,
        );
        let mut substituted_obligation = canonical_obligation;
        substituted_obligation.description = "attacker-controlled alias record".to_string();

        let evidence = TrustWpVerificationEngine::new()
            .verify_obligation_with_native_trust_ir_request(
                &public_bundle,
                &substituted_obligation,
                &native_bundle,
                native_trust_wp_request(&native_bundle),
                trust_ir::ProofId::new(2),
            );

        assert_eq!(evidence.status, EvidenceStatus::Unsupported);
        assert!(evidence.proof_strength.is_none());
        assert!(evidence.artifacts.is_empty());
        assert!(
            evidence.diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("exact canonical public-obligation record")
                    && diagnostic.contains("differs from its canonical bundle record")
            }),
            "{evidence:#?}"
        );
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api,
        trust_wp_typed_metadata_helper_api
    ))]
    #[test]
    fn native_trust_ir_metadata_binds_full_public_claim_digest_after_stripping_stale_metadata() {
        let public_obligation =
            obligation(ObligationKind::Postcondition, "native-canonical-digest");
        let clean_bundle = typed_bundle_with_obligations(
            vec![public_obligation.clone()],
            TrustWpPureExprV1::Bool { value: true },
        );
        let native_bundle = native_bundle_with_trust_wp_formula(
            trust_ir::ObligationKind::Postcondition,
            Some(trust_ir::ProofFormula::new("TrustWpPureExprV1", "true")),
            &clean_bundle,
            &public_obligation,
        );
        let expected_digest = clean_bundle
            .canonical_obligation_semantic_digest_sha256(&clean_bundle.obligations[0])
            .expect("clean canonical public claim digest");
        let mut changed_source = clean_bundle.clone();
        changed_source.obligations[0].source.line = Some(99);
        assert_ne!(
            changed_source
                .canonical_obligation_semantic_digest_sha256(&changed_source.obligations[0])
                .expect("changed public source remains digestible"),
            expected_digest,
            "canonical claim digest must bind public source identity"
        );
        let mut changed_metadata = clean_bundle.clone();
        changed_metadata.obligations[0].metadata.push(MetadataEntry {
            key: "audit.semantic-context".to_string(),
            value: "changed".to_string(),
        });
        assert_ne!(
            changed_metadata
                .canonical_obligation_semantic_digest_sha256(&changed_metadata.obligations[0])
                .expect("changed public semantic metadata remains digestible"),
            expected_digest,
            "canonical claim digest must bind non-transport public metadata"
        );
        let stale_entry = MetadataEntry {
            key: TRUST_TRUST_WP_CLAIM_DIGEST_METADATA_KEY.to_string(),
            value: serde_json::json!({
                "algorithm": "sha256",
                "value": "ff".repeat(32),
            })
            .to_string(),
        };
        let mut stale_bundle = clean_bundle.clone();
        stale_bundle.metadata.push(stale_entry.clone());
        stale_bundle.contracts[0].metadata.push(stale_entry.clone());
        stale_bundle.obligations[0].metadata.push(stale_entry);

        let stripped = strip_trust_wp_native_metadata_from_bundle(&stale_bundle);
        assert_eq!(
            stripped
                .canonical_obligation_semantic_digest_sha256(&stripped.obligations[0])
                .expect("stale transport metadata is stripped before canonical binding"),
            expected_digest
        );
        let metadata =
            trust_wp_native_replay_metadata_entries_from_trust_ir_bundle_with_claim_digest(
                &native_bundle,
                native_trust_wp_request(&native_bundle),
                trust_ir::ProofId::new(2),
                Some(ArtifactHash {
                    algorithm: "sha256".to_string(),
                    value: expected_digest.clone(),
                }),
            )
            .expect("controlled native metadata helper accepts canonical public claim digest");
        let claim_digest = metadata
            .iter()
            .find(|entry| entry.key == TRUST_TRUST_WP_CLAIM_DIGEST_METADATA_KEY)
            .map(|entry| {
                serde_json::from_str::<serde_json::Value>(&entry.value)
                    .expect("claim digest metadata is typed JSON")
            })
            .expect("controlled helper emits claim digest metadata");
        assert_eq!(claim_digest["algorithm"], "sha256");
        assert_eq!(claim_digest["value"], expected_digest);
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_claim_rejects_missing_public_contract_binding() {
        let canonical_obligation = obligation(ObligationKind::Postcondition, "native-post");
        let canonical_bundle = typed_bundle_with_obligations(
            vec![canonical_obligation.clone()],
            TrustWpPureExprV1::Bool { value: true },
        );
        let native_bundle = native_bundle_with_trust_wp_formula(
            trust_ir::ObligationKind::Postcondition,
            Some(trust_ir::ProofFormula::new("TrustWpPureExprV1", "true")),
            &canonical_bundle,
            &canonical_obligation,
        );
        let mut public_obligation = obligation(ObligationKind::Postcondition, "native-post");
        public_obligation.contract_id = None;
        let public_bundle = bundle_with(vec![public_obligation.clone()]);

        let error = native_trust_ir_claim_for_obligation(
            &public_bundle,
            &native_bundle,
            native_trust_wp_request(&native_bundle),
            trust_ir::ProofId::new(2),
            &public_obligation,
        )
        .expect_err("native claim authority requires an exact public contract binding");

        assert!(error.contains("contract-linked typed predicate"), "{error}");
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_claim_rejects_ineligible_trust_ir_obligation_kind() {
        let public_obligation = obligation(ObligationKind::Postcondition, "native-panic");
        let public_bundle = typed_bundle_with_obligations(
            vec![public_obligation.clone()],
            TrustWpPureExprV1::Bool { value: true },
        );
        let native_bundle = native_bundle_with_trust_wp_formula(
            trust_ir::ObligationKind::PanicFreedom,
            Some(trust_ir::ProofFormula::new("TrustWpPureExprV1", "true")),
            &public_bundle,
            &public_obligation,
        );

        let err = native_trust_ir_claim_for_obligation(
            &public_bundle,
            &native_bundle,
            native_trust_wp_request(&native_bundle),
            trust_ir::ProofId::new(2),
            &public_obligation,
        )
        .expect_err("panic-freedom is not an eligible trust_wp typed contract route");

        assert!(err.contains("ineligible") && err.contains("PanicFreedom"), "{err}");
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_claim_rejects_text_smtlib_formula_payload() {
        let public_obligation = obligation(ObligationKind::Postcondition, "native-smtlib");
        let public_bundle = typed_bundle_with_obligations(
            vec![public_obligation.clone()],
            TrustWpPureExprV1::Bool { value: true },
        );
        let native_bundle = native_bundle_with_trust_wp_formula(
            trust_ir::ObligationKind::Postcondition,
            Some(trust_ir::ProofFormula::smtlib2("true", "Bool")),
            &public_bundle,
            &public_obligation,
        );

        let err = native_trust_ir_claim_for_obligation(
            &public_bundle,
            &native_bundle,
            native_trust_wp_request(&native_bundle),
            trust_ir::ProofId::new(2),
            &public_obligation,
        )
        .expect_err("SMT-LIB text is not a typed trust_wp formula payload");

        // Pins the fail-closed rejection of text SMT-LIB2 payloads; only the
        // diagnostic spelling changed (`trust_wp`), the rejection is intact.
        assert!(
            err.contains("SMT-LIB2") && err.contains("not an eligible typed trust_wp"),
            "{err}"
        );
    }

    fn locally_shaped_candidate_evidence(
        manifest: &EngineManifest,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        replay: &TrustWpNativeReplay,
        summary_facts: &[SummaryFact],
    ) -> ObligationEvidence {
        let metadata = expected_native_replay_metadata(bundle, obligation, replay, summary_facts);
        ObligationEvidence {
            evidence_id: metadata.evidence_id,
            obligation_id: obligation.obligation_id.clone(),
            engine: manifest.clone(),
            status: EvidenceStatus::Proved,
            proof_strength: Some(ProofStrength::deductive()),
            artifacts: metadata.artifacts,
            counterexample: None::<Counterexample>,
            publication: EvidencePublicationMetadata {
                publication_plan_hash: bundle.publication.dpub_plan_hash.clone(),
                trust_engines_lock_hash: bundle.publication.trust_engines_lock_hash.clone(),
                evidence_bundle_hash: Some(metadata.evidence_bundle_hash),
                ..EvidencePublicationMetadata::default()
            },
            diagnostics: Vec::new(),
        }
    }

    #[cfg(not(feature = "trust-build"))]
    #[test]
    fn structured_trust_formula_predicate_fails_closed_without_trust_build() {
        let obligation = obligation(ObligationKind::Postcondition, "post-trust-formula");
        let mut bundle = TrustContractBundle::empty(
            "bundle-trust-wp-trust-formula",
            BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::deductive".to_string(),
            },
        );
        bundle.contracts.push(TrustContract {
            contract_id: obligation.contract_id.clone().expect("test obligation has contract"),
            kind: ContractKind::Ensures,
            predicate: ContractPredicate::CanonicalJson {
                schema: TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION.to_string(),
                value: trust_formula_value(true),
            },
            source: SourceLocation::default(),
            metadata: Vec::new(),
        });
        bundle.obligations = vec![obligation];

        let evidence = TrustWpVerificationEngine::new().verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].artifacts.is_empty());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains(TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION)
                && diagnostic.contains("NativeTrustWpBundleVerifier")
        }));
    }

    #[cfg(all(feature = "trust-build", not(trust_wp_proof_transport_api)))]
    #[test]
    fn trust_build_stale_trust_wp_dependency_fails_closed_without_transport_api() {
        let obligation = obligation(ObligationKind::Postcondition, "post-stale-trust-wp");
        let bundle = typed_bundle(obligation, TrustWpPureExprV1::Bool { value: true });

        let evidence = TrustWpVerificationEngine::new().verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].artifacts.is_empty());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains(TRUST_WP_PROOF_TRANSPORT_API_MISSING)
                && diagnostic.contains("first-party/trust-wp")
                && diagnostic.contains("EvidenceArtifact::has_transport")
        }));
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    #[test]
    fn trust_build_direct_trust_wp_trust_formula_reports_proof_grade_evidence() {
        let obligation = with_native_artifact_metadata(
            obligation(ObligationKind::Postcondition, "post-trust-formula"),
            "weakest_precondition",
        );
        let mut bundle = TrustContractBundle::empty(
            "bundle-trust-wp-trust-formula",
            BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::deductive".to_string(),
            },
        );
        bundle.contracts.push(TrustContract {
            contract_id: obligation.contract_id.clone().expect("test obligation has contract"),
            kind: ContractKind::Ensures,
            predicate: ContractPredicate::CanonicalJson {
                schema: TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION.to_string(),
                value: trust_formula_value(true),
            },
            source: SourceLocation::default(),
            metadata: Vec::new(),
        });
        bundle.obligations = vec![obligation];

        let evidence = TrustWpVerificationEngine::new().verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(
            evidence[0].status,
            EvidenceStatus::Proved,
            "diagnostics: {:?}",
            evidence[0].diagnostics
        );
        assert_eq!(evidence[0].proof_strength, Some(ProofStrength::deductive()));
        assert!(evidence[0].publication.evidence_bundle_hash.is_some());
        assert!(evidence[0].artifacts.iter().any(|artifact| {
            artifact.kind == EvidenceArtifactKind::SolverTranscript
                && artifact.hash.is_hash_addressed()
        }));
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains(TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION)
                && diagnostic.contains("NativeTrustWpBundleVerifier")
        }));
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    #[test]
    fn trust_build_direct_trust_spec_predicate_reports_proof_grade_evidence() {
        let obligation = with_native_artifact_metadata(
            obligation(ObligationKind::Postcondition, "post-trust-spec"),
            "weakest_precondition",
        );
        let mut bundle = TrustContractBundle::empty(
            "bundle-trust-wp-trust-spec",
            BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::deductive".to_string(),
            },
        );
        bundle.contracts.push(TrustContract {
            contract_id: obligation.contract_id.clone().expect("test obligation has contract"),
            kind: ContractKind::Ensures,
            predicate: trust_spec_true_predicate()
                .into_contract_predicate()
                .expect("trust spec serializes"),
            source: SourceLocation::default(),
            metadata: Vec::new(),
        });
        bundle.obligations = vec![obligation];

        let evidence = TrustWpVerificationEngine::new().verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(
            evidence[0].status,
            EvidenceStatus::Proved,
            "diagnostics: {:?}",
            evidence[0].diagnostics
        );
        assert_eq!(evidence[0].proof_strength, Some(ProofStrength::deductive()));
        assert!(evidence[0].publication.evidence_bundle_hash.is_some());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains(TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION)
                && diagnostic.contains(TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION)
        }));
    }

    #[test]
    fn malformed_trust_formula_predicate_fails_closed() {
        let obligation = obligation(ObligationKind::Postcondition, "post-bad-trust-formula");
        let mut bundle = TrustContractBundle::empty(
            "bundle-trust-wp-bad-trust-formula",
            BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::deductive".to_string(),
            },
        );
        bundle.contracts.push(TrustContract {
            contract_id: obligation.contract_id.clone().expect("test obligation has contract"),
            kind: ContractKind::Ensures,
            predicate: ContractPredicate::CanonicalJson {
                schema: TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION.to_string(),
                value: serde_json::json!({ "body": { "bool": true } }),
            },
            source: SourceLocation::default(),
            metadata: Vec::new(),
        });
        bundle.obligations = vec![obligation];

        let evidence = TrustWpVerificationEngine::new().verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("missing required field `schema`")
                || diagnostic.contains("missing required field")
        }));
    }

    #[test]
    fn mismatched_public_contract_kind_is_not_routed_to_trust_wp() {
        let obligation = obligation(ObligationKind::Postcondition, "post-requires-mismatch");
        let mut bundle = TrustContractBundle::empty(
            "bundle-trust-wp-kind-mismatch",
            BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::deductive".to_string(),
            },
        );
        bundle.contracts.push(TrustContract {
            contract_id: obligation.contract_id.clone().expect("test obligation has contract"),
            kind: ContractKind::Requires,
            predicate: ContractPredicate::CanonicalJson {
                schema: TRUST_WP_PURE_EXPR_SCHEMA_VERSION.to_string(),
                value: serde_json::to_value(TrustWpPureExprV1::Bool { value: true })
                    .expect("typed expr serializes"),
            },
            source: SourceLocation::default(),
            metadata: Vec::new(),
        });
        bundle.obligations = vec![obligation];

        let evidence = TrustWpVerificationEngine::new().verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].artifacts.is_empty());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("not backed by matching contract kind")
                && diagnostic.contains("Postcondition")
                && diagnostic.contains("Requires")
        }));
    }

    #[test]
    fn unsupported_trust_spec_fragment_fails_closed_without_text_heuristics() {
        let obligation = obligation(ObligationKind::Postcondition, "post-symbolic-trust-spec");
        let mut bundle = TrustContractBundle::empty(
            "bundle-trust-wp-symbolic-trust-spec",
            BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::deductive".to_string(),
            },
        );
        bundle.contracts.push(TrustContract {
            contract_id: obligation.contract_id.clone().expect("test obligation has contract"),
            kind: ContractKind::Ensures,
            predicate: trust_spec_result_predicate()
                .into_contract_predicate()
                .expect("trust spec serializes"),
            source: SourceLocation::default(),
            metadata: Vec::new(),
        });
        bundle.obligations = vec![obligation];

        let evidence = TrustWpVerificationEngine::new().verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_ne!(evidence[0].status, EvidenceStatus::Proved);
        assert!(evidence[0].proof_strength.is_none());
        // Pins that the symbolic TrustSpec fragment fails closed with a typed
        // fail-closed diagnostic (never a text heuristic). The last two
        // disjuncts pin the current spellings: the adapter wrapper says
        // "trust_wp native replay metadata" and trust-wp-core's error says
        // "missing required trust-wp metadata key".
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("TrustFormulaV1")
                || diagnostic.contains("native pure replay cannot prove")
                || diagnostic.contains("trust-wp native pure verifier returned unknown")
                || diagnostic.contains("comparison contains symbolic")
                || diagnostic.contains("NativeTrustWpBundleVerifier")
                || diagnostic.contains("vendored trust_wp proof transport artifact API is missing")
                || diagnostic.contains("requires typed native")
                || diagnostic.contains("trust_wp native replay metadata")
                || diagnostic.contains("missing required trust-wp metadata key")
        }));
    }

    #[test]
    fn supports_trust_wp_owned_full_verification_obligations() {
        let engine = TrustWpVerificationEngine::new();
        for kind in trust_wp_owned_obligation_kinds() {
            let support = engine.supports(&obligation(kind, "owned"));
            assert!(support.is_supported(), "expected trust_wp to own {support:?}");
        }

        let support = engine.supports(&obligation(ObligationKind::Ownership, "ownership"));
        assert!(matches!(support, SupportLevel::Unsupported { .. }));

        for kind in [ObligationKind::Invariant, ObligationKind::ArithmeticSafety] {
            let support = engine.supports(&obligation(kind, "not-replay-owned"));
            assert!(matches!(support, SupportLevel::Unsupported { .. }));
        }
    }

    #[test]
    fn owned_obligations_return_unsupported_until_native_proof_exists() {
        let engine = TrustWpVerificationEngine::new();
        let bundle = bundle_with(vec![
            obligation(ObligationKind::Precondition, "pre"),
            obligation(ObligationKind::Postcondition, "post"),
            obligation(ObligationKind::LoopInvariant, "loop"),
            obligation(ObligationKind::Refinement, "refinement"),
            obligation(ObligationKind::Termination, "termination"),
        ]);

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 5);
        for item in evidence {
            assert_eq!(item.engine.name, TRUST_WP_ENGINE_NAME);
            assert_eq!(item.status, EvidenceStatus::Unsupported);
            assert!(item.proof_strength.is_none());
            assert!(item.artifacts.is_empty());
            assert!(item.counterexample.is_none());
            #[cfg(not(feature = "trust-build"))]
            assert!(
                item.diagnostics.iter().any(|diagnostic| diagnostic.contains("not wired")),
                "missing not-wired diagnostic: {:?}",
                item.diagnostics
            );
            #[cfg(all(
                feature = "trust-build",
                trust_wp_proof_transport_api,
                trust_wp_structured_context_api
            ))]
            assert!(
                item.diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.contains("direct committed trust_wp replay")),
                "missing direct-replay diagnostic: {:?}",
                item.diagnostics
            );
            #[cfg(all(
                feature = "trust-build",
                trust_wp_proof_transport_api,
                not(trust_wp_structured_context_api)
            ))]
            assert!(
                item.diagnostics.iter().any(|diagnostic| {
                    diagnostic.contains(TRUST_WP_STRUCTURED_CONTEXT_API_MISSING)
                }),
                "missing structured-context diagnostic: {:?}",
                item.diagnostics
            );
            #[cfg(all(feature = "trust-build", not(trust_wp_proof_transport_api)))]
            assert!(
                item.diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.contains(TRUST_WP_PROOF_TRANSPORT_API_MISSING)),
                "missing stale-transport diagnostic: {:?}",
                item.diagnostics
            );
            assert!(
                item.diagnostics.iter().any(|diagnostic| {
                    diagnostic.contains(TRUST_WP_PROOF_EVIDENCE_SCHEMA_VERSION)
                        && diagnostic.contains(TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION)
                }),
                "missing replay schema diagnostic: {:?}",
                item.diagnostics
            );
            assert!(
                item.diagnostics.iter().any(|diagnostic| {
                    TRUST_WP_NATIVE_PURE_REPLAY_REQUIRED_ARTIFACTS
                        .iter()
                        .all(|artifact| diagnostic.contains(artifact))
                }),
                "missing required artifact diagnostic: {:?}",
                item.diagnostics
            );
        }
    }

    #[test]
    fn replay_shaped_evidence_is_rejected_without_trust_wp_aggregate_gate() {
        let obligation = obligation(ObligationKind::Postcondition, "post-typed");
        let bundle = typed_bundle(obligation, typed_expr(true));
        let replay = replay_typed_predicate(&typed_expr(true)).expect("true predicate replays");
        let evidence = locally_shaped_candidate_evidence(
            TrustWpVerificationEngine::new().manifest(),
            &bundle,
            &bundle.obligations[0],
            &replay,
            &[],
        );
        let engine = TrustWpVerificationEngine::new().with_native_replay_evidence(vec![evidence]);

        let result = engine.verify_with_context(
            &bundle,
            &bundle.obligations,
            &VerifierExecutionContext::new("trust-wp-replay"),
        );

        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
        assert_eq!(result.summary.proved, 0);
        assert_eq!(result.summary.unsupported, 1);
        assert!(!result.is_fully_proved());
        assert_eq!(result.evidence[0].status, EvidenceStatus::Unsupported);
        assert!(result.evidence[0].proof_strength.is_none());
        assert!(result.evidence[0].artifacts.is_empty());
        assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("VerifyBundleResult")
                && diagnostic.contains(TRUST_WP_AGGREGATE_NATIVE_REPLAY_GATE_SCHEMA_VERSION)
                && diagnostic.contains(TRUST_WP_AGGREGATE_NATIVE_REPLAY_GATE_COMMIT)
        }));
    }

    #[test]
    fn replay_shaped_evidence_missing_replay_artifact_is_rejected_structurally() {
        let obligation = obligation(ObligationKind::Postcondition, "post-missing-replay");
        let bundle = typed_bundle(obligation, typed_expr(true));
        let replay = replay_typed_predicate(&typed_expr(true)).expect("true predicate replays");
        let mut evidence = locally_shaped_candidate_evidence(
            TrustWpVerificationEngine::new().manifest(),
            &bundle,
            &bundle.obligations[0],
            &replay,
            &[],
        );
        evidence.artifacts.retain(|artifact| artifact.kind != EvidenceArtifactKind::ReplayLog);
        let engine = TrustWpVerificationEngine::new().with_native_replay_evidence(vec![evidence]);

        let result = engine.verify_with_context(
            &bundle,
            &bundle.obligations,
            &VerifierExecutionContext::new("trust-wp-replay-missing-artifact"),
        );

        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
        assert_eq!(result.summary.unsupported, 1);
        assert_eq!(result.evidence[0].status, EvidenceStatus::Unsupported);
        assert!(result.evidence[0].proof_strength.is_none());
        assert!(result.evidence[0].artifacts.is_empty());
        assert_eq!(result.evidence[0].evidence_id, "trust-wp:rejected:post-missing-replay");
        assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("missing deterministic native replay artifacts")
                && diagnostic.contains("replay-log")
        }));
    }

    #[cfg(not(feature = "trust-build"))]
    #[test]
    fn typed_requires_and_ensures_do_not_claim_strength_without_aggregate_gate() {
        let bundle = typed_bundle_with_obligations(
            vec![
                obligation(ObligationKind::Precondition, "pre-typed"),
                obligation(ObligationKind::Postcondition, "post-typed"),
            ],
            typed_expr(true),
        );
        let engine = TrustWpVerificationEngine::new();

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 2);
        for item in &evidence {
            assert_eq!(item.engine.name, TRUST_WP_ENGINE_NAME);
            assert_eq!(item.status, EvidenceStatus::Unsupported);
            assert!(item.proof_strength.is_none());
            assert!(item.publication.evidence_bundle_hash.is_none());
            assert!(item.artifacts.is_empty());
            assert!(item.diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("local typed TrustWpPureExprV1 replay")
                    && diagnostic.contains(TRUST_WP_AGGREGATE_NATIVE_REPLAY_GATE_SCHEMA_VERSION)
                    && diagnostic.contains(TRUST_WP_AGGREGATE_NATIVE_REPLAY_GATE_COMMIT)
            }));
            assert!(
                item.diagnostics.iter().any(|diagnostic| {
                    diagnostic.contains("proof_strength")
                        && diagnostic.contains("aggregate native replay evidence gate")
                }),
                "missing aggregate-gate no-strength diagnostic: {:?}",
                item.diagnostics
            );
        }
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    #[test]
    fn trust_build_direct_trust_wp_pure_expr_reports_proof_grade_evidence() {
        let obligation = with_native_artifact_metadata(
            obligation(ObligationKind::Postcondition, "post-direct"),
            "weakest_precondition",
        );
        let bundle = typed_bundle(obligation, TrustWpPureExprV1::Bool { value: true });
        let engine = TrustWpVerificationEngine::new();

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].engine.name, TRUST_WP_ENGINE_NAME);
        assert_eq!(evidence[0].status, EvidenceStatus::Proved);
        assert_eq!(evidence[0].proof_strength, Some(ProofStrength::deductive()));
        assert!(evidence[0].counterexample.is_none());
        assert!(evidence[0].publication.evidence_bundle_hash.is_some());
        assert!(evidence[0].artifacts.iter().any(|artifact| {
            artifact.kind == EvidenceArtifactKind::SolverTranscript
                && artifact.hash.is_hash_addressed()
        }));
        assert!(evidence[0].artifacts.iter().any(|artifact| {
            artifact.kind == EvidenceArtifactKind::EngineInput
                && !artifact.uri.trim().is_empty()
                && artifact.hash.is_hash_addressed()
                && artifact.materialization.is_none()
        }));
        assert!(evidence[0].artifacts.iter().any(|artifact| {
            artifact.kind == EvidenceArtifactKind::BuildManifest
                && !artifact.uri.trim().is_empty()
                && artifact.hash.is_hash_addressed()
                && artifact.materialization.is_none()
        }));
        assert!(evidence[0].artifacts.iter().any(|artifact| {
            artifact.kind == EvidenceArtifactKind::ProofCheckReport
                && !artifact.uri.trim().is_empty()
                && artifact.hash.is_hash_addressed()
        }));
        assert!(
            evidence[0].artifacts.iter().all(|artifact| {
                artifact.uri.starts_with("data:application/vnd.trust_wp.proof-artifact")
                    || artifact.uri.contains("://")
            }),
            "trust-wp proof artifacts must preserve concrete transport URIs: {:?}",
            evidence[0].artifacts
        );
        assert!(
            evidence[0]
                .satisfies_required_strength(bundle.obligations[0].required_strength.as_ref())
        );
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("NativeTrustWpBundleVerifier aggregate VerifyBundleResult")
                && diagnostic.contains(TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION)
        }));
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("trust-wp proof result metadata")
                && diagnostic.contains("trust-wp-core.native-pure-replay")
                && diagnostic.contains("replay_steps=")
        }));
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("trust-wp proof transport artifacts preserved")
                && diagnostic.contains(TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION)
        }));
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("trust-wp native TrustIr identity preserved")
                && diagnostic.contains("function_id=11")
                && diagnostic.contains("obligation_id=13")
                && diagnostic.contains("trust_ir_module_digest=sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
        }));
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    #[test]
    fn trust_build_multi_clause_evidence_uses_one_publication_bundle() {
        let obligations = vec![
            with_native_artifact_metadata(
                obligation(ObligationKind::Postcondition, "post-direct-a"),
                "weakest_precondition",
            ),
            with_native_artifact_metadata(
                obligation(ObligationKind::Postcondition, "post-direct-b"),
                "weakest_precondition",
            ),
        ];
        let bundle =
            typed_bundle_with_obligations(obligations, TrustWpPureExprV1::Bool { value: true });
        let result = TrustWpVerificationEngine::new().verify_with_context(
            &bundle,
            &bundle.obligations,
            &VerifierExecutionContext::new("trust-wp-multi-clause-publication"),
        );

        assert_eq!(result.status, VerificationRunStatus::Proved, "{result:#?}");
        assert_eq!(result.summary.proved, 2);
        assert_eq!(result.summary.publication_conflicts, 0);
        assert_eq!(result.evidence.len(), 2);
        let first = result.evidence[0]
            .publication
            .evidence_bundle_hash
            .as_deref()
            .expect("proof-grade evidence has a publication bundle");
        assert_eq!(result.evidence[1].publication.evidence_bundle_hash.as_deref(), Some(first));
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    #[test]
    fn trust_build_direct_trust_wp_proof_lineage_is_exact_and_mutations_fail_closed() {
        let obligation = with_native_artifact_metadata(
            obligation(ObligationKind::Postcondition, "post-lineage"),
            "weakest_precondition",
        );
        let bundle = typed_bundle(obligation, TrustWpPureExprV1::Bool { value: true });
        let evidence = TrustWpVerificationEngine::new().verify(&bundle, &bundle.obligations);
        let proved = &evidence[0];

        assert_eq!(proved.status, EvidenceStatus::Proved);
        assert!(proved.satisfies_proof_artifact_policy());
        let input = proved
            .artifacts
            .iter()
            .find(|artifact| {
                artifact.kind == EvidenceArtifactKind::NormalizedObligation
                    && artifact.materialization.is_some()
            })
            .expect("one exact combined structural input");
        let transcript = proved
            .artifacts
            .iter()
            .find(|artifact| artifact.kind == EvidenceArtifactKind::SolverTranscript)
            .expect("one exact replay transcript");
        let check = proved
            .artifacts
            .iter()
            .find(|artifact| artifact.kind == EvidenceArtifactKind::ProofCheckReport)
            .expect("one exact proof-check report");
        assert_eq!(
            transcript.materialization.as_ref().expect("transcript bytes").referenced_artifacts(),
            [EvidenceArtifactReference { kind: input.kind, hash: input.hash.clone() }]
        );
        assert_eq!(
            check.materialization.as_ref().expect("check bytes").referenced_artifacts(),
            [EvidenceArtifactReference { kind: transcript.kind, hash: transcript.hash.clone() }]
        );

        let mut owner_transplant = proved.clone();
        owner_transplant.obligation_id = "different-owner".to_string();
        assert!(!owner_transplant.satisfies_proof_artifact_policy());

        let mut role_relabel = proved.clone();
        role_relabel
            .artifacts
            .iter_mut()
            .find(|artifact| artifact.kind == EvidenceArtifactKind::SolverTranscript)
            .expect("transcript")
            .kind = EvidenceArtifactKind::ReplayLog;
        assert!(!role_relabel.satisfies_proof_artifact_policy());

        let mut wrong_input = proved.clone();
        let engine_input = wrong_input
            .artifacts
            .iter()
            .find(|artifact| artifact.kind == EvidenceArtifactKind::EngineInput)
            .expect("request digest descriptor")
            .clone();
        let transcript_index = wrong_input
            .artifacts
            .iter()
            .position(|artifact| artifact.kind == EvidenceArtifactKind::SolverTranscript)
            .expect("transcript");
        let transcript_materialization = wrong_input.artifacts[transcript_index]
            .materialization
            .as_ref()
            .expect("transcript bytes");
        let transcript_payload = transcript_materialization
            .bound_payload_bytes(EvidenceArtifactKind::SolverTranscript, "post-lineage")
            .expect("valid transcript envelope");
        let proof_binding_id = transcript_materialization.proof_binding_id().to_string();
        let (wrong_transcript_materialization, wrong_transcript_hash) =
            EvidenceArtifactMaterialization::new_bound(
                EvidenceArtifactKind::SolverTranscript,
                &transcript_payload,
                &proof_binding_id,
                "post-lineage",
                vec![EvidenceArtifactReference {
                    kind: engine_input.kind,
                    hash: engine_input.hash,
                }],
            )
            .expect("wrong lineage still has a well-formed envelope");
        wrong_input.artifacts[transcript_index].materialization =
            Some(wrong_transcript_materialization);
        wrong_input.artifacts[transcript_index].hash = wrong_transcript_hash.clone();
        wrong_input.artifacts[transcript_index].uri = format!(
            "artifact://trust-wp/proof-artifacts/solver-transcript/{}",
            wrong_transcript_hash.value
        );
        let check_index = wrong_input
            .artifacts
            .iter()
            .position(|artifact| artifact.kind == EvidenceArtifactKind::ProofCheckReport)
            .expect("check");
        let check_materialization =
            wrong_input.artifacts[check_index].materialization.as_ref().expect("check bytes");
        let check_payload = check_materialization
            .bound_payload_bytes(EvidenceArtifactKind::ProofCheckReport, "post-lineage")
            .expect("valid check envelope");
        let (new_check_materialization, new_check_hash) =
            EvidenceArtifactMaterialization::new_bound(
                EvidenceArtifactKind::ProofCheckReport,
                &check_payload,
                &proof_binding_id,
                "post-lineage",
                vec![EvidenceArtifactReference {
                    kind: EvidenceArtifactKind::SolverTranscript,
                    hash: wrong_transcript_hash,
                }],
            )
            .expect("updated check envelope");
        let new_check_uri = format!(
            "artifact://trust-wp/proof-artifacts/proof-check-report/{}",
            new_check_hash.value
        );
        wrong_input.artifacts[check_index].materialization = Some(new_check_materialization);
        wrong_input.artifacts[check_index].hash = new_check_hash;
        wrong_input.artifacts[check_index].uri = new_check_uri;
        assert!(!wrong_input.satisfies_proof_artifact_policy());
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    #[test]
    fn trust_build_direct_trust_wp_requires_structured_native_artifact_context() {
        let obligation = obligation(ObligationKind::Postcondition, "post-missing-native-context");
        let bundle = typed_bundle(obligation, TrustWpPureExprV1::Bool { value: true });

        let evidence = TrustWpVerificationEngine::new().verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].artifacts.is_empty());
        // Pins that obligations without typed native replay metadata fail
        // closed on the missing-key diagnostic. Current spellings: adapter
        // wrapper "trust_wp native replay metadata", trust-wp-core error
        // "missing required trust-wp metadata key".
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("trust_wp native replay metadata")
                && diagnostic.contains("missing required trust-wp metadata key")
        }));
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    #[test]
    fn trust_build_direct_trust_wp_rejects_string_marker_native_artifact_context() {
        let mut obligation =
            obligation(ObligationKind::Postcondition, "post-string-marker-native-context");
        for key in TRUST_TRUST_WP_NATIVE_REPLAY_REQUIRED_METADATA_KEYS {
            obligation
                .metadata
                .push(MetadataEntry { key: key.to_string(), value: "present".to_string() });
        }
        let bundle = typed_bundle(obligation, TrustWpPureExprV1::Bool { value: true });

        let evidence = TrustWpVerificationEngine::new().verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].artifacts.is_empty());
        // Pins that string-marker metadata values ("present") are rejected as
        // proof context. Current adapter wrapper spelling is "trust_wp native
        // replay metadata ... refusing proof strength from
        // metadata-only/string-marker evidence".
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("trust_wp native replay metadata")
                && diagnostic.contains("string-marker")
        }));
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    #[test]
    fn trust_build_direct_trust_wp_rejects_placeholder_native_solver_context() {
        use trust_wp_core::verify_bundle::BundleNativeToolIdentity;

        let mut obligation = with_native_artifact_metadata(
            obligation(ObligationKind::Postcondition, "post-placeholder-native-solver"),
            "weakest_precondition",
        );
        let solver_entry = obligation
            .metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_WP_NATIVE_SOLVER_METADATA_KEY)
            .expect("test metadata includes solver identity");
        solver_entry.value = serde_json::to_string(&BundleNativeToolIdentity::new("unknown"))
            .expect("placeholder solver serializes");
        let bundle = typed_bundle(obligation, TrustWpPureExprV1::Bool { value: true });

        let evidence = TrustWpVerificationEngine::new().verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].artifacts.is_empty());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("native_solvers") && diagnostic.contains("empty placeholder")
        }));
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    #[test]
    fn trust_build_request_rejects_semantic_proof_context_injection_and_round_trips_names() {
        use std::sync::Arc;

        use trust_wp_core::{
            formula::{BinOp, PureExpr},
            verify_bundle::{
                BundleClaim, BundleClaimFormat, BundleProofAtom, BundleProofAtomRole,
                BundleProofContext, BundleTmirSourceSpan, native_predicate_for_obligation,
            },
        };

        fn atom(
            index: u32,
            role: BundleProofAtomRole,
            format: BundleClaimFormat,
            payload: impl Into<String>,
        ) -> BundleProofAtom {
            BundleProofAtom::new(index, role, BundleClaim::new(format, payload))
                .with_native_replay_atom_id(100 + index)
                .with_native_obligation_id(13)
                .with_native_span(BundleTmirSourceSpan::new(4, 29, 7))
        }

        fn bundle_with_context(
            context: BundleProofContext,
            predicate: TrustWpPureExprV1,
        ) -> TrustContractBundle {
            let mut obligation = with_native_artifact_metadata(
                obligation(ObligationKind::Postcondition, "post-context-semantic-choke"),
                "weakest_precondition",
            );
            obligation.metadata.push(MetadataEntry {
                key: TRUST_WP_PROOF_CONTEXT_METADATA_KEY.to_string(),
                value: serde_json::to_string(&context).expect("proof context serializes"),
            });
            typed_bundle(obligation, predicate)
        }

        fn lower_request(
            bundle: &TrustContractBundle,
        ) -> Result<trust_wp_core::verify_bundle::VerifyBundleRequest, NativeContractLoweringOutcome>
        {
            let claim = typed_trust_wp_claim(bundle, &bundle.obligations[0])
                .expect("true/opaque-name target claim lowers");
            trust_wp_verify_bundle_request(bundle, &bundle.obligations[0], &claim, None)
        }

        fn lowering_diagnostic(error: NativeContractLoweringOutcome) -> String {
            match error {
                NativeContractLoweringOutcome::Failed { diagnostic, .. }
                | NativeContractLoweringOutcome::Unsupported { diagnostic } => diagnostic,
            }
        }

        let arithmetic_formula = serde_json::json!({
            "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
            "variables": [{"name": "x", "sort": "int"}],
            "body": {
                "op": "eq",
                "lhs": {
                    "op": "mul",
                    "lhs": {"var": "x"},
                    "rhs": {"var": "x"},
                },
                "rhs": {"var": "x"},
            },
        })
        .to_string();
        let arithmetic_contexts = [
            BundleProofContext::new(
                vec![atom(
                    0,
                    BundleProofAtomRole::Assumption,
                    BundleClaimFormat::TrustWpPureExprV1,
                    "(x * 2) > x",
                )],
                Vec::new(),
            ),
            BundleProofContext::new(
                Vec::new(),
                vec![atom(
                    0,
                    BundleProofAtomRole::Assertion,
                    BundleClaimFormat::TrustFormulaV1,
                    arithmetic_formula,
                )],
            ),
        ];
        for context in arithmetic_contexts {
            let bundle = bundle_with_context(context, TrustWpPureExprV1::Bool { value: true });
            let Err(NativeContractLoweringOutcome::Unsupported { diagnostic }) =
                lower_request(&bundle)
            else {
                panic!("arithmetic proof-context metadata must fail at final request choke point");
            };
            assert!(diagnostic.contains("arithmetic operator"), "{diagnostic}");
        }

        // These shapes are deliberately transparent or richer syntax in the
        // sibling parser. None may be reinterpreted into the tiny proof-input
        // fragment, even when it becomes a reflexive tautology after parsing.
        for payload in [
            "x as u8 == x",
            "(x: u8) == x",
            "f(x) == f(x)",
            "x.field == x.field",
            "old(x) == old(x)",
            "x[0] == x[0]",
        ] {
            let context = BundleProofContext::new(
                vec![atom(
                    0,
                    BundleProofAtomRole::Assumption,
                    BundleClaimFormat::TrustWpPureExprV1,
                    payload,
                )],
                Vec::new(),
            );
            let bundle = bundle_with_context(context, TrustWpPureExprV1::Bool { value: true });
            let Err(NativeContractLoweringOutcome::Unsupported { diagnostic }) =
                lower_request(&bundle)
            else {
                panic!("reinterpretable proof-context payload must fail: {payload}");
            };
            assert!(diagnostic.contains("proof-context assumption"), "{payload}: {diagnostic}");
        }

        for format in
            [BundleClaimFormat::SmtLib2, BundleClaimFormat::Other("opaque.test.v1".to_string())]
        {
            let context = BundleProofContext::new(
                vec![atom(0, BundleProofAtomRole::Assumption, format, "true")],
                Vec::new(),
            );
            let bundle = bundle_with_context(context, TrustWpPureExprV1::Bool { value: true });
            assert!(
                matches!(
                    lower_request(&bundle),
                    Err(NativeContractLoweringOutcome::Unsupported { .. })
                ),
                "opaque proof-context formats have no native decoder"
            );
        }

        let formula_true = serde_json::json!({
            "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
            "body": {"bool": true},
        })
        .to_string();
        let positive_context = BundleProofContext::new(
            vec![atom(
                0,
                BundleProofAtomRole::Assumption,
                BundleClaimFormat::TrustWpPureExprV1,
                "(_ctx >= -5) && (ready == true)",
            )],
            vec![atom(
                1,
                BundleProofAtomRole::Assertion,
                BundleClaimFormat::TrustFormulaV1,
                formula_true,
            )],
        );
        let target = TrustWpPureExprV1::Binary {
            op: TrustWpPureBinaryOpV1::Ge,
            lhs: Box::new(TrustWpPureExprV1::Var {
                name: "_x_0_s1".to_string(),
                sort: TrustWpPureSortV1::Int,
            }),
            rhs: Box::new(TrustWpPureExprV1::Int { value: -5 }),
        };
        let bundle = bundle_with_context(positive_context, target);
        let request = lower_request(&bundle).unwrap_or_else(|error| {
            panic!("arithmetic-free context must lower: {}", lowering_diagnostic(error))
        });
        let native = native_predicate_for_obligation(&request.obligations[0])
            .expect("final emitted target has an exact native decoder");
        assert_eq!(
            native.predicate,
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("_x_0_s1".to_string(), None)),
                BinOp::Ge,
                Arc::new(PureExpr::Int(-5)),
            ),
            "the final stable serializer/native parser round trip preserves the variable token structurally",
        );
        assert_eq!(request.obligations[0].metadata.proof_context.assumptions.len(), 1);
        assert_eq!(request.obligations[0].metadata.proof_context.assertions.len(), 1);

        // Every canonical PureExpr shape must normalize to the same final wire
        // payload in the target and in attached context. In particular, direct
        // Bool-variable Eq/Ne is anchored exactly once and remains structurally
        // identical after the sibling parser sees it.
        let bool_var = |name: &str| TrustWpPureExprV1::Var {
            name: name.to_string(),
            sort: TrustWpPureSortV1::Bool,
        };
        let bool_eq = || TrustWpPureExprV1::Binary {
            op: TrustWpPureBinaryOpV1::Eq,
            lhs: Box::new(bool_var("flag")),
            rhs: Box::new(bool_var("ready")),
        };
        let pure_cases = [
            ("bool-var", bool_var("flag")),
            ("not", TrustWpPureExprV1::Not { expr: Box::new(bool_var("flag")) }),
            (
                "and",
                TrustWpPureExprV1::Binary {
                    op: TrustWpPureBinaryOpV1::And,
                    lhs: Box::new(bool_var("flag")),
                    rhs: Box::new(bool_var("ready")),
                },
            ),
            (
                "eq-true",
                TrustWpPureExprV1::Binary {
                    op: TrustWpPureBinaryOpV1::Eq,
                    lhs: Box::new(bool_var("flag")),
                    rhs: Box::new(TrustWpPureExprV1::Bool { value: true }),
                },
            ),
            ("bool-eq", bool_eq()),
            (
                "bool-ne",
                TrustWpPureExprV1::Binary {
                    op: TrustWpPureBinaryOpV1::Ne,
                    lhs: Box::new(bool_var("flag")),
                    rhs: Box::new(bool_var("ready")),
                },
            ),
            ("nested-bool-eq", TrustWpPureExprV1::Not { expr: Box::new(bool_eq()) }),
            (
                "int-comparison",
                TrustWpPureExprV1::Binary {
                    op: TrustWpPureBinaryOpV1::Ge,
                    lhs: Box::new(TrustWpPureExprV1::Var {
                        name: "count".to_string(),
                        sort: TrustWpPureSortV1::Int,
                    }),
                    rhs: Box::new(TrustWpPureExprV1::Int { value: -5 }),
                },
            ),
        ];
        for (case, source_target) in pure_cases {
            let canonical_target = canonicalize_trust_wp_pure_expr(source_target.clone());
            let canonical = canonical_target.stable_text();
            let wire = canonical_target.native_replay_text();
            let context = BundleProofContext::new(
                vec![atom(
                    0,
                    BundleProofAtomRole::Assumption,
                    BundleClaimFormat::TrustWpPureExprV1,
                    canonical,
                )],
                Vec::new(),
            );
            let bundle = bundle_with_context(context, source_target);
            let request = lower_request(&bundle).unwrap_or_else(|error| {
                panic!("{case}: PureExpr target/context lowers: {}", lowering_diagnostic(error))
            });
            let obligation = &request.obligations[0];
            assert_eq!(obligation.claim.payload, wire, "{case}: target wire payload");
            let context_claim = &obligation.metadata.proof_context.assumptions[0].claim;
            assert_eq!(context_claim.payload, wire, "{case}: context wire payload");

            let target_native = native_predicate_for_obligation(obligation)
                .unwrap_or_else(|error| panic!("{case}: target native decode: {error:?}"));
            let context_probe = trust_wp_core::verify_bundle::BundleObligation::new(
                format!("context-{case}"),
                trust_wp_core::verify_bundle::BundleObligationKind::Postcondition,
                format!("demo::context::{case}"),
                context_claim.clone(),
            );
            let context_native = native_predicate_for_obligation(&context_probe)
                .unwrap_or_else(|error| panic!("{case}: context native decode: {error:?}"));
            assert_eq!(
                target_native.predicate, context_native.predicate,
                "{case}: target/context native AST parity",
            );
        }

        // The structured format admits exactly the state/binder nodes in the
        // shared schema. Exercise them through the real metadata attachment,
        // final normalization, and sibling decoder—not only the common JSON
        // validator. The `let` case is the compiler-shaped result binding.
        let structured_cases = [
            (
                "old",
                serde_json::json!({
                    "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
                    "variables": [{"name": "x", "sort": "int"}],
                    "body": {
                        "op": "eq",
                        "lhs": {"old": {"var": "x"}},
                        "rhs": {"var": "x"},
                    },
                }),
            ),
            (
                "let",
                serde_json::json!({
                    "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
                    "variables": [{"name": "x", "sort": "int"}],
                    "body": {
                        "op": "let",
                        "name": "result",
                        "sort": "int",
                        "value": {"var": "x"},
                        "body": {
                            "op": "ge",
                            "lhs": {"var": "result"},
                            "rhs": {"var": "x"},
                        },
                    },
                }),
            ),
            (
                "forall",
                serde_json::json!({
                    "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
                    "body": {
                        "op": "forall",
                        "name": "i",
                        "sort": "int",
                        "body": {"op": "eq", "lhs": {"var": "i"}, "rhs": {"var": "i"}},
                    },
                }),
            ),
            (
                "exists",
                serde_json::json!({
                    "schema": TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
                    "body": {
                        "op": "exists",
                        "name": "i",
                        "sort": "int",
                        "body": {"op": "eq", "lhs": {"var": "i"}, "rhs": {"var": "i"}},
                    },
                }),
            ),
        ];
        for (case, envelope) in structured_cases {
            let payload = serde_json::to_string(&envelope).expect("TrustFormula serializes");
            let noncanonical_context_payload =
                serde_json::to_string_pretty(&envelope).expect("pretty TrustFormula serializes");
            assert_ne!(
                noncanonical_context_payload, payload,
                "fixture must exercise context canonicalization"
            );
            let context = BundleProofContext::new(
                Vec::new(),
                vec![atom(
                    0,
                    BundleProofAtomRole::Assertion,
                    BundleClaimFormat::TrustFormulaV1,
                    noncanonical_context_payload,
                )],
            );
            let bundle = bundle_with_context(context, TrustWpPureExprV1::Bool { value: true });
            let claim = NativeTrustWpClaim::TrustFormulaV1(payload);
            let request =
                trust_wp_verify_bundle_request(&bundle, &bundle.obligations[0], &claim, None)
                    .unwrap_or_else(|error| {
                        panic!(
                            "{case}: structured target/context must survive final choke point: {}",
                            lowering_diagnostic(error)
                        )
                    });
            let obligation = &request.obligations[0];
            let target_native = native_predicate_for_obligation(obligation)
                .unwrap_or_else(|error| panic!("{case}: target native decode: {error:?}"));
            let context_claim = &obligation.metadata.proof_context.assertions[0].claim;
            assert_eq!(
                context_claim.payload, obligation.claim.payload,
                "{case}: target/context canonical TrustFormula payload parity"
            );
            let context_probe = trust_wp_core::verify_bundle::BundleObligation::new(
                format!("structured-context-{case}"),
                trust_wp_core::verify_bundle::BundleObligationKind::Postcondition,
                format!("demo::structured_context::{case}"),
                context_claim.clone(),
            );
            let context_native = native_predicate_for_obligation(&context_probe)
                .unwrap_or_else(|error| panic!("{case}: context native decode: {error:?}"));
            assert_eq!(
                target_native.predicate, context_native.predicate,
                "{case}: structured target/context native AST parity",
            );
        }
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    #[test]
    fn trust_build_request_rejects_duplicate_raw_proof_context_metadata_before_typed_decode() {
        fn bundle_with_raw_context(raw: &str) -> TrustContractBundle {
            let mut obligation = with_native_artifact_metadata(
                obligation(ObligationKind::Postcondition, "post-duplicate-proof-context"),
                "weakest_precondition",
            );
            obligation.metadata.push(MetadataEntry {
                key: TRUST_WP_PROOF_CONTEXT_METADATA_KEY.to_string(),
                value: raw.to_string(),
            });
            typed_bundle(obligation, TrustWpPureExprV1::Bool { value: true })
        }

        fn request_error(bundle: &TrustContractBundle) -> String {
            let claim = typed_trust_wp_claim(bundle, &bundle.obligations[0])
                .expect("target claim is independent of malformed context metadata");
            let Err(NativeContractLoweringOutcome::Unsupported { diagnostic }) =
                trust_wp_verify_bundle_request(bundle, &bundle.obligations[0], &claim, None)
            else {
                panic!("ambiguous raw proof-context metadata must fail closed");
            };
            diagnostic
        }

        let duplicate_assumptions = r#"{"assumptions":[],"assumptions":[],"assertions":[]}"#;
        let error = request_error(&bundle_with_raw_context(duplicate_assumptions));
        assert!(error.contains("duplicate JSON object key `assumptions`"), "{error}");

        let duplicate_nested_payload = r#"{
            "assumptions":[{
                "index":0,
                "role":"assumption",
                "claim":{
                    "format":"trust_wp_pure_expr_v1",
                    "payload":"true",
                    "payload":"false"
                }
            }],
            "assertions":[]
        }"#;
        let error = request_error(&bundle_with_raw_context(duplicate_nested_payload));
        assert!(error.contains("duplicate JSON object key `payload`"), "{error}");

        let mut split_scope = bundle_with_raw_context(r#"{"assumptions":[],"assertions":[]}"#);
        split_scope.metadata.push(MetadataEntry {
            key: TRUST_WP_PROOF_CONTEXT_METADATA_KEY.to_string(),
            value: r#"{"assumptions":[],"assertions":[]}"#.to_string(),
        });
        let error = request_error(&split_scope);
        assert!(error.contains("appeared more than once"), "{error}");
        assert!(error.contains(TRUST_WP_PROOF_CONTEXT_METADATA_KEY), "{error}");
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    #[test]
    fn trust_build_direct_trust_wp_rejects_malformed_proof_context_bindings() {
        use trust_wp_core::verify_bundle::{
            BundleClaim, BundleClaimFormat, BundleProofAtom, BundleProofAtomRole,
            BundleProofContext, BundleTmirObligationCause, BundleTmirObligationSource,
            BundleTmirSourceSpan,
        };

        fn assertion_atom() -> BundleProofAtom {
            BundleProofAtom::new(
                0,
                BundleProofAtomRole::Assertion,
                BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "true"),
            )
            .with_native_replay_atom_id(9)
            .with_native_obligation_id(13)
            .with_native_assertion_id(42)
            .with_native_span(BundleTmirSourceSpan::new(4, 29, 7))
        }

        fn obligation_with_proof_context(context: BundleProofContext) -> TrustObligation {
            let mut obligation = with_native_artifact_metadata(
                obligation(ObligationKind::Postcondition, "post-bad-proof-context"),
                "weakest_precondition",
            );
            let source = BundleTmirObligationSource::new(BundleTmirObligationCause::Postcondition)
                .with_function_id(11)
                .with_assertion_id(42);
            let source_entry = obligation
                .metadata
                .iter_mut()
                .find(|entry| entry.key == TRUST_WP_TMIR_OBLIGATION_SOURCE_METADATA_KEY)
                .expect("test metadata includes TrustIr obligation source");
            source_entry.value =
                serde_json::to_string(&source).expect("obligation source serializes");
            obligation.metadata.push(MetadataEntry {
                key: TRUST_WP_PROOF_CONTEXT_METADATA_KEY.to_string(),
                value: serde_json::to_string(&context).expect("proof context serializes"),
            });
            obligation
        }

        fn assert_rejected(mut atom: BundleProofAtom, expected_code: &str) {
            if expected_code == "obligation.metadata.proof_context.native_replay_atom_id" {
                atom.native_replay_atom_id = None;
            }
            let bundle = typed_bundle(
                obligation_with_proof_context(BundleProofContext::new(Vec::new(), vec![atom])),
                TrustWpPureExprV1::Bool { value: true },
            );
            let claim =
                typed_trust_wp_claim(&bundle, &bundle.obligations[0]).expect("typed claim lowers");
            let request =
                match trust_wp_verify_bundle_request(&bundle, &bundle.obligations[0], &claim, None)
                {
                    Ok(request) => request,
                    Err(_) => panic!("malformed proof context should reach request validation"),
                };

            let diagnostics = request.validation_diagnostics();
            assert!(
                diagnostics.iter().any(|diagnostic| diagnostic.code == expected_code),
                "missing `{expected_code}` diagnostic: {diagnostics:?}"
            );

            let evidence = TrustWpVerificationEngine::new().verify(&bundle, &bundle.obligations);
            assert_eq!(evidence.len(), 1);
            assert_ne!(evidence[0].status, EvidenceStatus::Proved);
            assert!(evidence[0].proof_strength.is_none());
            assert!(evidence[0].artifacts.is_empty());
        }

        assert_rejected(
            assertion_atom().with_native_obligation_id(99),
            "obligation.metadata.proof_context.native_obligation_id",
        );
        assert_rejected(
            assertion_atom().with_native_assertion_id(7),
            "obligation.metadata.proof_context.native_assertion_id",
        );
        assert_rejected(
            assertion_atom().with_native_span(BundleTmirSourceSpan::new(4, 30, 7)),
            "obligation.metadata.proof_context.native_span",
        );
        assert_rejected(
            assertion_atom(),
            "obligation.metadata.proof_context.native_replay_atom_id",
        );

        let unbound_assertion = BundleProofAtom::new(
            0,
            BundleProofAtomRole::Assertion,
            BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "true"),
        )
        .with_native_replay_atom_id(10)
        .with_native_span(BundleTmirSourceSpan::new(4, 29, 7));
        assert_rejected(unbound_assertion, "obligation.metadata.proof_context.assertion_binding");
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    #[test]
    fn trust_build_direct_trust_wp_preserves_summary_transport_artifact() {
        let mut obligation = with_native_artifact_metadata(
            obligation(ObligationKind::Postcondition, "post-summary-direct"),
            "weakest_precondition",
        );
        obligation.summary_facts.push(summary_fact(
            "summary-pointer-p-q",
            "5555555555555555555555555555555555555555555555555555555555555555",
        ));
        let bundle = typed_bundle(obligation, TrustWpPureExprV1::Bool { value: true });

        let evidence = TrustWpVerificationEngine::new().verify(&bundle, &bundle.obligations);

        assert_eq!(
            evidence[0].status,
            EvidenceStatus::Proved,
            "diagnostics: {:?}",
            evidence[0].diagnostics
        );
        assert!(evidence[0].artifacts.iter().any(|artifact| {
            artifact.kind == EvidenceArtifactKind::SummaryEvidence
                && !artifact.uri.trim().is_empty()
                && artifact.hash.is_hash_addressed()
                && artifact.materialization.is_none()
        }));
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    #[test]
    fn trust_build_direct_trust_wp_preserves_native_ai_summary_fact_artifact() {
        use trust_wp_core::verify_bundle::{
            BundleDigest, BundleSummaryFact as TrustWpSummaryFact,
            BundleSummaryFactKind as TrustWpSummaryFactKind,
        };

        let mut obligation = with_native_artifact_metadata(
            obligation(ObligationKind::Postcondition, "post-native-ai-summary"),
            "weakest_precondition",
        );
        let native_summary = TrustWpSummaryFact::new(
            "ai-pointer-binding",
            "TrustIr.abstract-interpretation",
            "dep_crate",
            "dep_crate::callee",
            TrustWpSummaryFactKind::PointerProvenanceEqBinding {
                left: "p_left".to_string(),
                right: "p_right".to_string(),
            },
            BundleDigest::new(
                "sha256",
                "6666666666666666666666666666666666666666666666666666666666666666",
            ),
        );
        obligation.metadata.push(MetadataEntry {
            key: TRUST_WP_NATIVE_SUMMARY_FACT_METADATA_KEY.to_string(),
            value: serde_json::to_string(&native_summary).expect("native summary serializes"),
        });
        let bundle = typed_bundle(obligation, TrustWpPureExprV1::Bool { value: true });

        let evidence = TrustWpVerificationEngine::new().verify(&bundle, &bundle.obligations);

        assert_eq!(
            evidence[0].status,
            EvidenceStatus::Proved,
            "diagnostics: {:?}",
            evidence[0].diagnostics
        );
        assert!(evidence[0].artifacts.iter().any(|artifact| {
            artifact.kind == EvidenceArtifactKind::SummaryEvidence
                && !artifact.uri.trim().is_empty()
                && artifact.hash.is_hash_addressed()
                && artifact.materialization.is_none()
        }));
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api,
        trust_wp_verify_bundle_replay_helper_api
    ))]
    #[test]
    fn trust_build_direct_trust_wp_replays_and_validates_result_metadata() {
        let obligation = with_native_artifact_metadata(
            obligation(ObligationKind::Postcondition, "post-result-metadata"),
            "weakest_precondition",
        );
        let bundle = typed_bundle(obligation, TrustWpPureExprV1::Bool { value: true });
        let claim =
            typed_trust_wp_claim(&bundle, &bundle.obligations[0]).expect("typed claim lowers");
        let request =
            match trust_wp_verify_bundle_request(&bundle, &bundle.obligations[0], &claim, None) {
                Ok(request) => request,
                Err(_) => panic!("request lowers"),
            };

        let result = {
            use trust_wp_core::verify_bundle::VerifyBundleEngine as _;
            trust_wp_core::verify_bundle::NativeTrustWpBundleVerifier.verify_bundle(request.clone())
        };
        trust_wp_core::verify_bundle::replay_verify_bundle_result_evidence(&request, &result)
            .expect("aggregate proof evidence replays");
        let obligation_result = result.obligation_results.first().expect("obligation result");
        let trust_wp_core::verify_bundle::BundleObligationStatus::Verified { evidence } =
            &obligation_result.status
        else {
            panic!("native direct verifier should prove true predicate");
        };

        validate_trust_wp_proof_result_metadata(
            &bundle.obligations[0],
            &claim,
            &obligation_result.metadata,
            evidence,
        )
        .expect("typed proof result metadata validates");
        assert_eq!(
            obligation_result
                .metadata
                .evidence
                .as_ref()
                .and_then(|metadata| { metadata.digest.as_ref() }),
            evidence.digest.as_ref()
        );

        let mut missing_solver = obligation_result.metadata.clone();
        missing_solver.solver = None;
        let err = validate_trust_wp_proof_result_metadata(
            &bundle.obligations[0],
            &claim,
            &missing_solver,
            evidence,
        )
        .expect_err("missing solver metadata fails closed");
        assert!(err.contains("missing solver/replay metadata"));

        let mut stale_result = result.clone();
        stale_result.aggregate_evidence = None;
        let err = trust_wp_core::verify_bundle::replay_verify_bundle_result_evidence(
            &request,
            &stale_result,
        )
        .expect_err("missing aggregate replay evidence fails closed");
        assert!(err.to_string().contains("missing aggregate proof evidence"));
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api,
        trust_wp_verify_bundle_replay_helper_api
    ))]
    #[test]
    fn trust_build_direct_trust_wp_rejects_replay_after_dropping_assumptions() {
        use trust_wp_core::verify_bundle::{
            BundleClaim, BundleClaimFormat, BundleProofAtom, BundleProofAtomRole,
            BundleProofContext, BundleTmirSourceSpan,
        };

        let mut obligation = with_native_artifact_metadata(
            obligation(ObligationKind::Postcondition, "post-assumption-drop"),
            "weakest_precondition",
        );
        obligation.metadata.push(MetadataEntry {
            key: TRUST_WP_PROOF_CONTEXT_METADATA_KEY.to_string(),
            value: serde_json::to_string(&BundleProofContext::new(
                vec![
                    BundleProofAtom::new(
                        0,
                        BundleProofAtomRole::Assumption,
                        BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "true"),
                    )
                    .with_native_replay_atom_id(8)
                    .with_native_obligation_id(13)
                    .with_native_span(BundleTmirSourceSpan::new(4, 29, 7)),
                ],
                vec![
                    BundleProofAtom::new(
                        1,
                        BundleProofAtomRole::Assertion,
                        BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "true"),
                    )
                    .with_native_replay_atom_id(9)
                    .with_native_obligation_id(13)
                    .with_native_span(BundleTmirSourceSpan::new(4, 29, 7)),
                ],
            ))
            .expect("proof context serializes"),
        });
        let bundle = typed_bundle(obligation, TrustWpPureExprV1::Bool { value: true });
        let claim =
            typed_trust_wp_claim(&bundle, &bundle.obligations[0]).expect("typed claim lowers");
        let request =
            match trust_wp_verify_bundle_request(&bundle, &bundle.obligations[0], &claim, None) {
                Ok(request) => request,
                Err(_) => panic!("request lowers"),
            };

        let result = {
            use trust_wp_core::verify_bundle::VerifyBundleEngine as _;
            trust_wp_core::verify_bundle::NativeTrustWpBundleVerifier.verify_bundle(request.clone())
        };
        trust_wp_core::verify_bundle::replay_verify_bundle_result_evidence(&request, &result)
            .expect("aggregate proof evidence replays with full context");
        let obligation_result = result.obligation_results.first().expect("obligation result");
        assert_eq!(
            obligation_result.metadata.solver.as_ref().map(|solver| solver.assumptions),
            Some(1)
        );
        assert_eq!(
            obligation_result.metadata.solver.as_ref().map(|solver| solver.assertions),
            Some(1)
        );

        let mut dropped_assumption_request = request.clone();
        dropped_assumption_request.obligations[0].metadata.proof_context.assumptions.clear();
        dropped_assumption_request.obligations[0].metadata.proof_context.assertions[0].index = 0;
        let err = trust_wp_core::verify_bundle::replay_verify_bundle_result_evidence(
            &dropped_assumption_request,
            &result,
        )
        .expect_err("dropping proof-context assumptions must invalidate proof evidence replay");

        assert_eq!(err.code, "proof_replay.mismatch");
        assert!(err.message.contains("proof context") || err.message.contains("request"));
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    #[test]
    fn trust_build_direct_trust_wp_rejects_text_only_transport_artifacts() {
        let obligation = with_native_artifact_metadata(
            obligation(ObligationKind::Postcondition, "post-text-only"),
            "weakest_precondition",
        );
        let bundle = typed_bundle(obligation, TrustWpPureExprV1::Bool { value: true });
        let claim =
            typed_trust_wp_claim(&bundle, &bundle.obligations[0]).expect("typed claim lowers");
        let request =
            match trust_wp_verify_bundle_request(&bundle, &bundle.obligations[0], &claim, None) {
                Ok(request) => request,
                Err(_) => panic!("request lowers"),
            };
        let result = {
            use trust_wp_core::verify_bundle::VerifyBundleEngine as _;
            trust_wp_core::verify_bundle::NativeTrustWpBundleVerifier.verify_bundle(request)
        };
        let obligation_result = result.obligation_results.first().expect("obligation result");
        let trust_wp_core::verify_bundle::BundleObligationStatus::Verified { evidence } =
            &obligation_result.status
        else {
            panic!("native direct verifier should prove true predicate");
        };
        let aggregate_evidence = result.aggregate_evidence.as_ref().expect("aggregate evidence");

        let mut text_only_evidence = evidence.clone();
        for artifact in &mut text_only_evidence.artifacts {
            artifact.uri = None;
            artifact.inline_bytes = None;
        }
        let err = trust_wp_verified_evidence_to_trust(
            TrustWpVerificationEngine::new().manifest(),
            &bundle,
            &bundle.obligations[0],
            &claim,
            &obligation_result.metadata,
            &text_only_evidence,
            aggregate_evidence,
        )
        .expect_err("text-only native replay artifacts fail closed");
        assert!(err.contains("text-only") && err.contains("without URI or inline transport bytes"));

        let mut text_only_aggregate = aggregate_evidence.clone();
        for artifact in &mut text_only_aggregate.artifacts {
            artifact.uri = None;
            artifact.inline_bytes = None;
        }
        let err = trust_wp_verified_evidence_to_trust(
            TrustWpVerificationEngine::new().manifest(),
            &bundle,
            &bundle.obligations[0],
            &claim,
            &obligation_result.metadata,
            evidence,
            &text_only_aggregate,
        )
        .expect_err("text-only aggregate manifest artifacts fail closed");
        assert!(err.contains("text-only") && err.contains("aggregate proof manifest"));
    }

    #[cfg(all(
        feature = "trust-build",
        trust_wp_proof_transport_api,
        trust_wp_structured_context_api
    ))]
    #[test]
    fn trust_build_direct_trust_wp_preserves_wp_sp_abduction_origin_modes() {
        for mode in ["weakest_precondition", "strongest_postcondition", "abduction"] {
            let obligation = with_native_artifact_metadata(
                obligation(ObligationKind::Postcondition, &format!("post-origin-{mode}")),
                mode,
            );
            let bundle = typed_bundle(obligation, TrustWpPureExprV1::Bool { value: true });
            let claim =
                typed_trust_wp_claim(&bundle, &bundle.obligations[0]).expect("typed claim lowers");
            let request =
                match trust_wp_verify_bundle_request(&bundle, &bundle.obligations[0], &claim, None)
                {
                    Ok(request) => request,
                    Err(_) => panic!("native-origin metadata lowers"),
                };
            assert_eq!(
                request.obligations[0]
                    .metadata
                    .native_origin
                    .as_ref()
                    .map(|origin| origin.mode.as_str()),
                Some(mode)
            );

            let evidence = TrustWpVerificationEngine::new().verify(&bundle, &bundle.obligations);

            assert_eq!(
                evidence[0].status,
                EvidenceStatus::Proved,
                "diagnostics: {:?}",
                evidence[0].diagnostics
            );
            assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
                diagnostic.contains(&format!("trust-wp native origin mode preserved: {mode}"))
            }));
        }
    }

    #[test]
    fn false_typed_postcondition_fails_without_proof_strength_upgrade() {
        let obligation = obligation(ObligationKind::Postcondition, "post-false");
        #[cfg(all(
            feature = "trust-build",
            trust_wp_proof_transport_api,
            trust_wp_structured_context_api
        ))]
        let obligation = with_native_artifact_metadata(obligation, "weakest_precondition");
        let bundle = typed_bundle(obligation, typed_expr(false));
        let engine = TrustWpVerificationEngine::new();

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        #[cfg(all(feature = "trust-build", not(trust_wp_proof_transport_api)))]
        {
            assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
            assert!(evidence[0].proof_strength.is_none());
            assert!(evidence[0].artifacts.is_empty());
            assert!(
                evidence[0]
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.contains(TRUST_WP_PROOF_TRANSPORT_API_MISSING))
            );
            return;
        }

        #[cfg(not(all(feature = "trust-build", not(trust_wp_proof_transport_api))))]
        {
            assert_eq!(evidence[0].status, EvidenceStatus::Failed);
            assert!(evidence[0].proof_strength.is_none());
            assert!(evidence[0].artifacts.is_empty());
            assert!(evidence[0].counterexample.is_some());
            assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("typed predicate is false")
                    && diagnostic.contains("native pure replay rule")
            }));
        }
    }

    #[cfg(not(feature = "trust-build"))]
    #[test]
    fn loop_invariant_phases_keep_stable_ids_but_require_aggregate_gate() {
        let bundle = typed_bundle_with_obligations(
            vec![
                obligation(ObligationKind::LoopInvariant, "loop-init"),
                obligation(ObligationKind::LoopInvariant, "loop-consecution"),
                obligation(ObligationKind::LoopInvariant, "loop-sufficiency"),
            ],
            typed_expr(true),
        );
        let engine = TrustWpVerificationEngine::new();

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 3);
        assert_eq!(evidence[0].obligation_id, "loop-init");
        assert_eq!(evidence[1].obligation_id, "loop-consecution");
        assert_eq!(evidence[2].obligation_id, "loop-sufficiency");
        for item in evidence {
            assert_eq!(item.status, EvidenceStatus::Unsupported);
            assert!(item.proof_strength.is_none());
            assert!(item.evidence_id.contains(&item.obligation_id));
            assert!(item.diagnostics.iter().any(|diagnostic| {
                diagnostic.contains(TRUST_WP_AGGREGATE_NATIVE_REPLAY_GATE_SCHEMA_VERSION)
            }));
        }
    }

    #[test]
    fn refinement_and_termination_remain_fail_closed_without_native_replay_evidence() {
        let bundle = typed_bundle_with_obligations(
            vec![
                obligation(ObligationKind::Refinement, "refinement-typed"),
                obligation(ObligationKind::Termination, "termination-typed"),
            ],
            typed_expr(true),
        );
        let engine = TrustWpVerificationEngine::new();

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 2);
        for item in evidence {
            assert_eq!(item.status, EvidenceStatus::Unsupported);
            assert!(item.proof_strength.is_none());
            assert!(item.diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("remains fail-closed") && diagnostic.contains("replay evidence")
            }));
        }
    }

    #[test]
    fn typed_native_replay_with_summary_facts_still_requires_aggregate_gate() {
        let mut obligation = obligation(ObligationKind::Postcondition, "post-summary");
        obligation.summary_facts.push(summary_fact(
            "summary-pointer-p-q",
            "1111111111111111111111111111111111111111111111111111111111111111",
        ));
        let bundle = typed_bundle(obligation, typed_expr(true));
        let replay = replay_typed_predicate(&typed_expr(true)).expect("true predicate replays");
        let evidence = locally_shaped_candidate_evidence(
            TrustWpVerificationEngine::new().manifest(),
            &bundle,
            &bundle.obligations[0],
            &replay,
            &bundle.obligations[0].summary_facts,
        );
        let engine = TrustWpVerificationEngine::new().with_native_replay_evidence(vec![evidence]);

        let result = engine.verify_with_context(
            &bundle,
            &bundle.obligations,
            &VerifierExecutionContext::new("trust-wp-summary-replay"),
        );

        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
        assert_eq!(result.summary.proved, 0);
        assert_eq!(result.summary.unsupported, 1);
        assert_eq!(result.evidence[0].status, EvidenceStatus::Unsupported);
        assert!(result.evidence[0].proof_strength.is_none());
        assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("VerifyBundleResult")
                && diagnostic.contains(TRUST_WP_AGGREGATE_NATIVE_REPLAY_GATE_COMMIT)
        }));
    }

    #[test]
    fn typed_native_replay_consumes_summary_fact_metadata_entries() {
        let mut obligation = obligation(ObligationKind::Postcondition, "post-summary-metadata");
        obligation.metadata.push(
            summary_fact(
                "summary-pointer-p-q",
                "2222222222222222222222222222222222222222222222222222222222222222",
            )
            .to_metadata_entry()
            .expect("summary fact serializes"),
        );
        let bundle = typed_bundle(obligation, typed_expr(true));
        let replay = replay_typed_predicate(&typed_expr(true)).expect("true predicate replays");
        let summary_facts =
            summary_facts_for_obligation(&bundle, &bundle.obligations[0]).expect("valid summary");
        let evidence = locally_shaped_candidate_evidence(
            TrustWpVerificationEngine::new().manifest(),
            &bundle,
            &bundle.obligations[0],
            &replay,
            &summary_facts,
        );
        let engine = TrustWpVerificationEngine::new().with_native_replay_evidence(vec![evidence]);

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("VerifyBundleResult")
                && diagnostic.contains(TRUST_WP_AGGREGATE_NATIVE_REPLAY_GATE_COMMIT)
        }));
    }

    #[test]
    fn typed_native_replay_rejects_tampered_summary_fact_digest() {
        let mut obligation = obligation(ObligationKind::Postcondition, "post-summary-tamper");
        obligation.summary_facts.push(summary_fact(
            "summary-pointer-p-q",
            "3333333333333333333333333333333333333333333333333333333333333333",
        ));
        let original_bundle = typed_bundle(obligation.clone(), typed_expr(true));
        let replay = replay_typed_predicate(&typed_expr(true)).expect("true predicate replays");
        let evidence = locally_shaped_candidate_evidence(
            TrustWpVerificationEngine::new().manifest(),
            &original_bundle,
            &original_bundle.obligations[0],
            &replay,
            &original_bundle.obligations[0].summary_facts,
        );

        obligation.summary_facts[0].digest.value =
            "4444444444444444444444444444444444444444444444444444444444444444".to_string();
        let tampered_bundle = typed_bundle(obligation, typed_expr(true));
        let engine = TrustWpVerificationEngine::new().with_native_replay_evidence(vec![evidence]);

        let evidence = engine.verify(&tampered_bundle, &tampered_bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("deterministic typed replay metadata"))
        );
    }

    #[test]
    fn copied_replay_evidence_for_false_predicate_is_rejected() {
        let obligation = obligation(ObligationKind::Postcondition, "post-typed");
        let true_bundle = typed_bundle(obligation.clone(), typed_expr(true));
        let replay = replay_typed_predicate(&typed_expr(true)).expect("true predicate replays");
        let copied_evidence = locally_shaped_candidate_evidence(
            TrustWpVerificationEngine::new().manifest(),
            &true_bundle,
            &true_bundle.obligations[0],
            &replay,
            &[],
        );
        let false_bundle = typed_bundle(obligation, typed_expr(false));
        let engine =
            TrustWpVerificationEngine::new().with_native_replay_evidence(vec![copied_evidence]);

        let evidence = engine.verify(&false_bundle, &false_bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("typed predicate is false")
                && diagnostic.contains("native pure replay rule")
        }));
    }

    #[test]
    fn diagnostic_or_unsupported_replay_shaped_evidence_is_rejected() {
        let obligation = obligation(ObligationKind::Postcondition, "post-typed");
        let bundle = typed_bundle(obligation, typed_expr(true));
        let replay = replay_typed_predicate(&typed_expr(true)).expect("true predicate replays");
        let mut evidence = locally_shaped_candidate_evidence(
            TrustWpVerificationEngine::new().manifest(),
            &bundle,
            &bundle.obligations[0],
            &replay,
            &[],
        );
        evidence.status = EvidenceStatus::Unsupported;
        evidence.proof_strength = None;
        evidence.diagnostics.push("diagnostic replay only".to_string());
        let engine = TrustWpVerificationEngine::new().with_native_replay_evidence(vec![evidence]);

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("diagnostic-only") && diagnostic.contains("not Proved")
        }));
    }

    #[test]
    fn timeout_replay_shaped_evidence_remains_structured_non_proof() {
        let obligation = obligation(ObligationKind::Postcondition, "post-timeout");
        let bundle = typed_bundle(obligation, typed_expr(true));
        let replay = replay_typed_predicate(&typed_expr(true)).expect("true predicate replays");
        let mut evidence = locally_shaped_candidate_evidence(
            TrustWpVerificationEngine::new().manifest(),
            &bundle,
            &bundle.obligations[0],
            &replay,
            &[],
        );
        evidence.status = EvidenceStatus::Timeout;
        evidence.proof_strength = None;
        evidence.artifacts.clear();
        evidence.diagnostics.push("native trust_wp replay timed out".to_string());
        let engine = TrustWpVerificationEngine::new().with_native_replay_evidence(vec![evidence]);

        let result = engine.verify_with_context(
            &bundle,
            &bundle.obligations,
            &VerifierExecutionContext::new("trust-wp-timeout-replay"),
        );

        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
        assert_eq!(result.summary.proved, 0);
        assert_eq!(result.summary.unsupported, 1);
        assert_eq!(result.evidence[0].status, EvidenceStatus::Unsupported);
        assert!(result.evidence[0].proof_strength.is_none());
        assert!(result.evidence[0].artifacts.is_empty());
        assert!(
            result.evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic.contains("status Timeout is not Proved") })
        );
    }

    #[test]
    fn source_strings_are_not_accepted_as_typed_trust_wp_formulas() {
        let obligation = obligation(ObligationKind::Postcondition, "post");
        let typed_bundle = typed_bundle(obligation.clone(), typed_expr(true));
        let replay = replay_typed_predicate(&typed_expr(true)).expect("true predicate replays");
        let evidence = locally_shaped_candidate_evidence(
            TrustWpVerificationEngine::new().manifest(),
            &typed_bundle,
            &typed_bundle.obligations[0],
            &replay,
            &[],
        );
        let source_string_bundle = bundle_with(vec![obligation]);
        let engine = TrustWpVerificationEngine::new().with_native_replay_evidence(vec![evidence]);

        let evidence = engine.verify(&source_string_bundle, &source_string_bundle.obligations);

        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("source TrustExpr strings")
                && diagnostic.contains("not trusted TrustWpPureExprV1")
        }));
    }

    #[test]
    fn metadata_and_attribute_presence_are_never_proof_evidence() {
        let engine = TrustWpVerificationEngine::new();
        let bundle = bundle_with(vec![obligation(ObligationKind::Postcondition, "post")]);

        let result = engine.verify_with_context(
            &bundle,
            &bundle.obligations,
            &VerifierExecutionContext::new("trust-wp-attrs"),
        );

        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
        assert_eq!(result.summary.proved, 0);
        assert_eq!(result.summary.unsupported, 1);
        assert!(!result.is_fully_proved());
        assert_eq!(result.evidence[0].status, EvidenceStatus::Unsupported);
        assert!(result.evidence[0].proof_strength.is_none());
        assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("never shells out")
                && diagnostic.contains("presence as proof evidence")
        }));
    }

    #[test]
    fn symbolic_or_unlowered_predicates_do_not_claim_proof_strength() {
        let engine = TrustWpVerificationEngine::new();
        let bundle = bundle_with(vec![obligation(ObligationKind::Postcondition, "symbolic")]);

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].artifacts.is_empty());
        assert!(evidence[0].diagnostics.iter().any(
            |diagnostic| diagnostic.contains("symbolic") && diagnostic.contains("fail-closed")
        ));
    }

    #[test]
    fn non_owned_obligation_still_fails_closed_when_called_directly() {
        let engine = TrustWpVerificationEngine::new();
        let bundle = bundle_with(vec![obligation(ObligationKind::Ownership, "ownership")]);

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(
            evidence[0].diagnostics.iter().any(|diagnostic| diagnostic.contains("not Ownership"))
        );
    }
}
