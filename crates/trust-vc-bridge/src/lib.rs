// dead_code audit: crate-level suppression removed
// trust-vc-bridge: tRustc integration boundary for trust_vc ownership verifier
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Fail-closed `trust-verifier-api` adapter for trust_vc.
//!
//! trust_vc exposes native typed proof APIs. This adapter advertises the
//! trust-vc-owned obligation surface and remains explicit fail-closed by default:
//! public `TrustContractBundle` data alone is never proof evidence. Callers
//! that already ran the native trust_vc lane may attach `TrustVcNativeUnitReport`
//! values; the adapter lowers the public bundle/obligation identity into
//! deterministic audit artifacts, converts the native report, and accepts only
//! checked replayable typed `TrustVcExpr` proof evidence that passes the local
//! shape gate.
//!
//! Contract attributes, metadata entries, and syntactic marker presence are
//! audit inputs only. This adapter never treats them as proof evidence.

#[cfg(feature = "trust-build")]
mod trust_ir_adapter_request;
#[cfg(feature = "trust-build")]
use std::collections::BTreeMap;

use serde_json::Value as JsonValue;
#[cfg(feature = "trust-build")]
pub use trust_ir_adapter_request::{
    TrustVcTmirAdapterEmissionError, trust_vc_trust_ir_adapter_request_from_bundle,
};
use trust_types::stable_sha256_hex;
#[cfg(feature = "trust-build")]
use trust_vc_core::{
    full_verification::{
        AssuranceLevel as TrustVcFullAssuranceLevel, FullVerificationEvidence,
        FullVerificationRequest, ProofEvidenceSource as TrustVcFullProofEvidenceSource,
        ReasoningKind as TrustVcFullReasoningKind, TypedMemorySafetyFact, VerifiedMemorySafetyFact,
        VerifiedProofEvidence,
    },
    ir::TrustVcExpr,
    vc::{ObligationKind as TrustVcCoreObligationKind, TypedProofObligation},
};
#[cfg(feature = "trust-build")]
use trust_vc_trust_engine::{
    TRUST_PROOF_ARTIFACT_BINDING_SCHEMA_VERSION, TrustAssuranceLevel as NativeTrustAssuranceLevel,
    TrustEvidenceCacheStatus as NativeTrustEvidenceCacheStatus, TrustExpr, TrustMirMemoryProofUnit,
    TrustOutcome as NativeTrustOutcome, TrustProofArtifactFormat as NativeTrustProofArtifactFormat,
    TrustProofEvidence as NativeTrustProofEvidence,
    TrustProofEvidenceProfile as NativeTrustProofEvidenceProfile,
    TrustProofEvidenceSource as NativeTrustProofEvidenceSource, TrustProofPolicy,
    TrustProofReasoningKind as NativeTrustProofReasoningKind,
    TrustReplayableProofArtifact as NativeTrustReplayableProofArtifact, TrustUnitReport,
    TrustVcNativeArtifactAdmissionStatus as NativeTrustVcArtifactAdmissionStatus,
    TrustVcNativeArtifactReplayStatus as NativeTrustVcArtifactReplayStatus,
    TrustVcNativeProofArtifact as NativeTrustVcProofArtifact, TrustVcNativeTrustIrBundleReport,
    TrustVcTrustEngine,
};
use trust_verifier_api::{
    API_VERSION, ArtifactHash, AssuranceLevel, ContractPredicate, Counterexample, EngineCapability,
    EngineKind, EngineManifest, EvidenceArtifact, EvidenceArtifactKind,
    EvidenceArtifactMaterialization, EvidencePublicationMetadata, EvidenceStatus, MetadataEntry,
    ObligationEvidence, ObligationKind, ProofStrength, ReasoningKind, SupportLevel,
    TrustContractBundle, TrustObligation, ValidatedVerificationRequest, VerificationEngine,
};
#[cfg(feature = "trust-build")]
use trust_verifier_api::{ContractKind, TRUST_SPEC_PREDICATE_SCHEMA_VERSION};

#[cfg(test)]
std::thread_local! {
    static TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn record_test_direct_mir_memory_solve() {
    TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| count.set(count.get().saturating_add(1)));
}

/// Public trust_vc engine name used in manifests and evidence IDs.
pub const TRUST_VC_ENGINE_NAME: &str = "trust-vc";

/// Fail-closed reason used when an obligation lacks the exact typed input and
/// proof material required by the active trust_vc bridge.
pub const TRUST_VC_TYPED_PROOF_INPUT_REQUIRED: &str = concat!(
    "trust-vc native proof requires an exact typed TrustContractBundle request ",
    "and replayable proof evidence",
);

/// Capability reason for builds that deliberately omit the native engine.
pub const TRUST_VC_BUILD_FEATURE_REQUIRED: &str =
    "trust-vc native proof support is disabled in this build (enable `trust-build`)";

/// trust_vc full-verification input shape required before proof evidence exists.
pub const TRUST_VC_TYPED_OBLIGATION_REQUIRED: &str = concat!(
    "trust-vc full verification requires trust_vc_core::vc::TypedProofObligation ",
    "with ConditionOrigin::TypedTrustVcExpr",
);

/// trust_vc native memory/ownership context required for ownership proof.
pub const TRUST_VC_OWNERSHIP_CONTEXT_REQUIRED: &str = "typed ownership and borrow state";

/// trust_vc native contract frame required for typed Requires/Ensures proof.
pub const TRUST_VC_CONTRACT_FRAME_REQUIRED: &str =
    "typed contract frame with result and old(...) bindings";

/// Metadata key marking trust-vc-native typed expression origins.
pub const TRUST_VC_CONDITION_ORIGIN_METADATA_KEY: &str = "trust_vc.condition_origin";

/// Required metadata value for typed trust_vc expression origins.
pub const TRUST_VC_CONDITION_ORIGIN_METADATA_VALUE: &str = "TypedTrustVcExpr";

/// Metadata key marking trust_vc typed proof-obligation lowering.
pub const TRUST_VC_PROOF_OBLIGATION_METADATA_KEY: &str = "trust_vc.proof_obligation";

/// Required metadata value for trust_vc typed proof obligations.
pub const TRUST_VC_PROOF_OBLIGATION_METADATA_VALUE: &str = "TypedProofObligation";

/// Metadata key marking trust_vc typed contract-frame availability.
pub const TRUST_VC_CONTRACT_FRAME_METADATA_KEY: &str = "trust_vc.contract_frame";

/// Required metadata value for trust_vc typed contract-frame availability.
pub const TRUST_VC_CONTRACT_FRAME_METADATA_VALUE: &str = "TypedContractFrame";

/// Metadata key marking the trust_vc postcondition `result` binding.
pub const TRUST_VC_RESULT_BINDING_METADATA_KEY: &str = "trust_vc.contract_frame.result";

/// Required metadata value for the trust_vc postcondition `result` binding.
pub const TRUST_VC_RESULT_BINDING_METADATA_VALUE: &str = "typed";

/// Metadata key marking trust_vc typed `old(...)` snapshot availability.
pub const TRUST_VC_OLD_SNAPSHOT_METADATA_KEY: &str = "trust_vc.contract_frame.old_snapshot";

/// Required metadata value for trust_vc typed `old(...)` snapshot availability.
pub const TRUST_VC_OLD_SNAPSHOT_METADATA_VALUE: &str = "typed";

/// Metadata key marking native ownership/borrow context availability.
pub const TRUST_VC_OWNERSHIP_CONTEXT_METADATA_KEY: &str = "trust_vc.ownership_context";

/// Required metadata value for native ownership/borrow context availability.
pub const TRUST_VC_OWNERSHIP_CONTEXT_METADATA_VALUE: &str = "typed";

/// Fail-closed reason for missing typed trust_vc proof artifacts.
pub const TRUST_VC_PROOF_ARTIFACTS_REQUIRED: &str = concat!(
    "trust-vc proof evidence requires normalized typed obligation, native engine input, ",
    "and a replayable proof certificate artifact",
);

/// trust_vc #2772 stable replayable proof-artifact id prefix.
pub const TRUST_VC_PROOF_ARTIFACT_ID_PREFIX: &str = "trust-vc-proof-certificate:v1:";

/// Trust adapter URI prefix for trust_vc replayable proof certificates.
pub const TRUST_VC_PROOF_CERTIFICATE_URI_PREFIX: &str = "artifact://trust-vc/proof-artifacts/";

/// URI prefix reserved for certificates produced by the dedicated in-process
/// MIR-memory lane while the live TrustVC release-admission receipt is held.
pub const TRUST_VC_DIRECT_MIR_MEMORY_PROOF_CERTIFICATE_URI_PREFIX: &str =
    "artifact://trust-vc/direct-mir-memory-proof-artifacts/";

/// Trust adapter URI prefix for trust-vc-admitted native Tmir proof certificates.
pub const TRUST_VC_NATIVE_TRUST_IR_PROOF_CERTIFICATE_URI_PREFIX: &str =
    "artifact://trust-vc/native-trust-ir-proof-artifacts/";

/// Exact public contract-predicate schema whose JSON value is a serialized
/// [`trust_ir::ProofFormula`]. This narrow representation is the only contract
/// form a kernel-certified native TrustIr import may use: the adapter compares
/// the decoded formula byte-for-semantics with both the module obligation and
/// the request-authenticated replay assertion before granting proof credit.
#[cfg(feature = "trust-build")]
pub const TRUST_VC_NATIVE_TRUST_IR_CONTRACT_FORMULA_SCHEMA: &str =
    "trust-vc.native-trust-ir-contract-formula.v1";

/// Map a public verifier obligation kind to the exact native Trust-IR kind that
/// trust-vc is permitted to import for it.
///
/// Both compiler emission and adapter validation use this function so the
/// proof producer and consumer cannot silently drift onto different mappings.
#[cfg(feature = "trust-build")]
#[must_use]
pub fn trust_vc_native_trust_ir_kind_for_public_obligation(
    kind: &ObligationKind,
) -> Option<trust_ir::ObligationKind> {
    match kind {
        ObligationKind::Precondition => Some(trust_ir::ObligationKind::Precondition),
        ObligationKind::Postcondition => Some(trust_ir::ObligationKind::Postcondition),
        ObligationKind::MemorySafety | ObligationKind::Ownership | ObligationKind::BoundsCheck => {
            Some(trust_ir::ObligationKind::MemorySafety)
        }
        _ => None,
    }
}

/// Schema used by the minimal Trust-side normalized trust_vc obligation artifact.
pub const TRUST_VC_NORMALIZED_OBLIGATION_SCHEMA_VERSION: &str = "trust_vc.normalized-obligation.v1";

/// Schema used by the minimal Trust-side native trust_vc engine input artifact.
pub const TRUST_VC_NATIVE_ENGINE_INPUT_SCHEMA_VERSION: &str = "trust_vc.native-engine-input.v1";

/// Trust adapter URI prefix for deterministic trust_vc lowering artifacts.
pub const TRUST_VC_NATIVE_LOWERING_ARTIFACT_URI_PREFIX: &str =
    "artifact://trust-vc/native-lowering/";

/// Schema accepted for direct trust_vc MIR memory proof units embedded in
/// verifier-api `MemoryIr` or `CanonicalJson` payloads.
pub const TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_VERSION: &str = "trust_vc.mir-memory-proof-unit.v1";

/// Obligation metadata key for an inline direct trust_vc MIR memory proof unit.
pub const TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY: &str = "trust_vc.mir_memory.proof_unit";

/// Obligation metadata key for the inline direct trust_vc MIR memory proof-unit schema.
pub const TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_METADATA_KEY: &str =
    "trust_vc.mir_memory.proof_unit.schema";

#[cfg(feature = "trust-build")]
const TRUST_VC_FORMULA_SCHEMA_METADATA_KEY: &str = "trust.vc.formula.schema";
#[cfg(feature = "trust-build")]
const TRUST_VC_FORMULA_SORT_METADATA_KEY: &str = "trust.vc.formula.sort";
#[cfg(feature = "trust-build")]
const TRUST_VC_FORMULA_SMTLIB_METADATA_KEY: &str = "trust.vc.formula.smtlib2";
#[cfg(feature = "trust-build")]
const TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY: &str = "trust.vc.formula.payload";
#[cfg(feature = "trust-build")]
const TRUST_VC_DIGEST_METADATA_KEY: &str = "trust.vc.digest.sha256";

/// Fail-closed reason for direct MIR memory obligations without typed units.
pub const TRUST_VC_MIR_MEMORY_PROOF_UNIT_REQUIRED: &str = concat!(
    "direct trust_vc MIR memory verification requires a typed ",
    "TrustMirMemoryProofUnit payload with typed ownership/borrow context",
);

/// Compiler-authored native-transport marker for a structured direct carrier
/// that was deliberately left unsolved until the router applies its deadline.
pub const TRUST_VC_DIRECT_MIR_MEMORY_TRANSPORT_STATUS_METADATA_KEY: &str =
    "trust.trust_ir.native.transport_status";
pub const TRUST_VC_DIRECT_MIR_MEMORY_TRANSPORT_STATUS_DEFERRED: &str = "deferred";
pub const TRUST_VC_DIRECT_MIR_MEMORY_TRANSPORT_REASON_METADATA_KEY: &str =
    "trust.trust_ir.native.unsupported_reason";
pub const TRUST_VC_DIRECT_MIR_MEMORY_DEFERRED_REASON: &str = "exact structured trust-vc MIR-memory proof unit deferred to the deadline-aware direct verifier; no opaque evidence was inserted into native TrustIr";

/// Fail-closed reason for heap/pointer details not covered by the current
/// trust_vc MIR memory facade.
pub const TRUST_VC_MIR_MEMORY_UNSUPPORTED_HEAP_POINTER_DETAILS: &str = concat!(
    "direct trust_vc MIR memory verification does not yet support heap, raw ",
    "pointer, allocation, dereference, or provenance detail payloads",
);

/// Fail-closed reason for missing trust_vc replayable proof-artifact identity.
pub const TRUST_VC_PROOF_ARTIFACT_ID_REQUIRED: &str = concat!(
    "trust-vc proof evidence requires a ProofCertificate artifact whose URI links ",
    "trust-vc-proof-certificate:v1:<sha256>",
);

/// Fail-closed reason for unchecked replayable certificate payloads.
pub const TRUST_VC_PROOF_CERTIFICATE_CHECK_REQUIRED: &str = concat!(
    "trust-vc proof evidence requires native trust_vc strict-checker or kernel ",
    "acceptance; digest-matching text payloads are not proof evidence",
);

/// Fail-closed reason for missing typed `TrustExpr` payloads in trust_vc evidence.
pub const TRUST_VC_TYPED_EXPR_EVIDENCE_REQUIRED: &str = concat!(
    "trust-vc TypedTrustVcExpr evidence must preserve the structured typed ",
    "TrustExpr payload, not only a diagnostic expression label",
);

/// Obligation metadata key binding public evidence to a native Tmir proof obligation.
pub const TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY: &str =
    "trust.trust_ir.native.proof_obligation_id";

/// Obligation metadata key binding public evidence to a native Tmir request.
pub const TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY: &str = "trust.trust_ir.native.request_id";

/// Obligation metadata key binding public evidence to its native verifier suite.
pub const TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY: &str =
    "trust.trust_ir.native.verifier_suite";

/// Optional native Tmir assertion identity emitted by compiler/sample metadata.
pub const TRUST_TRUST_IR_NATIVE_ASSERTION_ID_METADATA_KEY: &str =
    "trust.trust_ir.native.assertion_id";

/// Optional native Tmir module digest emitted by compiler/sample metadata.
pub const TRUST_TRUST_IR_NATIVE_TRUST_IR_MODULE_DIGEST_METADATA_KEY: &str =
    "trust.trust_ir.native.trust_ir_module_digest";

/// Native TrustIr request digest whose stable payload covers the replay atom
/// formula carrying the public semantic digest.
pub const TRUST_TRUST_IR_NATIVE_REQUEST_DIGEST_METADATA_KEY: &str =
    "trust.trust_ir.native.request_digest";

/// Optional native Tmir proof-evidence digest emitted by compiler/sample metadata.
pub const TRUST_TRUST_IR_NATIVE_EVIDENCE_DIGEST_METADATA_KEY: &str =
    "trust.trust_ir.native.evidence_digest";

/// Optional native Tmir proof-certificate digest emitted by compiler/sample metadata.
pub const TRUST_TRUST_IR_NATIVE_CERTIFICATE_DIGEST_METADATA_KEY: &str =
    "trust.trust_ir.native.certificate_digest";

/// Optional native Tmir compiler-facts digest emitted by compiler/sample metadata.
pub const TRUST_TRUST_IR_NATIVE_COMPILER_FACTS_DIGEST_METADATA_KEY: &str =
    "trust.trust_ir.native.compiler_facts_digest";

/// Optional native Tmir obligation-source digest emitted by compiler/sample metadata.
pub const TRUST_TRUST_IR_NATIVE_OBLIGATION_SOURCE_DIGEST_METADATA_KEY: &str =
    "trust.trust_ir.native.obligation_source_digest";

/// Optional native Tmir replay engine emitted by compiler/sample metadata.
pub const TRUST_TRUST_IR_NATIVE_REPLAY_ENGINE_METADATA_KEY: &str =
    "trust.trust_ir.native.replay_engine";

/// Optional native Tmir replay invocation emitted by compiler/sample metadata.
pub const TRUST_TRUST_IR_NATIVE_REPLAY_INVOCATION_METADATA_KEY: &str =
    "trust.trust_ir.native.replay_invocation";

/// Optional native Tmir replay transcript digest emitted by compiler/sample metadata.
pub const TRUST_TRUST_IR_NATIVE_REPLAY_TRANSCRIPT_DIGEST_METADATA_KEY: &str =
    "trust.trust_ir.native.replay_transcript_digest";

/// Optional native Tmir proof artifact fingerprint emitted by compiler/sample metadata.
pub const TRUST_TRUST_IR_NATIVE_ARTIFACT_FINGERPRINT_METADATA_KEY: &str =
    "trust.trust_ir.native.artifact_fingerprint";

/// Native Tmir trust_vc import metadata required for compiler-emitted proof certificates.
pub const TRUST_TRUST_IR_NATIVE_TRUST_VC_IMPORT_REQUIRED_METADATA_KEYS: &[&str] = &[
    TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY,
    TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY,
    TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
    TRUST_TRUST_IR_NATIVE_ASSERTION_ID_METADATA_KEY,
    TRUST_TRUST_IR_NATIVE_TRUST_IR_MODULE_DIGEST_METADATA_KEY,
    TRUST_TRUST_IR_NATIVE_REQUEST_DIGEST_METADATA_KEY,
    TRUST_TRUST_IR_NATIVE_EVIDENCE_DIGEST_METADATA_KEY,
    TRUST_TRUST_IR_NATIVE_CERTIFICATE_DIGEST_METADATA_KEY,
    TRUST_TRUST_IR_NATIVE_COMPILER_FACTS_DIGEST_METADATA_KEY,
    TRUST_TRUST_IR_NATIVE_OBLIGATION_SOURCE_DIGEST_METADATA_KEY,
    TRUST_TRUST_IR_NATIVE_REPLAY_ENGINE_METADATA_KEY,
    TRUST_TRUST_IR_NATIVE_REPLAY_INVOCATION_METADATA_KEY,
    TRUST_TRUST_IR_NATIVE_REPLAY_TRANSCRIPT_DIGEST_METADATA_KEY,
    TRUST_TRUST_IR_NATIVE_ARTIFACT_FINGERPRINT_METADATA_KEY,
];

// Trust (R1 corpus): the compiler stamps the per-obligation reason why no
// native TrustVc request/certificate exists under this key
// (`annotate_unsupported_trust_vc_native_trust_ir_import` in trust_verify.rs);
// the rejection evidence surfaces it as the leading diagnostic.
#[cfg_attr(not(feature = "trust-build"), allow(dead_code))]
const TRUST_TRUST_IR_NATIVE_UNSUPPORTED_REASON_METADATA_KEY: &str =
    "trust.trust_ir.native.unsupported_reason";

/// Fail-closed reason for omitting proof strength.
pub const TRUST_VC_PROOF_STRENGTH_OMITTED: &str = concat!(
    "proof_strength is intentionally omitted because no typed TrustVcExpr ",
    "full-verification proof evidence was produced",
);

/// `trust-verifier-api` engine adapter for trust_vc.
#[derive(Debug, Clone)]
pub struct TrustVcVerificationEngine {
    manifest: EngineManifest,
    native_unit_reports: Vec<TrustVcNativeUnitReport>,
    native_certificate_policy: TrustVcNativeProofCertificatePolicy,
}

impl TrustVcVerificationEngine {
    /// Create the fail-closed trust_vc adapter.
    #[must_use]
    pub fn new() -> Self {
        let mut manifest = EngineManifest::new(
            TRUST_VC_ENGINE_NAME,
            env!("CARGO_PKG_VERSION"),
            EngineKind::Deductive,
        );
        manifest.repository = Some("trust-vc-bridge".to_string());
        manifest.api_version = API_VERSION.to_string();
        manifest.capabilities = trust_vc_owned_obligation_kinds()
            .into_iter()
            .map(|obligation_kind| EngineCapability {
                obligation_kind,
                support: trust_vc_owned_support_level(),
            })
            .collect();
        manifest.proof_modes = vec![ReasoningKind::OwnershipAnalysis, ReasoningKind::Deductive];

        Self {
            manifest,
            native_unit_reports: Vec::new(),
            native_certificate_policy: TrustVcNativeProofCertificatePolicy::ReplayableCertificate,
        }
    }

    /// Test-only injection of legacy native-report DTOs.
    ///
    /// These reports are deliberately non-authoritative: their verification
    /// booleans are caller-constructible and do not carry an opaque replay
    /// receipt. Production certification uses either the validated native
    /// TrustIR bundle path or the dedicated in-process MIR-memory path while it
    /// still holds TrustVC's live release-admission receipt.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn with_native_unit_reports(
        mut self,
        native_unit_reports: Vec<TrustVcNativeUnitReport>,
    ) -> Self {
        self.native_unit_reports = native_unit_reports;
        self
    }

    /// Require a stricter replayable certificate policy for attached native reports.
    #[must_use]
    pub fn with_native_certificate_policy(
        mut self,
        native_certificate_policy: TrustVcNativeProofCertificatePolicy,
    ) -> Self {
        self.native_certificate_policy = native_certificate_policy;
        self
    }

    /// Consume trust_vc proof certificates from a typed native Tmir bundle.
    ///
    /// This path uses trust-vc's native `consume_native_trust_ir_bundle` API. It
    /// accepts only trust-vc-admitted proof artifacts whose Tmir proof-obligation
    /// id matches the public verifier obligation metadata.
    #[cfg(feature = "trust-build")]
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
    /// and already elapsed on entry, the trust-vc ownership analysis is not
    /// started and every obligation degrades to `Timeout` (sound: never
    /// `Proved`, via `from_summary`). A `None` deadline preserves the original
    /// unbounded behaviour exactly.
    #[cfg(feature = "trust-build")]
    #[must_use]
    pub fn evidence_from_native_trust_ir_bundle_with_deadline(
        &self,
        bundle: &TrustContractBundle,
        obligations: &[TrustObligation],
        native_bundle: &trust_ir::NativeVerificationBundle,
        deadline: Option<std::time::Instant>,
    ) -> Vec<ObligationEvidence> {
        // This method is a specialized adapter entry point and therefore does
        // not pass through VerificationEngine::verify. Enforce the identical
        // canonical bundle/subset boundary here before consulting any native
        // ID or certificate metadata.
        let semantic_digests = match bundle
            .canonical_obligation_semantic_digest_index_sha256(obligations)
        {
            Ok(index) => index,
            Err(reason) => {
                let error =
                    TrustVcNativeReportConversionError::CanonicalVerifierRequestRejected { reason };
                return obligations
                    .iter()
                    .map(|obligation| {
                        self.rejected_native_trust_ir_bundle_evidence(
                            bundle,
                            obligation,
                            error.clone(),
                        )
                    })
                    .collect();
            }
        };
        if let Err(errors) = native_bundle.validate() {
            let error = TrustVcNativeReportConversionError::NativeTmirBundleRejected {
                reason: format!("canonical native bundle validation failed: {errors:?}"),
            };
            return obligations
                .iter()
                .map(|obligation| {
                    self.rejected_native_trust_ir_bundle_evidence(bundle, obligation, error.clone())
                })
                .collect();
        }
        // Trust: the trust-vc native ownership analysis below is the
        // potentially expensive in-process solve. If the per-function budget is
        // already spent, do not start it; degrade every obligation to Timeout.
        if trust_vc_budget_deadline_exceeded(deadline) {
            return obligations
                .iter()
                .map(|obligation| self.budget_timeout_evidence(bundle, obligation))
                .collect();
        }
        // Consume the held bundle, not only its derived report.  The report
        // authenticates admission/replay metadata but cannot retain the exact
        // `ProofCertificate` bytes required by the public evidence envelope.
        // The bundle path performs the same trust-vc admission and then binds
        // the unique canonical certificate materialization to each import.
        let imports = trust_vc_native_trust_ir_imported_proof_artifacts_from_bundle(native_bundle);

        match imports {
            Ok(imports) => match TrustVcNativeTrustIrBundleIndex::new(native_bundle, &imports) {
                Ok(index) => obligations
                    .iter()
                    .map(|obligation| {
                        self.convert_native_trust_ir_bundle_evidence(
                            bundle,
                            obligation,
                            &semantic_digests,
                            &index,
                        )
                        .unwrap_or_else(|error| {
                            self.rejected_native_trust_ir_bundle_evidence(bundle, obligation, error)
                        })
                    })
                    .collect(),
                Err(error) => obligations
                    .iter()
                    .map(|obligation| {
                        self.rejected_native_trust_ir_bundle_evidence(
                            bundle,
                            obligation,
                            error.clone(),
                        )
                    })
                    .collect(),
            },
            Err(error) => obligations
                .iter()
                .map(|obligation| {
                    self.rejected_native_trust_ir_bundle_evidence(bundle, obligation, error.clone())
                })
                .collect(),
        }
    }

    /// Verify only exact compiler-authored structured MIR-memory proof units
    /// while retaining TrustVC's live release-admission receipt in-process.
    ///
    /// This is intentionally separate from the public legacy native-report DTO
    /// converter: serialized producer booleans never enter this authority path.
    /// The full router calls it only after establishing that no TrustVC native
    /// request binds the same public obligation. The deadline is a pre-solve
    /// cutoff; an individual in-progress TrustVC solve is not interruptible.
    #[cfg(feature = "trust-build")]
    #[must_use]
    pub fn evidence_from_release_admitted_direct_mir_memory_with_deadline(
        &self,
        bundle: &TrustContractBundle,
        obligations: &[TrustObligation],
        deadline: Option<std::time::Instant>,
    ) -> Vec<ObligationEvidence> {
        if let Err(reason) = bundle.canonical_obligation_semantic_digest_index_sha256(obligations) {
            let error =
                TrustVcNativeReportConversionError::CanonicalVerifierRequestRejected { reason };
            return obligations
                .iter()
                .map(|obligation| {
                    self.rejected_native_trust_ir_bundle_evidence(bundle, obligation, error.clone())
                })
                .collect();
        }
        if trust_vc_budget_deadline_exceeded(deadline) {
            return obligations
                .iter()
                .map(|obligation| self.budget_timeout_evidence(bundle, obligation))
                .collect();
        }

        obligations
            .iter()
            .map(|obligation| {
                if trust_vc_budget_deadline_exceeded(deadline) {
                    return self.budget_timeout_evidence(bundle, obligation);
                }
                match self.verify_direct_mir_memory_unit(bundle, obligation) {
                    Ok(Some(evidence)) => evidence,
                    Ok(None) => self.rejected_direct_mir_memory_evidence(
                        bundle,
                        obligation,
                        TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
                            origin: "public verifier obligation".to_string(),
                            reason: TRUST_VC_MIR_MEMORY_PROOF_UNIT_REQUIRED.to_string(),
                        },
                    ),
                    Err(error) => {
                        self.rejected_direct_mir_memory_evidence(bundle, obligation, error)
                    }
                }
            })
            .collect()
    }

    #[cfg(feature = "trust-build")]
    fn convert_native_trust_ir_bundle_evidence(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        semantic_digests: &trust_verifier_api::CanonicalObligationSemanticDigestIndex,
        index: &TrustVcNativeTrustIrBundleIndex<'_>,
    ) -> Result<ObligationEvidence, TrustVcNativeReportConversionError> {
        let identity = trust_vc_native_tmir_obligation_identity(obligation)?;
        let imported = index
            .imports
            .get(&(identity.request_id, identity.proof_obligation_id))
            .copied()
            .ok_or_else(|| {
                TrustVcNativeReportConversionError::NativeTmirImportMissingObligation {
                    obligation_id: obligation.obligation_id.clone(),
                    request_id: identity.request_id,
                    trust_ir_obligation_id: identity.proof_obligation_id,
                }
            })?;
        let source =
            index.obligation_sources.get(&identity.proof_obligation_id).copied().ok_or_else(
                || TrustVcNativeReportConversionError::NativeTmirImportMissingObligation {
                    obligation_id: obligation.obligation_id.clone(),
                    request_id: identity.request_id,
                    trust_ir_obligation_id: identity.proof_obligation_id,
                },
            )?;
        validate_native_trust_ir_import_field(
            obligation,
            "public_obligation_id",
            obligation.obligation_id.clone(),
            source.public_obligation_id.clone(),
        )?;
        let native_obligation =
            index.proof_obligations.get(&identity.proof_obligation_id).copied().ok_or_else(
                || TrustVcNativeReportConversionError::NativeTmirImportMissingObligation {
                    obligation_id: obligation.obligation_id.clone(),
                    request_id: identity.request_id,
                    trust_ir_obligation_id: identity.proof_obligation_id,
                },
            )?;
        let replay_formula = index
            .replay_assertion_formulas
            .get(&(identity.request_id, identity.proof_obligation_id))
            .copied()
            .ok_or_else(|| {
                TrustVcNativeReportConversionError::NativeTmirImportMissingObligation {
                    obligation_id: obligation.obligation_id.clone(),
                    request_id: identity.request_id,
                    trust_ir_obligation_id: identity.proof_obligation_id,
                }
            })?;
        let request_digest = index.request_digests.get(&identity.request_id).ok_or_else(|| {
            TrustVcNativeReportConversionError::NativeTmirImportMissingObligation {
                obligation_id: obligation.obligation_id.clone(),
                request_id: identity.request_id,
                trust_ir_obligation_id: identity.proof_obligation_id,
            }
        })?;
        validate_native_trust_ir_import_field(
            obligation,
            "request_digest",
            request_digest.to_string(),
            imported.request_digest.clone(),
        )?;
        validate_trust_vc_public_obligation_semantic_binding(
            bundle,
            obligation,
            semantic_digests,
            native_obligation,
            replay_formula,
        )?;
        validate_trust_vc_native_trust_ir_import_matches_obligation(obligation, imported)?;

        let supplemental_artifacts =
            trust_vc_native_report_artifacts_from_bundle(bundle, obligation).map_err(|error| {
                TrustVcNativeReportConversionError::RejectedByTrustVcEvidenceShape {
                    diagnostics: vec![error.to_string()],
                }
            })?;

        let evidence_id =
            format!("trust-vc:native-trust-ir:{}:{}", bundle.bundle_id, obligation.obligation_id);
        let proof_binding_id = format!(
            "trust_ir-native-trust-vc-request-{}-proof-{}",
            identity.request_id, identity.proof_obligation_id
        );
        let certificate_artifact = trust_vc_native_trust_ir_proof_certificate_artifact_from_import(
            imported,
            &proof_binding_id,
            &obligation.obligation_id,
        )?;
        let mut artifacts = vec![
            supplemental_artifacts.normalized_obligation,
            supplemental_artifacts.engine_input,
            certificate_artifact,
        ];
        artifacts.sort_by(|left, right| {
            (left.kind, left.uri.as_str(), left.hash.value.as_str()).cmp(&(
                right.kind,
                right.uri.as_str(),
                right.hash.value.as_str(),
            ))
        });

        let evidence = ObligationEvidence {
            evidence_id,
            obligation_id: obligation.obligation_id.clone(),
            engine: self.manifest().clone(),
            status: EvidenceStatus::Proved,
            proof_strength: Some(ProofStrength::certified(
                if requires_trust_vc_contract_frame(&obligation.kind) {
                    ReasoningKind::Deductive
                } else {
                    ReasoningKind::OwnershipAnalysis
                },
            )),
            artifacts,
            counterexample: None,
            publication: EvidencePublicationMetadata {
                publication_plan_hash: bundle.publication.dpub_plan_hash.clone(),
                trust_engines_lock_hash: bundle.publication.trust_engines_lock_hash.clone(),
                ..EvidencePublicationMetadata::default()
            },
            diagnostics: vec![
                "native trust_vc TrustIr proof certificate import accepted".to_string(),
                format!(
                    "trust-vc native TrustIr proof artifact identity: request={}, request_digest={}, assertion={}, trust_ir_obligation={}, replay_transcript_digest={}, evidence_digest={}, certificate_digest={}, compiler_facts_digest={}, obligation_source_digest={}, fact_refs={}, fingerprint={}",
                    imported.request_id,
                    imported.request_digest,
                    imported.assertion_id,
                    imported.trust_ir_obligation_id,
                    imported.replay_transcript_digest,
                    imported.evidence_digest,
                    imported.certificate_digest,
                    imported.compiler_facts_digest,
                    imported.obligation_source_digest,
                    imported.compiler_fact_refs.len(),
                    imported.artifact_fingerprint
                ),
            ],
        };

        let diagnostics = trust_vc_proof_evidence_shape_diagnostics(obligation, &evidence);
        if diagnostics.is_empty() {
            Ok(evidence)
        } else {
            Err(TrustVcNativeReportConversionError::RejectedByTrustVcEvidenceShape { diagnostics })
        }
    }

    #[cfg(feature = "trust-build")]
    fn rejected_native_trust_ir_bundle_evidence(
        &self,
        _bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        error: TrustVcNativeReportConversionError,
    ) -> ObligationEvidence {
        ObligationEvidence {
            evidence_id: format!("trust-vc:native-trust-ir:rejected:{}", obligation.obligation_id),
            obligation_id: obligation.obligation_id.clone(),
            engine: self.manifest().clone(),
            status: EvidenceStatus::Unsupported,
            proof_strength: None,
            artifacts: Vec::new(),
            counterexample: None::<Counterexample>,
            publication: EvidencePublicationMetadata::default(),
            diagnostics: {
                let mut diagnostics = Vec::new();
                // Trust (R1 corpus, root-cause surfacing): when the compiler's
                // certificate-import lane already recorded WHY this obligation
                // carries no TrustVc request (the per-obligation Unavailable
                // reason stamped under `trust.trust_ir.native.unsupported_reason`),
                // lead with that root cause — otherwise every fallthrough row
                // stamps only the generic "contains no TrustVc requests" wall
                // (44 cascade-noise rows on the first corpus sweep).
                if let Some(root_reason) = obligation
                    .metadata
                    .iter()
                    .find(|entry| {
                        entry.key == TRUST_TRUST_IR_NATIVE_UNSUPPORTED_REASON_METADATA_KEY
                    })
                    .map(|entry| entry.value.as_str())
                {
                    diagnostics.push(format!(
                        "trust-vc native request unavailable (root cause): {root_reason}"
                    ));
                }
                diagnostics.push(format!(
                    "native trust_vc Tmir proof-certificate evidence rejected for obligation {}: {error}",
                    obligation.obligation_id
                ));
                diagnostics.push(TRUST_VC_PROOF_STRENGTH_OMITTED.to_string());
                diagnostics
            },
        }
    }

    /// Trust: evidence for an obligation skipped because the per-function
    /// wall-clock budget was exhausted before trust-vc could solve it. Status is
    /// `Timeout`, which `FunctionVerdict::from_summary` maps to `TimedOut`
    /// *before* it ever considers `Proved` — so a budget-skipped obligation can
    /// never make a function `Proved`.
    #[cfg(feature = "trust-build")]
    fn budget_timeout_evidence(
        &self,
        _bundle: &TrustContractBundle,
        obligation: &TrustObligation,
    ) -> ObligationEvidence {
        ObligationEvidence {
            evidence_id: format!(
                "trust-vc:native-trust-ir:budget-timeout:{}",
                obligation.obligation_id
            ),
            obligation_id: obligation.obligation_id.clone(),
            engine: self.manifest().clone(),
            status: EvidenceStatus::Timeout,
            proof_strength: None,
            artifacts: Vec::new(),
            counterexample: None::<Counterexample>,
            publication: EvidencePublicationMetadata::default(),
            diagnostics: vec![
                "tracked per-function wall-clock budget (-Ztrust-verify-function-budget-ms) exceeded before this trust-vc obligation was solved; degraded to Timeout (sound: never Proved)".to_string(),
                TRUST_VC_PROOF_STRENGTH_OMITTED.to_string(),
            ],
        }
    }

    fn unsupported_evidence(
        &self,
        _bundle: &TrustContractBundle,
        obligation: &TrustObligation,
    ) -> ObligationEvidence {
        let mut diagnostics = Vec::new();
        #[cfg(not(feature = "trust-build"))]
        diagnostics.push(TRUST_VC_BUILD_FEATURE_REQUIRED.to_string());
        if requires_trust_vc_contract_frame(&obligation.kind) {
            diagnostics.push(format!(
                "{TRUST_VC_TYPED_PROOF_INPUT_REQUIRED}; trust_vc owns {:?} obligations only after TrustContractBundle lowering produces typed TrustVcExpr proof requests, a native TrustContractFrame, and native full-verification evidence",
                obligation.kind
            ));
            diagnostics.push(TRUST_VC_TYPED_OBLIGATION_REQUIRED.to_string());
            diagnostics.push(TRUST_VC_CONTRACT_FRAME_REQUIRED.to_string());
            if requires_trust_vc_result_binding(&obligation.kind) {
                diagnostics.push(
                    "postcondition trust_vc evidence requires a typed result binding in the contract frame"
                        .to_string(),
                );
            }
        } else if requires_trust_vc_ownership_context(&obligation.kind) {
            diagnostics.push(format!(
                "{TRUST_VC_TYPED_PROOF_INPUT_REQUIRED}; trust_vc owns {:?} obligations only after TrustContractBundle lowering produces typed TrustVcExpr proof requests, typed ownership/borrow context, and native full-verification evidence",
                obligation.kind
            ));
            diagnostics.push(TRUST_VC_TYPED_OBLIGATION_REQUIRED.to_string());
            diagnostics.push(TRUST_VC_MIR_MEMORY_PROOF_UNIT_REQUIRED.to_string());
        } else {
            diagnostics.push(format!(
                "trust-vc owns typed contract-frame and ownership/memory obligations, not {:?}",
                obligation.kind
            ));
        }
        if requires_trust_vc_ownership_context(&obligation.kind) {
            diagnostics.push(format!(
                "{:?} obligations require {TRUST_VC_OWNERSHIP_CONTEXT_REQUIRED}; context-free public TrustObligation data is not proof evidence",
                obligation.kind
            ));
        }
        diagnostics.push(TRUST_VC_PROOF_STRENGTH_OMITTED.to_string());
        diagnostics.push(
            "string-backed TrustExpr predicates, contract attributes, and metadata are audit inputs only; their presence is never trust_vc proof evidence"
                .to_string(),
        );

        ObligationEvidence {
            evidence_id: format!("trust-vc:unsupported:{}", obligation.obligation_id),
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
        let evidence = self.verify_one_inner(bundle, obligation);
        if std::env::var("TRUST_NATIVE_DEBUG").is_ok() {
            eprintln!(
                "[TRUST_VC_VERIFY] obl={} status={:?} strength={:?} diag=[{}]",
                obligation.obligation_id,
                evidence.status,
                evidence.proof_strength,
                evidence.diagnostics.join(" | ")
            );
        }
        evidence
    }

    fn verify_one_inner(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
    ) -> ObligationEvidence {
        match self.native_unit_report_for_obligation(obligation) {
            Ok(Some(report)) => return self.convert_native_unit_report(bundle, obligation, report),
            Ok(None) => {}
            Err(error) => {
                return self.rejected_native_report_evidence(bundle, obligation, error);
            }
        }

        #[cfg(feature = "trust-build")]
        if requires_trust_vc_contract_frame(&obligation.kind) {
            match self.verify_trust_ir_adapter_contract_frame(bundle, obligation) {
                Ok(Some(evidence)) => return evidence,
                Ok(None) => {}
                Err(error) => {
                    return self.rejected_trust_ir_adapter_evidence(bundle, obligation, error);
                }
            }
        }

        if !self.native_unit_reports.is_empty() {
            let mut rejected = self.unsupported_evidence(bundle, obligation);
            rejected.evidence_id = format!("trust-vc:rejected:{}", obligation.obligation_id);
            rejected.diagnostics.insert(
                0,
                format!(
                    "attached native trust_vc reports did not include proof evidence for obligation {}",
                    obligation.obligation_id
                ),
            );
            return rejected;
        }

        self.unsupported_evidence(bundle, obligation)
    }

    fn native_unit_report_for_obligation(
        &self,
        obligation: &TrustObligation,
    ) -> Result<Option<&TrustVcNativeUnitReport>, TrustVcNativeReportConversionError> {
        let mut matching_reports = self.native_unit_reports.iter().filter(|report| {
            report
                .proof_evidence
                .iter()
                .any(|evidence| evidence.obligation_id == obligation.obligation_id)
        });
        let Some(report) = matching_reports.next() else {
            return Ok(None);
        };
        if let Some(second_report) = matching_reports.next() {
            return Err(TrustVcNativeReportConversionError::AmbiguousNativeUnitReports {
                obligation_id: obligation.obligation_id.clone(),
                first_unit_id: report.unit_id.clone(),
                second_unit_id: second_report.unit_id.clone(),
            });
        }
        Ok(Some(report))
    }

    fn convert_native_unit_report(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        report: &TrustVcNativeUnitReport,
    ) -> ObligationEvidence {
        let supplemental_artifacts =
            match trust_vc_native_report_artifacts_from_bundle(bundle, obligation) {
                Ok(artifacts) => artifacts,
                Err(error) => {
                    return self.rejected_native_report_evidence(bundle, obligation, error);
                }
            };

        match trust_vc_obligation_evidence_from_native_unit_report(
            self,
            bundle,
            obligation,
            report,
            supplemental_artifacts,
            self.native_certificate_policy,
        ) {
            Ok(evidence) => evidence,
            Err(error) => self.rejected_native_report_evidence(bundle, obligation, error),
        }
    }

    fn rejected_native_report_evidence(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        error: impl std::fmt::Display,
    ) -> ObligationEvidence {
        let mut rejected = self.unsupported_evidence(bundle, obligation);
        rejected.evidence_id = format!("trust-vc:rejected:{}", obligation.obligation_id);
        rejected.diagnostics.insert(
            0,
            format!(
                "native trust_vc unit report rejected for obligation {}: {error}",
                obligation.obligation_id
            ),
        );
        rejected
    }

    #[cfg(feature = "trust-build")]
    fn verify_direct_mir_memory_unit(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
    ) -> Result<Option<ObligationEvidence>, TrustVcDirectMirMemoryError> {
        let Some(carrier) = validate_direct_mir_memory_carrier_from_bundle(bundle, obligation)?
        else {
            return Ok(None);
        };
        let proof_policy = trust_vc_trust_engine_proof_policy(self.native_certificate_policy);
        #[cfg(test)]
        record_test_direct_mir_memory_solve();
        let report = TrustVcTrustEngine::new()
            .verify_mir_memory_unit(&carrier.proof_unit, proof_policy)
            .map_err(|error| TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
                origin: carrier.origin.clone(),
                obligation_id: obligation.obligation_id.clone(),
                reason: error.to_string(),
            })?;
        if let NativeTrustOutcome::Refuted { model, .. } = report.outcome() {
            return Ok(Some(self.refuted_direct_mir_memory_evidence(
                bundle,
                obligation,
                &carrier.origin,
                model.as_deref(),
            )));
        }
        Ok(Some(self.release_admitted_direct_mir_memory_evidence(
            bundle,
            obligation,
            &carrier.origin,
            &carrier.proof_unit,
            &report,
        )?))
    }

    #[cfg(feature = "trust-build")]
    fn refuted_direct_mir_memory_evidence(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        origin: &str,
        model: Option<&str>,
    ) -> ObligationEvidence {
        let data = model
            .and_then(|model| serde_json::from_str::<JsonValue>(model).ok())
            .unwrap_or_else(|| serde_json::json!({ "model": model }));
        ObligationEvidence {
            evidence_id: format!(
                "trust-vc:direct-mir-memory:refuted:{}:{}",
                bundle.bundle_id, obligation.obligation_id
            ),
            obligation_id: obligation.obligation_id.clone(),
            engine: self.manifest().clone(),
            status: EvidenceStatus::Failed,
            proof_strength: None,
            artifacts: Vec::new(),
            counterexample: Some(Counterexample {
                format: "trust-vc.direct-mir-memory-counterexample.v1".to_string(),
                data,
            }),
            publication: EvidencePublicationMetadata {
                publication_plan_hash: bundle.publication.dpub_plan_hash.clone(),
                trust_engines_lock_hash: bundle.publication.trust_engines_lock_hash.clone(),
                ..EvidencePublicationMetadata::default()
            },
            diagnostics: vec![format!(
                "in-process TrustVC MIR-memory verifier refuted {} from exact carrier at {origin}",
                obligation.obligation_id
            )],
        }
    }

    #[cfg(feature = "trust-build")]
    fn release_admitted_direct_mir_memory_evidence(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        origin: &str,
        proof_unit: &TrustMirMemoryProofUnit,
        report: &TrustUnitReport,
    ) -> Result<ObligationEvidence, TrustVcDirectMirMemoryError> {
        // This helper inspects the live TrustVC artifact, including its opaque
        // release-admission object, exact unit binding, zero-hole/trust gates,
        // and unique assertion coverage. Never route this through the public
        // NativeUnitReport DTO, which intentionally erases that authority.
        let artifact =
            trust_vc_replayable_artifact_for_obligation(origin, report, proof_unit, obligation)?;
        let native_report =
            trust_vc_native_unit_report_from_trust_engine_report(report).map_err(|reason| {
                TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
                    origin: origin.to_string(),
                    obligation_id: obligation.obligation_id.clone(),
                    reason,
                }
            })?;
        let native_evidence = trust_vc_native_evidence_for_obligation(&native_report, obligation)
            .map_err(|error| {
            TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
                origin: origin.to_string(),
                obligation_id: obligation.obligation_id.clone(),
                reason: error.to_string(),
            }
        })?;
        let native_artifact = trust_vc_native_artifact_for_evidence(
            &native_report,
            native_evidence,
        )
        .ok_or_else(|| TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: "release-admitted report lost the exact per-obligation artifact binding"
                .to_string(),
        })?;
        if native_artifact.artifact_id != artifact.artifact_id() {
            return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
                origin: origin.to_string(),
                obligation_id: obligation.obligation_id.clone(),
                reason: format!(
                    "release-admitted artifact {} disagrees with proof-evidence artifact {}",
                    artifact.artifact_id(),
                    native_artifact.artifact_id
                ),
            });
        }
        if native_evidence.source != TrustVcNativeProofEvidenceSource::TypedTrustVcExpr {
            return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
                origin: origin.to_string(),
                obligation_id: obligation.obligation_id.clone(),
                reason: format!("unsupported direct evidence source {:?}", native_evidence.source),
            });
        }
        validate_native_proof_artifact_asserts_obligation(native_evidence, native_artifact)
            .map_err(|error| TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
                origin: origin.to_string(),
                obligation_id: obligation.obligation_id.clone(),
                reason: error.to_string(),
            })?;
        let typed_expr_digest =
            validate_native_typed_trust_expr(native_evidence).map_err(|error| {
                TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
                    origin: origin.to_string(),
                    obligation_id: obligation.obligation_id.clone(),
                    reason: error.to_string(),
                }
            })?;
        let reasoning = validate_trust_vc_native_static_proof_profile(obligation, native_evidence)
            .map_err(|error| TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
                origin: origin.to_string(),
                obligation_id: obligation.obligation_id.clone(),
                reason: error.to_string(),
            })?;
        let supplemental_artifacts =
            trust_vc_native_report_artifacts_from_bundle(bundle, obligation).map_err(|error| {
                TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
                    origin: origin.to_string(),
                    obligation_id: obligation.obligation_id.clone(),
                    reason: error.to_string(),
                }
            })?;

        let proof_binding_id = format!("trust-vc-direct-mir-memory:{}", artifact.digest());
        let (materialization, hash) = EvidenceArtifactMaterialization::new_bound(
            EvidenceArtifactKind::ProofCertificate,
            artifact.payload().as_bytes(),
            &proof_binding_id,
            &obligation.obligation_id,
            Vec::new(),
        )
        .ok_or_else(|| TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: "release-admitted Alethe certificate could not be materialized".to_string(),
        })?;
        let certificate_artifact = EvidenceArtifact {
            kind: EvidenceArtifactKind::ProofCertificate,
            uri: format!(
                "{TRUST_VC_DIRECT_MIR_MEMORY_PROOF_CERTIFICATE_URI_PREFIX}{}.alethe",
                hash.value
            ),
            hash,
            materialization: Some(materialization),
        };
        let mut artifacts = vec![
            supplemental_artifacts.normalized_obligation,
            supplemental_artifacts.engine_input,
            certificate_artifact,
        ];
        artifacts.sort_by(|left, right| {
            (left.kind, left.uri.as_str(), left.hash.value.as_str()).cmp(&(
                right.kind,
                right.uri.as_str(),
                right.hash.value.as_str(),
            ))
        });
        let evidence = ObligationEvidence {
            evidence_id: format!(
                "trust-vc:direct-mir-memory:{}:{}",
                bundle.bundle_id, obligation.obligation_id
            ),
            obligation_id: obligation.obligation_id.clone(),
            engine: self.manifest().clone(),
            status: EvidenceStatus::Proved,
            proof_strength: Some(ProofStrength::certified(reasoning)),
            artifacts,
            counterexample: None,
            publication: EvidencePublicationMetadata {
                publication_plan_hash: bundle.publication.dpub_plan_hash.clone(),
                trust_engines_lock_hash: bundle.publication.trust_engines_lock_hash.clone(),
                ..EvidencePublicationMetadata::default()
            },
            diagnostics: vec![
                "in-process TrustVC MIR-memory proof accepted with live release admission"
                    .to_string(),
                format!(
                    "trust-vc direct certificate stats: strict={}, kernel={}, clean_supported={} [diagnostic only], holes={}, trust_steps={}, admission={:?}",
                    artifact.strict_verified(),
                    artifact.kernel_verified(),
                    artifact.clean_supported(),
                    artifact.hole_count(),
                    artifact.trust_count(),
                    artifact.release_admission().status(),
                ),
                format!("trust-vc typed TrustExpr evidence preserved: sha256:{typed_expr_digest}"),
            ],
        };
        let diagnostics = trust_vc_proof_evidence_shape_diagnostics(obligation, &evidence);
        if diagnostics.is_empty() {
            Ok(evidence)
        } else {
            Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
                origin: origin.to_string(),
                obligation_id: obligation.obligation_id.clone(),
                reason: diagnostics.join("; "),
            })
        }
    }

    #[cfg(feature = "trust-build")]
    fn verify_trust_ir_adapter_contract_frame(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
    ) -> Result<Option<ObligationEvidence>, TrustVcActiveTmirAdapterError> {
        if !requires_trust_vc_contract_frame(&obligation.kind) {
            return Ok(None);
        }

        let request = trust_vc_trust_ir_adapter_request_from_bundle(bundle).map_err(|error| {
            TrustVcActiveTmirAdapterError::EmitRequest {
                obligation_id: obligation.obligation_id.clone(),
                reason: error.to_string(),
            }
        })?;
        let request = request
            .with_proof_policy(trust_vc_trust_engine_proof_policy(self.native_certificate_policy));
        let report = TrustVcTrustEngine::new().verify_trust_ir_adapter_request(&request).map_err(
            |error| TrustVcActiveTmirAdapterError::TrustVcTrustEngineRejected {
                obligation_id: obligation.obligation_id.clone(),
                reason: error.to_string(),
            },
        )?;
        let unit_report = report
            .units()
            .iter()
            .find(|unit| {
                unit.proof_evidence()
                    .iter()
                    .any(|evidence| evidence.obligation_id() == obligation.obligation_id)
            })
            .ok_or_else(|| TrustVcActiveTmirAdapterError::MissingNativeProofEvidence {
                obligation_id: obligation.obligation_id.clone(),
            })?;
        let native_report = trust_vc_native_unit_report_from_trust_engine_report(unit_report)
            .map_err(|reason| TrustVcActiveTmirAdapterError::ConvertTrustEngineReport {
                obligation_id: obligation.obligation_id.clone(),
                reason,
            })?;

        Ok(Some(self.convert_native_unit_report(bundle, obligation, &native_report)))
    }

    #[cfg(feature = "trust-build")]
    fn rejected_trust_ir_adapter_evidence(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        error: TrustVcActiveTmirAdapterError,
    ) -> ObligationEvidence {
        let mut rejected = self.unsupported_evidence(bundle, obligation);
        rejected.evidence_id = format!("trust-vc:rejected:{}", obligation.obligation_id);
        rejected.diagnostics.insert(
            0,
            format!(
                "active trust_vc Tmir adapter verification rejected obligation {}: {error}",
                obligation.obligation_id
            ),
        );
        rejected
    }

    #[cfg(feature = "trust-build")]
    fn rejected_direct_mir_memory_evidence(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        error: TrustVcDirectMirMemoryError,
    ) -> ObligationEvidence {
        let mut rejected = self.unsupported_evidence(bundle, obligation);
        rejected.evidence_id = format!("trust-vc:rejected:{}", obligation.obligation_id);
        rejected.diagnostics.insert(
            0,
            format!(
                "direct trust_vc MIR memory verification rejected obligation {}: {error}",
                obligation.obligation_id
            ),
        );
        rejected
    }
}

impl Default for TrustVcVerificationEngine {
    fn default() -> Self {
        Self::new()
    }
}

impl VerificationEngine for TrustVcVerificationEngine {
    fn manifest(&self) -> &EngineManifest {
        &self.manifest
    }

    fn supports(&self, obligation: &TrustObligation) -> SupportLevel {
        if is_trust_vc_owned_obligation_kind(&obligation.kind) {
            trust_vc_owned_support_level()
        } else {
            SupportLevel::Unsupported {
                reason: format!(
                    "trust-vc owns typed contract-frame and ownership/memory obligations, not {:?}",
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
        obligations.iter().map(|obligation| self.verify_one(bundle, obligation)).collect()
    }
}

fn trust_vc_owned_support_level() -> SupportLevel {
    #[cfg(feature = "trust-build")]
    {
        SupportLevel::Supported
    }
    #[cfg(not(feature = "trust-build"))]
    {
        SupportLevel::Experimental { reason: TRUST_VC_BUILD_FEATURE_REQUIRED.to_string() }
    }
}

/// Obligation kinds owned by the trust_vc adapter.
#[must_use]
pub fn trust_vc_owned_obligation_kinds() -> [ObligationKind; 5] {
    [
        ObligationKind::Precondition,
        ObligationKind::Postcondition,
        ObligationKind::MemorySafety,
        ObligationKind::Ownership,
        ObligationKind::BoundsCheck,
    ]
}

/// Returns true for obligations trust_vc is responsible for proving natively.
#[must_use]
pub fn is_trust_vc_owned_obligation_kind(kind: &ObligationKind) -> bool {
    matches!(
        kind,
        ObligationKind::Precondition
            | ObligationKind::Postcondition
            | ObligationKind::MemorySafety
            | ObligationKind::Ownership
            | ObligationKind::BoundsCheck
    )
}

/// Returns true when trust_vc needs a typed contract frame from Requires/Ensures
/// lowering rather than ownership/borrow context.
#[must_use]
pub fn requires_trust_vc_contract_frame(kind: &ObligationKind) -> bool {
    matches!(kind, ObligationKind::Precondition | ObligationKind::Postcondition)
}

/// Returns true when trust_vc postcondition evidence must carry a typed `result`
/// binding in the contract frame.
#[must_use]
pub fn requires_trust_vc_result_binding(kind: &ObligationKind) -> bool {
    matches!(kind, ObligationKind::Postcondition)
}

/// Returns true when trust_vc needs typed native ownership/borrow context.
#[must_use]
pub fn requires_trust_vc_ownership_context(kind: &ObligationKind) -> bool {
    matches!(
        kind,
        ObligationKind::MemorySafety | ObligationKind::Ownership | ObligationKind::BoundsCheck
    )
}

/// Metadata producers must attach before trust_vc proof evidence can be accepted.
#[must_use]
pub fn trust_vc_typed_proof_metadata() -> Vec<MetadataEntry> {
    vec![
        MetadataEntry {
            key: TRUST_VC_CONDITION_ORIGIN_METADATA_KEY.to_string(),
            value: TRUST_VC_CONDITION_ORIGIN_METADATA_VALUE.to_string(),
        },
        MetadataEntry {
            key: TRUST_VC_PROOF_OBLIGATION_METADATA_KEY.to_string(),
            value: TRUST_VC_PROOF_OBLIGATION_METADATA_VALUE.to_string(),
        },
        MetadataEntry {
            key: TRUST_VC_OWNERSHIP_CONTEXT_METADATA_KEY.to_string(),
            value: TRUST_VC_OWNERSHIP_CONTEXT_METADATA_VALUE.to_string(),
        },
    ]
}

/// Metadata producers must attach before trust_vc contract-frame proof evidence
/// can be accepted for a typed `requires` obligation.
#[must_use]
pub fn trust_vc_typed_contract_frame_metadata() -> Vec<MetadataEntry> {
    vec![
        MetadataEntry {
            key: TRUST_VC_CONDITION_ORIGIN_METADATA_KEY.to_string(),
            value: TRUST_VC_CONDITION_ORIGIN_METADATA_VALUE.to_string(),
        },
        MetadataEntry {
            key: TRUST_VC_PROOF_OBLIGATION_METADATA_KEY.to_string(),
            value: TRUST_VC_PROOF_OBLIGATION_METADATA_VALUE.to_string(),
        },
        MetadataEntry {
            key: TRUST_VC_CONTRACT_FRAME_METADATA_KEY.to_string(),
            value: TRUST_VC_CONTRACT_FRAME_METADATA_VALUE.to_string(),
        },
    ]
}

/// Metadata producers must attach before trust_vc contract-frame proof evidence
/// can be accepted for a typed `ensures` obligation with a `result` binding.
#[must_use]
pub fn trust_vc_typed_result_contract_frame_metadata() -> Vec<MetadataEntry> {
    let mut metadata = trust_vc_typed_contract_frame_metadata();
    metadata.push(MetadataEntry {
        key: TRUST_VC_RESULT_BINDING_METADATA_KEY.to_string(),
        value: TRUST_VC_RESULT_BINDING_METADATA_VALUE.to_string(),
    });
    metadata
}

/// Metadata producers attach this when the trust_vc contract frame includes typed
/// `old(...)` pre-state snapshots. Not every contract-frame obligation needs an
/// `old(...)` binding, so this is an explicit capability marker instead of a
/// universal acceptance requirement.
#[must_use]
pub fn trust_vc_typed_old_snapshot_metadata() -> MetadataEntry {
    MetadataEntry {
        key: TRUST_VC_OLD_SNAPSHOT_METADATA_KEY.to_string(),
        value: TRUST_VC_OLD_SNAPSHOT_METADATA_VALUE.to_string(),
    }
}

/// Returns true when external trust_vc evidence has the typed proof shape this
/// adapter may treat as an accepted proof.
///
/// The generic verifier API accepts any publication-grade proof with replay or
/// check artifacts. trust_vc is stricter: ownership/memory obligations also need
/// typed trust_vc lowering metadata and native trust_vc proof artifacts so textual,
/// context-free obligations cannot masquerade as ownership proofs.
#[must_use]
pub fn accepts_trust_vc_proof_evidence_shape(
    obligation: &TrustObligation,
    evidence: &ObligationEvidence,
) -> bool {
    trust_vc_proof_evidence_shape_diagnostics(obligation, evidence).is_empty()
}

/// Explain why a trust_vc evidence item cannot be accepted as typed proof
/// evidence. An empty vector means the evidence has the accepted shape.
#[must_use]
pub fn trust_vc_proof_evidence_shape_diagnostics(
    obligation: &TrustObligation,
    evidence: &ObligationEvidence,
) -> Vec<String> {
    let mut diagnostics = Vec::new();

    if evidence.obligation_id != obligation.obligation_id {
        diagnostics.push(format!(
            "trust-vc evidence obligation_id {} does not match requested obligation {}",
            evidence.obligation_id, obligation.obligation_id
        ));
    }
    if evidence.engine.name != TRUST_VC_ENGINE_NAME {
        diagnostics.push(format!(
            "trust-vc proof evidence must come from engine {TRUST_VC_ENGINE_NAME}, not {}",
            evidence.engine.name
        ));
    }
    if !is_trust_vc_owned_obligation_kind(&obligation.kind) {
        diagnostics.push(format!(
            "trust-vc owns typed contract-frame and ownership/memory obligations, not {:?}",
            obligation.kind
        ));
    }
    if evidence.status != EvidenceStatus::Proved {
        diagnostics.push(format!("trust-vc evidence status {:?} is not a proof", evidence.status));
    }
    match evidence.proof_strength.as_ref() {
        Some(proof_strength) if is_trust_vc_native_proof_strength(proof_strength) => {
            if !evidence.satisfies_strength_requirement(obligation.required_strength.as_ref()) {
                diagnostics.push(
                    "trust-vc proof evidence does not satisfy the requested proof strength"
                        .to_string(),
                );
            }
        }
        Some(proof_strength) => diagnostics.push(format!(
            "trust-vc proof_strength {:?} is not a certified ownership-analysis or deductive proof",
            proof_strength
        )),
        None => diagnostics.push(TRUST_VC_PROOF_STRENGTH_OMITTED.to_string()),
    }

    require_obligation_metadata(
        obligation,
        TRUST_VC_CONDITION_ORIGIN_METADATA_KEY,
        TRUST_VC_CONDITION_ORIGIN_METADATA_VALUE,
        &mut diagnostics,
    );
    require_obligation_metadata(
        obligation,
        TRUST_VC_PROOF_OBLIGATION_METADATA_KEY,
        TRUST_VC_PROOF_OBLIGATION_METADATA_VALUE,
        &mut diagnostics,
    );
    if requires_trust_vc_ownership_context(&obligation.kind) {
        require_obligation_metadata(
            obligation,
            TRUST_VC_OWNERSHIP_CONTEXT_METADATA_KEY,
            TRUST_VC_OWNERSHIP_CONTEXT_METADATA_VALUE,
            &mut diagnostics,
        );
    }
    if requires_trust_vc_contract_frame(&obligation.kind) {
        require_obligation_metadata(
            obligation,
            TRUST_VC_CONTRACT_FRAME_METADATA_KEY,
            TRUST_VC_CONTRACT_FRAME_METADATA_VALUE,
            &mut diagnostics,
        );
    }
    if requires_trust_vc_result_binding(&obligation.kind) {
        require_obligation_metadata(
            obligation,
            TRUST_VC_RESULT_BINDING_METADATA_KEY,
            TRUST_VC_RESULT_BINDING_METADATA_VALUE,
            &mut diagnostics,
        );
    }

    if !has_valid_trust_vc_lowering_artifact_kind(
        evidence,
        EvidenceArtifactKind::NormalizedObligation,
    ) {
        diagnostics.push(
            "trust-vc proof evidence is missing a deterministic normalized typed obligation artifact"
                .to_string(),
        );
    }
    if !has_valid_trust_vc_lowering_artifact_kind(evidence, EvidenceArtifactKind::EngineInput) {
        diagnostics.push(
            "trust-vc proof evidence is missing the deterministic native trust_vc engine input artifact"
                .to_string(),
        );
    }
    if !evidence.satisfies_proof_artifact_policy() {
        diagnostics.push(TRUST_VC_PROOF_ARTIFACTS_REQUIRED.to_string());
    }
    if !has_trust_vc_replayable_proof_certificate_artifact(evidence) {
        diagnostics.push(TRUST_VC_PROOF_ARTIFACT_ID_REQUIRED.to_string());
    }
    if has_trust_vc_native_trust_ir_proof_certificate_artifact(evidence) {
        if let Err(error) = trust_vc_native_tmir_obligation_identity(obligation) {
            diagnostics.push(error.to_string());
        }
        require_complete_native_trust_ir_import_metadata_shape(obligation, &mut diagnostics);
    }
    validate_optional_native_trust_ir_metadata_shape(obligation, &mut diagnostics);

    diagnostics
}

/// Bridge representation of trust_vc `TrustUnitReport` evidence.
///
/// This intentionally mirrors only the trust_vc #2772 fields that Trust must
/// consume before the private trust_vc crate is vendored into the Trust build.
/// It is not proof by itself: conversion still requires a replayable trust_vc
/// certificate, matching per-obligation artifact ids, and caller-supplied
/// normalized-obligation and engine-input artifacts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustVcNativeUnitReport {
    pub unit_id: String,
    pub proof_evidence: Vec<TrustVcNativeTrustProofEvidence>,
    pub proof_artifacts: Vec<TrustVcNativeReplayableProofArtifact>,
    pub proof_artifact: Option<TrustVcNativeReplayableProofArtifact>,
}

impl TrustVcNativeUnitReport {
    /// Create a native trust_vc unit report bridge value.
    #[must_use]
    pub fn new(unit_id: impl Into<String>) -> Self {
        Self {
            unit_id: unit_id.into(),
            proof_evidence: Vec::new(),
            proof_artifacts: Vec::new(),
            proof_artifact: None,
        }
    }

    /// Attach one per-obligation trust_vc proof evidence item.
    #[must_use]
    pub fn with_proof_evidence(mut self, evidence: TrustVcNativeTrustProofEvidence) -> Self {
        self.proof_evidence.push(evidence);
        self
    }

    /// Attach the unit-level replayable trust_vc proof artifact.
    #[must_use]
    pub fn with_proof_artifact(mut self, artifact: TrustVcNativeReplayableProofArtifact) -> Self {
        if !self.proof_artifacts.iter().any(|existing| existing.artifact_id == artifact.artifact_id)
        {
            self.proof_artifacts.push(artifact.clone());
        }
        self.proof_artifact = Some(artifact);
        self
    }

    /// Attach the unit-level replayable trust_vc proof artifacts.
    ///
    /// Modern trust_vc reports can carry one proof artifact per assertion. The
    /// legacy singleton remains populated only when exactly one artifact exists.
    #[must_use]
    pub fn with_proof_artifacts(
        mut self,
        artifacts: Vec<TrustVcNativeReplayableProofArtifact>,
    ) -> Self {
        for artifact in artifacts {
            if !self
                .proof_artifacts
                .iter()
                .any(|existing| existing.artifact_id == artifact.artifact_id)
            {
                self.proof_artifacts.push(artifact);
            }
        }
        self.proof_artifact = match self.proof_artifacts.as_slice() {
            [artifact] => Some(artifact.clone()),
            _ => None,
        };
        self
    }
}

/// Bridge representation of trust_vc `TrustProofEvidence`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustVcNativeTrustProofEvidence {
    pub obligation_id: String,
    pub source: TrustVcNativeProofEvidenceSource,
    pub typed_expr: Option<JsonValue>,
    pub evidence_profile: TrustVcNativeProofEvidenceProfile,
    pub reasoning_kind: TrustVcNativeProofReasoningKind,
    pub assurance_level: TrustVcNativeAssuranceLevel,
    pub proof_artifact_id: Option<String>,
    pub native_trust_ir_import: Option<TrustVcNativeTrustIrImportedProofArtifact>,
}

impl TrustVcNativeTrustProofEvidence {
    /// Create typed trust_vc expression evidence for one obligation.
    #[must_use]
    pub fn typed_trust_vc_expr(
        obligation_id: impl Into<String>,
        typed_expr: JsonValue,
        proof_artifact_id: impl Into<String>,
    ) -> Self {
        Self {
            obligation_id: obligation_id.into(),
            source: TrustVcNativeProofEvidenceSource::TypedTrustVcExpr,
            typed_expr: Some(typed_expr),
            evidence_profile: TrustVcNativeProofEvidenceProfile::TypedDeductiveObligation,
            reasoning_kind: TrustVcNativeProofReasoningKind::Deductive,
            assurance_level: TrustVcNativeAssuranceLevel::StaticProof,
            proof_artifact_id: Some(proof_artifact_id.into()),
            native_trust_ir_import: None,
        }
    }

    /// Create legacy source-text trust_vc evidence.
    ///
    /// Trust full-verifier conversion rejects this shape; the constructor is
    /// public so tests and callers can account for fail-closed legacy reports.
    #[must_use]
    pub fn legacy_source_text(obligation_id: impl Into<String>) -> Self {
        Self {
            obligation_id: obligation_id.into(),
            source: TrustVcNativeProofEvidenceSource::LegacySourceText,
            typed_expr: None,
            evidence_profile: TrustVcNativeProofEvidenceProfile::LegacyCompatibility,
            reasoning_kind: TrustVcNativeProofReasoningKind::Deductive,
            assurance_level: TrustVcNativeAssuranceLevel::CompatibilityEvidence,
            proof_artifact_id: None,
            native_trust_ir_import: None,
        }
    }

    /// Create bridge evidence from trust-vc's native typed full-verification
    /// output and the typed obligation that produced it.
    ///
    /// The upstream `VerifiedProofEvidence` summary intentionally omits the
    /// expression payload, so callers must supply the matching
    /// `TypedProofObligation` from the verified request. Raw
    /// `ProofObligation` compatibility evidence is not accepted here.
    #[cfg(feature = "trust-build")]
    #[must_use]
    pub fn from_verified_typed_obligation(
        verified: &VerifiedProofEvidence,
        obligation: &TypedProofObligation,
        proof_artifact_id: impl Into<String>,
    ) -> Self {
        Self {
            obligation_id: verified.name().to_string(),
            source: trust_vc_native_source_from_full_verification(verified.evidence_source()),
            typed_expr: Some(trust_vc_expr_evidence_payload(
                obligation.name(),
                obligation.expr(),
                "TypedProofObligation",
            )),
            evidence_profile: trust_vc_native_profile_from_verified_proof(verified),
            reasoning_kind: trust_vc_native_reasoning_from_full_verification(
                verified.reasoning_kind(),
            ),
            assurance_level: trust_vc_native_assurance_from_full_verification(
                verified.assurance_level(),
            ),
            proof_artifact_id: Some(proof_artifact_id.into()),
            native_trust_ir_import: None,
        }
    }

    /// Create bridge evidence from a verified native memory-safety fact.
    #[cfg(feature = "trust-build")]
    #[must_use]
    pub fn from_verified_memory_safety_fact(
        verified: &VerifiedMemorySafetyFact,
        proof_artifact_id: impl Into<String>,
    ) -> Self {
        Self {
            obligation_id: verified.name().to_string(),
            source: TrustVcNativeProofEvidenceSource::TypedTrustVcExpr,
            typed_expr: Some(trust_vc_expr_evidence_payload(
                verified.name(),
                verified.expr(),
                "TypedMemorySafetyFact",
            )),
            evidence_profile: TrustVcNativeProofEvidenceProfile::OwnershipMemory,
            reasoning_kind: trust_vc_native_reasoning_from_full_verification(
                verified.reasoning_kind(),
            ),
            assurance_level: trust_vc_native_assurance_from_full_verification(
                verified.assurance_level(),
            ),
            proof_artifact_id: Some(proof_artifact_id.into()),
            native_trust_ir_import: None,
        }
    }

    /// Set the trust_vc #2772 evidence profile carried by the native report.
    #[must_use]
    pub fn with_evidence_profile(mut self, profile: TrustVcNativeProofEvidenceProfile) -> Self {
        self.evidence_profile = profile;
        self
    }

    /// Set the trust_vc #2772 reasoning kind carried by the native report.
    #[must_use]
    pub fn with_reasoning_kind(mut self, reasoning_kind: TrustVcNativeProofReasoningKind) -> Self {
        self.reasoning_kind = reasoning_kind;
        self
    }

    /// Set the trust_vc #2772 assurance level carried by the native report.
    #[must_use]
    pub fn with_assurance_level(mut self, assurance_level: TrustVcNativeAssuranceLevel) -> Self {
        self.assurance_level = assurance_level;
        self
    }

    /// Override the replayable proof-artifact id linked by this evidence item.
    #[must_use]
    pub fn with_proof_artifact_id(mut self, proof_artifact_id: impl Into<String>) -> Self {
        self.proof_artifact_id = Some(proof_artifact_id.into());
        self
    }

    /// Override the structured typed `TrustExpr` payload preserved by trust_vc.
    #[must_use]
    pub fn with_typed_expr(mut self, typed_expr: JsonValue) -> Self {
        self.typed_expr = Some(typed_expr);
        self
    }

    /// Attach native Tmir certificate import/replay metadata admitted by trust_vc.
    #[must_use]
    pub fn with_native_trust_ir_import(
        mut self,
        native_trust_ir_import: TrustVcNativeTrustIrImportedProofArtifact,
    ) -> Self {
        self.native_trust_ir_import = Some(native_trust_ir_import);
        self
    }
}

/// Digest-bound native Tmir certificate import admitted by trust_vc.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustVcNativeTrustIrImportedProofArtifact {
    pub request_id: u32,
    pub assertion_id: String,
    pub trust_ir_module_digest: String,
    pub request_digest: String,
    pub trust_ir_obligation_id: u32,
    pub evidence_digest: String,
    pub certificate_digest: String,
    pub compiler_facts_digest: String,
    pub obligation_source_digest: String,
    pub compiler_fact_obligation_id: u32,
    pub compiler_fact_assertion_id: Option<u32>,
    pub compiler_fact_refs: Vec<TrustVcNativeCompilerFactBindingRef>,
    pub replay_engine: String,
    pub replay_invocation: String,
    pub replay_transcript_digest: String,
    pub artifact_fingerprint: String,
    certificate_materialization: Option<Vec<u8>>,
}

/// Stable compiler-fact reference preserved from trust_vc native Tmir metadata.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TrustVcNativeCompilerFactBindingRef {
    pub kind: String,
    pub id: u32,
}

/// Duplicate-free lookup tables for the soundness-critical native import
/// joins. Building these once makes per-public-obligation reconciliation
/// O(log N) and prevents `find` from silently selecting the first duplicate.
#[cfg(feature = "trust-build")]
struct TrustVcNativeTrustIrBundleIndex<'a> {
    imports: BTreeMap<(u32, u32), &'a TrustVcNativeTrustIrImportedProofArtifact>,
    obligation_sources: BTreeMap<u32, &'a trust_ir::NativeObligationSource>,
    proof_obligations: BTreeMap<u32, &'a trust_ir::ProofObligation>,
    replay_assertion_formulas: BTreeMap<(u32, u32), &'a trust_ir::ProofFormula>,
    request_digests: BTreeMap<u32, trust_ir::ProofDigest>,
}

#[cfg(feature = "trust-build")]
impl<'a> TrustVcNativeTrustIrBundleIndex<'a> {
    fn new(
        native_bundle: &'a trust_ir::NativeVerificationBundle,
        imports: &'a [TrustVcNativeTrustIrImportedProofArtifact],
    ) -> Result<Self, TrustVcNativeReportConversionError> {
        let mut import_index = BTreeMap::new();
        for import in imports {
            let key = (import.request_id, import.trust_ir_obligation_id);
            if import_index.insert(key, import).is_some() {
                return Err(TrustVcNativeReportConversionError::DuplicateNativeTmirImportBinding {
                    collection: "imports",
                    key: format!("request={};obligation={}", key.0, key.1),
                });
            }
        }

        let mut obligation_sources = BTreeMap::new();
        let mut public_source_ids = BTreeMap::new();
        for source in &native_bundle.compiler_facts.obligation_sources {
            let obligation_id = source.obligation.index();
            if obligation_sources.insert(obligation_id, source).is_some() {
                return Err(TrustVcNativeReportConversionError::DuplicateNativeTmirImportBinding {
                    collection: "obligation_sources.native_obligation",
                    key: obligation_id.to_string(),
                });
            }
            if public_source_ids
                .insert(source.public_obligation_id.as_str(), obligation_id)
                .is_some()
            {
                return Err(TrustVcNativeReportConversionError::DuplicateNativeTmirImportBinding {
                    collection: "obligation_sources.public_obligation",
                    key: source.public_obligation_id.clone(),
                });
            }
        }

        let mut proof_obligations = BTreeMap::new();
        for obligation in &native_bundle.module.proof_obligations {
            let obligation_id = obligation.id.index();
            if proof_obligations.insert(obligation_id, obligation).is_some() {
                return Err(TrustVcNativeReportConversionError::DuplicateNativeTmirImportBinding {
                    collection: "module.proof_obligations",
                    key: obligation_id.to_string(),
                });
            }
        }

        let mut replay_assertion_formulas = BTreeMap::new();
        let mut request_digests = BTreeMap::new();
        for native_request in &native_bundle.requests {
            let request_digest = native_request.stable_digest();
            let trust_ir::NativeVerificationRequest::TrustVc(request) = native_request else {
                continue;
            };
            let request_id = request.id.index();
            if request_digests.insert(request_id, request_digest).is_some() {
                return Err(TrustVcNativeReportConversionError::DuplicateNativeTmirImportBinding {
                    collection: "requests",
                    key: request_id.to_string(),
                });
            }
            for atom in &request.provenance.replay_context.atoms {
                if atom.kind != trust_ir::NativeReplayAtomKind::Assertion {
                    continue;
                }
                let Some(obligation) = atom.obligation else {
                    continue;
                };
                let key = (request_id, obligation.index());
                if replay_assertion_formulas.insert(key, &atom.formula).is_some() {
                    return Err(
                        TrustVcNativeReportConversionError::DuplicateNativeTmirImportBinding {
                            collection: "replay_assertion_formulas",
                            key: format!("request={};obligation={}", key.0, key.1),
                        },
                    );
                }
            }
        }

        Ok(Self {
            imports: import_index,
            obligation_sources,
            proof_obligations,
            replay_assertion_formulas,
            request_digests,
        })
    }
}

impl TrustVcNativeTrustIrImportedProofArtifact {
    #[cfg(feature = "trust-build")]
    fn from_native(
        request_id: u32,
        artifact: &NativeTrustVcProofArtifact,
    ) -> Result<Self, TrustVcNativeReportConversionError> {
        let admission = artifact.admission();
        if admission.replay_status() != NativeTrustVcArtifactReplayStatus::Replayable
            || admission.status() != NativeTrustVcArtifactAdmissionStatus::Accepted
        {
            return Err(TrustVcNativeReportConversionError::NativeTmirImportRejected {
                trust_ir_obligation_id: artifact.trust_ir_obligation_id(),
                replay_status: format!("{:?}", admission.replay_status()),
                status: format!("{:?}", admission.status()),
                reasons: admission
                    .rejection_reasons()
                    .iter()
                    .map(|reason| format!("{reason:?}"))
                    .collect(),
            });
        }

        Ok(Self {
            request_id,
            assertion_id: artifact.assertion_id().to_string(),
            trust_ir_module_digest: artifact.trust_ir_module_digest().to_string(),
            request_digest: artifact.request_digest().to_string(),
            trust_ir_obligation_id: artifact.trust_ir_obligation_id(),
            evidence_digest: artifact.evidence_digest().to_string(),
            certificate_digest: artifact.certificate_digest().to_string(),
            compiler_facts_digest: artifact
                .compiler_facts_binding()
                .compiler_facts_digest()
                .to_string(),
            obligation_source_digest: artifact
                .compiler_facts_binding()
                .obligation_source_digest()
                .to_string(),
            compiler_fact_obligation_id: artifact.compiler_facts_binding().obligation_id(),
            compiler_fact_assertion_id: artifact.compiler_facts_binding().assertion_id(),
            compiler_fact_refs: artifact
                .compiler_facts_binding()
                .fact_refs()
                .iter()
                .map(trust_vc_native_compiler_fact_ref_from_native)
                .collect(),
            replay_engine: artifact
                .solver_identity()
                .replay_engine()
                .unwrap_or_default()
                .to_string(),
            replay_invocation: artifact
                .solver_identity()
                .replay_invocation()
                .unwrap_or_default()
                .to_string(),
            replay_transcript_digest: artifact
                .solver_identity()
                .transcript_digest()
                .unwrap_or_default()
                .to_string(),
            artifact_fingerprint: artifact.artifact_fingerprint().to_string(),
            certificate_materialization: None,
        })
    }
}

/// Trust: true once the optional per-function wall-clock deadline has
/// elapsed. A `None` deadline (budget disabled) never trips.
#[cfg(feature = "trust-build")]
fn trust_vc_budget_deadline_exceeded(deadline: Option<std::time::Instant>) -> bool {
    deadline.is_some_and(|deadline| std::time::Instant::now() >= deadline)
}

#[cfg(feature = "trust-build")]
fn trust_vc_native_compiler_fact_ref_from_native(
    fact: &trust_vc_trust_engine::TrustVcNativeCompilerFactRef,
) -> TrustVcNativeCompilerFactBindingRef {
    let kind = match fact.kind() {
        trust_vc_trust_engine::TrustVcNativeCompilerFactKind::AdtLayout => "AdtLayout",
        trust_vc_trust_engine::TrustVcNativeCompilerFactKind::FatPointer => "FatPointer",
        trust_vc_trust_engine::TrustVcNativeCompilerFactKind::Cast => "Cast",
        trust_vc_trust_engine::TrustVcNativeCompilerFactKind::Monomorphization => {
            "Monomorphization"
        }
        _ => "Unknown",
    };
    TrustVcNativeCompilerFactBindingRef { kind: kind.to_string(), id: fact.id() }
}

/// Admit trust_vc native Tmir certificate-import reports as digest-bound proof objects.
///
/// This is intentionally stricter than accepting the report text: it delegates
/// admission to `trust-vc-trust-engine`, requires the upstream replay/admission
/// status to be replayable and accepted, and preserves the native Tmir
/// evidence digest, certificate digest, compiler-fact binding, and artifact
/// fingerprint for downstream identity checks.
#[cfg(feature = "trust-build")]
pub fn trust_vc_native_trust_ir_imported_proof_artifacts_from_report(
    report: &TrustVcNativeTrustIrBundleReport,
) -> Result<Vec<TrustVcNativeTrustIrImportedProofArtifact>, TrustVcNativeReportConversionError> {
    let artifacts = report
        .requests()
        .iter()
        .flat_map(|request| {
            request
                .admit_native_proof_artifacts()
                .into_iter()
                .map(move |artifact| (request.request_id(), artifact))
        })
        .collect::<Vec<_>>();
    if artifacts.is_empty() {
        return Err(TrustVcNativeReportConversionError::NativeTmirImportMissingArtifacts {
            module: report.module_name().to_string(),
        });
    }
    let imports = artifacts
        .iter()
        .map(|(request_id, artifact)| {
            TrustVcNativeTrustIrImportedProofArtifact::from_native(*request_id, artifact)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut seen = BTreeMap::new();
    for import in &imports {
        // The upstream report DTO remains able to deserialize historical
        // digest labels for diagnostics, but an imported proof object is an
        // authority-bearing boundary.  TrustIr native bundle validation and
        // every digest produced by that boundary are SHA-256-only, so reject a
        // legacy stable label before callers can publish it as import metadata.
        validate_trust_vc_native_trust_ir_import_binding(import)?;
        let key = (import.request_id, import.trust_ir_obligation_id);
        if seen.insert(key, ()).is_some() {
            return Err(TrustVcNativeReportConversionError::DuplicateNativeTmirImportBinding {
                collection: "imports",
                key: format!("request={};obligation={}", key.0, key.1),
            });
        }
    }
    Ok(imports)
}

/// Consume a native Tmir bundle with trust_vc and return admitted proof imports.
///
/// The compiler uses this to publish the same first-class identity, replay,
/// and compiler-fact metadata that trust_vc later validates when importing the
/// proof certificate as verifier evidence.
#[cfg(feature = "trust-build")]
pub fn trust_vc_native_trust_ir_imported_proof_artifacts_from_bundle(
    native_bundle: &trust_ir::NativeVerificationBundle,
) -> Result<Vec<TrustVcNativeTrustIrImportedProofArtifact>, TrustVcNativeReportConversionError> {
    let report = TrustVcTrustEngine::new().consume_native_trust_ir_bundle(native_bundle).map_err(
        |error| TrustVcNativeReportConversionError::NativeTmirBundleRejected {
            reason: error.to_string(),
        },
    )?;
    let mut imports = trust_vc_native_trust_ir_imported_proof_artifacts_from_report(&report)?;
    let mut certificates = BTreeMap::new();
    for certificate in &native_bundle.module.proof_certificates {
        let obligation_id = certificate.obligation.index();
        if certificates.insert(obligation_id, certificate).is_some() {
            return Err(TrustVcNativeReportConversionError::DuplicateNativeTmirImportBinding {
                collection: "module.proof_certificates",
                key: obligation_id.to_string(),
            });
        }
    }
    for import in &mut imports {
        let Some(certificate) = certificates.get(&import.trust_ir_obligation_id).copied() else {
            return Err(TrustVcNativeReportConversionError::NativeTmirImportCertificateMaterializationMissing {
                trust_ir_obligation_id: import.trust_ir_obligation_id,
                reason: "native bundle did not retain the imported TrustIr certificate".to_string(),
            });
        };
        let bytes = trust_types::canonical_json_bytes(certificate)
            .map_err(|error| format!("canonical TrustIr certificate JSON encoding failed: {error}"))
            .map_err(|reason| {
            TrustVcNativeReportConversionError::NativeTmirImportCertificateMaterializationMissing {
                trust_ir_obligation_id: import.trust_ir_obligation_id,
                reason,
            }
        })?;
        if bytes.is_empty()
            || bytes.len() > trust_verifier_api::MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES
        {
            return Err(TrustVcNativeReportConversionError::NativeTmirImportCertificateMaterializationMissing {
                trust_ir_obligation_id: import.trust_ir_obligation_id,
                reason: format!("canonical certificate payload has invalid byte length {}", bytes.len()),
            });
        }
        import.certificate_materialization = Some(bytes);
    }
    Ok(imports)
}

/// Public metadata entries that bind a trust_vc native Tmir import to a verifier
/// obligation. Request/proof/suite identity is emitted by the caller so this
/// helper returns the proof certificate, replay, and compiler-fact bindings.
#[cfg(feature = "trust-build")]
pub fn trust_vc_native_trust_ir_import_metadata_entries(
    import: &TrustVcNativeTrustIrImportedProofArtifact,
) -> Vec<MetadataEntry> {
    vec![
        MetadataEntry {
            key: TRUST_TRUST_IR_NATIVE_ASSERTION_ID_METADATA_KEY.to_string(),
            value: import.assertion_id.clone(),
        },
        MetadataEntry {
            key: TRUST_TRUST_IR_NATIVE_TRUST_IR_MODULE_DIGEST_METADATA_KEY.to_string(),
            value: import.trust_ir_module_digest.clone(),
        },
        MetadataEntry {
            key: TRUST_TRUST_IR_NATIVE_REQUEST_DIGEST_METADATA_KEY.to_string(),
            value: import.request_digest.clone(),
        },
        MetadataEntry {
            key: TRUST_TRUST_IR_NATIVE_EVIDENCE_DIGEST_METADATA_KEY.to_string(),
            value: import.evidence_digest.clone(),
        },
        MetadataEntry {
            key: TRUST_TRUST_IR_NATIVE_CERTIFICATE_DIGEST_METADATA_KEY.to_string(),
            value: import.certificate_digest.clone(),
        },
        MetadataEntry {
            key: TRUST_TRUST_IR_NATIVE_COMPILER_FACTS_DIGEST_METADATA_KEY.to_string(),
            value: import.compiler_facts_digest.clone(),
        },
        MetadataEntry {
            key: TRUST_TRUST_IR_NATIVE_OBLIGATION_SOURCE_DIGEST_METADATA_KEY.to_string(),
            value: import.obligation_source_digest.clone(),
        },
        MetadataEntry {
            key: TRUST_TRUST_IR_NATIVE_REPLAY_ENGINE_METADATA_KEY.to_string(),
            value: import.replay_engine.clone(),
        },
        MetadataEntry {
            key: TRUST_TRUST_IR_NATIVE_REPLAY_INVOCATION_METADATA_KEY.to_string(),
            value: import.replay_invocation.clone(),
        },
        MetadataEntry {
            key: TRUST_TRUST_IR_NATIVE_REPLAY_TRANSCRIPT_DIGEST_METADATA_KEY.to_string(),
            value: import.replay_transcript_digest.clone(),
        },
        MetadataEntry {
            key: TRUST_TRUST_IR_NATIVE_ARTIFACT_FINGERPRINT_METADATA_KEY.to_string(),
            value: import.artifact_fingerprint.clone(),
        },
    ]
}

/// Native trust_vc proof-evidence source mirrored from trust_vc #2769/#2772.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TrustVcNativeProofEvidenceSource {
    TypedTrustVcExpr,
    TypedCompatibilityBoundary,
    LegacySourceText,
}

/// Native trust_vc evidence profiles mirrored from trust_vc #2772.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TrustVcNativeProofEvidenceProfile {
    Unspecified,
    TypedContractFrame,
    OwnershipMemory,
    TypedInvariant,
    TypedTranslationValidation,
    TypedCastBootstrap,
    TypedAdtBootstrap,
    TypedPointerBootstrap,
    TypedFatPointerBootstrap,
    TypedDeductiveObligation,
    TypedCompatibility,
    LegacyCompatibility,
}

/// Native trust_vc proof-reasoning classes mirrored from trust_vc #2772.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TrustVcNativeProofReasoningKind {
    Unspecified,
    Deductive,
    Ownership,
    Constructive,
}

/// Native trust_vc assurance levels mirrored from trust_vc #2772.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TrustVcNativeAssuranceLevel {
    Unspecified,
    CompatibilityEvidence,
    AssumedEvidence,
    StaticProof,
    MetadataOnly,
}

/// Bridge representation of trust_vc `TrustReplayableProofArtifact`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustVcNativeReplayableProofArtifact {
    pub artifact_id: String,
    pub format: TrustVcNativeProofArtifactFormat,
    pub digest: String,
    pub payload: String,
    pub strict_verified: bool,
    pub clean_supported: bool,
    pub kernel_verified: bool,
    pub trust_count: u32,
    pub hole_count: u32,
    pub resolution_count: u32,
    pub theory_count: u32,
    pub assumption_obligation_ids: Vec<String>,
    pub assertion_obligation_ids: Vec<String>,
}

impl TrustVcNativeReplayableProofArtifact {
    /// Create an unchecked trust_vc Alethe artifact bridge value with a
    /// digest-derived id.
    ///
    /// Conversion rejects the value until native trust_vc marks it strict-checked
    /// or kernel-checked.
    #[must_use]
    pub fn alethe(payload: impl Into<String>) -> Self {
        let payload = payload.into();
        let digest_hex = stable_sha256_hex(payload.as_bytes());
        Self {
            artifact_id: format!("{TRUST_VC_PROOF_ARTIFACT_ID_PREFIX}{digest_hex}"),
            format: TrustVcNativeProofArtifactFormat::Alethe,
            digest: format!("sha256:{digest_hex}"),
            payload,
            strict_verified: false,
            clean_supported: false,
            kernel_verified: false,
            trust_count: 0,
            hole_count: 0,
            resolution_count: 0,
            theory_count: 0,
            assumption_obligation_ids: Vec::new(),
            assertion_obligation_ids: Vec::new(),
        }
    }

    /// Mark the replayable proof as accepted by trust-vc's strict checker.
    #[must_use]
    pub fn with_strict_verified(mut self, strict_verified: bool) -> Self {
        self.strict_verified = strict_verified;
        self
    }

    /// Mark the replayable proof as accepted by trust-vc's independent kernel.
    #[must_use]
    pub fn with_kernel_verified(mut self, kernel_verified: bool) -> Self {
        self.kernel_verified = kernel_verified;
        self
    }

    /// Declare assertion obligations discharged by this proof artifact.
    #[must_use]
    pub fn with_assertion_obligation_ids(mut self, ids: Vec<String>) -> Self {
        self.assertion_obligation_ids = ids;
        self
    }

    /// Declare assumption obligations admitted by this proof artifact.
    #[must_use]
    pub fn with_assumption_obligation_ids(mut self, ids: Vec<String>) -> Self {
        self.assumption_obligation_ids = ids;
        self
    }
}

/// Native trust_vc replayable proof format mirrored from trust_vc #2772.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TrustVcNativeProofArtifactFormat {
    Alethe,
}

/// Failure while running the direct trust_vc MIR memory path.
#[cfg(feature = "trust-build")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TrustVcDirectMirMemoryError {
    InvalidMetadataJson { origin: String, reason: String },
    MultipleProofUnitPayloads { first_origin: String, second_origin: String },
    UnsupportedSchema { origin: String, schema: String },
    UnsupportedHeapPointerDetails { origin: String, detail: String },
    InvalidProofUnitPayload { origin: String, reason: String },
    MissingObligation { origin: String, obligation_id: String },
    MissingOwnershipContext { origin: String, obligation_id: String },
    TrustVcTrustEngineRejected { origin: String, obligation_id: String, reason: String },
    // Trust: trust-vc's direct-MIR-memory verifier produced a genuine
    // counterexample for the obligation (e.g. `s[i % 9]` is OOB at `i = 8`).
    // This is a refutation, NOT a coverage gap — propagated by the compiler's
    // native evidence import to a `VerificationResult::Failed` under `-full`.
    Refuted { origin: String, obligation_id: String, model: Option<String> },
}

/// Exact non-authoritative carrier identity used by the router's private
/// post-solve receipt.
///
/// These digests do not prove an obligation. They let the router bind a live,
/// release-admitted result to the exact public claim and proof-unit bytes that
/// it validated immediately before the solve, then revalidate that binding at
/// evidence selection time.
#[cfg(feature = "trust-build")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustVcDirectMirMemoryCarrierBinding {
    public_semantic_digest: String,
    proof_unit_payload_digest: String,
    typed_predicate_digest: String,
}

#[cfg(feature = "trust-build")]
impl TrustVcDirectMirMemoryCarrierBinding {
    #[must_use]
    pub fn public_semantic_digest(&self) -> &str {
        &self.public_semantic_digest
    }

    #[must_use]
    pub fn proof_unit_payload_digest(&self) -> &str {
        &self.proof_unit_payload_digest
    }

    #[must_use]
    pub fn typed_predicate_digest(&self) -> &str {
        &self.typed_predicate_digest
    }
}

#[cfg(feature = "trust-build")]
impl std::fmt::Display for TrustVcDirectMirMemoryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidMetadataJson { origin, reason } => {
                write!(f, "invalid MIR memory proof-unit JSON at {origin}: {reason}")
            }
            Self::MultipleProofUnitPayloads { first_origin, second_origin } => write!(
                f,
                "multiple direct MIR memory proof-unit payloads were supplied at {first_origin} and {second_origin}"
            ),
            Self::UnsupportedSchema { origin, schema } => write!(
                f,
                "unsupported direct MIR memory payload schema `{schema}` at {origin}; expected {TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_VERSION}"
            ),
            Self::UnsupportedHeapPointerDetails { origin, detail } => write!(
                f,
                "{TRUST_VC_MIR_MEMORY_UNSUPPORTED_HEAP_POINTER_DETAILS}: unsupported field {detail} at {origin}"
            ),
            Self::InvalidProofUnitPayload { origin, reason } => {
                write!(f, "invalid direct MIR memory proof-unit payload at {origin}: {reason}")
            }
            Self::MissingObligation { origin, obligation_id } => write!(
                f,
                "direct MIR memory proof-unit payload at {origin} does not contain obligation `{obligation_id}`"
            ),
            Self::MissingOwnershipContext { origin, obligation_id } => write!(
                f,
                "direct MIR memory proof-unit payload at {origin} cannot prove `{obligation_id}` without typed ownership and borrow state"
            ),
            Self::TrustVcTrustEngineRejected { origin, obligation_id, reason } => write!(
                f,
                "trust-vc-trust-engine rejected direct MIR memory proof-unit payload at {origin} for `{obligation_id}`: {reason}"
            ),
            Self::Refuted { origin, obligation_id, model } => write!(
                f,
                "trust-vc-trust-engine refuted direct MIR memory proof-unit payload at {origin} for `{obligation_id}`{}",
                match model {
                    Some(model) => format!(": counterexample {model}"),
                    None => String::new(),
                }
            ),
        }
    }
}

#[cfg(feature = "trust-build")]
impl std::error::Error for TrustVcDirectMirMemoryError {}

#[cfg(feature = "trust-build")]
#[derive(Debug, Clone, PartialEq, Eq)]
enum TrustVcActiveTmirAdapterError {
    EmitRequest { obligation_id: String, reason: String },
    TrustVcTrustEngineRejected { obligation_id: String, reason: String },
    MissingNativeProofEvidence { obligation_id: String },
    ConvertTrustEngineReport { obligation_id: String, reason: String },
}

#[cfg(feature = "trust-build")]
impl std::fmt::Display for TrustVcActiveTmirAdapterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmitRequest { obligation_id, reason } => write!(
                f,
                "could not emit structured Tmir adapter request for `{obligation_id}`: {reason}"
            ),
            Self::TrustVcTrustEngineRejected { obligation_id, reason } => write!(
                f,
                "trust-vc-trust-engine rejected structured Tmir adapter request for `{obligation_id}`: {reason}"
            ),
            Self::MissingNativeProofEvidence { obligation_id } => write!(
                f,
                "trust-vc-trust-engine report did not include typed evidence for `{obligation_id}`"
            ),
            Self::ConvertTrustEngineReport { obligation_id, reason } => write!(
                f,
                "could not convert trust-vc-trust-engine report for `{obligation_id}` into native proof evidence: {reason}"
            ),
        }
    }
}

#[cfg(feature = "trust-build")]
impl std::error::Error for TrustVcActiveTmirAdapterError {}

/// Extra proof artifacts that must come from the Trust/trust-vc lowering path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustVcNativeReportArtifacts {
    pub normalized_obligation: EvidenceArtifact,
    pub engine_input: EvidenceArtifact,
}

impl TrustVcNativeReportArtifacts {
    /// Create supplemental artifacts required by #1104 acceptance.
    pub fn new(
        normalized_obligation: EvidenceArtifact,
        engine_input: EvidenceArtifact,
    ) -> Result<Self, TrustVcNativeReportConversionError> {
        validate_artifact_kind(
            "normalized_obligation",
            &normalized_obligation,
            EvidenceArtifactKind::NormalizedObligation,
        )?;
        validate_artifact_kind("engine_input", &engine_input, EvidenceArtifactKind::EngineInput)?;
        validate_supplemental_artifact_hash("normalized_obligation", &normalized_obligation)?;
        validate_supplemental_artifact_hash("engine_input", &engine_input)?;
        validate_supplemental_artifact_uri("normalized_obligation", &normalized_obligation)?;
        validate_supplemental_artifact_uri("engine_input", &engine_input)?;
        Ok(Self { normalized_obligation, engine_input })
    }
}

/// Lower public bundle/obligation identity into trust_vc native audit artifacts.
///
/// This is deliberately not a source parser and not proof evidence. It only
/// produces the deterministic `NormalizedObligation` and `EngineInput` artifact
/// identities needed to bind caller-supplied native trust_vc reports back to the
/// public verifier-api request.
pub fn trust_vc_native_report_artifacts_from_bundle(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<TrustVcNativeReportArtifacts, TrustVcNativeLoweringError> {
    let diagnostics = trust_vc_native_lowering_diagnostics(bundle, obligation);
    if !diagnostics.is_empty() {
        return Err(TrustVcNativeLoweringError::InvalidObligationShape {
            obligation_id: obligation.obligation_id.clone(),
            diagnostics,
        });
    }

    let normalized_obligation_payload = serde_json::json!({
        "schema_version": TRUST_VC_NORMALIZED_OBLIGATION_SCHEMA_VERSION,
        "bundle_id": &bundle.bundle_id,
        "subject": serde_json::to_value(&bundle.subject).map_err(|error| {
            TrustVcNativeLoweringError::SerializeLoweringPayload {
                label: "subject",
                reason: error.to_string(),
            }
        })?,
        "obligation": serde_json::to_value(obligation).map_err(|error| {
            TrustVcNativeLoweringError::SerializeLoweringPayload {
                label: "obligation",
                reason: error.to_string(),
            }
        })?,
    });

    let engine_input_payload = serde_json::json!({
        "schema_version": TRUST_VC_NATIVE_ENGINE_INPUT_SCHEMA_VERSION,
        "engine": TRUST_VC_ENGINE_NAME,
        "bundle_id": &bundle.bundle_id,
        "obligation_id": &obligation.obligation_id,
        "requires_contract_frame": requires_trust_vc_contract_frame(&obligation.kind),
        "requires_result_binding": requires_trust_vc_result_binding(&obligation.kind),
        "requires_ownership_context": requires_trust_vc_ownership_context(&obligation.kind),
        "contract": trust_vc_contract_payload(bundle, obligation)?,
        "metadata": serde_json::to_value(&obligation.metadata).map_err(|error| {
            TrustVcNativeLoweringError::SerializeLoweringPayload {
                label: "obligation_metadata",
                reason: error.to_string(),
            }
        })?,
    });

    TrustVcNativeReportArtifacts::new(
        trust_vc_lowering_artifact(
            EvidenceArtifactKind::NormalizedObligation,
            bundle,
            obligation,
            "normalized-obligation",
            &normalized_obligation_payload,
        )?,
        trust_vc_lowering_artifact(
            EvidenceArtifactKind::EngineInput,
            bundle,
            obligation,
            "native-engine-input",
            &engine_input_payload,
        )?,
    )
    .map_err(TrustVcNativeLoweringError::InvalidSupplementalArtifacts)
}

/// Failure while binding public verifier-api inputs to a native trust_vc report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TrustVcNativeLoweringError {
    InvalidObligationShape { obligation_id: String, diagnostics: Vec<String> },
    MissingContract { obligation_id: String, contract_id: String },
    SerializeLoweringPayload { label: &'static str, reason: String },
    InvalidSupplementalArtifacts(TrustVcNativeReportConversionError),
}

impl std::fmt::Display for TrustVcNativeLoweringError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidObligationShape { obligation_id, diagnostics } => write!(
                f,
                "trust-vc native lowering for {obligation_id} is missing required typed inputs: {}",
                diagnostics.join("; ")
            ),
            Self::MissingContract { obligation_id, contract_id } => write!(
                f,
                "trust-vc native lowering for {obligation_id} could not find contract {contract_id}"
            ),
            Self::SerializeLoweringPayload { label, reason } => {
                write!(f, "trust-vc native lowering could not serialize {label}: {reason}")
            }
            Self::InvalidSupplementalArtifacts(error) => {
                write!(
                    f,
                    "trust-vc native lowering produced invalid supplemental artifacts: {error}"
                )
            }
        }
    }
}

impl std::error::Error for TrustVcNativeLoweringError {}

#[cfg(feature = "trust-build")]
struct ValidatedDirectMirMemoryCarrier {
    origin: String,
    proof_unit: TrustMirMemoryProofUnit,
    proof_unit_payload_digest: String,
    typed_predicate_digest: String,
}

#[cfg(feature = "trust-build")]
fn unique_obligation_metadata_value<'a>(
    obligation: &'a TrustObligation,
    key: &str,
) -> Result<Option<&'a str>, TrustVcDirectMirMemoryError> {
    let mut matching = obligation.metadata.iter().filter(|entry| entry.key == key);
    let Some(first) = matching.next() else {
        return Ok(None);
    };
    if matching.next().is_some() {
        return Err(TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
            origin: "obligation metadata".to_string(),
            reason: format!("direct MIR-memory carrier contains duplicate `{key}` metadata"),
        });
    }
    Ok(Some(first.value.as_str()))
}

#[cfg(feature = "trust-build")]
fn required_unique_obligation_metadata_value<'a>(
    obligation: &'a TrustObligation,
    key: &str,
) -> Result<&'a str, TrustVcDirectMirMemoryError> {
    unique_obligation_metadata_value(obligation, key)?.ok_or_else(|| {
        TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
            origin: "obligation metadata".to_string(),
            reason: format!("direct MIR-memory carrier requires unique `{key}` metadata"),
        }
    })
}

#[cfg(feature = "trust-build")]
fn normalized_direct_mir_memory_public_predicate(
    obligation: &TrustObligation,
) -> Result<TrustExpr, TrustVcDirectMirMemoryError> {
    let schema = required_unique_obligation_metadata_value(
        obligation,
        TRUST_VC_FORMULA_SCHEMA_METADATA_KEY,
    )?;
    if schema != TRUST_SPEC_PREDICATE_SCHEMA_VERSION {
        return Err(TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
            origin: "obligation metadata".to_string(),
            reason: format!(
                "direct MIR-memory carrier requires {TRUST_VC_FORMULA_SCHEMA_METADATA_KEY}={TRUST_SPEC_PREDICATE_SCHEMA_VERSION}, got `{schema}`"
            ),
        });
    }
    let sort =
        required_unique_obligation_metadata_value(obligation, TRUST_VC_FORMULA_SORT_METADATA_KEY)?;
    if sort != "Bool" {
        return Err(TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
            origin: "obligation metadata".to_string(),
            reason: format!(
                "direct MIR-memory carrier requires {TRUST_VC_FORMULA_SORT_METADATA_KEY}=Bool, got `{sort}`"
            ),
        });
    }
    let smtlib = required_unique_obligation_metadata_value(
        obligation,
        TRUST_VC_FORMULA_SMTLIB_METADATA_KEY,
    )?;
    if smtlib.trim().is_empty() {
        return Err(TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
            origin: "obligation metadata".to_string(),
            reason: format!(
                "direct MIR-memory carrier requires nonempty `{TRUST_VC_FORMULA_SMTLIB_METADATA_KEY}` metadata"
            ),
        });
    }
    let vc_digest =
        required_unique_obligation_metadata_value(obligation, TRUST_VC_DIGEST_METADATA_KEY)?;
    if normalized_sha256_hex(vc_digest).is_none_or(|digest| {
        digest != vc_digest || digest.bytes().any(|byte| byte.is_ascii_uppercase())
    }) {
        return Err(TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
            origin: "obligation metadata".to_string(),
            reason: format!(
                "direct MIR-memory carrier requires canonical lowercase raw SHA-256 `{TRUST_VC_DIGEST_METADATA_KEY}` metadata"
            ),
        });
    }

    let payload = required_unique_obligation_metadata_value(
        obligation,
        TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY,
    )?;
    let predicate: trust_verifier_api::TrustSpecPredicate =
        trust_types::json_depth::from_str_deep(payload).map_err(|error| {
            TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
                origin: "obligation metadata".to_string(),
                reason: format!("invalid public typed formula payload: {error}"),
            }
        })?;
    let canonical_payload = serde_json::to_string(&predicate).map_err(|error| {
        TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
            origin: "obligation metadata".to_string(),
            reason: format!("could not canonicalize public typed formula payload: {error}"),
        }
    })?;
    if canonical_payload != payload {
        return Err(TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
            origin: "obligation metadata".to_string(),
            reason: "public typed formula payload is not in its canonical serialized form"
                .to_string(),
        });
    }

    let public = trust_ir_adapter_request::lowered_typed_cfg_predicate_from_metadata(obligation)
        .map_err(|error| TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
            origin: "obligation metadata".to_string(),
            reason: format!("public typed formula could not be lowered exactly: {error}"),
        })?;
    // The public formula is the bad-state VC. The MIR-memory unit asserts its
    // negation. Preserve the producer's exact normalization so harmless
    // double-negation rewrites cannot turn into an equivalence guess.
    match public {
        TrustExpr::BoolLiteral { value: true } => {
            Err(TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
                origin: "obligation metadata".to_string(),
                reason: "a definitely satisfiable public bad-state formula cannot mint a direct MIR-memory proof unit"
                    .to_string(),
            })
        }
        TrustExpr::BoolLiteral { value: false } => Ok(TrustExpr::bool_literal(true)),
        TrustExpr::Not { expr } => Ok(*expr),
        other => Ok(TrustExpr::not(other)),
    }
}

#[cfg(feature = "trust-build")]
fn validate_direct_mir_memory_obligation_carrier(
    obligation: &TrustObligation,
) -> Result<Option<ValidatedDirectMirMemoryCarrier>, TrustVcDirectMirMemoryError> {
    if !requires_trust_vc_ownership_context(&obligation.kind) {
        return Ok(None);
    }
    let Some(raw_payload) =
        unique_obligation_metadata_value(obligation, TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY)?
    else {
        return Ok(None);
    };
    let origin = format!("obligation metadata `{}`", TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY);
    let payload: JsonValue =
        trust_types::json_depth::from_str_deep(raw_payload).map_err(|error| {
            TrustVcDirectMirMemoryError::InvalidMetadataJson {
                origin: origin.clone(),
                reason: error.to_string(),
            }
        })?;
    if let Some(detail) = unsupported_mir_memory_payload_detail(&payload) {
        return Err(TrustVcDirectMirMemoryError::UnsupportedHeapPointerDetails { origin, detail });
    }
    require_structured_mir_memory_proof_unit_metadata(&origin, obligation)?;
    validate_direct_mir_memory_payload_for_obligation(&origin, &payload, obligation)?;
    let proof_unit: TrustMirMemoryProofUnit = trust_types::json_depth::from_str_deep(raw_payload)
        .map_err(|error| {
        TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
            origin: origin.clone(),
            reason: error.to_string(),
        }
    })?;
    let mut canonical_value = serde_json::to_value(&proof_unit).map_err(|error| {
        TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
            origin: origin.clone(),
            reason: format!("could not serialize typed MIR-memory proof unit: {error}"),
        }
    })?;
    trust_types::digest::canonicalize_json_in_place(&mut canonical_value);
    let canonical_payload = serde_json::to_string(&canonical_value).map_err(|error| {
        TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
            origin: origin.clone(),
            reason: format!("could not encode canonical typed MIR-memory proof unit: {error}"),
        }
    })?;
    if canonical_payload != raw_payload {
        return Err(TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
            origin,
            reason: "direct MIR-memory proof-unit JSON is not the exact canonical producer serialization (duplicate keys, alternate lexical forms, and whitespace variants are rejected)"
                .to_string(),
        });
    }
    let expected_predicate = normalized_direct_mir_memory_public_predicate(obligation)?;
    let [unit_obligation] = proof_unit.obligations() else {
        return Err(TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
            origin,
            reason: format!(
                "direct MIR-memory carrier must contain exactly one obligation row; found {}",
                proof_unit.obligations().len()
            ),
        });
    };
    if unit_obligation.id() != obligation.obligation_id {
        return Err(TrustVcDirectMirMemoryError::MissingObligation {
            origin,
            obligation_id: obligation.obligation_id.clone(),
        });
    }
    if unit_obligation.predicate() != &expected_predicate {
        return Err(TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
            origin,
            reason: format!(
                "sole proof-unit predicate for `{}` is not the exact normalized negation of the public `{TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY}` claim",
                obligation.obligation_id
            ),
        });
    }
    let typed_predicate_payload = serde_json::to_vec(&expected_predicate).map_err(|error| {
        TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
            origin: origin.clone(),
            reason: format!("could not encode the bound typed predicate: {error}"),
        }
    })?;
    Ok(Some(ValidatedDirectMirMemoryCarrier {
        origin,
        proof_unit,
        proof_unit_payload_digest: stable_sha256_hex(raw_payload.as_bytes()),
        typed_predicate_digest: stable_sha256_hex(&typed_predicate_payload),
    }))
}

#[cfg(feature = "trust-build")]
fn validate_direct_mir_memory_carrier_from_bundle(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<Option<ValidatedDirectMirMemoryCarrier>, TrustVcDirectMirMemoryError> {
    let Some(carrier) = validate_direct_mir_memory_obligation_carrier(obligation)? else {
        return Ok(None);
    };
    let carrier_payload = required_unique_obligation_metadata_value(
        obligation,
        TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY,
    )?;
    let exact_row_count =
        bundle.obligations.iter().filter(|candidate| *candidate == obligation).count();
    let same_id_count = bundle
        .obligations
        .iter()
        .filter(|candidate| candidate.obligation_id == obligation.obligation_id)
        .count();
    if exact_row_count != 1 || same_id_count != 1 {
        return Err(TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
            origin: carrier.origin,
            reason: format!(
                "direct carrier obligation `{}` is not the unique exact row in bundle `{}`",
                obligation.obligation_id, bundle.bundle_id
            ),
        });
    }
    for candidate in bundle
        .obligations
        .iter()
        .filter(|candidate| candidate.obligation_id != obligation.obligation_id)
    {
        for sibling_carrier in candidate
            .metadata
            .iter()
            .filter(|entry| entry.key == TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY)
        {
            let duplicates_current_carrier = sibling_carrier.value == carrier_payload;
            let mentions_current_obligation =
                trust_types::json_depth::from_str_deep::<JsonValue>(&sibling_carrier.value)
                    .ok()
                    .and_then(|payload| payload.get("obligations").cloned())
                    .and_then(|obligations| obligations.as_array().cloned())
                    .is_some_and(|obligations| {
                        obligations.iter().any(|row| {
                            row.get("id")
                                .and_then(JsonValue::as_str)
                                .is_some_and(|id| id == obligation.obligation_id)
                        })
                    });
            if duplicates_current_carrier || mentions_current_obligation {
                return Err(TrustVcDirectMirMemoryError::MultipleProofUnitPayloads {
                    first_origin: format!(
                        "obligation `{}` metadata `{TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY}`",
                        obligation.obligation_id
                    ),
                    second_origin: format!(
                        "sibling obligation `{}` carries a proof unit bound to `{}`",
                        candidate.obligation_id, obligation.obligation_id
                    ),
                });
            }
        }
    }
    if bundle.metadata.iter().any(|entry| entry.key == TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY)
    {
        return Err(TrustVcDirectMirMemoryError::MultipleProofUnitPayloads {
            first_origin: format!(
                "obligation metadata `{TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY}`"
            ),
            second_origin: "bundle metadata".to_string(),
        });
    }
    if let Some(contract) = bundle.contracts.iter().find(|contract| {
        matches!(
            &contract.predicate,
            ContractPredicate::MemoryIr { schema, .. }
                | ContractPredicate::CanonicalJson { schema, .. }
                if schema == TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_VERSION
        )
    }) {
        return Err(TrustVcDirectMirMemoryError::MultipleProofUnitPayloads {
            first_origin: format!(
                "obligation metadata `{TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY}`"
            ),
            second_origin: format!("contract `{}`", contract.contract_id),
        });
    }
    Ok(Some(carrier))
}

/// Recompute the exact direct-carrier identity used by the router's private
/// post-solve receipt. No proof authority is conferred by this public value.
#[cfg(feature = "trust-build")]
pub fn trust_vc_direct_mir_memory_carrier_binding(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<Option<TrustVcDirectMirMemoryCarrierBinding>, TrustVcDirectMirMemoryError> {
    let Some(carrier) = validate_direct_mir_memory_carrier_from_bundle(bundle, obligation)? else {
        return Ok(None);
    };
    let public_semantic_digest = bundle
        .canonical_obligation_semantic_digest_sha256(obligation)
        .map_err(|reason| TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
            origin: carrier.origin,
            reason: format!("public obligation semantics are not canonical: {reason}"),
        })?;
    Ok(Some(TrustVcDirectMirMemoryCarrierBinding {
        public_semantic_digest,
        proof_unit_payload_digest: carrier.proof_unit_payload_digest,
        typed_predicate_digest: carrier.typed_predicate_digest,
    }))
}

/// True only for an exact, typed MIR-memory carrier accepted by the dedicated
/// in-process lane before any solver is run. This is a routing predicate, not
/// proof authority.
#[cfg(feature = "trust-build")]
#[must_use]
pub fn trust_vc_has_exact_structured_direct_mir_memory_proof_unit(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> bool {
    matches!(trust_vc_direct_mir_memory_carrier_binding(bundle, obligation), Ok(Some(_)))
}

/// Validate an obligation-local structured MIR-memory carrier without running
/// TrustVC. The compiler uses this to defer the only solve to the router's
/// deadline-aware in-process lane.
#[cfg(feature = "trust-build")]
pub fn trust_vc_validate_structured_direct_mir_memory_obligation_metadata(
    obligation: &TrustObligation,
) -> Result<bool, TrustVcDirectMirMemoryError> {
    validate_direct_mir_memory_obligation_carrier(obligation).map(|carrier| carrier.is_some())
}

#[cfg(feature = "trust-build")]
fn require_structured_mir_memory_proof_unit_metadata(
    origin: &str,
    obligation: &TrustObligation,
) -> Result<(), TrustVcDirectMirMemoryError> {
    for (key, value) in [
        (TRUST_VC_CONDITION_ORIGIN_METADATA_KEY, TRUST_VC_CONDITION_ORIGIN_METADATA_VALUE),
        (TRUST_VC_PROOF_OBLIGATION_METADATA_KEY, TRUST_VC_PROOF_OBLIGATION_METADATA_VALUE),
        (TRUST_VC_OWNERSHIP_CONTEXT_METADATA_KEY, TRUST_VC_OWNERSHIP_CONTEXT_METADATA_VALUE),
        (
            TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_METADATA_KEY,
            TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_VERSION,
        ),
    ] {
        let actual = unique_obligation_metadata_value(obligation, key)?;
        if actual == Some(value) {
            continue;
        }
        return Err(TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
            origin: origin.to_string(),
            reason: format!(
                "structured trust_vc MIR memory proof-unit metadata requires exactly one {key}={value}; got {}",
                actual.unwrap_or("<missing>")
            ),
        });
    }
    Ok(())
}

#[cfg(feature = "trust-build")]
fn direct_proof_artifact_binding_fingerprint(
    artifact: &NativeTrustReplayableProofArtifact,
) -> String {
    #[derive(serde::Serialize)]
    struct Binding<'a> {
        schema_version: u32,
        artifact_id: &'a str,
        digest: &'a str,
        unit_id: &'a str,
        assumption_obligation_ids: &'a [String],
        assertion_obligation_ids: &'a [String],
    }

    let payload = serde_json::to_vec(&Binding {
        schema_version: TRUST_PROOF_ARTIFACT_BINDING_SCHEMA_VERSION,
        artifact_id: artifact.artifact_id(),
        digest: artifact.digest(),
        unit_id: artifact.unit_id(),
        assumption_obligation_ids: artifact.assumption_obligation_ids(),
        assertion_obligation_ids: artifact.assertion_obligation_ids(),
    })
    .expect("direct TrustVC proof-artifact binding fields are serializable");
    format!("sha256:{}", stable_sha256_hex(&payload))
}

#[cfg(feature = "trust-build")]
fn trust_vc_replayable_artifact_for_obligation<'a>(
    origin: &str,
    report: &'a TrustUnitReport,
    proof_unit: &TrustMirMemoryProofUnit,
    obligation: &TrustObligation,
) -> Result<&'a NativeTrustReplayableProofArtifact, TrustVcDirectMirMemoryError> {
    if !matches!(report.outcome(), NativeTrustOutcome::Verified) {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "direct MIR-memory certificate admission requires outcome Verified, got {:?}",
                report.outcome()
            ),
        });
    }
    if report.unit_id() != proof_unit.unit_id() {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "fresh TrustVC report is bound to unit `{}`, not direct proof unit `{}`",
                report.unit_id(),
                proof_unit.unit_id()
            ),
        });
    }
    // TrustVC's report-producing path is currently a fresh solve:
    // `verify_with_report` delegates to its uncached prepared-solve path. Keep
    // this explicit gate as defense in depth against future implementation or
    // serialized-report drift accidentally admitting cached authority here.
    if report.cache_status() != NativeTrustEvidenceCacheStatus::Miss {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "direct MIR-memory authority requires a fresh TrustVC solve (cache_status=Miss), got {:?}",
                report.cache_status()
            ),
        });
    }
    if report.proof_artifacts().len() != 1 {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "fresh TrustVC direct report must contain exactly one total replayable artifact, found {}",
                report.proof_artifacts().len()
            ),
        });
    }
    if report.proof_evidence().len() != 1 {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "fresh TrustVC direct report must contain exactly one total live evidence row, found {}",
                report.proof_evidence().len()
            ),
        });
    }
    let mut matching_artifacts = report.proof_artifacts().iter().filter(|artifact| {
        artifact.assertion_obligation_ids().iter().any(|id| id == &obligation.obligation_id)
    });
    let Some(artifact) = matching_artifacts.next() else {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: "trust-vc verified the MIR memory unit but did not return a replayable proof artifact covering the Trust obligation".to_string(),
        });
    };
    if let Some(second_artifact) = matching_artifacts.next() {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "trust-vc returned multiple replayable proof artifacts covering the Trust obligation: {} and {}",
                artifact.artifact_id(),
                second_artifact.artifact_id()
            ),
        });
    }
    if !artifact.assumption_obligation_ids().is_empty() {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "trust-vc replayable proof artifact {} carries assumption obligations {:?}; the narrow direct lane requires an assumption-free certificate",
                artifact.artifact_id(),
                artifact.assumption_obligation_ids()
            ),
        });
    }
    if artifact.assertion_obligation_ids() != [obligation.obligation_id.as_str()] {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "trust-vc replayable proof artifact {} must cover exactly the requested assertion, got {:?}",
                artifact.artifact_id(),
                artifact.assertion_obligation_ids()
            ),
        });
    }
    if artifact.format() != NativeTrustProofArtifactFormat::Alethe {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "trust-vc replayable proof artifact {} is not an Alethe certificate",
                artifact.artifact_id()
            ),
        });
    }
    if artifact.unit_id() != proof_unit.unit_id() {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "trust-vc replayable proof artifact {} is bound to unit `{}`, not direct MIR memory unit `{}`",
                artifact.artifact_id(),
                artifact.unit_id(),
                proof_unit.unit_id()
            ),
        });
    }
    if artifact.binding_fingerprint().is_empty() {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "trust-vc replayable proof artifact {} did not carry a binding fingerprint for the memory proof unit",
                artifact.artifact_id()
            ),
        });
    }
    let expected_binding_fingerprint = direct_proof_artifact_binding_fingerprint(artifact);
    if artifact.binding_fingerprint() != expected_binding_fingerprint {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "trust-vc replayable proof artifact {} has binding fingerprint {}, expected {}",
                artifact.artifact_id(),
                artifact.binding_fingerprint(),
                expected_binding_fingerprint
            ),
        });
    }
    let mut matching_evidence = report
        .proof_evidence()
        .iter()
        .filter(|evidence| evidence.obligation_id() == obligation.obligation_id);
    let Some(live_evidence) = matching_evidence.next() else {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: "fresh TrustVC report omitted live typed evidence for the direct obligation"
                .to_string(),
        });
    };
    if matching_evidence.next().is_some() {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: "fresh TrustVC report contained ambiguous live evidence rows for the direct obligation"
                .to_string(),
        });
    }
    let [unit_obligation] = proof_unit.obligations() else {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason:
                "direct MIR-memory unit no longer has exactly one obligation at evidence admission"
                    .to_string(),
        });
    };
    if live_evidence.typed_expr() != Some(unit_obligation.predicate()) {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: "fresh TrustVC evidence typed expression differs from the exact sole proof-unit predicate"
                .to_string(),
        });
    }
    if live_evidence.proof_artifact_id() != Some(artifact.artifact_id()) {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: "fresh TrustVC evidence does not name the selected replayable artifact"
                .to_string(),
        });
    }
    if live_evidence.proof_artifact_binding_fingerprint() != Some(artifact.binding_fingerprint()) {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason:
                "fresh TrustVC evidence does not carry the selected artifact binding fingerprint"
                    .to_string(),
        });
    }
    if artifact.hole_count() > 0 {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "trust-vc replayable proof artifact {} contains {} proof holes",
                artifact.artifact_id(),
                artifact.hole_count()
            ),
        });
    }
    // `clean_supported` reports whether this certificate can be exported
    // through Clean's narrower rule subset. It is not a TrustVC
    // release-admission input: the canonical admission object, strict checker,
    // independent kernel, hole gate above, and zero-trust gate below own that
    // decision. Treating the export-capability bit as another release veto made
    // valid arithmetic certificates fail despite `Admissible` authority.
    // (ay's clean proof whitelist restricts the clean-CIC re-check slice to
    // EUF-only BY DESIGN, so every arithmetic (Farkas/LIA) or BV bounds proof
    // reports `clean_supported=false` at any pinnable rev. This deliberately
    // reverses the one `clean_supported` conjunct of audit commit 72ada1163c —
    // a policy ALIGNMENT with the engine, not a silent relaxation; the flag
    // stays surfaced on the imported artifact as a metric so the clean slice's
    // expansion remains measurable.)
    if !artifact.strict_verified()
        || !artifact.kernel_verified()
        || artifact.trust_count() != 0
        || !artifact.release_admission().is_admissible()
    {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "trust-vc replayable proof artifact {} did not satisfy release-admissible replay gates (strict={}, kernel={}, clean_supported={} [diagnostic only], trust_count={}, admission={:?})",
                artifact.artifact_id(),
                artifact.strict_verified(),
                artifact.kernel_verified(),
                artifact.clean_supported(),
                artifact.trust_count(),
                artifact.release_admission().status(),
            ),
        });
    }
    let Some(id_digest) = artifact.artifact_id().strip_prefix(TRUST_VC_PROOF_ARTIFACT_ID_PREFIX)
    else {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "invalid trust-vc replayable proof artifact id {}",
                artifact.artifact_id()
            ),
        });
    };
    let Some(id_digest) = normalized_sha256_hex(id_digest) else {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "invalid trust-vc replayable proof artifact id {}",
                artifact.artifact_id()
            ),
        });
    };
    let Some(digest) = normalized_sha256_hex(artifact.digest()) else {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "invalid trust-vc replayable proof artifact digest {} for {}",
                artifact.digest(),
                artifact.artifact_id()
            ),
        });
    };
    let id_digest = id_digest.to_ascii_lowercase();
    let digest = digest.to_ascii_lowercase();
    if id_digest != digest {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "trust-vc replayable proof artifact id {} does not match digest {}",
                artifact.artifact_id(),
                artifact.digest()
            ),
        });
    }
    if artifact.payload().is_empty() {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: "trust-vc returned an empty replayable proof artifact".to_string(),
        });
    }
    let computed = stable_sha256_hex(artifact.payload().as_bytes());
    if computed != digest {
        return Err(TrustVcDirectMirMemoryError::TrustVcTrustEngineRejected {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "trust-vc replayable proof artifact {} payload digest mismatch: expected {}, computed {}",
                artifact.artifact_id(),
                digest,
                computed
            ),
        });
    }
    Ok(artifact)
}

#[cfg(feature = "trust-build")]
fn validate_direct_mir_memory_payload_for_obligation(
    origin: &str,
    payload: &JsonValue,
    obligation: &TrustObligation,
) -> Result<(), TrustVcDirectMirMemoryError> {
    let Some(object) = payload.as_object() else {
        return Err(TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
            origin: origin.to_string(),
            reason: "payload must be a JSON object shaped like TrustMirMemoryProofUnit".to_string(),
        });
    };

    let ownership = object
        .get("native_context")
        .and_then(JsonValue::as_object)
        .and_then(|native_context| native_context.get("ownership"));
    if !ownership.is_some_and(has_non_empty_mir_ownership_context) {
        return Err(TrustVcDirectMirMemoryError::MissingOwnershipContext {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
        });
    }

    let Some(obligations) = object.get("obligations").and_then(JsonValue::as_array) else {
        return Err(TrustVcDirectMirMemoryError::InvalidProofUnitPayload {
            origin: origin.to_string(),
            reason: "payload must contain an `obligations` array".to_string(),
        });
    };
    if !obligations.iter().any(|native_obligation| {
        native_obligation
            .get("id")
            .and_then(JsonValue::as_str)
            .is_some_and(|id| id == obligation.obligation_id)
    }) {
        return Err(TrustVcDirectMirMemoryError::MissingObligation {
            origin: origin.to_string(),
            obligation_id: obligation.obligation_id.clone(),
        });
    }
    Ok(())
}

#[cfg(feature = "trust-build")]
fn has_non_empty_mir_ownership_context(ownership: &JsonValue) -> bool {
    let Some(ownership) = ownership.as_object() else {
        return false;
    };
    ["places", "borrows", "lifetimes", "alias_facts", "provenance_facts"].iter().any(|field| {
        ownership.get(*field).and_then(JsonValue::as_array).is_some_and(|items| !items.is_empty())
    })
}

#[cfg(feature = "trust-build")]
fn unsupported_mir_memory_payload_detail(value: &JsonValue) -> Option<String> {
    fn visit(value: &JsonValue, path: &str) -> Option<String> {
        match value {
            JsonValue::Object(map) => {
                for (key, nested) in map {
                    let normalized = key
                        .chars()
                        .filter(|ch| ch.is_ascii_alphanumeric())
                        .collect::<String>()
                        .to_ascii_lowercase();
                    if normalized.contains("heap")
                        || normalized.contains("rawptr")
                        || normalized.contains("pointer")
                        || normalized.contains("provenance")
                        || normalized.contains("alloc")
                        || normalized.contains("deref")
                    {
                        return Some(format!("{path}.{key}"));
                    }
                    let nested_path = format!("{path}.{key}");
                    if let Some(detail) = visit(nested, &nested_path) {
                        return Some(detail);
                    }
                }
                None
            }
            JsonValue::Array(items) => {
                for (index, nested) in items.iter().enumerate() {
                    let nested_path = format!("{path}[{index}]");
                    if let Some(detail) = visit(nested, &nested_path) {
                        return Some(detail);
                    }
                }
                None
            }
            JsonValue::Null | JsonValue::Bool(_) | JsonValue::Number(_) | JsonValue::String(_) => {
                None
            }
        }
    }

    visit(value, "$")
}

#[cfg(feature = "trust-build")]
fn trust_vc_trust_engine_proof_policy(
    _policy: TrustVcNativeProofCertificatePolicy,
) -> TrustProofPolicy {
    // The bridge's historical policy names predate TrustVC's release gate.
    // Neither a replayable payload nor strict-checker acceptance is sufficient
    // for proof authority. Local engine runs must require the complete TrustVC
    // release admission (strict + kernel, no holes/trust residue, bound unit).
    TrustProofPolicy::RequireReleaseAdmissibleCertificate
}

#[cfg(feature = "trust-build")]
fn trust_vc_native_unit_report_from_trust_engine_report(
    report: &TrustUnitReport,
) -> Result<TrustVcNativeUnitReport, String> {
    if !matches!(report.outcome(), NativeTrustOutcome::Verified) {
        return Err(format!(
            "direct MIR memory verification returned non-proof outcome {:?}",
            report.outcome()
        ));
    }

    let mut native_report = TrustVcNativeUnitReport::new(report.unit_id());
    for evidence in report.proof_evidence() {
        native_report = native_report
            .with_proof_evidence(trust_vc_native_evidence_from_trust_engine(evidence)?);
    }
    let proof_artifacts = report
        .proof_artifacts()
        .iter()
        .map(trust_vc_native_artifact_from_trust_engine)
        .collect::<Result<Vec<_>, _>>()?;
    native_report = native_report.with_proof_artifacts(proof_artifacts);
    Ok(native_report)
}

#[cfg(feature = "trust-build")]
fn trust_vc_native_evidence_from_trust_engine(
    evidence: &NativeTrustProofEvidence,
) -> Result<TrustVcNativeTrustProofEvidence, String> {
    let typed_expr =
        evidence.typed_expr().map(serde_json::to_value).transpose().map_err(|error| {
            format!("could not serialize native typed TrustExpr evidence: {error}")
        })?;
    Ok(TrustVcNativeTrustProofEvidence {
        obligation_id: evidence.obligation_id().to_string(),
        source: trust_vc_native_evidence_source_from_trust_engine(evidence.source()),
        typed_expr,
        evidence_profile: trust_vc_native_evidence_profile_from_trust_engine(
            evidence.evidence_profile(),
        ),
        reasoning_kind: trust_vc_native_reasoning_kind_from_trust_engine(evidence.reasoning_kind()),
        assurance_level: trust_vc_native_assurance_level_from_trust_engine(
            evidence.assurance_level(),
        ),
        proof_artifact_id: evidence.proof_artifact_id().map(str::to_string),
        native_trust_ir_import: None,
    })
}

#[cfg(feature = "trust-build")]
fn trust_vc_native_artifact_from_trust_engine(
    artifact: &NativeTrustReplayableProofArtifact,
) -> Result<TrustVcNativeReplayableProofArtifact, String> {
    let format = match artifact.format() {
        NativeTrustProofArtifactFormat::Alethe => TrustVcNativeProofArtifactFormat::Alethe,
        _ => return Err("unsupported trust-vc-trust-engine proof artifact format".to_string()),
    };
    Ok(TrustVcNativeReplayableProofArtifact {
        artifact_id: artifact.artifact_id().to_string(),
        format,
        digest: artifact.digest().to_string(),
        payload: artifact.payload().to_string(),
        strict_verified: artifact.strict_verified(),
        clean_supported: artifact.clean_supported(),
        kernel_verified: artifact.kernel_verified(),
        trust_count: artifact.trust_count(),
        hole_count: artifact.hole_count(),
        resolution_count: artifact.resolution_count(),
        theory_count: artifact.theory_count(),
        assumption_obligation_ids: artifact.assumption_obligation_ids().to_vec(),
        assertion_obligation_ids: artifact.assertion_obligation_ids().to_vec(),
    })
}

#[cfg(feature = "trust-build")]
fn trust_vc_native_evidence_source_from_trust_engine(
    source: NativeTrustProofEvidenceSource,
) -> TrustVcNativeProofEvidenceSource {
    match source {
        NativeTrustProofEvidenceSource::TypedTrustVcExpr => {
            TrustVcNativeProofEvidenceSource::TypedTrustVcExpr
        }
        NativeTrustProofEvidenceSource::LegacySourceText => {
            TrustVcNativeProofEvidenceSource::LegacySourceText
        }
        _ => TrustVcNativeProofEvidenceSource::LegacySourceText,
    }
}

#[cfg(feature = "trust-build")]
fn trust_vc_native_evidence_profile_from_trust_engine(
    profile: NativeTrustProofEvidenceProfile,
) -> TrustVcNativeProofEvidenceProfile {
    match profile {
        NativeTrustProofEvidenceProfile::TypedContractFrame => {
            TrustVcNativeProofEvidenceProfile::TypedContractFrame
        }
        NativeTrustProofEvidenceProfile::OwnershipMemory => {
            TrustVcNativeProofEvidenceProfile::OwnershipMemory
        }
        NativeTrustProofEvidenceProfile::TypedInvariant => {
            TrustVcNativeProofEvidenceProfile::TypedInvariant
        }
        NativeTrustProofEvidenceProfile::TypedTranslationValidation => {
            TrustVcNativeProofEvidenceProfile::TypedTranslationValidation
        }
        NativeTrustProofEvidenceProfile::TypedCastBootstrap => {
            TrustVcNativeProofEvidenceProfile::TypedCastBootstrap
        }
        NativeTrustProofEvidenceProfile::TypedAdtBootstrap => {
            TrustVcNativeProofEvidenceProfile::TypedAdtBootstrap
        }
        NativeTrustProofEvidenceProfile::TypedPointerBootstrap => {
            TrustVcNativeProofEvidenceProfile::TypedPointerBootstrap
        }
        NativeTrustProofEvidenceProfile::TypedFatPointerBootstrap => {
            TrustVcNativeProofEvidenceProfile::TypedFatPointerBootstrap
        }
        NativeTrustProofEvidenceProfile::TypedDeductiveObligation => {
            TrustVcNativeProofEvidenceProfile::TypedDeductiveObligation
        }
        NativeTrustProofEvidenceProfile::TypedCompatibility => {
            TrustVcNativeProofEvidenceProfile::TypedCompatibility
        }
        NativeTrustProofEvidenceProfile::LegacyCompatibility => {
            TrustVcNativeProofEvidenceProfile::LegacyCompatibility
        }
        NativeTrustProofEvidenceProfile::Unspecified => {
            TrustVcNativeProofEvidenceProfile::Unspecified
        }
        _ => TrustVcNativeProofEvidenceProfile::Unspecified,
    }
}

#[cfg(feature = "trust-build")]
fn trust_vc_native_reasoning_kind_from_trust_engine(
    reasoning_kind: NativeTrustProofReasoningKind,
) -> TrustVcNativeProofReasoningKind {
    match reasoning_kind {
        NativeTrustProofReasoningKind::Deductive => TrustVcNativeProofReasoningKind::Deductive,
        NativeTrustProofReasoningKind::Ownership => TrustVcNativeProofReasoningKind::Ownership,
        NativeTrustProofReasoningKind::Constructive => {
            TrustVcNativeProofReasoningKind::Constructive
        }
        NativeTrustProofReasoningKind::Unspecified => TrustVcNativeProofReasoningKind::Unspecified,
        _ => TrustVcNativeProofReasoningKind::Unspecified,
    }
}

#[cfg(feature = "trust-build")]
fn trust_vc_native_assurance_level_from_trust_engine(
    assurance_level: NativeTrustAssuranceLevel,
) -> TrustVcNativeAssuranceLevel {
    match assurance_level {
        NativeTrustAssuranceLevel::CompatibilityEvidence => {
            TrustVcNativeAssuranceLevel::CompatibilityEvidence
        }
        NativeTrustAssuranceLevel::AssumedEvidence => TrustVcNativeAssuranceLevel::AssumedEvidence,
        NativeTrustAssuranceLevel::StaticProof => TrustVcNativeAssuranceLevel::StaticProof,
        NativeTrustAssuranceLevel::MetadataOnly => TrustVcNativeAssuranceLevel::MetadataOnly,
        NativeTrustAssuranceLevel::Unspecified => TrustVcNativeAssuranceLevel::Unspecified,
        _ => TrustVcNativeAssuranceLevel::Unspecified,
    }
}

/// trust_vc native certificate policy to enforce during conversion.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TrustVcNativeProofCertificatePolicy {
    ReplayableCertificate,
    StrictReplayableCertificate,
}

/// Verify a trust_vc typed full-verification request and convert its accepted
/// typed evidence summaries into the bridge report consumed by this adapter.
///
/// The request must carry first-class `TypedProofObligation` or
/// `TypedMemorySafetyFact` values. Raw `ProofObligation` compatibility
/// evidence remains rejected here because it can be string-backed and does not
/// preserve the native typed boundary required by Trust's trust_vc adapter.
#[cfg(feature = "trust-build")]
pub fn trust_vc_native_unit_report_from_full_verification_request(
    unit_id: impl Into<String>,
    request: FullVerificationRequest,
    proof_artifact: TrustVcNativeReplayableProofArtifact,
) -> Result<TrustVcNativeUnitReport, TrustVcNativeReportConversionError> {
    let unit_id = unit_id.into();
    let requested_evidence = request.evidence().to_vec();
    let result = request.verify().map_err(|error| {
        TrustVcNativeReportConversionError::FullVerificationFailed {
            unit_id: unit_id.clone(),
            reason: error.to_string(),
        }
    })?;
    let proof_artifact_id = proof_artifact.artifact_id.clone();
    let mut report =
        TrustVcNativeUnitReport::new(unit_id.clone()).with_proof_artifact(proof_artifact);

    for evidence in requested_evidence {
        match evidence {
            FullVerificationEvidence::TypedObligation(obligation) => {
                let verified = result
                    .verified_evidence()
                    .iter()
                    .find(|verified| verified.name() == obligation.name())
                    .ok_or_else(|| {
                        TrustVcNativeReportConversionError::MissingFullVerificationEvidence {
                            unit_id: unit_id.clone(),
                            evidence_name: obligation.name().to_string(),
                        }
                    })?;
                report = report.with_proof_evidence(
                    TrustVcNativeTrustProofEvidence::from_verified_typed_obligation(
                        verified,
                        &obligation,
                        proof_artifact_id.clone(),
                    ),
                );
            }
            FullVerificationEvidence::MemorySafetyFact(fact) => {
                report =
                    report.with_proof_evidence(trust_vc_native_evidence_from_verified_memory_fact(
                        &unit_id,
                        &fact,
                        result.verified_memory_safety_facts(),
                        proof_artifact_id.clone(),
                    )?);
            }
            FullVerificationEvidence::RawObligation(obligation) => {
                return Err(TrustVcNativeReportConversionError::UnsupportedFullVerificationEvidence {
                    unit_id,
                    evidence_name: obligation.name().to_string(),
                    reason: "adapter requires TypedProofObligation or TypedMemorySafetyFact evidence, not RawObligation compatibility evidence".to_string(),
                });
            }
            _ => {
                return Err(TrustVcNativeReportConversionError::UnsupportedFullVerificationEvidence {
                    unit_id,
                    evidence_name: "unknown".to_string(),
                    reason: "adapter does not accept this non-exhaustive trust_vc full-verification evidence variant".to_string(),
                });
            }
        }
    }

    Ok(report)
}

/// Validate a legacy native-report DTO without granting proof authority.
///
/// The DTO exposes caller-settable `strict_verified` / `kernel_verified`
/// booleans and loses TrustVC's opaque release admission, unit binding, and
/// replay receipt. Consequently this compatibility converter always rejects a
/// report at the final certificate gate. Authority is available only through
/// the validated native TrustIR import, or through the dedicated in-process
/// MIR-memory converter while it still holds TrustVC's live release-admission
/// object and exact admitted bytes. The latter is not a general contract or
/// refinement-proof bridge.
pub fn trust_vc_obligation_evidence_from_native_unit_report(
    engine: &TrustVcVerificationEngine,
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    report: &TrustVcNativeUnitReport,
    supplemental_artifacts: TrustVcNativeReportArtifacts,
    policy: TrustVcNativeProofCertificatePolicy,
) -> Result<ObligationEvidence, TrustVcNativeReportConversionError> {
    let native_evidence = trust_vc_native_evidence_for_obligation(report, obligation)?;
    let artifact =
        trust_vc_native_artifact_for_evidence(report, native_evidence).ok_or_else(|| {
            TrustVcNativeReportConversionError::MissingUnitProofArtifact {
                obligation_id: obligation.obligation_id.clone(),
                unit_id: report.unit_id.clone(),
            }
        })?;

    trust_vc_obligation_evidence_from_native_report(
        engine,
        bundle,
        obligation,
        native_evidence,
        artifact,
        supplemental_artifacts,
        policy,
    )
}

fn trust_vc_native_evidence_for_obligation<'a>(
    report: &'a TrustVcNativeUnitReport,
    obligation: &TrustObligation,
) -> Result<&'a TrustVcNativeTrustProofEvidence, TrustVcNativeReportConversionError> {
    let mut matching_evidence = report
        .proof_evidence
        .iter()
        .filter(|evidence| evidence.obligation_id == obligation.obligation_id);
    let Some(evidence) = matching_evidence.next() else {
        return Err(TrustVcNativeReportConversionError::MissingNativeProofEvidence {
            obligation_id: obligation.obligation_id.clone(),
            unit_id: report.unit_id.clone(),
        });
    };
    if matching_evidence.next().is_some() {
        return Err(TrustVcNativeReportConversionError::AmbiguousNativeProofEvidence {
            obligation_id: obligation.obligation_id.clone(),
            unit_id: report.unit_id.clone(),
        });
    }
    Ok(evidence)
}

fn trust_vc_native_artifact_for_evidence<'a>(
    report: &'a TrustVcNativeUnitReport,
    native_evidence: &TrustVcNativeTrustProofEvidence,
) -> Option<&'a TrustVcNativeReplayableProofArtifact> {
    if let Some(proof_artifact_id) = native_evidence.proof_artifact_id.as_deref() {
        if let Some(artifact) =
            report.proof_artifacts.iter().find(|artifact| artifact.artifact_id == proof_artifact_id)
        {
            return Some(artifact);
        }
        return report
            .proof_artifact
            .as_ref()
            .filter(|artifact| artifact.artifact_id == proof_artifact_id);
    }

    if let Some(artifact) = report.proof_artifact.as_ref() {
        return Some(artifact);
    }
    match report.proof_artifacts.as_slice() {
        [artifact] => Some(artifact),
        _ => None,
    }
}

/// Convert one trust_vc native proof evidence item plus its unit artifact into
/// public verifier evidence.
pub fn trust_vc_obligation_evidence_from_native_report(
    engine: &TrustVcVerificationEngine,
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    native_evidence: &TrustVcNativeTrustProofEvidence,
    native_artifact: &TrustVcNativeReplayableProofArtifact,
    supplemental_artifacts: TrustVcNativeReportArtifacts,
    policy: TrustVcNativeProofCertificatePolicy,
) -> Result<ObligationEvidence, TrustVcNativeReportConversionError> {
    if native_evidence.obligation_id != obligation.obligation_id {
        return Err(TrustVcNativeReportConversionError::ObligationIdMismatch {
            expected: obligation.obligation_id.clone(),
            actual: native_evidence.obligation_id.clone(),
        });
    }
    if native_evidence.source != TrustVcNativeProofEvidenceSource::TypedTrustVcExpr {
        return Err(TrustVcNativeReportConversionError::UnsupportedEvidenceSource {
            obligation_id: obligation.obligation_id.clone(),
            source: native_evidence.source,
        });
    }
    let expected_supplemental_artifacts =
        trust_vc_native_report_artifacts_from_bundle(bundle, obligation).map_err(|error| {
            TrustVcNativeReportConversionError::RejectedByTrustVcEvidenceShape {
                diagnostics: vec![error.to_string()],
            }
        })?;
    validate_supplemental_artifact_binding(
        "normalized_obligation",
        &supplemental_artifacts.normalized_obligation,
        &expected_supplemental_artifacts.normalized_obligation,
    )?;
    validate_supplemental_artifact_binding(
        "engine_input",
        &supplemental_artifacts.engine_input,
        &expected_supplemental_artifacts.engine_input,
    )?;
    let typed_expr_digest = validate_native_typed_trust_expr(native_evidence)?;
    if let Some(native_trust_ir_import) = &native_evidence.native_trust_ir_import {
        validate_trust_vc_native_trust_ir_import_matches_obligation(
            obligation,
            native_trust_ir_import,
        )?;
    }
    let proof_strength =
        trust_vc_native_static_proof_strength(obligation, native_evidence, native_artifact)?;

    let evidence_id = format!("trust-vc:{}:{}", bundle.bundle_id, obligation.obligation_id);
    let native_identity = trust_vc_native_tmir_obligation_identity(obligation)?;
    let proof_binding_id = format!(
        "trust_ir-native-trust-vc-request-{}-proof-{}",
        native_identity.request_id, native_identity.proof_obligation_id
    );
    let certificate_artifact = trust_vc_proof_certificate_artifact_from_native(
        native_evidence,
        native_artifact,
        policy,
        &proof_binding_id,
        &obligation.obligation_id,
    )?;
    let mut artifacts = vec![
        supplemental_artifacts.normalized_obligation,
        supplemental_artifacts.engine_input,
        certificate_artifact,
    ];
    artifacts.sort_by(|left, right| {
        (left.kind, left.uri.as_str(), left.hash.value.as_str()).cmp(&(
            right.kind,
            right.uri.as_str(),
            right.hash.value.as_str(),
        ))
    });

    let mut diagnostics = vec![
        "native trust_vc replayable proof certificate accepted".to_string(),
        format!(
            "trust-vc certificate stats: strict={}, kernel={}, holes={}, trust_steps={}",
            native_artifact.strict_verified,
            native_artifact.kernel_verified,
            native_artifact.hole_count,
            native_artifact.trust_count
        ),
        format!(
            "trust-vc evidence profile: {:?}, reasoning={:?}, assurance={:?}",
            native_evidence.evidence_profile,
            native_evidence.reasoning_kind,
            native_evidence.assurance_level
        ),
        format!("trust-vc typed TrustExpr evidence preserved: sha256:{typed_expr_digest}"),
    ];
    if let Some(native_trust_ir_import) = &native_evidence.native_trust_ir_import {
        diagnostics.push(format!(
            "trust-vc native Tmir import identity preserved: request={}, assertion={}, trust_ir_obligation={}, replay_engine={}, replay_transcript_digest={}, evidence_digest={}, certificate_digest={}, compiler_facts_digest={}, obligation_source_digest={}, fact_refs={}, fingerprint={}",
            native_trust_ir_import.request_id,
            native_trust_ir_import.assertion_id,
            native_trust_ir_import.trust_ir_obligation_id,
            native_trust_ir_import.replay_engine,
            native_trust_ir_import.replay_transcript_digest,
            native_trust_ir_import.evidence_digest,
            native_trust_ir_import.certificate_digest,
            native_trust_ir_import.compiler_facts_digest,
            native_trust_ir_import.obligation_source_digest,
            native_trust_ir_import.compiler_fact_refs.len(),
            native_trust_ir_import.artifact_fingerprint
        ));
    }

    let evidence = ObligationEvidence {
        evidence_id,
        obligation_id: obligation.obligation_id.clone(),
        engine: engine.manifest().clone(),
        status: EvidenceStatus::Proved,
        proof_strength: Some(proof_strength),
        artifacts,
        counterexample: None,
        publication: EvidencePublicationMetadata {
            publication_plan_hash: bundle.publication.dpub_plan_hash.clone(),
            trust_engines_lock_hash: bundle.publication.trust_engines_lock_hash.clone(),
            ..EvidencePublicationMetadata::default()
        },
        diagnostics,
    };

    let diagnostics = trust_vc_proof_evidence_shape_diagnostics(obligation, &evidence);
    if diagnostics.is_empty() {
        Ok(evidence)
    } else {
        Err(TrustVcNativeReportConversionError::RejectedByTrustVcEvidenceShape { diagnostics })
    }
}

/// Convert trust_vc proof-artifact data into the verifier-api proof certificate
/// artifact shape required by #1104.
pub fn trust_vc_proof_certificate_artifact_from_native(
    native_evidence: &TrustVcNativeTrustProofEvidence,
    native_artifact: &TrustVcNativeReplayableProofArtifact,
    policy: TrustVcNativeProofCertificatePolicy,
    proof_binding_id: &str,
    obligation_id: &str,
) -> Result<EvidenceArtifact, TrustVcNativeReportConversionError> {
    let Some(evidence_artifact_id) = native_evidence.proof_artifact_id.as_deref() else {
        return Err(TrustVcNativeReportConversionError::MissingProofArtifactId {
            obligation_id: native_evidence.obligation_id.clone(),
        });
    };
    if evidence_artifact_id != native_artifact.artifact_id {
        return Err(TrustVcNativeReportConversionError::ProofArtifactIdMismatch {
            obligation_id: native_evidence.obligation_id.clone(),
            evidence_artifact_id: evidence_artifact_id.to_string(),
            artifact_id: native_artifact.artifact_id.clone(),
        });
    }
    validate_native_proof_artifact_asserts_obligation(native_evidence, native_artifact)?;
    validate_native_replayable_artifact(native_artifact, policy)?;

    let (materialization, hash) = EvidenceArtifactMaterialization::new_bound(
        EvidenceArtifactKind::ProofCertificate,
        native_artifact.payload.as_bytes(),
        proof_binding_id,
        obligation_id,
        Vec::new(),
    )
    .ok_or_else(|| {
        TrustVcNativeReportConversionError::ProofArtifactMaterializationUnavailable {
            artifact_id: native_artifact.artifact_id.clone(),
            byte_len: native_artifact.payload.len(),
        }
    })?;
    Ok(EvidenceArtifact {
        kind: EvidenceArtifactKind::ProofCertificate,
        uri: format!(
            "{TRUST_VC_PROOF_CERTIFICATE_URI_PREFIX}{TRUST_VC_PROOF_ARTIFACT_ID_PREFIX}{}.alethe",
            hash.value
        ),
        hash,
        materialization: Some(materialization),
    })
}

/// Convert a trust-vc-admitted native Tmir proof artifact into verifier-api
/// `ProofCertificate` evidence.
#[cfg(feature = "trust-build")]
pub fn trust_vc_native_trust_ir_proof_certificate_artifact_from_import(
    imported: &TrustVcNativeTrustIrImportedProofArtifact,
    proof_binding_id: &str,
    obligation_id: &str,
) -> Result<EvidenceArtifact, TrustVcNativeReportConversionError> {
    validate_trust_vc_native_trust_ir_import_binding(imported)?;
    let bytes = imported.certificate_materialization.as_ref().ok_or_else(|| {
        TrustVcNativeReportConversionError::NativeTmirImportCertificateMaterializationMissing {
            trust_ir_obligation_id: imported.trust_ir_obligation_id,
            reason: "report-only import does not retain exact TrustIr certificate bytes"
                .to_string(),
        }
    })?;
    let (materialization, hash) = EvidenceArtifactMaterialization::new_bound(
        EvidenceArtifactKind::ProofCertificate,
        bytes,
        proof_binding_id,
        obligation_id,
        Vec::new(),
    )
    .ok_or_else(|| {
        TrustVcNativeReportConversionError::NativeTmirImportCertificateMaterializationMissing {
            trust_ir_obligation_id: imported.trust_ir_obligation_id,
            reason: format!(
                "canonical TrustIr certificate payload has invalid byte length {}",
                bytes.len()
            ),
        }
    })?;
    Ok(EvidenceArtifact {
        kind: EvidenceArtifactKind::ProofCertificate,
        uri: format!("{TRUST_VC_NATIVE_TRUST_IR_PROOF_CERTIFICATE_URI_PREFIX}{}.json", hash.value),
        hash,
        materialization: Some(materialization),
    })
}

/// Failure returned while converting trust_vc native report data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TrustVcNativeReportConversionError {
    MissingNativeProofEvidence {
        unit_id: String,
        obligation_id: String,
    },
    AmbiguousNativeProofEvidence {
        unit_id: String,
        obligation_id: String,
    },
    AmbiguousNativeUnitReports {
        obligation_id: String,
        first_unit_id: String,
        second_unit_id: String,
    },
    MissingUnitProofArtifact {
        unit_id: String,
        obligation_id: String,
    },
    ObligationIdMismatch {
        expected: String,
        actual: String,
    },
    UnsupportedEvidenceSource {
        obligation_id: String,
        source: TrustVcNativeProofEvidenceSource,
    },
    UnsupportedEvidenceProfile {
        obligation_id: String,
        profile: TrustVcNativeProofEvidenceProfile,
    },
    EvidenceProfileMismatch {
        obligation_id: String,
        obligation_kind: ObligationKind,
        profile: TrustVcNativeProofEvidenceProfile,
    },
    UnsupportedReasoningKind {
        obligation_id: String,
        reasoning_kind: TrustVcNativeProofReasoningKind,
    },
    UnsupportedAssuranceLevel {
        obligation_id: String,
        assurance_level: TrustVcNativeAssuranceLevel,
    },
    MissingTypedTrustExprEvidence {
        obligation_id: String,
    },
    InvalidTypedTrustExprEvidence {
        obligation_id: String,
        reason: String,
    },
    MissingProofArtifactId {
        obligation_id: String,
    },
    ProofArtifactIdMismatch {
        obligation_id: String,
        evidence_artifact_id: String,
        artifact_id: String,
    },
    ProofArtifactMissingAssertionObligation {
        artifact_id: String,
        obligation_id: String,
    },
    ProofArtifactAssumesRequestedObligation {
        artifact_id: String,
        obligation_id: String,
    },
    InvalidProofArtifactId {
        artifact_id: String,
    },
    InvalidProofArtifactDigest {
        artifact_id: String,
        digest: String,
    },
    ProofArtifactDigestMismatch {
        artifact_id: String,
        digest: String,
    },
    EmptyProofArtifactPayload {
        artifact_id: String,
    },
    ProofArtifactMaterializationUnavailable {
        artifact_id: String,
        byte_len: usize,
    },
    ProofArtifactPayloadDigestMismatch {
        artifact_id: String,
        expected: String,
        actual: String,
    },
    ProofArtifactContainsHoles {
        artifact_id: String,
        hole_count: u32,
    },
    UncheckedProofCertificate {
        artifact_id: String,
    },
    StrictProofCertificateRequired {
        artifact_id: String,
    },
    NativeTmirImportMissingArtifacts {
        module: String,
    },
    NativeTmirImportCertificateMaterializationMissing {
        trust_ir_obligation_id: u32,
        reason: String,
    },
    NativeTmirBundleRejected {
        reason: String,
    },
    CanonicalVerifierRequestRejected {
        reason: String,
    },
    DuplicateNativeTmirImportBinding {
        collection: &'static str,
        key: String,
    },
    UnsupportedPublicNativeObligationKind {
        obligation_id: String,
        kind: ObligationKind,
    },
    InvalidPublicObligationSemanticBinding {
        obligation_id: String,
        reason: String,
    },
    NativeTmirImportRejected {
        trust_ir_obligation_id: u32,
        replay_status: String,
        status: String,
        reasons: Vec<String>,
    },
    NativeTmirImportInvalidIdentity {
        trust_ir_obligation_id: u32,
        field: &'static str,
    },
    NativeTmirImportMissingObligation {
        obligation_id: String,
        request_id: u32,
        trust_ir_obligation_id: u32,
    },
    NativeTmirImportBindingMismatch {
        obligation_id: String,
        field: &'static str,
        expected: String,
        actual: String,
    },
    NativeTmirObligationIdentityMissing {
        obligation_id: String,
        metadata_key: &'static str,
    },
    NativeTmirObligationIdentityInvalid {
        obligation_id: String,
        metadata_key: &'static str,
        value: String,
    },
    NativeTmirObligationSuiteMismatch {
        obligation_id: String,
        suite: String,
    },
    InvalidSupplementalArtifactKind {
        label: &'static str,
        expected: EvidenceArtifactKind,
        actual: EvidenceArtifactKind,
    },
    InvalidSupplementalArtifactHash {
        label: &'static str,
        algorithm: String,
        value: String,
    },
    InvalidSupplementalArtifactUri {
        label: &'static str,
        uri: String,
    },
    SupplementalArtifactBindingMismatch {
        label: &'static str,
        expected_uri: String,
        actual_uri: String,
        expected_hash: String,
        actual_hash: String,
    },
    FullVerificationFailed {
        unit_id: String,
        reason: String,
    },
    MissingFullVerificationEvidence {
        unit_id: String,
        evidence_name: String,
    },
    UnsupportedFullVerificationEvidence {
        unit_id: String,
        evidence_name: String,
        reason: String,
    },
    RejectedByTrustVcEvidenceShape {
        diagnostics: Vec<String>,
    },
}

impl std::fmt::Display for TrustVcNativeReportConversionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingNativeProofEvidence { unit_id, obligation_id } => write!(
                f,
                "trust-vc unit report {unit_id} did not include proof evidence for {obligation_id}"
            ),
            Self::AmbiguousNativeProofEvidence { unit_id, obligation_id } => write!(
                f,
                "trust-vc unit report {unit_id} included multiple proof evidence entries for {obligation_id}"
            ),
            Self::AmbiguousNativeUnitReports { obligation_id, first_unit_id, second_unit_id } => {
                write!(
                    f,
                    "multiple native trust_vc unit reports included proof evidence for {obligation_id}: {first_unit_id} and {second_unit_id}"
                )
            }
            Self::MissingUnitProofArtifact { unit_id, obligation_id } => write!(
                f,
                "trust-vc unit report {unit_id} did not include a replayable proof artifact for {obligation_id}"
            ),
            Self::ObligationIdMismatch { expected, actual } => {
                write!(f, "trust-vc proof evidence obligation {actual} does not match {expected}")
            }
            Self::UnsupportedEvidenceSource { obligation_id, source } => write!(
                f,
                "trust-vc proof evidence for {obligation_id} came from unsupported source {source:?}"
            ),
            Self::UnsupportedEvidenceProfile { obligation_id, profile } => write!(
                f,
                "trust-vc proof evidence for {obligation_id} used unsupported profile {profile:?}; compatibility evidence is not typed static proof"
            ),
            Self::EvidenceProfileMismatch { obligation_id, obligation_kind, profile } => write!(
                f,
                "trust-vc proof evidence for {obligation_id} used profile {profile:?}, which does not prove {obligation_kind:?}"
            ),
            Self::UnsupportedReasoningKind { obligation_id, reasoning_kind } => write!(
                f,
                "trust-vc proof evidence for {obligation_id} used unsupported reasoning kind {reasoning_kind:?}"
            ),
            Self::UnsupportedAssuranceLevel { obligation_id, assurance_level } => write!(
                f,
                "trust-vc proof evidence for {obligation_id} used assurance {assurance_level:?}; only static_proof evidence counts as typed static proof"
            ),
            Self::MissingTypedTrustExprEvidence { obligation_id } => write!(
                f,
                "trust-vc proof evidence for {obligation_id} did not preserve typed TrustExpr evidence"
            ),
            Self::InvalidTypedTrustExprEvidence { obligation_id, reason } => write!(
                f,
                "trust-vc proof evidence for {obligation_id} carried invalid typed TrustExpr evidence: {reason}"
            ),
            Self::MissingProofArtifactId { obligation_id } => write!(
                f,
                "trust-vc proof evidence for {obligation_id} did not link a proof artifact id"
            ),
            Self::ProofArtifactIdMismatch { obligation_id, evidence_artifact_id, artifact_id } => {
                write!(
                    f,
                    "trust-vc proof evidence for {obligation_id} links {evidence_artifact_id}, not unit artifact {artifact_id}"
                )
            }
            Self::ProofArtifactMissingAssertionObligation { artifact_id, obligation_id } => write!(
                f,
                "trust-vc proof artifact {artifact_id} does not list {obligation_id} as a discharged assertion"
            ),
            Self::ProofArtifactAssumesRequestedObligation { artifact_id, obligation_id } => write!(
                f,
                "trust-vc proof artifact {artifact_id} lists {obligation_id} as an assumption, not a discharged assertion"
            ),
            Self::InvalidProofArtifactId { artifact_id } => {
                write!(f, "invalid trust_vc proof artifact id {artifact_id}")
            }
            Self::InvalidProofArtifactDigest { artifact_id, digest } => {
                write!(f, "invalid trust_vc proof artifact digest {digest} for {artifact_id}")
            }
            Self::ProofArtifactDigestMismatch { artifact_id, digest } => {
                write!(f, "trust-vc proof artifact id {artifact_id} does not match digest {digest}")
            }
            Self::EmptyProofArtifactPayload { artifact_id } => {
                write!(f, "trust-vc proof artifact {artifact_id} has an empty payload")
            }
            Self::ProofArtifactMaterializationUnavailable { artifact_id, byte_len } => write!(
                f,
                "trust-vc proof artifact {artifact_id} cannot carry its exact {byte_len}-byte payload within the bounded proof transport"
            ),
            Self::ProofArtifactPayloadDigestMismatch { artifact_id, expected, actual } => write!(
                f,
                "trust-vc proof artifact {artifact_id} payload digest mismatch: expected {expected}, computed {actual}"
            ),
            Self::ProofArtifactContainsHoles { artifact_id, hole_count } => {
                write!(f, "trust-vc proof artifact {artifact_id} contains {hole_count} proof holes")
            }
            Self::UncheckedProofCertificate { artifact_id } => {
                write!(f, "{TRUST_VC_PROOF_CERTIFICATE_CHECK_REQUIRED}: {artifact_id}")
            }
            Self::StrictProofCertificateRequired { artifact_id } => write!(
                f,
                "trust-vc proof artifact {artifact_id} was not accepted by the strict checker"
            ),
            Self::NativeTmirImportMissingArtifacts { module } => write!(
                f,
                "trust-vc native Tmir report for module {module} did not contain admitted proof artifacts"
            ),
            Self::NativeTmirImportCertificateMaterializationMissing {
                trust_ir_obligation_id,
                reason,
            } => write!(
                f,
                "trust-vc native Tmir import for obligation {trust_ir_obligation_id} has no exact certificate materialization: {reason}"
            ),
            Self::NativeTmirBundleRejected { reason } => {
                write!(f, "trust-vc rejected native Tmir bundle input: {reason}")
            }
            Self::CanonicalVerifierRequestRejected { reason } => write!(
                f,
                "trust-vc rejected non-canonical public verifier bundle/request input: {reason}"
            ),
            Self::DuplicateNativeTmirImportBinding { collection, key } => {
                write!(f, "trust-vc rejected ambiguous native Tmir {collection} binding for {key}")
            }
            Self::UnsupportedPublicNativeObligationKind { obligation_id, kind } => write!(
                f,
                "trust-vc public obligation {obligation_id} has no admitted native TrustIr kind mapping for {kind:?}"
            ),
            Self::InvalidPublicObligationSemanticBinding { obligation_id, reason } => write!(
                f,
                "trust-vc native TrustIr proof for public obligation {obligation_id} has invalid canonical semantic binding: {reason}"
            ),
            Self::NativeTmirImportRejected {
                trust_ir_obligation_id,
                replay_status,
                status,
                reasons,
            } => write!(
                f,
                "trust-vc native Tmir import for obligation {trust_ir_obligation_id} was rejected: replay_status={replay_status}, admission_status={status}, reasons={}",
                reasons.join(", ")
            ),
            Self::NativeTmirImportInvalidIdentity { trust_ir_obligation_id, field } => write!(
                f,
                "trust-vc native Tmir import for obligation {trust_ir_obligation_id} had invalid identity field {field}"
            ),
            Self::NativeTmirImportMissingObligation {
                obligation_id,
                request_id,
                trust_ir_obligation_id,
            } => write!(
                f,
                "trust-vc native Tmir import did not include admitted proof artifact for public obligation {obligation_id} bound to native request {request_id} and Tmir proof obligation {trust_ir_obligation_id}"
            ),
            Self::NativeTmirImportBindingMismatch { obligation_id, field, expected, actual } => {
                write!(
                    f,
                    "trust-vc native Tmir import for {obligation_id} had mismatched {field}: expected {expected}, got {actual}"
                )
            }
            Self::NativeTmirObligationIdentityMissing { obligation_id, metadata_key } => write!(
                f,
                "trust-vc native Tmir evidence for {obligation_id} requires obligation metadata `{metadata_key}`"
            ),
            Self::NativeTmirObligationIdentityInvalid { obligation_id, metadata_key, value } => {
                write!(
                    f,
                    "trust-vc native Tmir evidence for {obligation_id} has invalid `{metadata_key}` value `{value}`"
                )
            }
            Self::NativeTmirObligationSuiteMismatch { obligation_id, suite } => write!(
                f,
                "trust-vc native Tmir evidence for {obligation_id} is bound to verifier suite `{suite}`, not trust-vc"
            ),
            Self::InvalidSupplementalArtifactKind { label, expected, actual } => write!(
                f,
                "trust-vc supplemental artifact {label} had kind {actual:?}, expected {expected:?}"
            ),
            Self::InvalidSupplementalArtifactHash { label, algorithm, value } => write!(
                f,
                "trust-vc supplemental artifact {label} had invalid digest {algorithm}:{value}"
            ),
            Self::InvalidSupplementalArtifactUri { label, uri } => write!(
                f,
                "trust-vc supplemental artifact {label} had invalid deterministic lowering URI {uri}"
            ),
            Self::SupplementalArtifactBindingMismatch {
                label,
                expected_uri,
                actual_uri,
                expected_hash,
                actual_hash,
            } => write!(
                f,
                "trust-vc supplemental artifact {label} did not match deterministic Trust lowering: expected {expected_uri}#{expected_hash}, got {actual_uri}#{actual_hash}"
            ),
            Self::FullVerificationFailed { unit_id, reason } => {
                write!(f, "trust-vc typed full verification failed for {unit_id}: {reason}")
            }
            Self::MissingFullVerificationEvidence { unit_id, evidence_name } => write!(
                f,
                "trust-vc typed full verification for {unit_id} did not return verified evidence for {evidence_name}"
            ),
            Self::UnsupportedFullVerificationEvidence { unit_id, evidence_name, reason } => write!(
                f,
                "trust-vc typed full verification evidence {evidence_name} for {unit_id} is unsupported: {reason}"
            ),
            Self::RejectedByTrustVcEvidenceShape { diagnostics } => write!(
                f,
                "converted trust_vc evidence failed Trust acceptance shape: {}",
                diagnostics.join("; ")
            ),
        }
    }
}

impl std::error::Error for TrustVcNativeReportConversionError {}

#[cfg(feature = "trust-build")]
fn trust_vc_native_evidence_from_verified_memory_fact(
    unit_id: &str,
    fact: &TypedMemorySafetyFact,
    verified_facts: &[VerifiedMemorySafetyFact],
    proof_artifact_id: String,
) -> Result<TrustVcNativeTrustProofEvidence, TrustVcNativeReportConversionError> {
    let verified = verified_facts
        .iter()
        .find(|verified| verified.name() == fact.name())
        .ok_or_else(|| TrustVcNativeReportConversionError::MissingFullVerificationEvidence {
            unit_id: unit_id.to_string(),
            evidence_name: fact.name().to_string(),
        })?;
    Ok(TrustVcNativeTrustProofEvidence::from_verified_memory_safety_fact(
        verified,
        proof_artifact_id,
    ))
}

#[cfg(feature = "trust-build")]
fn trust_vc_native_source_from_full_verification(
    source: TrustVcFullProofEvidenceSource,
) -> TrustVcNativeProofEvidenceSource {
    match source {
        TrustVcFullProofEvidenceSource::NativeTrustVcExpr => {
            TrustVcNativeProofEvidenceSource::TypedTrustVcExpr
        }
        TrustVcFullProofEvidenceSource::TypedCompatibilityBoundary => {
            TrustVcNativeProofEvidenceSource::TypedCompatibilityBoundary
        }
        _ => TrustVcNativeProofEvidenceSource::LegacySourceText,
    }
}

#[cfg(feature = "trust-build")]
fn trust_vc_native_profile_from_verified_proof(
    verified: &VerifiedProofEvidence,
) -> TrustVcNativeProofEvidenceProfile {
    match verified.reasoning_kind() {
        TrustVcFullReasoningKind::Ownership => TrustVcNativeProofEvidenceProfile::OwnershipMemory,
        TrustVcFullReasoningKind::Deductive => match verified.obligation_kind() {
            TrustVcCoreObligationKind::Requires | TrustVcCoreObligationKind::Ensures => {
                TrustVcNativeProofEvidenceProfile::TypedContractFrame
            }
            TrustVcCoreObligationKind::LoopInvariant => {
                TrustVcNativeProofEvidenceProfile::TypedInvariant
            }
            _ => TrustVcNativeProofEvidenceProfile::TypedDeductiveObligation,
        },
        TrustVcFullReasoningKind::Constructive => {
            TrustVcNativeProofEvidenceProfile::TypedDeductiveObligation
        }
        _ => TrustVcNativeProofEvidenceProfile::Unspecified,
    }
}

#[cfg(feature = "trust-build")]
fn trust_vc_native_reasoning_from_full_verification(
    reasoning: TrustVcFullReasoningKind,
) -> TrustVcNativeProofReasoningKind {
    match reasoning {
        TrustVcFullReasoningKind::Deductive => TrustVcNativeProofReasoningKind::Deductive,
        TrustVcFullReasoningKind::Ownership => TrustVcNativeProofReasoningKind::Ownership,
        TrustVcFullReasoningKind::Constructive => TrustVcNativeProofReasoningKind::Constructive,
        _ => TrustVcNativeProofReasoningKind::Unspecified,
    }
}

#[cfg(feature = "trust-build")]
fn trust_vc_native_assurance_from_full_verification(
    assurance: TrustVcFullAssuranceLevel,
) -> TrustVcNativeAssuranceLevel {
    match assurance {
        TrustVcFullAssuranceLevel::StaticProof => TrustVcNativeAssuranceLevel::StaticProof,
        TrustVcFullAssuranceLevel::AssumedEvidence => TrustVcNativeAssuranceLevel::AssumedEvidence,
        TrustVcFullAssuranceLevel::MetadataOnly => TrustVcNativeAssuranceLevel::MetadataOnly,
        _ => TrustVcNativeAssuranceLevel::Unspecified,
    }
}

#[cfg(feature = "trust-build")]
fn trust_vc_expr_evidence_payload(
    name: &str,
    expr: &TrustVcExpr,
    evidence_kind: &str,
) -> JsonValue {
    let debug = format!("{expr:?}");
    serde_json::json!({
        "kind": trust_vc_expr_kind(expr),
        "name": name,
        "evidence_kind": evidence_kind,
        "format": "trust_vc_core::ir::TrustVcExpr",
        "encoding": "debug-fingerprint",
        "debug_sha256": stable_sha256_hex(debug.as_bytes()),
    })
}

#[cfg(feature = "trust-build")]
fn trust_vc_expr_kind(expr: &TrustVcExpr) -> &'static str {
    match expr {
        TrustVcExpr::BoolLit(_) => "bool_literal",
        TrustVcExpr::StringLit(_) => "string_literal",
        TrustVcExpr::IntLit { .. } => "int_literal",
        TrustVcExpr::Var { .. } => "variable",
        TrustVcExpr::Arith { .. } => "arith",
        TrustVcExpr::Neg(_) => "neg",
        TrustVcExpr::Compare { .. } => "compare",
        TrustVcExpr::Logic { .. } => "logic",
        TrustVcExpr::Not(_) => "not",
        TrustVcExpr::Implies { .. } => "implies",
        TrustVcExpr::Ite { .. } => "ite",
        TrustVcExpr::Match { .. } => "match",
        TrustVcExpr::Let { .. } => "let",
        TrustVcExpr::Cast { .. } => "cast",
        TrustVcExpr::CollectionOp { .. } => "collection_op",
        TrustVcExpr::Index { .. } => "index",
        TrustVcExpr::Quantifier { .. } => "quantifier",
        TrustVcExpr::FnCall { .. } => "fn_call",
        TrustVcExpr::SpecClosure { .. } => "spec_closure",
        TrustVcExpr::IntConst { .. } => "int_const",
        TrustVcExpr::SpecialArith { .. } => "special_arith",
        TrustVcExpr::WrappingArith { .. } => "wrapping_arith",
        TrustVcExpr::Choose { .. } => "choose",
        TrustVcExpr::ReadPlace { .. } => "read_place",
        TrustVcExpr::PlaceDisjoint { .. } => "place_disjoint",
        TrustVcExpr::ProphecyNew { .. } => "prophecy_new",
        TrustVcExpr::ProphecyResolve { .. } => "prophecy_resolve",
        _ => "unknown",
    }
}

fn validate_native_typed_trust_expr(
    evidence: &TrustVcNativeTrustProofEvidence,
) -> Result<String, TrustVcNativeReportConversionError> {
    let typed_expr = evidence.typed_expr.as_ref().ok_or_else(|| {
        TrustVcNativeReportConversionError::MissingTypedTrustExprEvidence {
            obligation_id: evidence.obligation_id.clone(),
        }
    })?;
    let Some(object) = typed_expr.as_object() else {
        return Err(TrustVcNativeReportConversionError::InvalidTypedTrustExprEvidence {
            obligation_id: evidence.obligation_id.clone(),
            reason: "payload must be a JSON object with a structured `kind`".to_string(),
        });
    };
    let Some(kind) = typed_expr.get("kind").and_then(JsonValue::as_str) else {
        return Err(TrustVcNativeReportConversionError::InvalidTypedTrustExprEvidence {
            obligation_id: evidence.obligation_id.clone(),
            reason: "missing string field `kind`".to_string(),
        });
    };
    if kind.is_empty() {
        return Err(TrustVcNativeReportConversionError::InvalidTypedTrustExprEvidence {
            obligation_id: evidence.obligation_id.clone(),
            reason: "empty `kind` field".to_string(),
        });
    }
    if is_placeholder_typed_expr_label(kind) {
        return Err(TrustVcNativeReportConversionError::InvalidTypedTrustExprEvidence {
            obligation_id: evidence.obligation_id.clone(),
            reason: format!("placeholder/text evidence kind `{kind}` is not a typed TrustExpr"),
        });
    }
    if let Some(field) = typed_expr_placeholder_field(object) {
        return Err(TrustVcNativeReportConversionError::InvalidTypedTrustExprEvidence {
            obligation_id: evidence.obligation_id.clone(),
            reason: format!(
                "placeholder/text evidence field `{field}` is not accepted as typed TrustExpr"
            ),
        });
    }
    if let Some(bound_obligation_id) = object.get("tRust_obligation_id").and_then(JsonValue::as_str)
        && bound_obligation_id != evidence.obligation_id
    {
        return Err(TrustVcNativeReportConversionError::InvalidTypedTrustExprEvidence {
            obligation_id: evidence.obligation_id.clone(),
            reason: concat!(
                "payload must carry first-class typed TrustExpr identity with ",
                "`tRust_obligation_id` matching the obligation"
            )
            .to_string(),
        });
    }
    if !is_structured_trust_vc_trust_expr_payload(object)
        && !typed_expr_binds_obligation(object, &evidence.obligation_id)
    {
        return Err(TrustVcNativeReportConversionError::InvalidTypedTrustExprEvidence {
            obligation_id: evidence.obligation_id.clone(),
            reason: concat!(
                "payload must be a structured native trust_vc TrustExpr or carry ",
                "first-class typed TrustExpr identity with `name` or ",
                "`tRust_obligation_id` matching the obligation"
            )
            .to_string(),
        });
    }
    let canonical = serde_json::to_vec(typed_expr).map_err(|error| {
        TrustVcNativeReportConversionError::InvalidTypedTrustExprEvidence {
            obligation_id: evidence.obligation_id.clone(),
            reason: format!("could not serialize canonical payload: {error}"),
        }
    })?;
    Ok(stable_sha256_hex(&canonical))
}

fn is_placeholder_typed_expr_label(value: &str) -> bool {
    matches!(
        normalized_evidence_label(value).as_str(),
        "placeholder"
            | "todo"
            | "stub"
            | "text"
            | "rawtext"
            | "sourcetext"
            | "legacysourcetext"
            | "diagnostic"
            | "unchecked"
    )
}

fn typed_expr_placeholder_field(object: &serde_json::Map<String, JsonValue>) -> Option<&str> {
    object.keys().find_map(|key| {
        let normalized = normalized_evidence_label(key);
        matches!(
            normalized.as_str(),
            "placeholder" | "text" | "rawtext" | "sourcetext" | "legacysourcetext" | "diagnostic"
        )
        .then_some(key.as_str())
    })
}

fn typed_expr_binds_obligation(
    object: &serde_json::Map<String, JsonValue>,
    obligation_id: &str,
) -> bool {
    ["name", "tRust_obligation_id"].iter().any(|field| {
        object.get(*field).and_then(JsonValue::as_str).is_some_and(|value| value == obligation_id)
    })
}

fn is_structured_trust_vc_trust_expr_payload(object: &serde_json::Map<String, JsonValue>) -> bool {
    let Some(kind) = object.get("kind").and_then(JsonValue::as_str) else {
        return false;
    };
    match kind {
        "bool_literal" => object.get("value").is_some_and(JsonValue::is_boolean),
        "int_literal" => {
            object.contains_key("value") && object.get("sort").is_some_and(JsonValue::is_object)
        }
        "variable" => {
            object.get("name").is_some_and(JsonValue::is_string)
                && object.get("sort").is_some_and(JsonValue::is_object)
        }
        "old" => {
            object.get("source").is_some_and(JsonValue::is_string)
                && object.get("snapshot").is_some_and(JsonValue::is_string)
                && object.get("sort").is_some_and(JsonValue::is_object)
        }
        "arith" => {
            object.get("op").is_some_and(JsonValue::is_string)
                && object.get("left").is_some_and(JsonValue::is_object)
                && object.get("right").is_some_and(JsonValue::is_object)
                && object.get("sort").is_some_and(JsonValue::is_object)
        }
        "compare" | "logic" => {
            object.get("op").is_some_and(JsonValue::is_string)
                && object.get("left").is_some_and(JsonValue::is_object)
                && object.get("right").is_some_and(JsonValue::is_object)
        }
        "not" => object.get("expr").is_some_and(JsonValue::is_object),
        "implies" => {
            object.get("premise").is_some_and(JsonValue::is_object)
                && object.get("conclusion").is_some_and(JsonValue::is_object)
        }
        "cast" => {
            object.get("expr").is_some_and(JsonValue::is_object)
                && object.get("from_sort").is_some_and(JsonValue::is_object)
                && object.get("to_sort").is_some_and(JsonValue::is_object)
        }
        "call" => {
            object.get("function").is_some_and(JsonValue::is_string)
                && object.get("args").is_some_and(JsonValue::is_array)
                && object.get("return_sort").is_some_and(JsonValue::is_object)
        }
        "quantifier" => {
            object.get("quantifier_kind").is_some_and(JsonValue::is_string)
                && object.get("bound_vars").is_some_and(JsonValue::is_array)
                && object.get("body").is_some_and(JsonValue::is_object)
        }
        _ => false,
    }
}

#[cfg(feature = "trust-build")]
fn validate_trust_vc_public_obligation_semantic_binding(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    semantic_digests: &trust_verifier_api::CanonicalObligationSemanticDigestIndex,
    native_obligation: &trust_ir::ProofObligation,
    replay_formula: &trust_ir::ProofFormula,
) -> Result<(), TrustVcNativeReportConversionError> {
    let expected_kind = trust_vc_native_trust_ir_kind_for_public_obligation(&obligation.kind)
        .ok_or_else(|| {
            TrustVcNativeReportConversionError::UnsupportedPublicNativeObligationKind {
                obligation_id: obligation.obligation_id.clone(),
                kind: obligation.kind.clone(),
            }
        })?;
    validate_native_trust_ir_import_field(
        obligation,
        "obligation_kind",
        expected_kind.to_string(),
        native_obligation.kind.to_string(),
    )?;

    let formula = native_obligation.formula.as_ref().ok_or_else(|| {
        TrustVcNativeReportConversionError::NativeTmirImportInvalidIdentity {
            trust_ir_obligation_id: native_obligation.id.index(),
            field: "formula",
        }
    })?;
    if formula != replay_formula {
        return Err(TrustVcNativeReportConversionError::InvalidPublicObligationSemanticBinding {
            obligation_id: obligation.obligation_id.clone(),
            reason: "module proof formula differs from the request-authenticated replay assertion formula"
                .to_string(),
        });
    }
    validate_kernel_contract_formula_binding(bundle, obligation, formula)?;
    let source = native_obligation.source.as_ref().ok_or_else(|| {
        TrustVcNativeReportConversionError::NativeTmirImportInvalidIdentity {
            trust_ir_obligation_id: native_obligation.id.index(),
            field: "source",
        }
    })?;
    let public = source.public.as_ref().ok_or_else(|| {
        TrustVcNativeReportConversionError::NativeTmirImportInvalidIdentity {
            trust_ir_obligation_id: native_obligation.id.index(),
            field: "source.public",
        }
    })?;
    validate_native_trust_ir_import_field(
        obligation,
        "source.public.obligation_id",
        obligation.obligation_id.clone(),
        public.obligation_id.clone(),
    )?;
    let expected_label = semantic_digests.get(&obligation.obligation_id).ok_or_else(|| {
        TrustVcNativeReportConversionError::InvalidPublicObligationSemanticBinding {
            obligation_id: obligation.obligation_id.clone(),
            reason: "validated semantic digest index omitted the requested obligation".to_string(),
        }
    })?;
    let expected =
        trust_vc_proof_digest_from_canonical_sha256_hex(expected_label).ok_or_else(|| {
            TrustVcNativeReportConversionError::InvalidPublicObligationSemanticBinding {
                obligation_id: obligation.obligation_id.clone(),
                reason: "validated semantic digest index returned a non-canonical SHA-256 digest"
                    .to_string(),
            }
        })?;
    if public.semantic_digest != expected {
        return Err(TrustVcNativeReportConversionError::NativeTmirImportBindingMismatch {
            obligation_id: obligation.obligation_id.clone(),
            field: "source.public.semantic_digest",
            expected: expected.to_string(),
            actual: public.semantic_digest.to_string(),
        });
    }
    Ok(())
}

#[cfg(feature = "trust-build")]
fn validate_kernel_contract_formula_binding(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    native_formula: &trust_ir::ProofFormula,
) -> Result<(), TrustVcNativeReportConversionError> {
    let expected_contract_kind = match obligation.kind {
        ObligationKind::Precondition => ContractKind::Requires,
        ObligationKind::Postcondition => ContractKind::Ensures,
        _ => return Ok(()),
    };
    let contract_id = obligation.contract_id.as_deref().ok_or_else(|| {
        TrustVcNativeReportConversionError::InvalidPublicObligationSemanticBinding {
            obligation_id: obligation.obligation_id.clone(),
            reason: "kernel-certified contract import is missing its exact public contract"
                .to_string(),
        }
    })?;
    let contract =
        bundle.contracts.iter().find(|contract| contract.contract_id == contract_id).ok_or_else(
            || TrustVcNativeReportConversionError::InvalidPublicObligationSemanticBinding {
                obligation_id: obligation.obligation_id.clone(),
                reason: format!(
                    "kernel-certified contract import references missing contract {contract_id}"
                ),
            },
        )?;
    if contract.kind != expected_contract_kind {
        return Err(TrustVcNativeReportConversionError::InvalidPublicObligationSemanticBinding {
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "kernel-certified {:?} import requires a {expected_contract_kind:?} contract, got {:?}",
                obligation.kind, contract.kind
            ),
        });
    }
    let ContractPredicate::TrustIr { schema, value } = &contract.predicate else {
        return Err(
            TrustVcNativeReportConversionError::InvalidPublicObligationSemanticBinding {
                obligation_id: obligation.obligation_id.clone(),
                reason: "kernel-certified contract import requires an exact typed TrustIr proof-formula predicate"
                    .to_string(),
            },
        );
    };
    if schema != TRUST_VC_NATIVE_TRUST_IR_CONTRACT_FORMULA_SCHEMA {
        return Err(TrustVcNativeReportConversionError::InvalidPublicObligationSemanticBinding {
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "kernel-certified contract predicate schema must be {TRUST_VC_NATIVE_TRUST_IR_CONTRACT_FORMULA_SCHEMA}, got {schema}"
            ),
        });
    }
    let public_formula: trust_ir::ProofFormula = serde_json::from_value(value.clone()).map_err(
        |error| TrustVcNativeReportConversionError::InvalidPublicObligationSemanticBinding {
            obligation_id: obligation.obligation_id.clone(),
            reason: format!(
                "kernel-certified contract predicate is not a canonical TrustIr ProofFormula: {error}"
            ),
        },
    )?;
    if &public_formula != native_formula {
        return Err(TrustVcNativeReportConversionError::InvalidPublicObligationSemanticBinding {
            obligation_id: obligation.obligation_id.clone(),
            reason: "public typed contract formula differs from the kernel-replayed native formula"
                .to_string(),
        });
    }
    Ok(())
}

#[cfg(feature = "trust-build")]
fn trust_vc_proof_digest_from_canonical_sha256_hex(value: &str) -> Option<trust_ir::ProofDigest> {
    if value.len() != 64
        || !value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return None;
    }
    let mut bytes = [0_u8; 32];
    for (index, pair) in value.as_bytes().chunks_exact(2).enumerate() {
        let nibble = |byte| match byte {
            b'0'..=b'9' => Some(byte - b'0'),
            b'a'..=b'f' => Some(byte - b'a' + 10),
            _ => None,
        };
        bytes[index] = (nibble(pair[0])? << 4) | nibble(pair[1])?;
    }
    Some(trust_ir::ProofDigest::sha256(bytes))
}

fn validate_trust_vc_native_trust_ir_import_binding(
    imported: &TrustVcNativeTrustIrImportedProofArtifact,
) -> Result<(), TrustVcNativeReportConversionError> {
    let parsed_assertion_id = imported.assertion_id.parse::<u32>().ok();
    let invalid_field = if parsed_assertion_id.is_none() {
        Some("assertion_id")
    } else if !is_sha256_digest_label(&imported.trust_ir_module_digest) {
        Some("trust_ir_module_digest")
    } else if !is_sha256_digest_label(&imported.request_digest) {
        Some("request_digest")
    } else if !is_sha256_digest_label(&imported.evidence_digest) {
        Some("evidence_digest")
    } else if !is_sha256_digest_label(&imported.certificate_digest) {
        Some("certificate_digest")
    } else if !is_sha256_digest_label(&imported.compiler_facts_digest) {
        Some("compiler_facts_digest")
    } else if !is_sha256_digest_label(&imported.obligation_source_digest) {
        Some("obligation_source_digest")
    } else if imported.compiler_fact_obligation_id != imported.trust_ir_obligation_id {
        Some("compiler_fact_obligation_id")
    } else if imported.compiler_fact_assertion_id.is_none()
        || imported.compiler_fact_assertion_id != parsed_assertion_id
    {
        Some("compiler_fact_assertion_id")
    } else if imported.compiler_fact_refs.is_empty() {
        Some("compiler_fact_refs")
    } else if imported.replay_engine.trim().is_empty() {
        Some("replay_engine")
    } else if imported.replay_invocation.trim().is_empty() {
        Some("replay_invocation")
    } else if !is_sha256_digest_label(&imported.replay_transcript_digest) {
        Some("replay_transcript_digest")
    } else if normalized_sha256_hex(&imported.artifact_fingerprint).is_none() {
        Some("artifact_fingerprint")
    } else {
        None
    };

    if let Some(field) = invalid_field {
        return Err(TrustVcNativeReportConversionError::NativeTmirImportInvalidIdentity {
            trust_ir_obligation_id: imported.trust_ir_obligation_id,
            field,
        });
    }
    Ok(())
}

fn validate_trust_vc_native_trust_ir_import_matches_obligation(
    obligation: &TrustObligation,
    imported: &TrustVcNativeTrustIrImportedProofArtifact,
) -> Result<(), TrustVcNativeReportConversionError> {
    validate_trust_vc_native_trust_ir_import_binding(imported)?;
    let identity = trust_vc_native_tmir_obligation_identity(obligation)?;
    validate_required_native_trust_ir_string_metadata(
        obligation,
        TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY,
        TRUST_VC_ENGINE_NAME,
        "verifier_suite",
    )?;
    validate_native_trust_ir_import_field(
        obligation,
        "request_id",
        identity.request_id.to_string(),
        imported.request_id.to_string(),
    )?;
    validate_native_trust_ir_import_field(
        obligation,
        "proof_obligation_id",
        identity.proof_obligation_id.to_string(),
        imported.trust_ir_obligation_id.to_string(),
    )?;
    validate_required_native_trust_ir_u32_metadata(
        obligation,
        TRUST_TRUST_IR_NATIVE_ASSERTION_ID_METADATA_KEY,
        imported.assertion_id.parse::<u32>().expect("validated assertion id"),
        "assertion_id",
    )?;
    validate_required_native_trust_ir_digest_metadata(
        obligation,
        TRUST_TRUST_IR_NATIVE_TRUST_IR_MODULE_DIGEST_METADATA_KEY,
        &imported.trust_ir_module_digest,
        "trust_ir_module_digest",
    )?;
    validate_required_native_trust_ir_digest_metadata(
        obligation,
        TRUST_TRUST_IR_NATIVE_REQUEST_DIGEST_METADATA_KEY,
        &imported.request_digest,
        "request_digest",
    )?;
    validate_required_native_trust_ir_digest_metadata(
        obligation,
        TRUST_TRUST_IR_NATIVE_EVIDENCE_DIGEST_METADATA_KEY,
        &imported.evidence_digest,
        "evidence_digest",
    )?;
    validate_required_native_trust_ir_digest_metadata(
        obligation,
        TRUST_TRUST_IR_NATIVE_CERTIFICATE_DIGEST_METADATA_KEY,
        &imported.certificate_digest,
        "certificate_digest",
    )?;
    validate_required_native_trust_ir_digest_metadata(
        obligation,
        TRUST_TRUST_IR_NATIVE_COMPILER_FACTS_DIGEST_METADATA_KEY,
        &imported.compiler_facts_digest,
        "compiler_facts_digest",
    )?;
    validate_required_native_trust_ir_digest_metadata(
        obligation,
        TRUST_TRUST_IR_NATIVE_OBLIGATION_SOURCE_DIGEST_METADATA_KEY,
        &imported.obligation_source_digest,
        "obligation_source_digest",
    )?;
    validate_required_native_trust_ir_string_metadata(
        obligation,
        TRUST_TRUST_IR_NATIVE_REPLAY_ENGINE_METADATA_KEY,
        &imported.replay_engine,
        "replay_engine",
    )?;
    validate_required_native_trust_ir_string_metadata(
        obligation,
        TRUST_TRUST_IR_NATIVE_REPLAY_INVOCATION_METADATA_KEY,
        &imported.replay_invocation,
        "replay_invocation",
    )?;
    validate_required_native_trust_ir_digest_metadata(
        obligation,
        TRUST_TRUST_IR_NATIVE_REPLAY_TRANSCRIPT_DIGEST_METADATA_KEY,
        &imported.replay_transcript_digest,
        "replay_transcript_digest",
    )?;
    validate_required_native_trust_ir_digest_metadata(
        obligation,
        TRUST_TRUST_IR_NATIVE_ARTIFACT_FINGERPRINT_METADATA_KEY,
        &imported.artifact_fingerprint,
        "artifact_fingerprint",
    )?;
    Ok(())
}

fn validate_native_trust_ir_import_field(
    obligation: &TrustObligation,
    field: &'static str,
    expected: String,
    actual: String,
) -> Result<(), TrustVcNativeReportConversionError> {
    if expected == actual {
        Ok(())
    } else {
        Err(TrustVcNativeReportConversionError::NativeTmirImportBindingMismatch {
            obligation_id: obligation.obligation_id.clone(),
            field,
            expected,
            actual,
        })
    }
}

fn validate_required_native_trust_ir_u32_metadata(
    obligation: &TrustObligation,
    metadata_key: &'static str,
    expected: u32,
    field: &'static str,
) -> Result<(), TrustVcNativeReportConversionError> {
    if obligation_metadata_value(obligation, metadata_key).is_none() {
        return Err(TrustVcNativeReportConversionError::NativeTmirObligationIdentityMissing {
            obligation_id: obligation.obligation_id.clone(),
            metadata_key,
        });
    }
    validate_optional_native_trust_ir_u32_metadata(obligation, metadata_key, expected, field)
}

fn validate_required_native_trust_ir_string_metadata(
    obligation: &TrustObligation,
    metadata_key: &'static str,
    expected: &str,
    field: &'static str,
) -> Result<(), TrustVcNativeReportConversionError> {
    if obligation_metadata_value(obligation, metadata_key).is_none() {
        return Err(TrustVcNativeReportConversionError::NativeTmirObligationIdentityMissing {
            obligation_id: obligation.obligation_id.clone(),
            metadata_key,
        });
    }
    validate_optional_native_trust_ir_string_metadata(obligation, metadata_key, expected, field)
}

fn validate_required_native_trust_ir_digest_metadata(
    obligation: &TrustObligation,
    metadata_key: &'static str,
    expected: &str,
    field: &'static str,
) -> Result<(), TrustVcNativeReportConversionError> {
    if obligation_metadata_value(obligation, metadata_key).is_none() {
        return Err(TrustVcNativeReportConversionError::NativeTmirObligationIdentityMissing {
            obligation_id: obligation.obligation_id.clone(),
            metadata_key,
        });
    }
    validate_optional_native_trust_ir_digest_metadata(obligation, metadata_key, expected, field)
}

fn validate_optional_native_trust_ir_u32_metadata(
    obligation: &TrustObligation,
    metadata_key: &'static str,
    expected: u32,
    field: &'static str,
) -> Result<(), TrustVcNativeReportConversionError> {
    let Some(actual) = obligation_metadata_value(obligation, metadata_key) else {
        return Ok(());
    };
    let actual = actual.parse::<u32>().map_err(|_| {
        TrustVcNativeReportConversionError::NativeTmirObligationIdentityInvalid {
            obligation_id: obligation.obligation_id.clone(),
            metadata_key,
            value: actual.to_string(),
        }
    })?;
    validate_native_trust_ir_import_field(
        obligation,
        field,
        expected.to_string(),
        actual.to_string(),
    )
}

fn validate_optional_native_trust_ir_string_metadata(
    obligation: &TrustObligation,
    metadata_key: &'static str,
    expected: &str,
    field: &'static str,
) -> Result<(), TrustVcNativeReportConversionError> {
    let Some(actual) = obligation_metadata_value(obligation, metadata_key) else {
        return Ok(());
    };
    if actual.trim().is_empty() {
        return Err(TrustVcNativeReportConversionError::NativeTmirObligationIdentityInvalid {
            obligation_id: obligation.obligation_id.clone(),
            metadata_key,
            value: actual.to_string(),
        });
    }
    validate_native_trust_ir_import_field(
        obligation,
        field,
        expected.trim().to_string(),
        actual.trim().to_string(),
    )
}

fn validate_optional_native_trust_ir_digest_metadata(
    obligation: &TrustObligation,
    metadata_key: &'static str,
    expected: &str,
    field: &'static str,
) -> Result<(), TrustVcNativeReportConversionError> {
    let Some(actual) = obligation_metadata_value(obligation, metadata_key) else {
        return Ok(());
    };
    let Some(expected) = canonical_sha256_digest_label(expected) else {
        return Err(TrustVcNativeReportConversionError::NativeTmirImportInvalidIdentity {
            trust_ir_obligation_id: 0,
            field,
        });
    };
    let actual = canonical_sha256_digest_label(actual).ok_or_else(|| {
        TrustVcNativeReportConversionError::NativeTmirObligationIdentityInvalid {
            obligation_id: obligation.obligation_id.clone(),
            metadata_key,
            value: actual.to_string(),
        }
    })?;
    validate_native_trust_ir_import_field(obligation, field, expected, actual)
}

fn trust_vc_native_static_proof_strength(
    obligation: &TrustObligation,
    evidence: &TrustVcNativeTrustProofEvidence,
    artifact: &TrustVcNativeReplayableProofArtifact,
) -> Result<ProofStrength, TrustVcNativeReportConversionError> {
    let reasoning = validate_trust_vc_native_static_proof_profile(obligation, evidence)?;
    let _ = artifact;
    // A legacy DTO may describe a strict-checked proof for diagnostics, but it
    // cannot carry proof authority. In particular, never synthesize Certified
    // from its public booleans. The later artifact gate rejects even this
    // SmtBacked compatibility value before evidence can be returned.
    Ok(ProofStrength { reasoning, assurance: AssuranceLevel::SmtBacked })
}

fn validate_trust_vc_native_static_proof_profile(
    obligation: &TrustObligation,
    evidence: &TrustVcNativeTrustProofEvidence,
) -> Result<ReasoningKind, TrustVcNativeReportConversionError> {
    let obligation_id = obligation.obligation_id.clone();
    match evidence.evidence_profile {
        TrustVcNativeProofEvidenceProfile::Unspecified
        | TrustVcNativeProofEvidenceProfile::TypedCompatibility
        | TrustVcNativeProofEvidenceProfile::LegacyCompatibility => {
            return Err(TrustVcNativeReportConversionError::UnsupportedEvidenceProfile {
                obligation_id,
                profile: evidence.evidence_profile,
            });
        }
        TrustVcNativeProofEvidenceProfile::TypedContractFrame
            if !requires_trust_vc_contract_frame(&obligation.kind) =>
        {
            return Err(TrustVcNativeReportConversionError::EvidenceProfileMismatch {
                obligation_id,
                obligation_kind: obligation.kind.clone(),
                profile: evidence.evidence_profile,
            });
        }
        TrustVcNativeProofEvidenceProfile::OwnershipMemory
            if !requires_trust_vc_ownership_context(&obligation.kind) =>
        {
            return Err(TrustVcNativeReportConversionError::EvidenceProfileMismatch {
                obligation_id,
                obligation_kind: obligation.kind.clone(),
                profile: evidence.evidence_profile,
            });
        }
        TrustVcNativeProofEvidenceProfile::TypedInvariant
        | TrustVcNativeProofEvidenceProfile::TypedTranslationValidation
        | TrustVcNativeProofEvidenceProfile::TypedCastBootstrap
        | TrustVcNativeProofEvidenceProfile::TypedAdtBootstrap
        | TrustVcNativeProofEvidenceProfile::TypedPointerBootstrap
        | TrustVcNativeProofEvidenceProfile::TypedFatPointerBootstrap
        | TrustVcNativeProofEvidenceProfile::TypedDeductiveObligation => {
            return Err(TrustVcNativeReportConversionError::EvidenceProfileMismatch {
                obligation_id,
                obligation_kind: obligation.kind.clone(),
                profile: evidence.evidence_profile,
            });
        }
        TrustVcNativeProofEvidenceProfile::TypedContractFrame
        | TrustVcNativeProofEvidenceProfile::OwnershipMemory => {}
    }

    if evidence.assurance_level != TrustVcNativeAssuranceLevel::StaticProof {
        return Err(TrustVcNativeReportConversionError::UnsupportedAssuranceLevel {
            obligation_id,
            assurance_level: evidence.assurance_level,
        });
    }

    match (evidence.evidence_profile, evidence.reasoning_kind) {
        (
            TrustVcNativeProofEvidenceProfile::TypedContractFrame,
            TrustVcNativeProofReasoningKind::Deductive,
        ) => Ok(ReasoningKind::Deductive),
        (
            TrustVcNativeProofEvidenceProfile::OwnershipMemory,
            TrustVcNativeProofReasoningKind::Ownership,
        ) => Ok(ReasoningKind::OwnershipAnalysis),
        (_, reasoning_kind) => Err(TrustVcNativeReportConversionError::UnsupportedReasoningKind {
            obligation_id,
            reasoning_kind,
        }),
    }
}

fn validate_native_replayable_artifact(
    artifact: &TrustVcNativeReplayableProofArtifact,
    policy: TrustVcNativeProofCertificatePolicy,
) -> Result<(), TrustVcNativeReportConversionError> {
    let Some(id_digest) = artifact.artifact_id.strip_prefix(TRUST_VC_PROOF_ARTIFACT_ID_PREFIX)
    else {
        return Err(TrustVcNativeReportConversionError::InvalidProofArtifactId {
            artifact_id: artifact.artifact_id.clone(),
        });
    };
    if normalized_sha256_hex(id_digest).is_none() {
        return Err(TrustVcNativeReportConversionError::InvalidProofArtifactId {
            artifact_id: artifact.artifact_id.clone(),
        });
    }
    let Some(digest) = normalized_sha256_hex(&artifact.digest) else {
        return Err(TrustVcNativeReportConversionError::InvalidProofArtifactDigest {
            artifact_id: artifact.artifact_id.clone(),
            digest: artifact.digest.clone(),
        });
    };
    let id_digest = id_digest.to_ascii_lowercase();
    let digest = digest.to_ascii_lowercase();
    if id_digest != digest {
        return Err(TrustVcNativeReportConversionError::ProofArtifactDigestMismatch {
            artifact_id: artifact.artifact_id.clone(),
            digest: artifact.digest.clone(),
        });
    }
    if artifact.payload.is_empty() {
        return Err(TrustVcNativeReportConversionError::EmptyProofArtifactPayload {
            artifact_id: artifact.artifact_id.clone(),
        });
    }
    let computed = stable_sha256_hex(artifact.payload.as_bytes());
    if computed != digest {
        return Err(TrustVcNativeReportConversionError::ProofArtifactPayloadDigestMismatch {
            artifact_id: artifact.artifact_id.clone(),
            expected: digest,
            actual: computed,
        });
    }
    if artifact.hole_count > 0 {
        return Err(TrustVcNativeReportConversionError::ProofArtifactContainsHoles {
            artifact_id: artifact.artifact_id.clone(),
            hole_count: artifact.hole_count,
        });
    }
    if !artifact.strict_verified && !artifact.kernel_verified {
        return Err(TrustVcNativeReportConversionError::UncheckedProofCertificate {
            artifact_id: artifact.artifact_id.clone(),
        });
    }
    if policy == TrustVcNativeProofCertificatePolicy::StrictReplayableCertificate
        && !artifact.strict_verified
    {
        return Err(TrustVcNativeReportConversionError::StrictProofCertificateRequired {
            artifact_id: artifact.artifact_id.clone(),
        });
    }
    // Final authority gate: the legacy DTO erased the TrustVC release-admission
    // receipt and has no local replay. A payload digest plus producer booleans is
    // evidence transport, not proof verification.
    Err(TrustVcNativeReportConversionError::UncheckedProofCertificate {
        artifact_id: artifact.artifact_id.clone(),
    })
}

fn validate_native_proof_artifact_asserts_obligation(
    evidence: &TrustVcNativeTrustProofEvidence,
    artifact: &TrustVcNativeReplayableProofArtifact,
) -> Result<(), TrustVcNativeReportConversionError> {
    if artifact.assertion_obligation_ids.iter().any(|id| id == &evidence.obligation_id) {
        return Ok(());
    }
    if artifact.assumption_obligation_ids.iter().any(|id| id == &evidence.obligation_id) {
        return Err(TrustVcNativeReportConversionError::ProofArtifactAssumesRequestedObligation {
            artifact_id: artifact.artifact_id.clone(),
            obligation_id: evidence.obligation_id.clone(),
        });
    }
    Err(TrustVcNativeReportConversionError::ProofArtifactMissingAssertionObligation {
        artifact_id: artifact.artifact_id.clone(),
        obligation_id: evidence.obligation_id.clone(),
    })
}

fn validate_artifact_kind(
    label: &'static str,
    artifact: &EvidenceArtifact,
    expected: EvidenceArtifactKind,
) -> Result<(), TrustVcNativeReportConversionError> {
    if artifact.kind == expected {
        Ok(())
    } else {
        Err(TrustVcNativeReportConversionError::InvalidSupplementalArtifactKind {
            label,
            expected,
            actual: artifact.kind,
        })
    }
}

fn validate_supplemental_artifact_hash(
    label: &'static str,
    artifact: &EvidenceArtifact,
) -> Result<(), TrustVcNativeReportConversionError> {
    if artifact.hash.algorithm == "sha256" && normalized_sha256_hex(&artifact.hash.value).is_some()
    {
        Ok(())
    } else {
        Err(TrustVcNativeReportConversionError::InvalidSupplementalArtifactHash {
            label,
            algorithm: artifact.hash.algorithm.clone(),
            value: artifact.hash.value.clone(),
        })
    }
}

fn validate_supplemental_artifact_uri(
    label: &'static str,
    artifact: &EvidenceArtifact,
) -> Result<(), TrustVcNativeReportConversionError> {
    if artifact.uri.starts_with(TRUST_VC_NATIVE_LOWERING_ARTIFACT_URI_PREFIX) {
        Ok(())
    } else {
        Err(TrustVcNativeReportConversionError::InvalidSupplementalArtifactUri {
            label,
            uri: artifact.uri.clone(),
        })
    }
}

fn validate_supplemental_artifact_binding(
    label: &'static str,
    actual: &EvidenceArtifact,
    expected: &EvidenceArtifact,
) -> Result<(), TrustVcNativeReportConversionError> {
    if actual == expected {
        Ok(())
    } else {
        Err(TrustVcNativeReportConversionError::SupplementalArtifactBindingMismatch {
            label,
            expected_uri: expected.uri.clone(),
            actual_uri: actual.uri.clone(),
            expected_hash: format!("{}:{}", expected.hash.algorithm, expected.hash.value),
            actual_hash: format!("{}:{}", actual.hash.algorithm, actual.hash.value),
        })
    }
}

fn trust_vc_native_lowering_diagnostics(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Vec<String> {
    let mut diagnostics = Vec::new();

    if !is_trust_vc_owned_obligation_kind(&obligation.kind) {
        diagnostics.push(format!(
            "trust-vc owns typed contract-frame and ownership/memory obligations, not {:?}",
            obligation.kind
        ));
        return diagnostics;
    }

    require_obligation_metadata(
        obligation,
        TRUST_VC_CONDITION_ORIGIN_METADATA_KEY,
        TRUST_VC_CONDITION_ORIGIN_METADATA_VALUE,
        &mut diagnostics,
    );
    require_obligation_metadata(
        obligation,
        TRUST_VC_PROOF_OBLIGATION_METADATA_KEY,
        TRUST_VC_PROOF_OBLIGATION_METADATA_VALUE,
        &mut diagnostics,
    );

    if requires_trust_vc_contract_frame(&obligation.kind) {
        require_obligation_metadata(
            obligation,
            TRUST_VC_CONTRACT_FRAME_METADATA_KEY,
            TRUST_VC_CONTRACT_FRAME_METADATA_VALUE,
            &mut diagnostics,
        );
        match obligation.contract_id.as_deref() {
            Some(contract_id)
                if bundle.contracts.iter().any(|contract| contract.contract_id == contract_id) => {}
            Some(contract_id) => diagnostics.push(format!(
                "trust-vc contract-frame lowering requires contract `{contract_id}` in the bundle"
            )),
            None => diagnostics.push(
                "trust-vc contract-frame lowering requires a contract-linked obligation"
                    .to_string(),
            ),
        }
    }

    if requires_trust_vc_result_binding(&obligation.kind) {
        require_obligation_metadata(
            obligation,
            TRUST_VC_RESULT_BINDING_METADATA_KEY,
            TRUST_VC_RESULT_BINDING_METADATA_VALUE,
            &mut diagnostics,
        );
    }

    if requires_trust_vc_ownership_context(&obligation.kind) {
        require_obligation_metadata(
            obligation,
            TRUST_VC_OWNERSHIP_CONTEXT_METADATA_KEY,
            TRUST_VC_OWNERSHIP_CONTEXT_METADATA_VALUE,
            &mut diagnostics,
        );
    }

    diagnostics
}

fn trust_vc_contract_payload(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<Option<JsonValue>, TrustVcNativeLoweringError> {
    let Some(contract_id) = obligation.contract_id.as_deref() else {
        return Ok(None);
    };
    let contract =
        bundle.contracts.iter().find(|contract| contract.contract_id == contract_id).ok_or_else(
            || TrustVcNativeLoweringError::MissingContract {
                obligation_id: obligation.obligation_id.clone(),
                contract_id: contract_id.to_string(),
            },
        )?;

    let predicate_class = match &contract.predicate {
        ContractPredicate::TrustExpr { .. } => "trust-expr-source",
        ContractPredicate::TrustIr { .. } => "trust-ir",
        ContractPredicate::MathIr { .. } => "math-ir",
        ContractPredicate::MemoryIr { .. } => "memory-ir",
        ContractPredicate::TemporalModelRef { .. } => "temporal-model-ref",
        ContractPredicate::CanonicalJson { .. } => "canonical-json",
        ContractPredicate::Unsupported { .. } => "unsupported",
        _ => "other",
    };

    Ok(Some(serde_json::json!({
        "contract": serde_json::to_value(contract).map_err(|error| {
            TrustVcNativeLoweringError::SerializeLoweringPayload {
                label: "contract",
                reason: error.to_string(),
            }
        })?,
        "predicate_class": predicate_class,
    })))
}

fn trust_vc_lowering_artifact(
    kind: EvidenceArtifactKind,
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    label: &'static str,
    payload: &JsonValue,
) -> Result<EvidenceArtifact, TrustVcNativeLoweringError> {
    let payload = serde_json::to_vec(payload).map_err(|error| {
        TrustVcNativeLoweringError::SerializeLoweringPayload { label, reason: error.to_string() }
    })?;
    let digest = stable_sha256_hex(&payload);
    Ok(EvidenceArtifact {
        kind,
        uri: format!(
            "{TRUST_VC_NATIVE_LOWERING_ARTIFACT_URI_PREFIX}{}/{}/{}.json",
            uri_component(&bundle.bundle_id),
            uri_component(&obligation.obligation_id),
            label
        ),
        hash: ArtifactHash { algorithm: "sha256".to_string(), value: digest },
        materialization: None,
    })
}

fn uri_component(value: &str) -> String {
    let component: String = value
        .chars()
        .map(
            |ch| {
                if ch.is_ascii_alphanumeric() || matches!(ch, '-' | '_' | '.') { ch } else { '_' }
            },
        )
        .collect();
    if component.is_empty() { "unnamed".to_string() } else { component }
}

fn is_trust_vc_native_proof_strength(proof_strength: &trust_verifier_api::ProofStrength) -> bool {
    matches!(proof_strength.reasoning, ReasoningKind::OwnershipAnalysis | ReasoningKind::Deductive)
        && proof_strength.assurance == AssuranceLevel::Certified
}

fn require_obligation_metadata(
    obligation: &TrustObligation,
    key: &str,
    value: &str,
    diagnostics: &mut Vec<String>,
) {
    if !has_obligation_metadata(obligation, key, value) {
        diagnostics
            .push(format!("trust-vc proof evidence requires obligation metadata {key}={value}"));
    }
}

fn has_obligation_metadata(obligation: &TrustObligation, key: &str, value: &str) -> bool {
    obligation.metadata.iter().any(|entry| entry.key == key && entry.value == value)
}

fn require_complete_native_trust_ir_import_metadata_shape(
    obligation: &TrustObligation,
    diagnostics: &mut Vec<String>,
) {
    for key in TRUST_TRUST_IR_NATIVE_TRUST_VC_IMPORT_REQUIRED_METADATA_KEYS {
        if obligation_metadata_value(obligation, key).is_none() {
            diagnostics.push(format!(
                "trust-vc native Tmir proof certificate requires obligation metadata `{key}`"
            ));
        }
    }
}

fn validate_optional_native_trust_ir_metadata_shape(
    obligation: &TrustObligation,
    diagnostics: &mut Vec<String>,
) {
    for key in [
        TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY,
        TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
        TRUST_TRUST_IR_NATIVE_ASSERTION_ID_METADATA_KEY,
    ] {
        if let Some(value) = obligation_metadata_value(obligation, key)
            && value.parse::<u32>().is_err()
        {
            diagnostics.push(format!(
                "trust-vc native Tmir metadata `{key}` must be a stable u32 identity, got `{value}`"
            ));
        }
    }

    for key in [
        TRUST_TRUST_IR_NATIVE_TRUST_IR_MODULE_DIGEST_METADATA_KEY,
        TRUST_TRUST_IR_NATIVE_REQUEST_DIGEST_METADATA_KEY,
        TRUST_TRUST_IR_NATIVE_EVIDENCE_DIGEST_METADATA_KEY,
        TRUST_TRUST_IR_NATIVE_CERTIFICATE_DIGEST_METADATA_KEY,
        TRUST_TRUST_IR_NATIVE_COMPILER_FACTS_DIGEST_METADATA_KEY,
        TRUST_TRUST_IR_NATIVE_OBLIGATION_SOURCE_DIGEST_METADATA_KEY,
        TRUST_TRUST_IR_NATIVE_REPLAY_TRANSCRIPT_DIGEST_METADATA_KEY,
        TRUST_TRUST_IR_NATIVE_ARTIFACT_FINGERPRINT_METADATA_KEY,
    ] {
        if let Some(value) = obligation_metadata_value(obligation, key)
            && !is_sha256_digest_label(value)
        {
            diagnostics.push(format!(
                "trust-vc native Tmir metadata `{key}` must be a SHA-256 digest, got `{value}`"
            ));
        }
    }

    for key in [
        TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY,
        TRUST_TRUST_IR_NATIVE_REPLAY_ENGINE_METADATA_KEY,
        TRUST_TRUST_IR_NATIVE_REPLAY_INVOCATION_METADATA_KEY,
    ] {
        if let Some(value) = obligation_metadata_value(obligation, key)
            && value.trim().is_empty()
        {
            diagnostics.push(format!("trust-vc native Tmir metadata `{key}` must not be empty"));
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct TrustVcNativeTmirObligationIdentity {
    request_id: u32,
    proof_obligation_id: u32,
}

fn trust_vc_native_tmir_obligation_identity(
    obligation: &TrustObligation,
) -> Result<TrustVcNativeTmirObligationIdentity, TrustVcNativeReportConversionError> {
    let suite =
        obligation_metadata_value(obligation, TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY)
            .ok_or_else(|| {
                TrustVcNativeReportConversionError::NativeTmirObligationIdentityMissing {
                    obligation_id: obligation.obligation_id.clone(),
                    metadata_key: TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY,
                }
            })?;
    if !suite.eq_ignore_ascii_case(TRUST_VC_ENGINE_NAME) {
        return Err(TrustVcNativeReportConversionError::NativeTmirObligationSuiteMismatch {
            obligation_id: obligation.obligation_id.clone(),
            suite: suite.to_string(),
        });
    }

    let request_id = required_native_trust_ir_u32_metadata(
        obligation,
        TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY,
    )?;
    let proof_obligation_id = required_native_trust_ir_u32_metadata(
        obligation,
        TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
    )?;

    Ok(TrustVcNativeTmirObligationIdentity { request_id, proof_obligation_id })
}

fn required_native_trust_ir_u32_metadata(
    obligation: &TrustObligation,
    metadata_key: &'static str,
) -> Result<u32, TrustVcNativeReportConversionError> {
    let value = obligation_metadata_value(obligation, metadata_key).ok_or_else(|| {
        TrustVcNativeReportConversionError::NativeTmirObligationIdentityMissing {
            obligation_id: obligation.obligation_id.clone(),
            metadata_key,
        }
    })?;
    value.parse::<u32>().map_err(|_| {
        TrustVcNativeReportConversionError::NativeTmirObligationIdentityInvalid {
            obligation_id: obligation.obligation_id.clone(),
            metadata_key,
            value: value.to_string(),
        }
    })
}

fn obligation_metadata_value<'a>(obligation: &'a TrustObligation, key: &str) -> Option<&'a str> {
    obligation.metadata.iter().find(|entry| entry.key == key).map(|entry| entry.value.as_str())
}

fn has_valid_trust_vc_lowering_artifact_kind(
    evidence: &ObligationEvidence,
    kind: EvidenceArtifactKind,
) -> bool {
    evidence
        .artifacts
        .iter()
        .any(|artifact| artifact.kind == kind && is_valid_trust_vc_lowering_artifact(artifact))
}

fn is_valid_trust_vc_lowering_artifact(artifact: &EvidenceArtifact) -> bool {
    artifact.uri.starts_with(TRUST_VC_NATIVE_LOWERING_ARTIFACT_URI_PREFIX)
        && artifact.hash.algorithm == "sha256"
        && normalized_sha256_hex(&artifact.hash.value).is_some()
}

fn has_trust_vc_replayable_proof_certificate_artifact(evidence: &ObligationEvidence) -> bool {
    evidence.artifacts.iter().any(|artifact| {
        is_trust_vc_replayable_proof_certificate_artifact(artifact)
            || is_trust_vc_direct_mir_memory_proof_certificate_artifact(artifact)
            || is_trust_vc_native_trust_ir_proof_certificate_artifact(artifact)
    })
}

fn has_trust_vc_native_trust_ir_proof_certificate_artifact(evidence: &ObligationEvidence) -> bool {
    evidence.artifacts.iter().any(is_trust_vc_native_trust_ir_proof_certificate_artifact)
}

fn is_trust_vc_replayable_proof_certificate_artifact(
    artifact: &trust_verifier_api::EvidenceArtifact,
) -> bool {
    if artifact.kind != EvidenceArtifactKind::ProofCertificate {
        return false;
    }
    if artifact.hash.algorithm != "sha256" {
        return false;
    }
    let Some(hash) = normalized_sha256_hex(&artifact.hash.value) else {
        return false;
    };
    let expected_id = format!("{TRUST_VC_PROOF_ARTIFACT_ID_PREFIX}{hash}");
    let expected_uri = format!("{TRUST_VC_PROOF_CERTIFICATE_URI_PREFIX}{expected_id}");
    let expected_alethe_uri = format!("{expected_uri}.alethe");
    artifact.uri == expected_uri || artifact.uri == expected_alethe_uri
}

fn is_trust_vc_direct_mir_memory_proof_certificate_artifact(
    artifact: &trust_verifier_api::EvidenceArtifact,
) -> bool {
    if artifact.kind != EvidenceArtifactKind::ProofCertificate
        || artifact.hash.algorithm != "sha256"
    {
        return false;
    }
    let Some(hash) = normalized_sha256_hex(&artifact.hash.value) else {
        return false;
    };
    artifact.uri
        == format!("{TRUST_VC_DIRECT_MIR_MEMORY_PROOF_CERTIFICATE_URI_PREFIX}{hash}.alethe")
}

/// Validate the public evidence shape emitted by the dedicated in-process
/// direct MIR-memory lane. This function does not itself confer authority; the
/// router combines it with its private knowledge that the genuine adapter was
/// invoked after an exact matching native request was found absent.
#[must_use]
pub fn trust_vc_direct_mir_memory_evidence_has_certificate_shape(
    evidence: &ObligationEvidence,
) -> bool {
    evidence.status == EvidenceStatus::Proved
        && evidence.evidence_id.starts_with("trust-vc:direct-mir-memory:")
        && evidence.proof_strength.as_ref().is_some_and(|strength| {
            strength.assurance == AssuranceLevel::Certified
                && strength.reasoning == ReasoningKind::OwnershipAnalysis
        })
        && evidence.satisfies_proof_artifact_policy()
        && evidence
            .artifacts
            .iter()
            .filter(|artifact| is_trust_vc_direct_mir_memory_proof_certificate_artifact(artifact))
            .count()
            == 1
        && !evidence.artifacts.iter().any(|artifact| {
            is_trust_vc_replayable_proof_certificate_artifact(artifact)
                || is_trust_vc_native_trust_ir_proof_certificate_artifact(artifact)
        })
}

fn is_trust_vc_native_trust_ir_proof_certificate_artifact(
    artifact: &trust_verifier_api::EvidenceArtifact,
) -> bool {
    if artifact.kind != EvidenceArtifactKind::ProofCertificate {
        return false;
    }
    if artifact.hash.algorithm != "sha256" {
        return false;
    }
    let Some(hash) = normalized_sha256_hex(&artifact.hash.value) else {
        return false;
    };
    let expected_uri = format!("{TRUST_VC_NATIVE_TRUST_IR_PROOF_CERTIFICATE_URI_PREFIX}{hash}");
    let expected_json_uri = format!("{expected_uri}.json");
    artifact.uri == expected_uri || artifact.uri == expected_json_uri
}

fn normalized_sha256_hex(value: &str) -> Option<&str> {
    let hash = value.trim().strip_prefix("sha256:").unwrap_or(value.trim());
    if hash.len() == 64 && hash.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        Some(hash)
    } else {
        None
    }
}

fn is_sha256_digest_label(value: &str) -> bool {
    canonical_sha256_digest_label(value).is_some()
}

fn canonical_sha256_digest_label(value: &str) -> Option<String> {
    let value = value.trim();
    if let Some(hash) = value.strip_prefix("sha256:")
        && hash.len() == 64
        && hash.bytes().all(|byte| byte.is_ascii_hexdigit())
    {
        return Some(format!("sha256:{}", hash.to_ascii_lowercase()));
    }
    if value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        Some(format!("sha256:{}", value.to_ascii_lowercase()))
    } else {
        None
    }
}

fn normalized_evidence_label(value: &str) -> String {
    value.chars().filter(|ch| ch.is_ascii_alphanumeric()).collect::<String>().to_ascii_lowercase()
}

#[cfg(test)]
mod tests {
    use serde_json::json;
    #[cfg(feature = "trust-build")]
    use trust_vc_trust_engine::{TrustCompareOp, TrustLogicOp, TrustSort, TrustVariable};
    use trust_verifier_api::{
        ArtifactHash, BundleSubject, ContractKind, ContractPredicate, EvidenceArtifact,
        MetadataEntry, ProofStrength, SourceLocation, TrustContract, VerificationRunResult,
        VerificationRunStatus, VerifierExecutionContext,
    };
    #[cfg(feature = "trust-build")]
    use trust_verifier_api::{
        TrustSpecBinaryOp, TrustSpecExpr, TrustSpecPredicate, TrustSpecSort, TrustSpecUnaryOp,
        TrustSpecVariable, TrustSpecVariableOrigin,
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

    fn typed_trust_vc_obligation(kind: ObligationKind, id: &str) -> TrustObligation {
        let mut obligation = obligation(kind, id);
        obligation.metadata = trust_vc_typed_proof_metadata();
        set_native_trust_ir_bundle_metadata(&mut obligation, "trust-vc", 0, 0);
        obligation
    }

    fn typed_trust_vc_contract_obligation(kind: ObligationKind, id: &str) -> TrustObligation {
        let mut obligation = obligation(kind.clone(), id);
        obligation.metadata = if requires_trust_vc_result_binding(&kind) {
            trust_vc_typed_result_contract_frame_metadata()
        } else {
            trust_vc_typed_contract_frame_metadata()
        };
        set_native_trust_ir_bundle_metadata(&mut obligation, "trust-vc", 0, 0);
        obligation
    }

    fn bundle_with(obligations: Vec<TrustObligation>) -> TrustContractBundle {
        let mut bundle = TrustContractBundle::empty(
            "bundle-trust-vc",
            BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::owned".to_string(),
            },
        );
        bundle.contracts.push(TrustContract {
            contract_id: "contract-pre".to_string(),
            kind: ContractKind::Requires,
            predicate: ContractPredicate::TrustExpr { text: "x > 0".to_string() },
            source: SourceLocation::default(),
            metadata: vec![MetadataEntry {
                key: "rust.attr".to_string(),
                value: "#[requires(x > 0)]".to_string(),
            }],
        });
        bundle.metadata.push(MetadataEntry {
            key: "trust_vc.attr.present".to_string(),
            value: "true".to_string(),
        });
        for obligation in &obligations {
            let Some(contract_id) = obligation.contract_id.as_deref() else {
                continue;
            };
            if !requires_trust_vc_contract_frame(&obligation.kind)
                || bundle.contracts.iter().any(|contract| contract.contract_id == contract_id)
            {
                continue;
            }
            bundle.contracts.push(TrustContract {
                contract_id: contract_id.to_string(),
                kind: if requires_trust_vc_result_binding(&obligation.kind) {
                    ContractKind::Ensures
                } else {
                    ContractKind::Requires
                },
                predicate: ContractPredicate::TrustExpr { text: "true".to_string() },
                source: SourceLocation::default(),
                metadata: Vec::new(),
            });
        }
        bundle.obligations = obligations;
        bundle
    }

    #[cfg(feature = "trust-build")]
    fn active_trust_ir_contract_bundle(
        kind: ObligationKind,
        obligation_id: &str,
    ) -> (TrustContractBundle, TrustObligation) {
        let (contract_kind, predicate) = if requires_trust_vc_result_binding(&kind) {
            (
                ContractKind::Ensures,
                TrustSpecPredicate::new(
                    TrustSpecExpr::binary(
                        TrustSpecBinaryOp::Eq,
                        TrustSpecExpr::result(TrustSpecSort::Int),
                        TrustSpecExpr::result(TrustSpecSort::Int),
                    ),
                    Vec::new(),
                ),
            )
        } else {
            (
                ContractKind::Requires,
                TrustSpecPredicate::new(TrustSpecExpr::bool_literal(true), Vec::new()),
            )
        };
        let contract_id = format!("contract.{obligation_id}");
        let mut obligation = obligation(kind.clone(), obligation_id);
        obligation.contract_id = Some(contract_id.clone());
        obligation.metadata = if requires_trust_vc_result_binding(&kind) {
            trust_vc_typed_result_contract_frame_metadata()
        } else {
            trust_vc_typed_contract_frame_metadata()
        };
        set_native_trust_ir_bundle_metadata(&mut obligation, "trust-vc", 0, 0);

        let mut bundle = TrustContractBundle::empty(
            "bundle-trust-vc-active-trust_ir",
            BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::active_trust_ir_contract".to_string(),
            },
        );
        bundle.contracts.push(TrustContract {
            contract_id,
            kind: contract_kind,
            predicate: predicate.into_contract_predicate().expect("predicate serializes"),
            source: SourceLocation::default(),
            metadata: vec![MetadataEntry {
                key: "trust.contract.lowering".to_string(),
                value: "spec_expr".to_string(),
            }],
        });
        bundle.obligations = vec![obligation.clone()];
        (bundle, obligation)
    }

    fn trust_vc_artifact(kind: EvidenceArtifactKind, name: &str) -> EvidenceArtifact {
        EvidenceArtifact {
            kind,
            uri: format!(
                "{TRUST_VC_NATIVE_LOWERING_ARTIFACT_URI_PREFIX}bundle-trust-vc/{name}.json"
            ),
            hash: ArtifactHash {
                algorithm: "sha256".to_string(),
                value: stable_sha256_hex(name.as_bytes()),
            },
            materialization: None,
        }
    }

    fn proof_check_artifacts() -> Vec<EvidenceArtifact> {
        vec![
            trust_vc_artifact(EvidenceArtifactKind::NormalizedObligation, "typed-obligation"),
            trust_vc_artifact(EvidenceArtifactKind::EngineInput, "native-input"),
            trust_vc_artifact(EvidenceArtifactKind::ProofCheckReport, "proof-check"),
        ]
    }

    fn replayable_certificate_artifacts(obligation_id: &str) -> Vec<EvidenceArtifact> {
        let (materialization, hash) = EvidenceArtifactMaterialization::new_bound(
            EvidenceArtifactKind::ProofCertificate,
            b"checked trust-vc test certificate",
            format!("trust-vc-test:{obligation_id}"),
            obligation_id,
            Vec::new(),
        )
        .expect("test certificate has a valid owner-bound materialization");
        let artifact_id = format!("{TRUST_VC_PROOF_ARTIFACT_ID_PREFIX}{}", hash.value);
        vec![
            trust_vc_artifact(EvidenceArtifactKind::NormalizedObligation, "typed-obligation"),
            trust_vc_artifact(EvidenceArtifactKind::EngineInput, "native-input"),
            EvidenceArtifact {
                kind: EvidenceArtifactKind::ProofCertificate,
                uri: format!("{TRUST_VC_PROOF_CERTIFICATE_URI_PREFIX}{artifact_id}.alethe"),
                hash,
                materialization: Some(materialization),
            },
        ]
    }

    fn native_trust_ir_certificate_artifacts(obligation_id: &str) -> Vec<EvidenceArtifact> {
        let (materialization, hash) = EvidenceArtifactMaterialization::new_bound(
            EvidenceArtifactKind::ProofCertificate,
            b"checked native TrustIr trust-vc test certificate",
            format!("trust-vc-native-test:{obligation_id}"),
            obligation_id,
            Vec::new(),
        )
        .expect("native TrustIr test certificate has exact owner-bound bytes");
        vec![
            trust_vc_artifact(EvidenceArtifactKind::NormalizedObligation, "typed-obligation"),
            trust_vc_artifact(EvidenceArtifactKind::EngineInput, "native-input"),
            EvidenceArtifact {
                kind: EvidenceArtifactKind::ProofCertificate,
                uri: format!(
                    "{TRUST_VC_NATIVE_TRUST_IR_PROOF_CERTIFICATE_URI_PREFIX}{}.json",
                    hash.value
                ),
                hash,
                materialization: Some(materialization),
            },
        ]
    }

    fn mismatched_replayable_certificate_artifacts(obligation_id: &str) -> Vec<EvidenceArtifact> {
        let mut artifacts = replayable_certificate_artifacts(obligation_id);
        let certificate = artifacts
            .iter_mut()
            .find(|artifact| artifact.kind == EvidenceArtifactKind::ProofCertificate)
            .expect("certificate artifact exists");
        certificate.uri = format!(
            "{TRUST_VC_PROOF_CERTIFICATE_URI_PREFIX}{TRUST_VC_PROOF_ARTIFACT_ID_PREFIX}ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff.alethe?materialization-sha256={}",
            certificate.hash.value
        );
        artifacts
    }

    fn native_supplemental_artifacts(
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
    ) -> TrustVcNativeReportArtifacts {
        trust_vc_native_report_artifacts_from_bundle(bundle, obligation)
            .expect("supplemental artifacts match deterministic lowering")
    }

    fn native_supplemental_artifact(kind: EvidenceArtifactKind, name: &str) -> EvidenceArtifact {
        EvidenceArtifact {
            kind,
            uri: format!(
                "{TRUST_VC_NATIVE_LOWERING_ARTIFACT_URI_PREFIX}bundle-trust-vc/{name}.json"
            ),
            hash: ArtifactHash {
                algorithm: "sha256".to_string(),
                value: stable_sha256_hex(name.as_bytes()),
            },
            materialization: None,
        }
    }

    fn native_trust_vc_artifact() -> TrustVcNativeReplayableProofArtifact {
        native_trust_vc_artifact_for("post")
    }

    fn native_trust_vc_artifact_for(
        assertion_obligation_id: &str,
    ) -> TrustVcNativeReplayableProofArtifact {
        TrustVcNativeReplayableProofArtifact::alethe("(proof trust_vc unit post)")
            .with_strict_verified(true)
            .with_kernel_verified(true)
            .with_assumption_obligation_ids(vec!["pre".to_string()])
            .with_assertion_obligation_ids(vec![assertion_obligation_id.to_string()])
    }

    #[cfg(feature = "trust-build")]
    fn native_trust_ir_report(replayable: bool) -> TrustVcNativeTrustIrBundleReport {
        let solver_identity = if replayable {
            json!({
                "prover": "trust-vc",
                "solvers": [{
                    "name": "lean4",
                    "version": "4.18.0",
                    "revision": "rev-1",
                    "digest": "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
                }],
                "replay_engine": "trust-vc",
                "replay_invocation": "trust-vc import --native-bundle",
                "transcript_digest": "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
            })
        } else {
            json!({
                "prover": "trust-vc",
                "solvers": [{
                    "name": "lean4",
                    "version": "4.18.0",
                    "revision": "rev-1",
                    "digest": "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
                }]
            })
        };
        let compiler_facts_binding = json!({
            "compiler_facts_digest": "sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee",
            "obligation_source_digest": "sha256:4444444444444444444444444444444444444444444444444444444444444444",
            "obligation_id": 0,
            "function_id": 0,
            "source_span": {"file_id": 0, "line": 12, "column": 5},
            "assertion_id": 6,
            "cause": "borrow_check",
            "monomorphization_id": 0,
            "fact_refs": [{"kind": "monomorphization", "id": 0}]
        });
        let proof_evidence = json!({
            "obligation_id": 0,
            "assertion_id": 6,
            "trust_ir_module_digest": "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd",
            "request_digest": "sha256:abababababababababababababababababababababababababababababababab",
            "obligation_kind": "memory_safety",
            "obligation_status": "discharged",
            "description": "borrow projection stays in bounds",
            "formula_schema": "smtlib2",
            "formula_sort": "Bool",
            "prover": "trust-vc",
            "evidence_digest": "sha256:1111111111111111111111111111111111111111111111111111111111111111",
            "certificate_digest": "sha256:2222222222222222222222222222222222222222222222222222222222222222",
            "suite_identity": {
                "suite": "trust-vc",
                "name": "trust-vc",
                "producer": "trust-vc-rev",
                "version": "1.0.0",
                "tool_digest": "sha256:3333333333333333333333333333333333333333333333333333333333333333"
            },
            "solver_identity": solver_identity,
            "replay_metadata": {
                "source": "request_provenance",
                "engine": "trust-vc",
                "invocation": "trust-vc import --native-bundle",
                "transcript_digest": "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
            },
            "compiler_facts_binding": compiler_facts_binding,
            "evidence_kind": "lean_proof",
            "trusted": false
        });
        let request = json!({
            "request_id": 7,
            "mode": "import_proof_certificates",
            "lineage_roots": [3],
            "proof_evidence": [proof_evidence]
        });
        serde_json::from_value(json!({
            "producer": "Trust",
            "input_kind": "rust_mir",
            "input_digest": "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            "trust_ir_module_digest": "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd",
            "compiler_facts_digest": "sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee",
            "module_name": "demo",
            "requests": [request]
        }))
        .expect("native Tmir report JSON matches trust_vc schema")
    }

    fn native_trust_ir_bundle_metadata(
        suite: &str,
        request_id: u32,
        proof_obligation_id: u32,
    ) -> Vec<MetadataEntry> {
        vec![
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY.to_string(),
                value: suite.to_string(),
            },
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY.to_string(),
                value: request_id.to_string(),
            },
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY.to_string(),
                value: proof_obligation_id.to_string(),
            },
        ]
    }

    fn complete_native_trust_ir_import_metadata() -> Vec<MetadataEntry> {
        vec![
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_ASSERTION_ID_METADATA_KEY.to_string(),
                value: "6".to_string(),
            },
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_TRUST_IR_MODULE_DIGEST_METADATA_KEY.to_string(),
                value: format!("sha256:{}", "a".repeat(64)),
            },
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_REQUEST_DIGEST_METADATA_KEY.to_string(),
                value: format!("sha256:{}", "2".repeat(64)),
            },
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_EVIDENCE_DIGEST_METADATA_KEY.to_string(),
                value: format!("sha256:{}", "b".repeat(64)),
            },
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_CERTIFICATE_DIGEST_METADATA_KEY.to_string(),
                value: format!("sha256:{}", "c".repeat(64)),
            },
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_COMPILER_FACTS_DIGEST_METADATA_KEY.to_string(),
                value: format!("sha256:{}", "d".repeat(64)),
            },
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_OBLIGATION_SOURCE_DIGEST_METADATA_KEY.to_string(),
                value: format!("sha256:{}", "e".repeat(64)),
            },
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_REPLAY_ENGINE_METADATA_KEY.to_string(),
                value: "trust-vc".to_string(),
            },
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_REPLAY_INVOCATION_METADATA_KEY.to_string(),
                value: "trust-vc import --native-bundle".to_string(),
            },
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_REPLAY_TRANSCRIPT_DIGEST_METADATA_KEY.to_string(),
                value: format!("sha256:{}", "f".repeat(64)),
            },
            MetadataEntry {
                key: TRUST_TRUST_IR_NATIVE_ARTIFACT_FINGERPRINT_METADATA_KEY.to_string(),
                value: format!("sha256:{}", "1".repeat(64)),
            },
        ]
    }

    fn set_native_trust_ir_bundle_metadata(
        obligation: &mut TrustObligation,
        suite: &str,
        request_id: u32,
        proof_obligation_id: u32,
    ) {
        clear_native_trust_ir_bundle_metadata(obligation);
        obligation.metadata.extend(native_trust_ir_bundle_metadata(
            suite,
            request_id,
            proof_obligation_id,
        ));
    }

    fn clear_native_trust_ir_bundle_metadata(obligation: &mut TrustObligation) {
        obligation.metadata.retain(|entry| {
            !matches!(
                entry.key.as_str(),
                TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY
                    | TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY
                    | TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY
            )
        });
    }

    #[cfg(feature = "trust-build")]
    fn native_trust_ir_import_metadata(
        import: &TrustVcNativeTrustIrImportedProofArtifact,
    ) -> Vec<MetadataEntry> {
        trust_vc_native_trust_ir_import_metadata_entries(import)
    }

    #[cfg(feature = "trust-build")]
    fn compiler_raw_trust_vc_native_trust_ir_bundle(
        public_obligation: &TrustObligation,
    ) -> Result<
        trust_ir::NativeVerificationBundle,
        trust_ir_bridge::NativeVerificationBundleBuildError,
    > {
        let public_bundle = bundle_with(vec![public_obligation.clone()]);
        let source_digest = trust_ir::ProofDigest::sha256([0xA7; 32]);
        let proof_id = trust_ir::ProofId::new(0);
        let function_id = trust_ir::FuncId::new(0);
        let public_obligation_semantic_digest = public_bundle
            .canonical_obligation_semantic_digest_sha256(public_obligation)
            .expect("public obligation semantics canonicalize");
        let public_obligation_semantic_digest =
            trust_vc_proof_digest_from_canonical_sha256_hex(&public_obligation_semantic_digest)
                .expect("canonical public semantic digest is lowercase raw SHA-256");
        let native_kind =
            trust_vc_native_trust_ir_kind_for_public_obligation(&public_obligation.kind)
                .expect("fixture public kind maps to trust-vc native TrustIr");

        let mut module = trust_ir::Module::new("compiler_raw_trust_vc_native_trust_ir_bridge");
        let source_file = module.intern_file("src/lib.rs");
        let func_ty = module.add_func_type(trust_ir::FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
        });
        let entry = trust_ir::BlockId::new(0);
        let mut function =
            trust_ir::Function::new(function_id, "compiler_owned_value", func_ty, entry)
                .with_producer(trust_ir::Producer::TrustIr);
        let mut block = trust_ir::Block::new(entry);
        block.body.push(
            trust_ir::InstrNode::new(trust_ir::Inst::Return { values: Vec::new() })
                .with_span(trust_ir::SourceSpan { file: 0, line: 12, col: 9 }),
        );
        function.blocks.push(block);
        module.add_function(function);
        module.proof_obligations.push(
            trust_ir::ProofObligation::new(
                proof_id,
                native_kind,
                trust_ir::ProofStatus::Discharged,
                "compiler raw trust_vc memory proof",
            )
            .with_function(function_id)
            .with_formula(trust_ir::ProofFormula {
                schema: "trust.vc.compiler-memory-claim.v1".to_string(),
                payload: json!({ "memory_safe": true }).to_string(),
                smtlib: None,
                sort: None,
            })
            .with_source(
                trust_ir::ProofObligationSourceIdentity::new(
                    "compiler-raw:memory",
                    "trust-assertion:compiler-raw:memory",
                )
                .with_range(trust_ir::ProofObligationSourceRange {
                    file: source_file,
                    start_line: 12,
                    start_col: 9,
                    end_line: 12,
                    end_col: 20,
                })
                .with_public(trust_ir::PublicObligationIdentity {
                    obligation_id: public_obligation.obligation_id.clone(),
                    semantic_digest: public_obligation_semantic_digest,
                }),
            ),
        );
        module.proof_certificates.push(trust_ir::ProofCertificate {
            obligation: proof_id,
            prover: "trust-vc".to_string(),
            evidence: trust_ir::ProofEvidence::LeanProof(
                "exact trust_vc.NativeTmir.compiler_owned_value_memory".to_string(),
            ),
        });

        trust_ir_bridge::native_verification_bundle_from_module(module, source_digest, function_id)
    }

    fn native_typed_expr_payload(obligation_id: &str) -> JsonValue {
        json!({
            "kind": "bool_literal",
            "value": true,
            "tRust_obligation_id": obligation_id,
        })
    }

    #[cfg(feature = "trust-build")]
    fn direct_mir_memory_unit_payload(obligation_id: &str) -> JsonValue {
        json!({
            "source_id": "bundle-trust-vc",
            "unit_id": "demo::owned",
            "native_context": {
                "function_signature": {
                    "name": "demo::owned",
                    "params": [
                        {
                            "name": "ptr_live",
                            "sort": { "kind": "bool" }
                        }
                    ],
                    "return_sort": { "kind": "bool" }
                },
                "ownership": {
                    "places": [
                        {
                            "place": "x",
                            "sort": {
                                "kind": "bit_vector",
                                "width": 32,
                                "signed": false
                            }
                        }
                    ],
                    "borrows": [
                        {
                            "region": "r0",
                            "place": "x",
                            "kind": "shared"
                        }
                    ]
                }
            },
            "obligations": [
                {
                    "id": obligation_id,
                    "predicate": {
                        "kind": "compare",
                        "op": "eq",
                        "left": {
                            "kind": "variable",
                            "name": "ptr_live",
                            "sort": { "kind": "bool" }
                        },
                        "right": {
                            "kind": "variable",
                            "name": "ptr_live",
                            "sort": { "kind": "bool" }
                        }
                    },
                    "location": "src/lib.rs:12:9"
                }
            ]
        })
    }

    #[cfg(feature = "trust-build")]
    fn release_admissible_direct_mir_memory_unit_payload(obligation_id: &str) -> JsonValue {
        let mut payload = direct_mir_memory_unit_payload(obligation_id);
        let sort = TrustSort::MathInt;
        let i = TrustExpr::variable("i", sort.clone());
        let sixteen = TrustExpr::int_literal(16, sort.clone());
        let contradiction = TrustExpr::logic(
            TrustLogicOp::And,
            TrustExpr::compare(TrustCompareOp::Lt, i.clone(), sixteen.clone()),
            TrustExpr::compare(TrustCompareOp::Ge, i, sixteen),
        );
        payload["native_context"]["function_signature"]["params"] = json!([{
            "name": "i",
            "sort": serde_json::to_value(&sort).expect("MathInt sort serializes"),
        }]);
        payload["obligations"][0]["predicate"] =
            serde_json::to_value(TrustExpr::not(contradiction))
                .expect("release-admissible QF_LIA predicate serializes");
        payload
    }

    #[cfg(feature = "trust-build")]
    fn canonical_direct_mir_memory_unit_payload(payload: JsonValue) -> String {
        let unit: TrustMirMemoryProofUnit =
            serde_json::from_value(payload).expect("direct MIR memory fixture deserializes");
        let mut payload =
            serde_json::to_value(&unit).expect("direct MIR memory fixture serializes");
        trust_types::digest::canonicalize_json_in_place(&mut payload);
        serde_json::to_string(&payload).expect("direct MIR memory fixture canonicalizes")
    }

    #[cfg(feature = "trust-build")]
    fn attach_direct_mir_memory_public_formula(
        obligation: &mut TrustObligation,
        comparison: TrustSpecBinaryOp,
    ) {
        let variable = TrustSpecVariable {
            name: "ptr_live".to_string(),
            sort: TrustSpecSort::Bool,
            origin: TrustSpecVariableOrigin::Inferred,
        };
        let ptr = TrustSpecExpr::variable("ptr_live", TrustSpecSort::Bool);
        let predicate = TrustSpecPredicate::new(
            TrustSpecExpr::unary(
                TrustSpecUnaryOp::Not,
                TrustSpecExpr::binary(comparison, ptr.clone(), ptr),
            ),
            vec![variable],
        );
        obligation.metadata.extend([
            MetadataEntry {
                key: TRUST_VC_FORMULA_SCHEMA_METADATA_KEY.to_string(),
                value: TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
            },
            MetadataEntry {
                key: TRUST_VC_FORMULA_SORT_METADATA_KEY.to_string(),
                value: "Bool".to_string(),
            },
            MetadataEntry {
                key: TRUST_VC_FORMULA_SMTLIB_METADATA_KEY.to_string(),
                value: "(not (= ptr_live ptr_live))".to_string(),
            },
            MetadataEntry {
                key: TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY.to_string(),
                value: serde_json::to_string(&predicate)
                    .expect("direct public formula canonicalizes"),
            },
            MetadataEntry {
                key: TRUST_VC_DIGEST_METADATA_KEY.to_string(),
                value: stable_sha256_hex(obligation.obligation_id.as_bytes()),
            },
        ]);
    }

    #[cfg(feature = "trust-build")]
    fn attach_direct_mir_memory_carrier(
        obligation: &mut TrustObligation,
        payload: JsonValue,
        comparison: TrustSpecBinaryOp,
    ) {
        attach_direct_mir_memory_public_formula(obligation, comparison);
        obligation.metadata.extend([
            MetadataEntry {
                key: TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_METADATA_KEY.to_string(),
                value: TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_VERSION.to_string(),
            },
            MetadataEntry {
                key: TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY.to_string(),
                value: canonical_direct_mir_memory_unit_payload(payload),
            },
        ]);
    }

    #[cfg(feature = "trust-build")]
    fn attach_release_admissible_direct_mir_memory_carrier(obligation: &mut TrustObligation) {
        let variable = TrustSpecVariable {
            name: "i".to_string(),
            sort: TrustSpecSort::Int,
            origin: TrustSpecVariableOrigin::Inferred,
        };
        let i = TrustSpecExpr::variable("i", TrustSpecSort::Int);
        let sixteen = TrustSpecExpr::int_literal("16");
        let bad_state = TrustSpecExpr::binary(
            TrustSpecBinaryOp::And,
            TrustSpecExpr::binary(TrustSpecBinaryOp::Lt, i.clone(), sixteen.clone()),
            TrustSpecExpr::binary(TrustSpecBinaryOp::Ge, i, sixteen),
        );
        let predicate = TrustSpecPredicate::new(bad_state, vec![variable]);
        obligation.metadata.extend([
            MetadataEntry {
                key: TRUST_VC_FORMULA_SCHEMA_METADATA_KEY.to_string(),
                value: TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
            },
            MetadataEntry {
                key: TRUST_VC_FORMULA_SORT_METADATA_KEY.to_string(),
                value: "Bool".to_string(),
            },
            MetadataEntry {
                key: TRUST_VC_FORMULA_SMTLIB_METADATA_KEY.to_string(),
                value: "(and (< i 16) (>= i 16))".to_string(),
            },
            MetadataEntry {
                key: TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY.to_string(),
                value: serde_json::to_string(&predicate)
                    .expect("release-admissible public formula canonicalizes"),
            },
            MetadataEntry {
                key: TRUST_VC_DIGEST_METADATA_KEY.to_string(),
                value: stable_sha256_hex(obligation.obligation_id.as_bytes()),
            },
            MetadataEntry {
                key: TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_METADATA_KEY.to_string(),
                value: TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_VERSION.to_string(),
            },
            MetadataEntry {
                key: TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY.to_string(),
                value: canonical_direct_mir_memory_unit_payload(
                    release_admissible_direct_mir_memory_unit_payload(&obligation.obligation_id),
                ),
            },
        ]);
    }

    #[cfg(feature = "trust-build")]
    fn direct_mir_memory_contract(obligation_id: &str, value: JsonValue) -> TrustContract {
        TrustContract {
            contract_id: format!("contract-{obligation_id}"),
            kind: ContractKind::Asserts,
            predicate: ContractPredicate::MemoryIr {
                schema: TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_VERSION.to_string(),
                value,
            },
            source: SourceLocation::default(),
            metadata: Vec::new(),
        }
    }

    #[cfg(feature = "trust-build")]
    fn verified_direct_mir_memory_fixture(
        obligation_id: &str,
    ) -> (TrustObligation, TrustMirMemoryProofUnit, TrustUnitReport) {
        let mut obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, obligation_id);
        obligation.required_strength = None;
        obligation.contract_id = None;
        let proof_unit: TrustMirMemoryProofUnit = serde_json::from_value(
            release_admissible_direct_mir_memory_unit_payload(obligation_id),
        )
        .expect("direct MIR memory fixture deserializes");
        let report = TrustVcTrustEngine::new()
            .verify_mir_memory_unit(
                &proof_unit,
                TrustProofPolicy::RequireReleaseAdmissibleCertificate,
            )
            .expect("direct MIR memory fixture has genuine live release admission");
        (obligation, proof_unit, report)
    }

    /// Replace the certificate of `report`'s sole proof artifact with `payload`,
    /// recomputing every identity the admission path derives from it (digest,
    /// artifact id, binding fingerprint, and the live evidence row's copies of
    /// the last two). The self-report metrics — `strict_verified`,
    /// `kernel_verified`, `trust_count`, `hole_count`, `release_admission` — are
    /// left untouched, because the point of the substitution is to ask what the
    /// admission path checks about the certificate BODY once every derived
    /// identity is consistent.
    #[cfg(feature = "trust-build")]
    fn substitute_direct_mir_memory_certificate(
        report: TrustUnitReport,
        payload: &str,
    ) -> TrustUnitReport {
        let digest = format!("sha256:{}", stable_sha256_hex(payload.as_bytes()));
        let artifact_id = format!(
            "{TRUST_VC_PROOF_ARTIFACT_ID_PREFIX}{}",
            digest.strip_prefix("sha256:").expect("digest carries the sha256 prefix")
        );
        let report = mutate_direct_mir_memory_report(report, |value| {
            value["proof_artifacts"][0]["payload"] = json!(payload);
            value["proof_artifacts"][0]["digest"] = json!(&digest);
            value["proof_artifacts"][0]["artifact_id"] = json!(&artifact_id);
            value["proof_evidence"][0]["proof_artifact_id"] = json!(&artifact_id);
        });
        let fingerprint = direct_proof_artifact_binding_fingerprint(&report.proof_artifacts()[0]);
        mutate_direct_mir_memory_report(report, |value| {
            value["proof_artifacts"][0]["binding_fingerprint"] = json!(&fingerprint);
            value["proof_evidence"][0]["proof_artifact_binding_fingerprint"] = json!(&fingerprint);
        })
    }

    /// The direct MIR-memory certificate is the whole reason the compiler's
    /// `DirectTrustVcLive` authority reports `Trusted` rather than `Certified`
    /// (docs/TCB.md). This test states the boundary that admission actually
    /// enforces over that certificate, in both directions, so the TCB row and
    /// the code cannot drift apart:
    ///
    ///  * the certificate is CONTENT-BOUND — swapping the Alethe text without
    ///    re-deriving the digest is rejected, so the bytes the evidence carries
    ///    are the bytes trust-vc produced; but
    ///  * the certificate is NEVER RE-CHECKED — a self-consistent substitution
    ///    whose derivation establishes nothing is admitted with the same
    ///    `certified`/`OwnershipAnalysis` strength as the real refutation.
    ///
    /// The second half is not a live hole: `verify_direct_mir_memory_unit`
    /// obtains the report from the in-process engine, and admission separately
    /// requires `cache_status() == Miss`, so no serialized or cached report can
    /// reach this seam. It is the *missing control* — nothing between trust-vc's
    /// own checkers and a `Proved` evidence row looks at the derivation — and it
    /// is exactly what a kernel reconstruction would have to replace before this
    /// lane could earn `Certified`.
    ///
    /// If a future change makes the substituted certificate fail here, that is
    /// progress, not a broken test: update this test AND the `DirectTrustVcLive`
    /// row of docs/TCB.md together, because the row's "what is trusted" column
    /// will have changed.
    #[cfg(feature = "trust-build")]
    #[test]
    fn direct_mir_memory_admission_binds_the_alethe_certificate_but_never_rechecks_it() {
        let (obligation, proof_unit, report) =
            verified_direct_mir_memory_fixture("memory.certificate_boundary");
        let genuine = report.proof_artifacts()[0].payload().to_string();
        assert!(
            genuine.contains(":rule la_generic") && genuine.contains("(step t7 (cl)"),
            "the lane's release-admissible shape is a QF_LIA Farkas refutation closing on the \
             empty clause; the certificate boundary test is written against that shape: {genuine}"
        );

        // The substituted derivation proves nothing: `(cl)` is claimed directly
        // off a one-coefficient `la_generic`, with none of the `and_pos` /
        // `th_resolution` steps that connect the assumption to the empty clause
        // in the genuine refutation. The two halves below feed admission THIS
        // SAME body and differ only in whether the identities derived from it
        // were recomputed, so what they discriminate is exactly identity binding
        // versus derivation checking.
        let forged = concat!(
            "(assume t0 (and (< i 16) (<= 16 i)))\n",
            "(step t1 (cl) :rule la_generic :args (1))\n",
        );

        // Content binding holds: the body cannot be swapped underneath a digest
        // computed over the real refutation.
        let unbound = mutate_first_direct_mir_memory_artifact(report.clone(), |artifact| {
            artifact["payload"] = json!(forged);
        });
        let error = trust_vc_replayable_artifact_for_obligation(
            "substituted trust-vc certificate",
            &unbound,
            &proof_unit,
            &obligation,
        )
        .expect_err("a certificate body that does not hash to the artifact digest is not evidence");
        assert!(
            error.to_string().contains("payload digest mismatch"),
            "unexpected rejection: {error}"
        );

        // Derivation checking does not: recompute the identities and the same
        // body is admitted.
        let substituted = substitute_direct_mir_memory_certificate(report, forged);
        let artifact = trust_vc_replayable_artifact_for_obligation(
            "substituted trust-vc certificate",
            &substituted,
            &proof_unit,
            &obligation,
        )
        .expect("admission binds certificate identity, not certificate validity");
        assert_eq!(artifact.payload(), forged);
        assert!(artifact.strict_verified() && artifact.kernel_verified());
        assert_eq!(artifact.trust_count(), 0);
        assert_eq!(artifact.hole_count(), 0);

        let mut carrier = obligation;
        attach_release_admissible_direct_mir_memory_carrier(&mut carrier);
        let bundle = bundle_with(vec![carrier.clone()]);
        let evidence = TrustVcVerificationEngine::new()
            .release_admitted_direct_mir_memory_evidence(
                &bundle,
                &carrier,
                "substituted trust-vc certificate",
                &proof_unit,
                &substituted,
            )
            .expect("the substituted certificate reaches a published evidence row");
        assert_eq!(evidence.status, EvidenceStatus::Proved);
        assert_eq!(
            evidence.proof_strength,
            Some(ProofStrength::certified(ReasoningKind::OwnershipAnalysis)),
            "the strength that mints DirectTrustVcLive is derived from the self-report, not from \
             the derivation the certificate carries",
        );
        assert!(trust_vc_direct_mir_memory_evidence_has_certificate_shape(&evidence));
        assert!(
            evidence.artifacts.iter().any(|artifact| {
                artifact.materialization.as_ref().is_some_and(|materialization| {
                    std::str::from_utf8(materialization.bytes())
                        .is_ok_and(|bytes| bytes.contains(forged))
                })
            }),
            "the published evidence carries the substituted derivation verbatim, which is what a \
             kernel reconstruction would have to consume",
        );
    }

    #[cfg(feature = "trust-build")]
    fn mutate_first_direct_mir_memory_artifact(
        report: TrustUnitReport,
        mutate: impl FnOnce(&mut JsonValue),
    ) -> TrustUnitReport {
        mutate_direct_mir_memory_report(report, |value| {
            let artifacts = value
                .get_mut("proof_artifacts")
                .and_then(JsonValue::as_array_mut)
                .expect("direct MIR memory fixture report carries replayable proof artifacts");
            let artifact = artifacts.first_mut().expect("direct MIR memory fixture has artifact");
            mutate(artifact);
        })
    }

    #[cfg(feature = "trust-build")]
    fn mutate_direct_mir_memory_report(
        report: TrustUnitReport,
        mutate: impl FnOnce(&mut JsonValue),
    ) -> TrustUnitReport {
        let mut value = serde_json::to_value(report).expect("trust-vc report serializes");
        mutate(&mut value);
        serde_json::from_value(value).expect("mutated trust-vc report deserializes")
    }

    fn native_contract_frame_evidence(
        obligation_id: &str,
        artifact: &TrustVcNativeReplayableProofArtifact,
    ) -> TrustVcNativeTrustProofEvidence {
        TrustVcNativeTrustProofEvidence::typed_trust_vc_expr(
            obligation_id,
            native_typed_expr_payload(obligation_id),
            artifact.artifact_id.clone(),
        )
        .with_evidence_profile(TrustVcNativeProofEvidenceProfile::TypedContractFrame)
        .with_reasoning_kind(TrustVcNativeProofReasoningKind::Deductive)
        .with_assurance_level(TrustVcNativeAssuranceLevel::StaticProof)
    }

    fn native_ownership_memory_evidence(
        obligation_id: &str,
        artifact: &TrustVcNativeReplayableProofArtifact,
    ) -> TrustVcNativeTrustProofEvidence {
        TrustVcNativeTrustProofEvidence::typed_trust_vc_expr(
            obligation_id,
            native_typed_expr_payload(obligation_id),
            artifact.artifact_id.clone(),
        )
        .with_evidence_profile(TrustVcNativeProofEvidenceProfile::OwnershipMemory)
        .with_reasoning_kind(TrustVcNativeProofReasoningKind::Ownership)
        .with_assurance_level(TrustVcNativeAssuranceLevel::StaticProof)
    }

    fn proved_trust_vc_evidence(
        engine: &TrustVcVerificationEngine,
        obligation: &TrustObligation,
        artifacts: Vec<EvidenceArtifact>,
    ) -> ObligationEvidence {
        let reasoning = if requires_trust_vc_ownership_context(&obligation.kind) {
            ReasoningKind::OwnershipAnalysis
        } else {
            ReasoningKind::Deductive
        };
        ObligationEvidence {
            evidence_id: format!("trust-vc:proved:{}", obligation.obligation_id),
            obligation_id: obligation.obligation_id.clone(),
            engine: engine.manifest().clone(),
            status: EvidenceStatus::Proved,
            proof_strength: Some(ProofStrength::certified(reasoning)),
            artifacts,
            counterexample: None,
            publication: EvidencePublicationMetadata::default(),
            diagnostics: Vec::new(),
        }
    }

    #[test]
    fn legacy_native_report_cannot_convert_to_proof_certificate_evidence() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = native_trust_vc_artifact();
        let report = TrustVcNativeUnitReport::new("crate::proof")
            .with_proof_evidence(native_contract_frame_evidence("post", &artifact))
            .with_proof_artifact(artifact.clone());

        let err = trust_vc_obligation_evidence_from_native_unit_report(
            &engine,
            &bundle,
            &obligation,
            &report,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::StrictReplayableCertificate,
        )
        .expect_err("legacy report booleans cannot authorize a certificate");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::UncheckedProofCertificate { .. }
        ));
    }

    #[test]
    fn proof_certificate_artifact_rejects_binding_without_replay_receipt() {
        let artifact = native_trust_vc_artifact();
        let native_evidence = native_contract_frame_evidence("post", &artifact);

        let err = trust_vc_proof_certificate_artifact_from_native(
            &native_evidence,
            &artifact,
            TrustVcNativeProofCertificatePolicy::StrictReplayableCertificate,
            "trust-vc-test-proof",
            "post",
        )
        .expect_err("caller-set verification booleans are not a replay receipt");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::UncheckedProofCertificate { .. }
        ));
    }

    #[test]
    fn native_trust_vc_report_rejects_missing_replay_certificate_artifact() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = native_trust_vc_artifact();
        let report = TrustVcNativeUnitReport::new("crate::proof")
            .with_proof_evidence(native_contract_frame_evidence("post", &artifact));

        let err = trust_vc_obligation_evidence_from_native_unit_report(
            &engine,
            &bundle,
            &obligation,
            &report,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::StrictReplayableCertificate,
        )
        .expect_err("native evidence without a unit replay certificate fails closed");

        assert!(matches!(err, TrustVcNativeReportConversionError::MissingUnitProofArtifact { .. }));
    }

    #[test]
    fn native_trust_vc_unit_report_rejects_absent_linked_proof_artifact_id() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = native_trust_vc_artifact();
        let native_evidence = native_contract_frame_evidence("post", &artifact)
            .with_proof_artifact_id(
                "trust-vc-proof-certificate:v1:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            );
        let report = TrustVcNativeUnitReport::new("crate::proof")
            .with_proof_evidence(native_evidence)
            .with_proof_artifact(artifact);

        let err = trust_vc_obligation_evidence_from_native_unit_report(
            &engine,
            &bundle,
            &obligation,
            &report,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::StrictReplayableCertificate,
        )
        .expect_err("unit report must not fall back to a different singleton proof artifact");

        assert!(matches!(err, TrustVcNativeReportConversionError::MissingUnitProofArtifact { .. }));
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_import_report_preserves_digest_bound_artifact_identity() {
        let report = native_trust_ir_report(true);

        let artifacts = trust_vc_native_trust_ir_imported_proof_artifacts_from_report(&report)
            .expect("native Tmir import report admits proof artifacts");
        let again = trust_vc_native_trust_ir_imported_proof_artifacts_from_report(&report)
            .expect("native Tmir import identity is deterministic");

        assert_eq!(artifacts, again);
        assert_eq!(artifacts.len(), 1);
        assert_eq!(artifacts[0].request_id, 7);
        assert_eq!(artifacts[0].assertion_id, "6");
        assert_eq!(artifacts[0].trust_ir_obligation_id, 0);
        assert_eq!(
            artifacts[0].evidence_digest,
            "sha256:1111111111111111111111111111111111111111111111111111111111111111"
        );
        assert_eq!(
            artifacts[0].certificate_digest,
            "sha256:2222222222222222222222222222222222222222222222222222222222222222"
        );
        assert_eq!(artifacts[0].compiler_fact_obligation_id, 0);
        assert_eq!(artifacts[0].compiler_fact_assertion_id, Some(6));
        assert_eq!(artifacts[0].replay_engine, "trust-vc");
        assert_eq!(
            artifacts[0].replay_transcript_digest,
            "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
        );
        assert!(
            artifacts[0]
                .compiler_fact_refs
                .iter()
                .any(|fact| fact.kind == "Monomorphization" && fact.id == 0),
            "compiler fact refs were not preserved: {:?}",
            artifacts[0].compiler_fact_refs
        );
        assert_eq!(
            normalized_sha256_hex(&artifacts[0].artifact_fingerprint)
                .expect("hash-addressed fingerprint")
                .len(),
            64
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_import_report_rejects_legacy_digest_authority() {
        let mut report = serde_json::to_value(native_trust_ir_report(true))
            .expect("native Tmir report serializes");
        report["requests"][0]["proof_evidence"][0]["request_digest"] =
            json!(format!("trust_ir-stable-v1:{}", "a".repeat(64)));
        let report = serde_json::from_value(report)
            .expect("legacy report DTO remains readable for compatibility diagnostics");

        let err = trust_vc_native_trust_ir_imported_proof_artifacts_from_report(&report)
            .expect_err("legacy digest labels cannot cross the proof-import authority boundary");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::NativeTmirImportInvalidIdentity {
                field: "request_digest",
                ..
            }
        ));
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_import_report_fails_closed_without_replay_metadata() {
        let report = native_trust_ir_report(false);

        let err = trust_vc_native_trust_ir_imported_proof_artifacts_from_report(&report)
            .expect_err("missing replay metadata rejects native Tmir import");

        assert!(matches!(err, TrustVcNativeReportConversionError::NativeTmirImportRejected { .. }));
        assert!(err.to_string().contains("MissingReplayIdentity"));
        assert!(err.to_string().contains("MissingReplayTranscriptDigest"));
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn legacy_native_report_cannot_authorize_even_with_import_identity() {
        let engine = TrustVcVerificationEngine::new();
        let native_import = trust_vc_native_trust_ir_imported_proof_artifacts_from_report(
            &native_trust_ir_report(true),
        )
        .expect("native Tmir import admits")
        .remove(0);
        let mut obligation =
            typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        set_native_trust_ir_bundle_metadata(
            &mut obligation,
            "trust-vc",
            native_import.request_id,
            native_import.trust_ir_obligation_id,
        );
        obligation.metadata.extend(native_trust_ir_import_metadata(&native_import));
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = native_trust_vc_artifact();
        let report = TrustVcNativeUnitReport::new("crate::proof")
            .with_proof_evidence(
                native_contract_frame_evidence("post", &artifact)
                    .with_native_trust_ir_import(native_import.clone()),
            )
            .with_proof_artifact(artifact);

        let err = trust_vc_obligation_evidence_from_native_unit_report(
            &engine,
            &bundle,
            &obligation,
            &report,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::StrictReplayableCertificate,
        )
        .expect_err("import metadata does not restore the erased replay receipt");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::UncheckedProofCertificate { .. }
        ));
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_vc_report_rejects_native_trust_ir_import_without_public_identity_metadata() {
        let engine = TrustVcVerificationEngine::new();
        let mut obligation =
            typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        clear_native_trust_ir_bundle_metadata(&mut obligation);
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = native_trust_vc_artifact();
        let native_import = trust_vc_native_trust_ir_imported_proof_artifacts_from_report(
            &native_trust_ir_report(true),
        )
        .expect("native Tmir import admits")
        .remove(0);
        let native_evidence = native_contract_frame_evidence("post", &artifact)
            .with_native_trust_ir_import(native_import);

        let err = trust_vc_obligation_evidence_from_native_report(
            &engine,
            &bundle,
            &obligation,
            &native_evidence,
            &artifact,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::ReplayableCertificate,
        )
        .expect_err("native Tmir import must be bound to public request/proof metadata");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::NativeTmirObligationIdentityMissing { .. }
        ));
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_vc_report_rejects_mismatched_native_trust_ir_fact_metadata() {
        let engine = TrustVcVerificationEngine::new();
        let native_import = trust_vc_native_trust_ir_imported_proof_artifacts_from_report(
            &native_trust_ir_report(true),
        )
        .expect("native Tmir import admits")
        .remove(0);
        let mut obligation =
            typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        set_native_trust_ir_bundle_metadata(
            &mut obligation,
            "trust-vc",
            native_import.request_id,
            native_import.trust_ir_obligation_id,
        );
        obligation.metadata.extend(native_trust_ir_import_metadata(&native_import));
        obligation
            .metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_TRUST_IR_NATIVE_COMPILER_FACTS_DIGEST_METADATA_KEY)
            .expect("compiler facts metadata exists")
            .value =
            "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff".to_string();
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = native_trust_vc_artifact();
        let native_evidence = native_contract_frame_evidence("post", &artifact)
            .with_native_trust_ir_import(native_import);

        let err = trust_vc_obligation_evidence_from_native_report(
            &engine,
            &bundle,
            &obligation,
            &native_evidence,
            &artifact,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::ReplayableCertificate,
        )
        .expect_err("native Tmir import must match compiler-facts metadata");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::NativeTmirImportBindingMismatch {
                field: "compiler_facts_digest",
                ..
            }
        ));
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_bundle_bridge_rejects_opaque_lean_authority_before_import() {
        let mut obligation =
            typed_trust_vc_obligation(ObligationKind::MemorySafety, "memory.compiler_raw");
        obligation.required_strength = None;
        obligation.contract_id = None;

        let error = compiler_raw_trust_vc_native_trust_ir_bundle(&obligation)
            .expect_err("opaque Lean proof metadata must not build an admission-ready bundle");
        let trust_ir_bridge::NativeVerificationBundleBuildError::Validation(errors) = error else {
            panic!("expected strict native bundle validation failure, got {error:?}");
        };
        assert!(
            errors.iter().any(|error| matches!(
                error,
                trust_ir::NativeVerificationBundleError::TrustVcCertificateNotDischarged {
                    request: trust_ir::NativeRequestId(0),
                    obligation: trust_ir::ProofId(0),
                    prover,
                    status: trust_ir::ProofStatus::Discharged,
                } if prover == "trust-vc"
            )),
            "opaque Lean proof metadata must fail before TrustVc import: {errors:?}"
        );
    }

    #[cfg(feature = "trust-build")]
    fn native_trust_ir_semantic_binding_fixture(
        label: &str,
    ) -> (
        TrustContractBundle,
        TrustObligation,
        trust_verifier_api::CanonicalObligationSemanticDigestIndex,
        trust_ir::ProofFormula,
        trust_ir::ProofObligation,
    ) {
        let mut obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, label);
        obligation.required_strength = None;
        obligation.contract_id = None;
        let bundle = bundle_with(vec![obligation.clone()]);
        let digests = bundle
            .canonical_obligation_semantic_digest_index_sha256(&bundle.obligations)
            .expect("semantic index");
        let semantic_digest = trust_vc_proof_digest_from_canonical_sha256_hex(
            digests.get(&obligation.obligation_id).expect("digest"),
        )
        .expect("canonical digest parses");
        let formula = trust_ir::ProofFormula {
            // Public authority is deliberately absent from the formula. The
            // exact claim stays independently replay-bound below while typed
            // source identity owns the public semantic binding.
            schema: "trust.vc.normalized-memory-claim.v1".to_string(),
            payload: json!({ "memory_safe": true }).to_string(),
            smtlib: None,
            sort: None,
        };
        let native = trust_ir::ProofObligation::new(
            trust_ir::ProofId::new(0),
            trust_ir::ObligationKind::MemorySafety,
            trust_ir::ProofStatus::Discharged,
            "test",
        )
        .with_formula(formula.clone())
        .with_source(
            trust_ir::ProofObligationSourceIdentity::new(
                format!("rust:{label}"),
                format!("trust-assertion:rust:{label}"),
            )
            .with_public(trust_ir::PublicObligationIdentity {
                obligation_id: obligation.obligation_id.clone(),
                semantic_digest,
            }),
        );
        (bundle, obligation, digests, formula, native)
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_semantic_binding_accepts_typed_embedded_public_identity() {
        let (bundle, obligation, digests, formula, native) =
            native_trust_ir_semantic_binding_fixture("memory.typed-source");

        validate_trust_vc_public_obligation_semantic_binding(
            &bundle,
            &obligation,
            &digests,
            &native,
            &formula,
        )
        .expect("typed embedded public identity and exact replay claim are authoritative");
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_semantic_binding_rejects_embedded_public_id_substitution() {
        let (bundle, obligation, digests, formula, mut native) =
            native_trust_ir_semantic_binding_fixture("memory.public-id-substitution");
        native
            .source
            .as_mut()
            .and_then(|source| source.public.as_mut())
            .expect("typed public source")
            .obligation_id = "substituted-public-obligation".to_string();

        let error = validate_trust_vc_public_obligation_semantic_binding(
            &bundle,
            &obligation,
            &digests,
            &native,
            &formula,
        )
        .expect_err("embedded public obligation substitution must fail closed")
        .to_string();
        assert!(error.contains("source.public.obligation_id"), "{error}");
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_semantic_binding_rejects_embedded_digest_substitution() {
        let (bundle, obligation, digests, formula, mut native) =
            native_trust_ir_semantic_binding_fixture("memory.digest-substitution");
        native
            .source
            .as_mut()
            .and_then(|source| source.public.as_mut())
            .expect("typed public source")
            .semantic_digest
            .bytes[0] ^= 1;

        let error = validate_trust_vc_public_obligation_semantic_binding(
            &bundle,
            &obligation,
            &digests,
            &native,
            &formula,
        )
        .expect_err("embedded public semantic digest substitution must fail closed")
        .to_string();
        assert!(error.contains("source.public.semantic_digest"), "{error}");
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_semantic_binding_rejects_formula_replay_substitution() {
        let (bundle, obligation, digests, formula, native) =
            native_trust_ir_semantic_binding_fixture("memory.replay-substitution");
        let mut substituted_replay = formula;
        substituted_replay.payload.push(' ');

        let error = validate_trust_vc_public_obligation_semantic_binding(
            &bundle,
            &obligation,
            &digests,
            &native,
            &substituted_replay,
        )
        .expect_err("module/replay formula substitution must fail closed")
        .to_string();
        assert!(error.contains("differs from the request-authenticated replay"), "{error}");
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_semantic_binding_rejects_native_kind_substitution() {
        let (bundle, obligation, digests, formula, mut native) =
            native_trust_ir_semantic_binding_fixture("memory.kind-substitution");
        native.kind = trust_ir::ObligationKind::BoundsCheck;

        let error = validate_trust_vc_public_obligation_semantic_binding(
            &bundle,
            &obligation,
            &digests,
            &native,
            &formula,
        )
        .expect_err("coarse native-kind substitution must fail closed")
        .to_string();
        assert!(error.contains("obligation_kind"), "{error}");
    }

    #[test]
    fn engine_rejects_forgeable_attached_native_trust_vc_report() {
        let mut obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, "memory");
        obligation.required_strength = None;
        obligation.contract_id = None;
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = native_trust_vc_artifact_for("memory");
        let report = TrustVcNativeUnitReport::new("crate::memory")
            .with_proof_evidence(native_ownership_memory_evidence("memory", &artifact))
            .with_proof_artifact(artifact);
        let engine = TrustVcVerificationEngine::new().with_native_unit_reports(vec![report]);

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].artifacts.is_empty());
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic.contains(TRUST_VC_MIR_MEMORY_PROOF_UNIT_REQUIRED) })
        );

        let result = engine.verify_with_context(
            &bundle,
            &bundle.obligations,
            &VerifierExecutionContext::new("trust-vc-native-report"),
        );
        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
        assert_eq!(result.summary.unsupported, 1);
    }

    #[test]
    fn native_trust_vc_report_rejects_duplicate_proof_evidence_for_obligation() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = native_trust_vc_artifact();
        let native_evidence = native_contract_frame_evidence("post", &artifact);
        let report = TrustVcNativeUnitReport::new("crate::post")
            .with_proof_evidence(native_evidence.clone())
            .with_proof_evidence(native_evidence)
            .with_proof_artifact(artifact);

        let err = trust_vc_obligation_evidence_from_native_unit_report(
            &engine,
            &bundle,
            &obligation,
            &report,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::ReplayableCertificate,
        )
        .expect_err("duplicate native proof evidence entries must fail closed");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::AmbiguousNativeProofEvidence {
                unit_id,
                obligation_id,
            } if unit_id == "crate::post" && obligation_id == "post"
        ));
    }

    #[test]
    fn engine_rejects_ambiguous_attached_native_trust_vc_reports_for_obligation() {
        let mut obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, "memory");
        obligation.required_strength = None;
        obligation.contract_id = None;
        let bundle = bundle_with(vec![obligation]);
        let first_artifact = native_trust_vc_artifact_for("memory");
        let first_report = TrustVcNativeUnitReport::new("crate::memory:first")
            .with_proof_evidence(native_ownership_memory_evidence("memory", &first_artifact))
            .with_proof_artifact(first_artifact);
        let second_artifact =
            TrustVcNativeReplayableProofArtifact::alethe("(proof trust_vc unit memory second)")
                .with_strict_verified(true)
                .with_kernel_verified(true)
                .with_assertion_obligation_ids(vec!["memory".to_string()]);
        let second_report = TrustVcNativeUnitReport::new("crate::memory:second")
            .with_proof_evidence(native_ownership_memory_evidence("memory", &second_artifact))
            .with_proof_artifact(second_artifact);
        let engine = TrustVcVerificationEngine::new()
            .with_native_unit_reports(vec![first_report, second_report]);

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].artifacts.is_empty());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("multiple native trust_vc unit reports")
                && diagnostic.contains("crate::memory:first")
                && diagnostic.contains("crate::memory:second")
        }));
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn active_trust_ir_adapter_legacy_report_cannot_mint_proof_authority() {
        let engine = TrustVcVerificationEngine::new();
        let (bundle, obligation) = active_trust_ir_contract_bundle(
            ObligationKind::Postcondition,
            "ensures.result_reflexive",
        );

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        let _ = obligation;
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported, "{:?}", evidence[0]);
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].artifacts.is_empty());
        assert!(evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("release-admissible")
                || diagnostic.contains(TRUST_VC_PROOF_CERTIFICATE_CHECK_REQUIRED)
        }));
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn active_trust_ir_adapter_lane_does_not_promote_contract_assumption_without_artifact() {
        let engine = TrustVcVerificationEngine::new();
        let (bundle, _obligation) =
            active_trust_ir_contract_bundle(ObligationKind::Precondition, "requires.true");

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].artifacts.is_empty());
        assert!(
            evidence[0].diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("active trust_vc Tmir adapter verification rejected")
                    && diagnostic.contains("must contain at least one assertion obligation")
            }),
            "diagnostics: {:?}",
            evidence[0].diagnostics
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn direct_mir_memory_legacy_report_cannot_mint_proof_authority() {
        let mut obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, "memory");
        obligation.required_strength = None;
        obligation.contract_id = Some("contract-memory".to_string());
        let unit_payload = direct_mir_memory_unit_payload("memory");
        let mut bundle = bundle_with(vec![obligation.clone()]);
        bundle.contracts.push(direct_mir_memory_contract("memory", unit_payload));
        let engine = TrustVcVerificationEngine::new();

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].artifacts.is_empty());
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains(TRUST_VC_MIR_MEMORY_PROOF_UNIT_REQUIRED))
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn structured_direct_transport_validation_never_mints_opaque_trust_ir_evidence() {
        let mut obligation =
            typed_trust_vc_obligation(ObligationKind::Ownership, "memory.native_trust_ir");
        obligation.required_strength = None;
        obligation.contract_id = None;
        attach_direct_mir_memory_carrier(
            &mut obligation,
            direct_mir_memory_unit_payload("memory.native_trust_ir"),
            TrustSpecBinaryOp::Eq,
        );

        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| count.set(0));
        assert!(
            trust_vc_validate_structured_direct_mir_memory_obligation_metadata(&obligation)
                .expect("structured transport validates without minting opaque TrustIr evidence")
        );
        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| assert_eq!(count.get(), 0));
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn direct_mir_memory_artifact_selection_rejects_assumed_requested_obligation() {
        let (obligation, proof_unit, report) = verified_direct_mir_memory_fixture("memory.assumed");
        let report = mutate_first_direct_mir_memory_artifact(report, |artifact| {
            artifact["assumption_obligation_ids"] = json!(["memory.assumed"]);
        });

        let error = trust_vc_replayable_artifact_for_obligation(
            "mutated trust-vc report",
            &report,
            &proof_unit,
            &obligation,
        )
        .expect_err("assumed unsafe-memory obligation must not count as proved");

        assert!(
            error.to_string().contains("requires an assumption-free certificate"),
            "unexpected rejection: {error}"
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn direct_mir_memory_artifact_selection_rejects_ambiguous_coverage() {
        let (obligation, proof_unit, report) =
            verified_direct_mir_memory_fixture("memory.ambiguous");
        let mut value = serde_json::to_value(report).expect("trust-vc report serializes");
        let artifacts = value
            .get_mut("proof_artifacts")
            .and_then(JsonValue::as_array_mut)
            .expect("direct MIR memory fixture report carries replayable proof artifacts");
        let duplicate = artifacts.first().expect("direct MIR memory fixture has artifact").clone();
        artifacts.push(duplicate);
        let report: TrustUnitReport =
            serde_json::from_value(value).expect("duplicated trust-vc report deserializes");

        let error = trust_vc_replayable_artifact_for_obligation(
            "mutated trust-vc report",
            &report,
            &proof_unit,
            &obligation,
        )
        .expect_err("ambiguous unsafe-memory artifact coverage must fail closed");

        assert!(
            error.to_string().contains("exactly one total replayable artifact"),
            "unexpected rejection: {error}"
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn direct_mir_memory_artifact_selection_rejects_wrong_unit_binding() {
        let (obligation, proof_unit, report) = verified_direct_mir_memory_fixture("memory.unit");
        let report = mutate_first_direct_mir_memory_artifact(report, |artifact| {
            artifact["unit_id"] = json!("other::memory_unit");
        });

        let error = trust_vc_replayable_artifact_for_obligation(
            "mutated trust-vc report",
            &report,
            &proof_unit,
            &obligation,
        )
        .expect_err("unsafe-memory proof artifact must be unit-bound");

        assert!(
            error.to_string().contains("not direct MIR memory unit"),
            "unexpected rejection: {error}"
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn direct_mir_memory_report_rejects_cache_hit_before_authority_admission() {
        let (obligation, proof_unit, report) = verified_direct_mir_memory_fixture("memory.cache");
        let report = mutate_direct_mir_memory_report(report, |report| {
            report["cache_status"] = json!("hit");
        });

        let error = trust_vc_replayable_artifact_for_obligation(
            "mutated trust-vc report",
            &report,
            &proof_unit,
            &obligation,
        )
        .expect_err("a cache hit cannot stand in for the required fresh direct solve");

        assert!(
            error.to_string().contains("requires a fresh TrustVC solve"),
            "unexpected rejection: {error}"
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn direct_mir_memory_report_rejects_second_total_live_evidence_row() {
        let (obligation, proof_unit, report) =
            verified_direct_mir_memory_fixture("memory.second_evidence");
        let report = mutate_direct_mir_memory_report(report, |report| {
            let evidence = report["proof_evidence"]
                .as_array_mut()
                .expect("live report carries proof evidence");
            let duplicate = evidence[0].clone();
            evidence.push(duplicate);
        });

        let error = trust_vc_replayable_artifact_for_obligation(
            "mutated trust-vc report",
            &report,
            &proof_unit,
            &obligation,
        )
        .expect_err("a second total evidence row makes the direct report ambiguous");

        assert!(
            error.to_string().contains("exactly one total live evidence row"),
            "unexpected rejection: {error}"
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn direct_mir_memory_report_rejects_wrong_live_typed_expression() {
        let (obligation, proof_unit, report) =
            verified_direct_mir_memory_fixture("memory.typed_expr");
        let report = mutate_direct_mir_memory_report(report, |report| {
            report["proof_evidence"][0]["typed_expr"] =
                json!({ "kind": "bool_literal", "value": false });
        });

        let error = trust_vc_replayable_artifact_for_obligation(
            "mutated trust-vc report",
            &report,
            &proof_unit,
            &obligation,
        )
        .expect_err("live evidence must retain the sole exact proof-unit predicate");

        assert!(
            error.to_string().contains("typed expression differs"),
            "unexpected rejection: {error}"
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn direct_mir_memory_report_rejects_wrong_live_artifact_id() {
        let (obligation, proof_unit, report) =
            verified_direct_mir_memory_fixture("memory.artifact_id");
        let report = mutate_direct_mir_memory_report(report, |report| {
            report["proof_evidence"][0]["proof_artifact_id"] =
                json!("trust-vc-proof-certificate:v1:wrong");
        });

        let error = trust_vc_replayable_artifact_for_obligation(
            "mutated trust-vc report",
            &report,
            &proof_unit,
            &obligation,
        )
        .expect_err("live evidence must name the selected exact artifact");

        assert!(
            error.to_string().contains("does not name the selected replayable artifact"),
            "unexpected rejection: {error}"
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn direct_mir_memory_report_rejects_wrong_live_binding_fingerprint() {
        let (obligation, proof_unit, report) =
            verified_direct_mir_memory_fixture("memory.evidence_binding");
        let report = mutate_direct_mir_memory_report(report, |report| {
            report["proof_evidence"][0]["proof_artifact_binding_fingerprint"] =
                json!("sha256:0000000000000000000000000000000000000000000000000000000000000000");
        });

        let error = trust_vc_replayable_artifact_for_obligation(
            "mutated trust-vc report",
            &report,
            &proof_unit,
            &obligation,
        )
        .expect_err("live evidence must retain the selected artifact binding");

        assert!(
            error.to_string().contains("does not carry the selected artifact binding"),
            "unexpected rejection: {error}"
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn direct_mir_memory_report_rejects_stale_artifact_binding_fingerprint() {
        let (obligation, proof_unit, report) =
            verified_direct_mir_memory_fixture("memory.stale_binding");
        let report = mutate_first_direct_mir_memory_artifact(report, |artifact| {
            artifact["digest"] =
                json!("sha256:0000000000000000000000000000000000000000000000000000000000000000");
        });

        let error = trust_vc_replayable_artifact_for_obligation(
            "mutated trust-vc report",
            &report,
            &proof_unit,
            &obligation,
        )
        .expect_err("a stale artifact binding must fail before release admission");

        assert!(
            error.to_string().contains("has binding fingerprint")
                && error.to_string().contains("expected"),
            "unexpected rejection: {error}"
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn direct_mir_memory_report_rejects_recomputed_binding_over_mutated_artifact() {
        let (obligation, proof_unit, report) =
            verified_direct_mir_memory_fixture("memory.recomputed_binding");
        let report = mutate_first_direct_mir_memory_artifact(report, |artifact| {
            artifact["digest"] =
                json!("sha256:0000000000000000000000000000000000000000000000000000000000000000");
        });
        let recomputed = direct_proof_artifact_binding_fingerprint(&report.proof_artifacts()[0]);
        let report = mutate_direct_mir_memory_report(report, |report| {
            report["proof_artifacts"][0]["binding_fingerprint"] = json!(&recomputed);
            report["proof_evidence"][0]["proof_artifact_binding_fingerprint"] = json!(&recomputed);
        });

        let error = trust_vc_replayable_artifact_for_obligation(
            "mutated trust-vc report",
            &report,
            &proof_unit,
            &obligation,
        )
        .expect_err("recomputing binding metadata cannot authorize a mutated artifact");

        assert!(
            error.to_string().contains("artifact id")
                && error.to_string().contains("does not match digest"),
            "unexpected rejection: {error}"
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn live_direct_mir_memory_artifact_accepts_release_admitted_non_clean_certificate() {
        let (obligation, proof_unit, report) =
            verified_direct_mir_memory_fixture("memory.non_clean");

        let artifact = trust_vc_replayable_artifact_for_obligation(
            "live trust-vc report",
            &report,
            &proof_unit,
            &obligation,
        )
        .expect("live QF_LIA artifact has genuine TrustVC release admission");

        assert!(!artifact.clean_supported());
        assert!(artifact.strict_verified());
        assert!(artifact.kernel_verified());
        assert_eq!(artifact.trust_count(), 0);
        assert_eq!(artifact.hole_count(), 0);
        assert!(artifact.release_admission().is_admissible());
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn live_release_admitted_direct_mir_memory_report_mints_bound_certificate() {
        let obligation_id = "memory.direct_release";
        let (mut obligation, proof_unit, report) =
            verified_direct_mir_memory_fixture(obligation_id);
        attach_release_admissible_direct_mir_memory_carrier(&mut obligation);
        let bundle = bundle_with(vec![obligation.clone()]);
        let evidence = TrustVcVerificationEngine::new()
            .release_admitted_direct_mir_memory_evidence(
                &bundle,
                &obligation,
                "live release-admitted test report",
                &proof_unit,
                &report,
            )
            .expect("live release-admitted report retains proof authority");

        assert_eq!(evidence.status, EvidenceStatus::Proved);
        assert_eq!(
            evidence.proof_strength,
            Some(ProofStrength::certified(ReasoningKind::OwnershipAnalysis))
        );
        assert!(trust_vc_direct_mir_memory_evidence_has_certificate_shape(&evidence));
        assert!(evidence.artifacts.iter().any(|artifact| {
            artifact.uri.starts_with(TRUST_VC_DIRECT_MIR_MEMORY_PROOF_CERTIFICATE_URI_PREFIX)
        }));
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn deadline_aware_direct_mir_memory_lane_preserves_typed_refutation() {
        let obligation_id = "memory.direct_refuted";
        let mut payload = direct_mir_memory_unit_payload(obligation_id);
        payload["obligations"][0]["predicate"]["op"] = json!("ne");
        let mut obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, obligation_id);
        obligation.required_strength = None;
        obligation.contract_id = None;
        attach_direct_mir_memory_carrier(&mut obligation, payload, TrustSpecBinaryOp::Ne);
        let bundle = bundle_with(vec![obligation.clone()]);

        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| count.set(0));

        let evidence = TrustVcVerificationEngine::new()
            .evidence_from_release_admitted_direct_mir_memory_with_deadline(
                &bundle,
                std::slice::from_ref(&obligation),
                None,
            );
        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| assert_eq!(count.get(), 1));

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Failed, "{:#?}", evidence[0]);
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].artifacts.is_empty());
        let counterexample =
            evidence[0].counterexample.as_ref().expect("refutation retains typed counterexample");
        assert_eq!(counterexample.format, "trust-vc.direct-mir-memory-counterexample.v1");
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn exact_direct_mir_memory_carrier_solves_once_and_proves() {
        let obligation_id = "memory.direct_proved";
        let mut obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, obligation_id);
        obligation.required_strength = None;
        obligation.contract_id = None;
        attach_release_admissible_direct_mir_memory_carrier(&mut obligation);
        let bundle = bundle_with(vec![obligation.clone()]);

        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| count.set(0));
        let evidence = TrustVcVerificationEngine::new()
            .evidence_from_release_admitted_direct_mir_memory_with_deadline(
                &bundle,
                &[obligation],
                None,
            );
        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| assert_eq!(count.get(), 1));

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Proved, "{:#?}", evidence[0]);
        assert!(trust_vc_direct_mir_memory_evidence_has_certificate_shape(&evidence[0]));
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn canonical_sorted_mir_memory_transport_validates_without_solving() {
        let obligation_id = "memory.transport_only";
        let mut obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, obligation_id);
        obligation.contract_id = None;
        attach_direct_mir_memory_carrier(
            &mut obligation,
            direct_mir_memory_unit_payload(obligation_id),
            TrustSpecBinaryOp::Eq,
        );
        let raw = obligation
            .metadata
            .iter()
            .find(|entry| entry.key == TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY)
            .expect("direct proof-unit metadata")
            .value
            .as_str();
        let typed: TrustMirMemoryProofUnit =
            serde_json::from_str(raw).expect("canonical direct carrier parses as the typed unit");
        let expected = canonical_direct_mir_memory_unit_payload(
            serde_json::to_value(&typed).expect("typed direct carrier serializes"),
        );
        assert_eq!(raw, expected, "fixture must pin the recursively sorted typed encoding");

        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| count.set(0));
        assert!(
            trust_vc_validate_structured_direct_mir_memory_obligation_metadata(&obligation)
                .expect("exact structured transport validates")
        );
        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| assert_eq!(count.get(), 0));
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn direct_mir_memory_transport_rejects_whitespace_and_reordered_json_without_solving() {
        let obligation_id = "memory.transport_noncanonical";
        let mut obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, obligation_id);
        obligation.contract_id = None;
        attach_direct_mir_memory_carrier(
            &mut obligation,
            direct_mir_memory_unit_payload(obligation_id),
            TrustSpecBinaryOp::Eq,
        );
        let metadata_index = obligation
            .metadata
            .iter()
            .position(|entry| entry.key == TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY)
            .expect("direct proof-unit metadata");
        let canonical = obligation.metadata[metadata_index].value.clone();
        let typed: TrustMirMemoryProofUnit = serde_json::from_str(&canonical)
            .expect("canonical direct carrier parses as the typed unit");
        let reordered =
            serde_json::to_string(&typed).expect("typed struct-order spelling serializes");
        assert_ne!(reordered, canonical, "struct order must differ from sorted canonical order");

        for alternate in [format!("{canonical}\n"), reordered] {
            obligation.metadata[metadata_index].value = alternate;
            TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| count.set(0));
            let error =
                trust_vc_validate_structured_direct_mir_memory_obligation_metadata(&obligation)
                    .expect_err("alternate direct-carrier JSON spelling must fail closed");
            TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| assert_eq!(count.get(), 0));
            assert!(error.to_string().contains("exact canonical producer serialization"));
        }
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn direct_mir_memory_transport_rejects_duplicate_top_level_key_without_solving() {
        let obligation_id = "memory.transport_duplicate_key";
        let mut obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, obligation_id);
        obligation.contract_id = None;
        attach_direct_mir_memory_carrier(
            &mut obligation,
            direct_mir_memory_unit_payload(obligation_id),
            TrustSpecBinaryOp::Eq,
        );
        let entry = obligation
            .metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY)
            .expect("direct proof-unit metadata");
        assert!(entry.value.starts_with('{'));
        entry.value = format!("{{\"source_id\":\"bundle-trust-vc\",{}", &entry.value[1..]);

        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| count.set(0));
        assert!(
            trust_vc_validate_structured_direct_mir_memory_obligation_metadata(&obligation)
                .is_err(),
            "duplicate top-level key must fail closed"
        );
        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| assert_eq!(count.get(), 0));
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn direct_mir_memory_transport_rejects_explicit_empty_verifier_variables_without_solving() {
        let obligation_id = "memory.transport_empty_variables";
        let mut obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, obligation_id);
        obligation.contract_id = None;
        attach_direct_mir_memory_carrier(
            &mut obligation,
            direct_mir_memory_unit_payload(obligation_id),
            TrustSpecBinaryOp::Eq,
        );
        let entry = obligation
            .metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY)
            .expect("direct proof-unit metadata");
        let mut alternate: JsonValue =
            serde_json::from_str(&entry.value).expect("canonical direct carrier JSON");
        alternate
            .as_object_mut()
            .expect("direct carrier is an object")
            .insert("verifier_variables".to_string(), JsonValue::Array(Vec::new()));
        trust_types::digest::canonicalize_json_in_place(&mut alternate);
        entry.value = serde_json::to_string(&alternate).expect("alternate carrier serializes");

        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| count.set(0));
        let error = trust_vc_validate_structured_direct_mir_memory_obligation_metadata(&obligation)
            .expect_err("explicit empty optional vector must not be an alternate canonical form");
        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| assert_eq!(count.get(), 0));
        assert!(error.to_string().contains("exact canonical producer serialization"));
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn deep_within_bound_direct_carrier_parses_and_validates_without_solve() {
        let obligation_id = "memory.deep_within_bound";
        let mut obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, obligation_id);
        obligation.contract_id = None;
        attach_direct_mir_memory_carrier(
            &mut obligation,
            direct_mir_memory_unit_payload(obligation_id),
            TrustSpecBinaryOp::Eq,
        );

        let mut deep_sort = TrustSort::Bool;
        for _ in 0..256 {
            deep_sort = TrustSort::Seq { elem: Box::new(deep_sort) };
        }
        let proof_unit: TrustMirMemoryProofUnit =
            serde_json::from_value(direct_mir_memory_unit_payload(obligation_id))
                .expect("base direct carrier deserializes");
        let deep_payload = canonical_direct_mir_memory_unit_payload(
            serde_json::to_value(
                proof_unit.with_variable(TrustVariable::new("deep_unused", deep_sort)),
            )
            .expect("within-bound deep carrier serializes"),
        );
        assert!(trust_types::json_depth::json_nesting_depth(&deep_payload) > 128);
        assert!(
            trust_types::json_depth::json_nesting_depth(&deep_payload)
                <= trust_types::json_depth::MAX_DEEP_NESTING
        );
        obligation
            .metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY)
            .expect("direct carrier metadata exists")
            .value = deep_payload;

        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| count.set(0));
        assert!(
            trust_vc_validate_structured_direct_mir_memory_obligation_metadata(&obligation)
                .expect("within-bound deep carrier parses and validates exactly")
        );
        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| assert_eq!(count.get(), 0));
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn over_depth_direct_carrier_fails_before_any_solve() {
        let obligation_id = "memory.over_depth";
        let mut obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, obligation_id);
        obligation.contract_id = None;
        attach_direct_mir_memory_carrier(
            &mut obligation,
            direct_mir_memory_unit_payload(obligation_id),
            TrustSpecBinaryOp::Eq,
        );

        let mut nested_sort = String::new();
        for _ in 0..=trust_types::json_depth::MAX_DEEP_NESTING {
            nested_sort.push_str(r#"{"kind":"seq","elem":"#);
        }
        nested_sort.push_str(r#"{"kind":"bool"}"#);
        for _ in 0..=trust_types::json_depth::MAX_DEEP_NESTING {
            nested_sort.push('}');
        }
        let base_payload =
            canonical_direct_mir_memory_unit_payload(direct_mir_memory_unit_payload(obligation_id));
        let obligations_offset = base_payload
            .find(r#""obligations":"#)
            .expect("canonical proof unit carries obligations");
        let over_depth_payload = format!(
            "{}\"verifier_variables\":[{{\"name\":\"deep_unused\",\"sort\":{nested_sort}}}],{}",
            &base_payload[..obligations_offset],
            &base_payload[obligations_offset..],
        );
        assert!(
            trust_types::json_depth::json_nesting_depth(&over_depth_payload)
                > trust_types::json_depth::MAX_DEEP_NESTING
        );
        obligation
            .metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY)
            .expect("direct carrier metadata exists")
            .value = over_depth_payload;
        let bundle = bundle_with(vec![obligation.clone()]);

        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| count.set(0));
        let evidence = TrustVcVerificationEngine::new()
            .evidence_from_release_admitted_direct_mir_memory_with_deadline(
                &bundle,
                &[obligation],
                None,
            );
        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| assert_eq!(count.get(), 0));
        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("recursion limit exceeded"))
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn generic_verification_never_solves_a_direct_mir_memory_carrier() {
        let obligation_id = "memory.generic_zero_solve";
        let mut obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, obligation_id);
        obligation.contract_id = None;
        attach_direct_mir_memory_carrier(
            &mut obligation,
            direct_mir_memory_unit_payload(obligation_id),
            TrustSpecBinaryOp::Eq,
        );
        let bundle = bundle_with(vec![obligation.clone()]);

        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| count.set(0));
        let evidence = TrustVcVerificationEngine::new().verify(&bundle, &[obligation]);
        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| assert_eq!(count.get(), 0));
        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn expired_direct_deadline_rejects_before_any_solve() {
        let obligation_id = "memory.expired_zero_solve";
        let mut obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, obligation_id);
        obligation.contract_id = None;
        attach_direct_mir_memory_carrier(
            &mut obligation,
            direct_mir_memory_unit_payload(obligation_id),
            TrustSpecBinaryOp::Eq,
        );
        let bundle = bundle_with(vec![obligation.clone()]);

        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| count.set(0));
        let evidence = TrustVcVerificationEngine::new()
            .evidence_from_release_admitted_direct_mir_memory_with_deadline(
                &bundle,
                &[obligation],
                Some(std::time::Instant::now()),
            );
        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| assert_eq!(count.get(), 0));
        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Timeout);
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn two_distinct_direct_carriers_solve_independently() {
        let mut first =
            typed_trust_vc_obligation(ObligationKind::MemorySafety, "memory.unique.first");
        first.required_strength = Some(ProofStrength::certified(ReasoningKind::OwnershipAnalysis));
        first.contract_id = None;
        attach_release_admissible_direct_mir_memory_carrier(&mut first);
        let mut second =
            typed_trust_vc_obligation(ObligationKind::MemorySafety, "memory.unique.second");
        second.required_strength = Some(ProofStrength::certified(ReasoningKind::OwnershipAnalysis));
        second.contract_id = None;
        attach_release_admissible_direct_mir_memory_carrier(&mut second);
        let bundle = bundle_with(vec![first.clone(), second.clone()]);

        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| count.set(0));
        let evidence = TrustVcVerificationEngine::new()
            .evidence_from_release_admitted_direct_mir_memory_with_deadline(
                &bundle,
                &[first, second],
                None,
            );
        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| assert_eq!(count.get(), 2));
        assert_eq!(evidence.len(), 2);
        assert!(evidence.iter().all(|row| row.status == EvidenceStatus::Proved));
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn sibling_substituted_direct_carrier_is_rejected_before_solve() {
        let mut first =
            typed_trust_vc_obligation(ObligationKind::MemorySafety, "memory.bound.first");
        first.contract_id = None;
        attach_direct_mir_memory_carrier(
            &mut first,
            direct_mir_memory_unit_payload("memory.bound.first"),
            TrustSpecBinaryOp::Eq,
        );
        let mut second =
            typed_trust_vc_obligation(ObligationKind::MemorySafety, "memory.bound.second");
        second.contract_id = None;
        attach_direct_mir_memory_carrier(
            &mut second,
            direct_mir_memory_unit_payload("memory.bound.first"),
            TrustSpecBinaryOp::Eq,
        );
        let bundle = bundle_with(vec![first.clone(), second]);

        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| count.set(0));
        let evidence = TrustVcVerificationEngine::new()
            .evidence_from_release_admitted_direct_mir_memory_with_deadline(
                &bundle,
                &[first],
                None,
            );
        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| assert_eq!(count.get(), 0));
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("carries a proof unit bound to"))
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn malformed_distinct_sibling_carrier_does_not_erase_valid_direct_proof() {
        let mut valid =
            typed_trust_vc_obligation(ObligationKind::MemorySafety, "memory.isolated.valid");
        valid.required_strength = Some(ProofStrength::certified(ReasoningKind::OwnershipAnalysis));
        valid.contract_id = None;
        attach_release_admissible_direct_mir_memory_carrier(&mut valid);
        let mut malformed =
            typed_trust_vc_obligation(ObligationKind::MemorySafety, "memory.isolated.malformed");
        malformed.required_strength =
            Some(ProofStrength::certified(ReasoningKind::OwnershipAnalysis));
        malformed.contract_id = None;
        malformed.metadata.push(MetadataEntry {
            key: TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY.to_string(),
            value: "{not json".to_string(),
        });
        let bundle = bundle_with(vec![valid.clone(), malformed.clone()]);

        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| count.set(0));
        let evidence = TrustVcVerificationEngine::new()
            .evidence_from_release_admitted_direct_mir_memory_with_deadline(
                &bundle,
                &[valid, malformed],
                None,
            );
        TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| assert_eq!(count.get(), 1));
        assert_eq!(evidence.len(), 2);
        assert_eq!(evidence[0].status, EvidenceStatus::Proved, "{:#?}", evidence[0]);
        assert_eq!(evidence[1].status, EvidenceStatus::Unsupported);
        assert!(
            evidence[1]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("invalid MIR memory proof-unit JSON"))
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn native_trust_ir_proof_evidence_rejects_metadata_only_mir_memory_payload() {
        let mut obligation = obligation(ObligationKind::MemorySafety, "memory.metadata_only");
        obligation.required_strength = None;
        obligation.contract_id = None;
        obligation.metadata.push(MetadataEntry {
            key: TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY.to_string(),
            value: direct_mir_memory_unit_payload("memory.metadata_only").to_string(),
        });

        let error = trust_vc_validate_structured_direct_mir_memory_obligation_metadata(&obligation)
            .expect_err("metadata-only MIR memory JSON must not enter the direct lane");
        assert!(
            error
                .to_string()
                .contains("structured trust_vc MIR memory proof-unit metadata requires"),
            "unexpected metadata-only rejection reason: {error}"
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn direct_mir_memory_multi_obligation_reports_remain_non_authoritative() {
        let mut first = typed_trust_vc_obligation(ObligationKind::MemorySafety, "memory.first");
        first.required_strength = None;
        first.contract_id = Some("contract-memory".to_string());
        let mut second = typed_trust_vc_obligation(ObligationKind::MemorySafety, "memory.second");
        second.required_strength = None;
        second.contract_id = Some("contract-memory".to_string());

        let mut unit_payload = direct_mir_memory_unit_payload("memory.first");
        let obligations = unit_payload
            .get_mut("obligations")
            .and_then(JsonValue::as_array_mut)
            .expect("direct MIR fixture has obligations");
        let mut second_payload = obligations[0].clone();
        second_payload
            .as_object_mut()
            .expect("direct MIR obligation is an object")
            .insert("id".to_string(), json!("memory.second"));
        obligations.push(second_payload);

        let mut bundle = bundle_with(vec![first, second]);
        bundle.contracts.push(TrustContract {
            contract_id: "contract-memory".to_string(),
            kind: ContractKind::Asserts,
            predicate: ContractPredicate::MemoryIr {
                schema: TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_VERSION.to_string(),
                value: unit_payload,
            },
            source: SourceLocation::default(),
            metadata: Vec::new(),
        });
        let engine = TrustVcVerificationEngine::new();

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 2);
        let first = evidence
            .iter()
            .find(|item| item.obligation_id == "memory.first")
            .expect("first obligation evidence exists");
        assert_eq!(first.status, EvidenceStatus::Unsupported, "{first:?}");
        assert!(first.proof_strength.is_none());
        assert!(first.artifacts.is_empty());

        let second = evidence
            .iter()
            .find(|item| item.obligation_id == "memory.second")
            .expect("second obligation evidence exists");
        assert_eq!(second.status, EvidenceStatus::Unsupported, "{second:?}");
        assert!(second.proof_strength.is_none());
        assert!(second.artifacts.is_empty());
        assert!(
            first
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains(TRUST_VC_MIR_MEMORY_PROOF_UNIT_REQUIRED))
        );
        assert!(
            second
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains(TRUST_VC_MIR_MEMORY_PROOF_UNIT_REQUIRED))
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn direct_mir_memory_unit_rejects_unsupported_heap_pointer_details() {
        let mut obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, "memory");
        obligation.required_strength = None;
        obligation.contract_id = Some("contract-memory".to_string());
        let mut unit_payload = direct_mir_memory_unit_payload("memory");
        unit_payload
            .as_object_mut()
            .expect("unit payload is an object")
            .insert("heap_allocations".to_string(), json!([]));
        let mut bundle = bundle_with(vec![obligation]);
        bundle.contracts.push(direct_mir_memory_contract("memory", unit_payload));
        let engine = TrustVcVerificationEngine::new();

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].artifacts.is_empty());
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains(TRUST_VC_MIR_MEMORY_PROOF_UNIT_REQUIRED))
        );
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn direct_mir_memory_unit_rejects_invalid_metadata_json_for_owned_obligation_kinds() {
        let engine = TrustVcVerificationEngine::new();

        for (kind, obligation_id) in [
            (ObligationKind::MemorySafety, "memory.invalid_json"),
            (ObligationKind::Ownership, "ownership.invalid_json"),
            (ObligationKind::BoundsCheck, "bounds.invalid_json"),
        ] {
            let mut obligation = typed_trust_vc_obligation(kind, obligation_id);
            obligation.required_strength = None;
            obligation.contract_id = None;
            obligation.metadata.push(MetadataEntry {
                key: TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY.to_string(),
                value: "{not json".to_string(),
            });
            let bundle = bundle_with(vec![obligation.clone()]);

            TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| count.set(0));
            let evidence = engine.evidence_from_release_admitted_direct_mir_memory_with_deadline(
                &bundle,
                &[obligation],
                None,
            );
            TEST_DIRECT_MIR_MEMORY_SOLVE_COUNT.with(|count| assert_eq!(count.get(), 0));

            assert_eq!(evidence.len(), 1);
            assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
            assert!(evidence[0].proof_strength.is_none());
            assert!(evidence[0].artifacts.is_empty());
            assert!(
                evidence[0]
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.contains("invalid MIR memory proof-unit JSON")),
                "missing invalid JSON diagnostic for {obligation_id}: {:?}",
                evidence[0].diagnostics
            );
        }
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn direct_mir_memory_unit_rejects_unsupported_contract_schema_for_owned_obligation_kinds() {
        let engine = TrustVcVerificationEngine::new();

        for (kind, obligation_id) in [
            (ObligationKind::MemorySafety, "memory.future_schema"),
            (ObligationKind::Ownership, "ownership.future_schema"),
            (ObligationKind::BoundsCheck, "bounds.future_schema"),
        ] {
            let contract_id = format!("contract-{obligation_id}");
            let mut obligation = typed_trust_vc_obligation(kind, obligation_id);
            obligation.required_strength = None;
            obligation.contract_id = Some(contract_id.clone());
            let mut bundle = bundle_with(vec![obligation]);
            bundle.contracts.push(TrustContract {
                contract_id,
                kind: ContractKind::Asserts,
                predicate: ContractPredicate::MemoryIr {
                    schema: "trust_vc.mir_memory_proof_unit.future".to_string(),
                    value: json!({ "obligations": [] }),
                },
                source: SourceLocation::default(),
                metadata: Vec::new(),
            });

            let evidence = engine.verify(&bundle, &bundle.obligations);

            assert_eq!(evidence.len(), 1);
            assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
            assert!(evidence[0].proof_strength.is_none());
            assert!(evidence[0].artifacts.is_empty());
            assert!(
                evidence[0]
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.contains(TRUST_VC_MIR_MEMORY_PROOF_UNIT_REQUIRED))
            );
        }
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn direct_mir_memory_unit_rejects_mismatched_obligation_for_owned_obligation_kinds() {
        let engine = TrustVcVerificationEngine::new();

        for (kind, obligation_id) in [
            (ObligationKind::MemorySafety, "memory.expected"),
            (ObligationKind::Ownership, "ownership.expected"),
            (ObligationKind::BoundsCheck, "bounds.expected"),
        ] {
            let contract_id = format!("contract-{obligation_id}");
            let mut obligation = typed_trust_vc_obligation(kind, obligation_id);
            obligation.required_strength = None;
            obligation.contract_id = Some(contract_id.clone());
            let mut bundle = bundle_with(vec![obligation]);
            bundle.contracts.push(TrustContract {
                contract_id,
                kind: ContractKind::Asserts,
                predicate: ContractPredicate::MemoryIr {
                    schema: TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_VERSION.to_string(),
                    value: direct_mir_memory_unit_payload("different.obligation"),
                },
                source: SourceLocation::default(),
                metadata: Vec::new(),
            });

            let evidence = engine.verify(&bundle, &bundle.obligations);

            assert_eq!(evidence.len(), 1);
            assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
            assert!(evidence[0].proof_strength.is_none());
            assert!(evidence[0].artifacts.is_empty());
            assert!(
                evidence[0]
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.contains(TRUST_VC_MIR_MEMORY_PROOF_UNIT_REQUIRED))
            );
        }
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn direct_mir_memory_unit_rejects_empty_ownership_context() {
        let mut obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, "memory");
        obligation.required_strength = None;
        obligation.contract_id = Some("contract-memory".to_string());
        let mut unit_payload = direct_mir_memory_unit_payload("memory");
        unit_payload
            .get_mut("native_context")
            .and_then(JsonValue::as_object_mut)
            .expect("unit payload has native context")
            .insert("ownership".to_string(), json!({}));
        let mut bundle = bundle_with(vec![obligation]);
        bundle.contracts.push(direct_mir_memory_contract("memory", unit_payload));
        let engine = TrustVcVerificationEngine::new();

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(evidence[0].artifacts.is_empty());
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("typed ownership and borrow state")),
            "missing empty ownership diagnostic: {:?}",
            evidence[0].diagnostics
        );
    }

    #[test]
    fn engine_rejects_invalid_native_trust_vc_report_fail_closed() {
        let mut obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, "memory");
        obligation.required_strength = None;
        obligation.contract_id = None;
        let bundle = bundle_with(vec![obligation]);
        let mut artifact = native_trust_vc_artifact_for("memory");
        let native_evidence = native_ownership_memory_evidence("memory", &artifact);
        artifact.payload.push_str(" tampered");
        let report = TrustVcNativeUnitReport::new("crate::memory")
            .with_proof_evidence(native_evidence)
            .with_proof_artifact(artifact);
        let engine = TrustVcVerificationEngine::new().with_native_unit_reports(vec![report]);

        let result = engine.verify_with_context(
            &bundle,
            &bundle.obligations,
            &VerifierExecutionContext::new("trust-vc-native-rejected"),
        );

        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
        assert_eq!(result.summary.unsupported, 1);
        assert_eq!(result.evidence[0].status, EvidenceStatus::Unsupported);
        assert!(result.evidence[0].proof_strength.is_none());
        assert!(result.evidence[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("native trust_vc unit report rejected")
                && diagnostic.contains("payload digest mismatch")
        }));
    }

    #[test]
    fn native_trust_vc_lowering_artifacts_are_deterministic_and_hash_addressed() {
        let mut obligation = typed_trust_vc_obligation(ObligationKind::Ownership, "ownership");
        obligation.required_strength = None;
        obligation.contract_id = None;
        let bundle = bundle_with(vec![obligation.clone()]);

        let artifacts = trust_vc_native_report_artifacts_from_bundle(&bundle, &obligation)
            .expect("typed trust_vc obligation lowers to audit artifacts");
        let again = trust_vc_native_report_artifacts_from_bundle(&bundle, &obligation)
            .expect("lowering is deterministic");

        assert_eq!(artifacts, again);
        for artifact in [artifacts.normalized_obligation, artifacts.engine_input] {
            assert_eq!(artifact.hash.algorithm, "sha256");
            assert_eq!(artifact.hash.value.len(), 64);
            assert!(artifact.hash.value.bytes().all(|byte| byte.is_ascii_hexdigit()));
            assert!(artifact.uri.starts_with(TRUST_VC_NATIVE_LOWERING_ARTIFACT_URI_PREFIX));
        }
    }

    #[test]
    fn native_trust_vc_report_rejects_unlinked_proof_artifact_id() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = native_trust_vc_artifact();
        let native_evidence = native_contract_frame_evidence("post", &artifact)
            .with_proof_artifact_id(
                "trust-vc-proof-certificate:v1:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            );

        let err = trust_vc_obligation_evidence_from_native_report(
            &engine,
            &bundle,
            &obligation,
            &native_evidence,
            &artifact,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::ReplayableCertificate,
        )
        .expect_err("mismatched artifact ids fail closed");

        assert!(matches!(err, TrustVcNativeReportConversionError::ProofArtifactIdMismatch { .. }));
    }

    #[test]
    fn native_trust_vc_report_rejects_precondition_bound_only_as_assumption() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_contract_obligation(ObligationKind::Precondition, "pre");
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = native_trust_vc_artifact();
        let native_evidence = native_contract_frame_evidence("pre", &artifact);

        let err = trust_vc_obligation_evidence_from_native_report(
            &engine,
            &bundle,
            &obligation,
            &native_evidence,
            &artifact,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::ReplayableCertificate,
        )
        .expect_err("precondition assumptions are not discharged proof artifacts");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::ProofArtifactAssumesRequestedObligation { .. }
        ));
    }

    #[test]
    fn native_trust_vc_report_rejects_payload_digest_mismatch() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        let bundle = bundle_with(vec![obligation.clone()]);
        let mut artifact = native_trust_vc_artifact();
        artifact.payload.push_str(" tampered");
        let native_evidence = native_contract_frame_evidence("post", &artifact);

        let err = trust_vc_obligation_evidence_from_native_report(
            &engine,
            &bundle,
            &obligation,
            &native_evidence,
            &artifact,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::ReplayableCertificate,
        )
        .expect_err("tampered payload fails closed");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::ProofArtifactPayloadDigestMismatch { .. }
        ));
    }

    #[test]
    fn native_trust_vc_report_rejects_unchecked_certificate_payload() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = TrustVcNativeReplayableProofArtifact::alethe("(unchecked alethe payload)")
            .with_assertion_obligation_ids(vec!["post".to_string()]);
        let native_evidence = native_contract_frame_evidence("post", &artifact);

        let err = trust_vc_obligation_evidence_from_native_report(
            &engine,
            &bundle,
            &obligation,
            &native_evidence,
            &artifact,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::ReplayableCertificate,
        )
        .expect_err("unchecked replayable payloads fail closed");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::UncheckedProofCertificate { .. }
        ));
    }

    #[test]
    fn native_trust_vc_report_rejects_legacy_source_text_evidence() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = native_trust_vc_artifact();
        let native_evidence = TrustVcNativeTrustProofEvidence {
            proof_artifact_id: Some(artifact.artifact_id.clone()),
            ..TrustVcNativeTrustProofEvidence::legacy_source_text("post")
        };

        let err = trust_vc_obligation_evidence_from_native_report(
            &engine,
            &bundle,
            &obligation,
            &native_evidence,
            &artifact,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::ReplayableCertificate,
        )
        .expect_err("legacy trust_vc source text evidence fails closed");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::UnsupportedEvidenceSource { .. }
        ));
    }

    #[cfg(feature = "trust-build")]
    #[test]
    fn full_verification_request_dto_does_not_carry_proof_authority() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = native_trust_vc_artifact();
        let request = FullVerificationRequest::new()
            .with_evidence(TypedProofObligation::ensures("post", TrustVcExpr::BoolLit(true)));

        let report = trust_vc_native_unit_report_from_full_verification_request(
            "crate::full",
            request,
            artifact,
        )
        .expect("typed full-verification request converts to native report");
        let err = trust_vc_obligation_evidence_from_native_unit_report(
            &engine,
            &bundle,
            &obligation,
            &report,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::StrictReplayableCertificate,
        )
        .expect_err("typed obligation DTO still lacks an opaque replay receipt");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::UncheckedProofCertificate { .. }
        ));
    }

    #[test]
    fn native_trust_vc_report_rejects_typed_compatibility_profile() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = native_trust_vc_artifact();
        let native_evidence = native_contract_frame_evidence("post", &artifact)
            .with_evidence_profile(TrustVcNativeProofEvidenceProfile::TypedCompatibility);

        let err = trust_vc_obligation_evidence_from_native_report(
            &engine,
            &bundle,
            &obligation,
            &native_evidence,
            &artifact,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::ReplayableCertificate,
        )
        .expect_err("typed compatibility evidence must not count as static proof");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::UnsupportedEvidenceProfile {
                profile: TrustVcNativeProofEvidenceProfile::TypedCompatibility,
                ..
            }
        ));
    }

    #[test]
    fn native_trust_vc_evidence_profiles_cannot_cross_contract_ownership_boundary() {
        let artifact = native_trust_vc_artifact();

        let mut memory = typed_trust_vc_obligation(ObligationKind::MemorySafety, "memory");
        memory.contract_id = None;
        let contract_frame = native_contract_frame_evidence("memory", &artifact);
        let err = validate_trust_vc_native_static_proof_profile(&memory, &contract_frame)
            .expect_err("contract-frame evidence cannot masquerade as a MemorySafety proof");
        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::EvidenceProfileMismatch {
                obligation_kind: ObligationKind::MemorySafety,
                profile: TrustVcNativeProofEvidenceProfile::TypedContractFrame,
                ..
            }
        ));

        let postcondition =
            typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        let ownership_memory = native_ownership_memory_evidence("post", &artifact);
        let err = validate_trust_vc_native_static_proof_profile(&postcondition, &ownership_memory)
            .expect_err("ownership-memory evidence cannot masquerade as a contract proof");
        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::EvidenceProfileMismatch {
                obligation_kind: ObligationKind::Postcondition,
                profile: TrustVcNativeProofEvidenceProfile::OwnershipMemory,
                ..
            }
        ));
    }

    #[test]
    fn native_trust_vc_report_rejects_assumed_evidence_as_static_proof() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = native_trust_vc_artifact();
        let native_evidence = native_contract_frame_evidence("post", &artifact)
            .with_assurance_level(TrustVcNativeAssuranceLevel::AssumedEvidence);

        let err = trust_vc_obligation_evidence_from_native_report(
            &engine,
            &bundle,
            &obligation,
            &native_evidence,
            &artifact,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::ReplayableCertificate,
        )
        .expect_err("assumed trust_vc evidence must not count as static proof");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::UnsupportedAssuranceLevel {
                assurance_level: TrustVcNativeAssuranceLevel::AssumedEvidence,
                ..
            }
        ));
    }

    #[test]
    fn native_trust_vc_report_rejects_missing_typed_trustexpr_evidence() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = native_trust_vc_artifact();
        let mut native_evidence = native_contract_frame_evidence("post", &artifact);
        native_evidence.typed_expr = None;

        let err = trust_vc_obligation_evidence_from_native_report(
            &engine,
            &bundle,
            &obligation,
            &native_evidence,
            &artifact,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::ReplayableCertificate,
        )
        .expect_err("TypedTrustVcExpr evidence without typed_expr payload must fail closed");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::MissingTypedTrustExprEvidence { .. }
        ));
    }

    #[test]
    fn native_trust_vc_report_rejects_malformed_typed_trustexpr_evidence() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = native_trust_vc_artifact();
        let native_evidence =
            native_contract_frame_evidence("post", &artifact).with_typed_expr(json!({
                "diagnostic": "result >= old(x)",
            }));

        let err = trust_vc_obligation_evidence_from_native_report(
            &engine,
            &bundle,
            &obligation,
            &native_evidence,
            &artifact,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::ReplayableCertificate,
        )
        .expect_err("typed expression payload without a TrustExpr kind must fail closed");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::InvalidTypedTrustExprEvidence { .. }
        ));
    }

    #[test]
    fn native_trust_vc_report_rejects_structured_payload_without_replay_receipt() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = native_trust_vc_artifact();
        let native_evidence =
            native_contract_frame_evidence("post", &artifact).with_typed_expr(json!({
                "kind": "bool_literal",
                "value": true,
            }));

        let err = trust_vc_obligation_evidence_from_native_report(
            &engine,
            &bundle,
            &obligation,
            &native_evidence,
            &artifact,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::ReplayableCertificate,
        )
        .expect_err("typed payload plus producer booleans is not a replay receipt");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::UncheckedProofCertificate { .. }
        ));
    }

    #[test]
    fn native_trust_vc_report_rejects_mismatched_typed_trustexpr_evidence_identity() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = native_trust_vc_artifact();
        let native_evidence =
            native_contract_frame_evidence("post", &artifact).with_typed_expr(json!({
                "kind": "bool_literal",
                "value": true,
                "tRust_obligation_id": "other-post",
            }));

        let err = trust_vc_obligation_evidence_from_native_report(
            &engine,
            &bundle,
            &obligation,
            &native_evidence,
            &artifact,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::ReplayableCertificate,
        )
        .expect_err("typed expression payload bound to another obligation must fail closed");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::InvalidTypedTrustExprEvidence { .. }
        ));
        assert!(err.to_string().contains("matching the obligation"));
    }

    #[test]
    fn native_trust_vc_report_rejects_placeholder_typed_trustexpr_evidence() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = native_trust_vc_artifact();
        let native_evidence =
            native_contract_frame_evidence("post", &artifact).with_typed_expr(json!({
                "kind": "placeholder",
                "text": "todo: proof omitted",
            }));

        let err = trust_vc_obligation_evidence_from_native_report(
            &engine,
            &bundle,
            &obligation,
            &native_evidence,
            &artifact,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::ReplayableCertificate,
        )
        .expect_err("placeholder typed expression payload must fail closed");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::InvalidTypedTrustExprEvidence { .. }
        ));
        assert!(err.to_string().contains("placeholder"));
    }

    #[test]
    fn native_trust_vc_ownership_profile_still_requires_replay_receipt() {
        let engine = TrustVcVerificationEngine::new();
        let mut obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, "memory");
        obligation.required_strength =
            Some(ProofStrength::certified(ReasoningKind::OwnershipAnalysis));
        obligation.contract_id = None;
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = native_trust_vc_artifact_for("memory");
        let report = TrustVcNativeUnitReport::new("crate::memory")
            .with_proof_evidence(native_ownership_memory_evidence("memory", &artifact))
            .with_proof_artifact(artifact);

        let err = trust_vc_obligation_evidence_from_native_unit_report(
            &engine,
            &bundle,
            &obligation,
            &report,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::StrictReplayableCertificate,
        )
        .expect_err("ownership labels do not replace proof replay");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::UncheckedProofCertificate { .. }
        ));
    }

    #[test]
    fn native_trust_vc_report_rejects_missing_supplemental_artifact_kinds() {
        let err = TrustVcNativeReportArtifacts::new(
            native_supplemental_artifact(EvidenceArtifactKind::ProofCheckReport, "wrong"),
            native_supplemental_artifact(EvidenceArtifactKind::EngineInput, "native-input"),
        )
        .expect_err("wrong normalized artifact kind fails closed");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::InvalidSupplementalArtifactKind {
                expected: EvidenceArtifactKind::NormalizedObligation,
                actual: EvidenceArtifactKind::ProofCheckReport,
                ..
            }
        ));
    }

    #[test]
    fn native_trust_vc_report_rejects_placeholder_supplemental_artifact_hashes() {
        let err = TrustVcNativeReportArtifacts::new(
            EvidenceArtifact {
                kind: EvidenceArtifactKind::NormalizedObligation,
                uri: format!(
                    "{TRUST_VC_NATIVE_LOWERING_ARTIFACT_URI_PREFIX}bundle-trust-vc/typed-obligation.json"
                ),
                hash: ArtifactHash {
                    algorithm: "sha256".to_string(),
                    value: "placeholder".to_string(),
                },
                materialization: None,
            },
            native_supplemental_artifact(EvidenceArtifactKind::EngineInput, "native-input"),
        )
        .expect_err("placeholder normalized artifact hash fails closed");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::InvalidSupplementalArtifactHash {
                label: "normalized_obligation",
                ..
            }
        ));
    }

    #[test]
    fn native_trust_vc_report_rejects_non_deterministic_supplemental_artifact_binding() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = native_trust_vc_artifact();
        let native_evidence = native_contract_frame_evidence("post", &artifact);
        let mut supplemental = native_supplemental_artifacts(&bundle, &obligation);
        supplemental.normalized_obligation.hash.value =
            stable_sha256_hex(b"placeholder typed proof");

        let err = trust_vc_obligation_evidence_from_native_report(
            &engine,
            &bundle,
            &obligation,
            &native_evidence,
            &artifact,
            supplemental,
            TrustVcNativeProofCertificatePolicy::ReplayableCertificate,
        )
        .expect_err("non-deterministic supplemental artifacts fail closed");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::SupplementalArtifactBindingMismatch {
                label: "normalized_obligation",
                ..
            }
        ));
    }

    #[test]
    fn strict_native_trust_vc_policy_requires_strict_checked_artifact() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "post");
        let bundle = bundle_with(vec![obligation.clone()]);
        let artifact = TrustVcNativeReplayableProofArtifact::alethe("(proof trust_vc unit post)")
            .with_kernel_verified(true)
            .with_assertion_obligation_ids(vec!["post".to_string()]);
        let native_evidence = native_contract_frame_evidence("post", &artifact);

        let err = trust_vc_obligation_evidence_from_native_report(
            &engine,
            &bundle,
            &obligation,
            &native_evidence,
            &artifact,
            native_supplemental_artifacts(&bundle, &obligation),
            TrustVcNativeProofCertificatePolicy::StrictReplayableCertificate,
        )
        .expect_err("strict policy requires strict checker acceptance");

        assert!(matches!(
            err,
            TrustVcNativeReportConversionError::StrictProofCertificateRequired { .. }
        ));
    }

    #[test]
    fn supports_only_trust_vc_owned_obligations() {
        let engine = TrustVcVerificationEngine::new();
        for kind in trust_vc_owned_obligation_kinds() {
            let support = engine.supports(&obligation(kind, "owned"));
            assert!(support.is_supported(), "expected trust_vc to own {support:?}");
            #[cfg(feature = "trust-build")]
            assert_eq!(support, SupportLevel::Supported);
            #[cfg(not(feature = "trust-build"))]
            assert_eq!(
                support,
                SupportLevel::Experimental { reason: TRUST_VC_BUILD_FEATURE_REQUIRED.to_string() }
            );
        }

        assert!(engine.manifest().capabilities.iter().all(|capability| {
            #[cfg(feature = "trust-build")]
            {
                capability.support == SupportLevel::Supported
            }
            #[cfg(not(feature = "trust-build"))]
            {
                matches!(capability.support, SupportLevel::Experimental { .. })
            }
        }));

        let support = engine.supports(&obligation(ObligationKind::ArithmeticSafety, "arith"));
        assert!(matches!(support, SupportLevel::Unsupported { .. }));

        let support = engine.supports(&obligation(ObligationKind::Termination, "term"));
        assert!(matches!(support, SupportLevel::Unsupported { .. }));
    }

    #[test]
    fn owned_obligations_return_unsupported_until_native_proof_exists() {
        let engine = TrustVcVerificationEngine::new();
        let bundle = bundle_with(vec![
            obligation(ObligationKind::MemorySafety, "memory"),
            obligation(ObligationKind::Ownership, "ownership"),
            obligation(ObligationKind::BoundsCheck, "bounds"),
        ]);

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 3);
        for item in evidence {
            assert_eq!(item.engine.name, TRUST_VC_ENGINE_NAME);
            assert_eq!(item.status, EvidenceStatus::Unsupported);
            assert!(item.proof_strength.is_none());
            assert!(item.artifacts.is_empty());
            assert!(
                item.diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.contains(TRUST_VC_TYPED_PROOF_INPUT_REQUIRED)),
                "missing typed-input diagnostic: {:?}",
                item.diagnostics
            );
            assert!(
                item.diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.contains("ConditionOrigin::TypedTrustVcExpr")),
                "missing typed TrustVcExpr diagnostic: {:?}",
                item.diagnostics
            );
            assert!(
                item.diagnostics.iter().any(
                    |diagnostic| diagnostic.contains("proof_strength is intentionally omitted")
                ),
                "missing omitted proof_strength diagnostic: {:?}",
                item.diagnostics
            );
        }
    }

    #[test]
    fn attribute_presence_is_never_proof_evidence() {
        let engine = TrustVcVerificationEngine::new();
        let bundle = bundle_with(vec![obligation(ObligationKind::Precondition, "pre")]);

        let result = engine.verify_with_context(
            &bundle,
            &bundle.obligations,
            &VerifierExecutionContext::new("trust-vc-attrs"),
        );

        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
        assert_eq!(result.summary.proved, 0);
        assert_eq!(result.summary.unsupported, 1);
        assert!(!result.is_fully_proved());
        assert_eq!(result.evidence[0].status, EvidenceStatus::Unsupported);
        assert!(result.evidence[0].proof_strength.is_none());
        assert!(
            result.evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("presence is never trust_vc proof evidence"))
        );
    }

    #[test]
    fn string_backed_memory_obligation_requires_typed_context_and_no_proof_strength() {
        let engine = TrustVcVerificationEngine::new();
        let bundle = bundle_with(vec![obligation(ObligationKind::MemorySafety, "memory")]);

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("typed ownership and borrow state"))
        );
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("context-free public TrustObligation"))
        );
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("string-backed TrustExpr"))
        );
    }

    #[test]
    fn context_free_ownership_obligation_requires_full_verification_evidence() {
        let engine = TrustVcVerificationEngine::new();
        let bundle = bundle_with(vec![obligation(ObligationKind::Ownership, "ownership")]);

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("TypedProofObligation"))
        );
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("typed ownership and borrow state"))
        );
    }

    #[test]
    fn accepts_typed_trust_vc_proof_evidence_shape() {
        let engine = TrustVcVerificationEngine::new();
        let mut obligation = typed_trust_vc_obligation(ObligationKind::Ownership, "ownership");
        obligation.required_strength =
            Some(ProofStrength::certified(ReasoningKind::OwnershipAnalysis));
        let bundle = bundle_with(vec![obligation.clone()]);
        let evidence = proved_trust_vc_evidence(
            &engine,
            &obligation,
            replayable_certificate_artifacts(&obligation.obligation_id),
        );

        assert!(evidence.is_unbounded_proof());
        assert!(accepts_trust_vc_proof_evidence_shape(&obligation, &evidence));
        assert!(trust_vc_proof_evidence_shape_diagnostics(&obligation, &evidence).is_empty());

        let result = VerificationRunResult::from_evidence(
            VerifierExecutionContext::new("typed-trust-vc-proof").snapshot(),
            &bundle,
            engine.manifest().clone(),
            &bundle.obligations,
            vec![evidence],
        );
        assert_eq!(result.status, VerificationRunStatus::Proved);
        assert_eq!(result.summary.proved, 1);
        assert_eq!(result.to_manifest().accepted_evidence.len(), 1);
    }

    #[test]
    fn native_trust_ir_certificate_shape_requires_public_request_proof_identity() {
        let engine = TrustVcVerificationEngine::new();
        let mut obligation = typed_trust_vc_obligation(ObligationKind::Ownership, "ownership");
        clear_native_trust_ir_bundle_metadata(&mut obligation);
        let evidence = proved_trust_vc_evidence(
            &engine,
            &obligation,
            native_trust_ir_certificate_artifacts(&obligation.obligation_id),
        );

        assert!(!accepts_trust_vc_proof_evidence_shape(&obligation, &evidence));
        let diagnostics = trust_vc_proof_evidence_shape_diagnostics(&obligation, &evidence);
        assert!(
            diagnostics.iter().any(|diagnostic| {
                diagnostic.contains(TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY)
                    || diagnostic.contains(TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY)
            }),
            "native Tmir shape accepted without request/proof metadata: {diagnostics:?}"
        );
    }

    #[test]
    fn native_trust_ir_certificate_shape_rejects_sparse_public_import_metadata() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_obligation(ObligationKind::Ownership, "ownership");
        let evidence = proved_trust_vc_evidence(
            &engine,
            &obligation,
            native_trust_ir_certificate_artifacts(&obligation.obligation_id),
        );

        let diagnostics = trust_vc_proof_evidence_shape_diagnostics(&obligation, &evidence);
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic
                    .contains(TRUST_TRUST_IR_NATIVE_ASSERTION_ID_METADATA_KEY)),
            "native Tmir shape accepted sparse metadata: {diagnostics:?}"
        );
    }

    #[test]
    fn native_trust_ir_certificate_shape_accepts_complete_public_import_metadata() {
        let engine = TrustVcVerificationEngine::new();
        let mut obligation = typed_trust_vc_obligation(ObligationKind::Ownership, "ownership");
        obligation.required_strength = None;
        obligation.metadata.extend(complete_native_trust_ir_import_metadata());
        let evidence = proved_trust_vc_evidence(
            &engine,
            &obligation,
            native_trust_ir_certificate_artifacts(&obligation.obligation_id),
        );

        let diagnostics = trust_vc_proof_evidence_shape_diagnostics(&obligation, &evidence);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn native_trust_ir_certificate_shape_rejects_legacy_digest_authority() {
        let engine = TrustVcVerificationEngine::new();
        let mut obligation = typed_trust_vc_obligation(ObligationKind::Ownership, "ownership");
        obligation.required_strength = None;
        obligation.metadata.extend(complete_native_trust_ir_import_metadata());
        obligation
            .metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_TRUST_IR_NATIVE_TRUST_IR_MODULE_DIGEST_METADATA_KEY)
            .expect("complete native import metadata contains the module digest")
            .value = format!("trust_ir-stable-v1:{}", "a".repeat(64));
        let evidence = proved_trust_vc_evidence(
            &engine,
            &obligation,
            native_trust_ir_certificate_artifacts(&obligation.obligation_id),
        );

        let diagnostics = trust_vc_proof_evidence_shape_diagnostics(&obligation, &evidence);
        assert!(!accepts_trust_vc_proof_evidence_shape(&obligation, &evidence));
        assert!(
            diagnostics.iter().any(|diagnostic| {
                diagnostic.contains(TRUST_TRUST_IR_NATIVE_TRUST_IR_MODULE_DIGEST_METADATA_KEY)
                    && diagnostic.contains("must be a SHA-256 digest")
            }),
            "legacy digest label reached native certificate acceptance: {diagnostics:?}"
        );
    }

    #[test]
    fn rejects_typed_trust_vc_shape_with_placeholder_supplemental_artifact() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_obligation(ObligationKind::Ownership, "ownership");
        let mut artifacts = replayable_certificate_artifacts(&obligation.obligation_id);
        let normalized = artifacts
            .iter_mut()
            .find(|artifact| artifact.kind == EvidenceArtifactKind::NormalizedObligation)
            .expect("normalized artifact exists");
        normalized.hash.value = "placeholder".to_string();
        let evidence = proved_trust_vc_evidence(&engine, &obligation, artifacts);

        assert!(!accepts_trust_vc_proof_evidence_shape(&obligation, &evidence));
        assert!(
            trust_vc_proof_evidence_shape_diagnostics(&obligation, &evidence)
                .iter()
                .any(|diagnostic| diagnostic.contains("deterministic normalized typed obligation"))
        );
    }

    #[test]
    fn rejects_sound_trust_vc_shape_without_checked_certificate_assurance() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_obligation(ObligationKind::Ownership, "ownership");
        let mut evidence = proved_trust_vc_evidence(
            &engine,
            &obligation,
            replayable_certificate_artifacts(&obligation.obligation_id),
        );
        evidence.proof_strength = Some(ProofStrength::deductive());

        assert!(!accepts_trust_vc_proof_evidence_shape(&obligation, &evidence));
        assert!(
            trust_vc_proof_evidence_shape_diagnostics(&obligation, &evidence)
                .iter()
                .any(|diagnostic| diagnostic.contains("certified ownership-analysis"))
        );
    }

    #[test]
    fn accepts_typed_contract_frame_result_evidence_shape() {
        let engine = TrustVcVerificationEngine::new();
        let obligation =
            typed_trust_vc_contract_obligation(ObligationKind::Postcondition, "ensures-result");
        let mut bundle = bundle_with(vec![obligation.clone()]);
        bundle.metadata.push(trust_vc_typed_old_snapshot_metadata());
        let evidence = proved_trust_vc_evidence(
            &engine,
            &obligation,
            replayable_certificate_artifacts(&obligation.obligation_id),
        );

        assert!(evidence.is_unbounded_proof());
        assert!(accepts_trust_vc_proof_evidence_shape(&obligation, &evidence));
        assert!(trust_vc_proof_evidence_shape_diagnostics(&obligation, &evidence).is_empty());

        let result = VerificationRunResult::from_evidence(
            VerifierExecutionContext::new("typed-trust-vc-contract-frame").snapshot(),
            &bundle,
            engine.manifest().clone(),
            &bundle.obligations,
            vec![evidence],
        );
        assert_eq!(result.status, VerificationRunStatus::Proved);
        assert_eq!(result.summary.proved, 1);
    }

    #[test]
    fn contract_frame_evidence_requires_frame_metadata_not_ownership_context() {
        let engine = TrustVcVerificationEngine::new();
        let mut obligation = obligation(ObligationKind::Postcondition, "ensures-result");
        obligation.metadata = trust_vc_typed_contract_frame_metadata();
        let evidence = proved_trust_vc_evidence(
            &engine,
            &obligation,
            replayable_certificate_artifacts(&obligation.obligation_id),
        );

        assert!(!accepts_trust_vc_proof_evidence_shape(&obligation, &evidence));

        let diagnostics = trust_vc_proof_evidence_shape_diagnostics(&obligation, &evidence);
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("trust_vc.contract_frame.result=typed")),
            "missing result-binding diagnostic: {diagnostics:?}"
        );
        assert!(
            diagnostics.iter().all(|diagnostic| !diagnostic.contains("ownership_context=typed")),
            "contract-frame diagnostics must not require ownership context: {diagnostics:?}"
        );
    }

    #[test]
    fn typed_requires_contract_frame_evidence_does_not_require_result_binding() {
        let engine = TrustVcVerificationEngine::new();
        let obligation =
            typed_trust_vc_contract_obligation(ObligationKind::Precondition, "requires-input");
        let evidence = proved_trust_vc_evidence(
            &engine,
            &obligation,
            replayable_certificate_artifacts(&obligation.obligation_id),
        );

        assert!(accepts_trust_vc_proof_evidence_shape(&obligation, &evidence));
        assert!(
            trust_vc_proof_evidence_shape_diagnostics(&obligation, &evidence)
                .iter()
                .all(|diagnostic| !diagnostic.contains("trust_vc.contract_frame.result")),
        );
    }

    #[test]
    fn rejects_string_context_free_trust_vc_proof_shape_even_with_generic_artifacts() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = obligation(ObligationKind::MemorySafety, "memory");
        let evidence = proved_trust_vc_evidence(
            &engine,
            &obligation,
            replayable_certificate_artifacts(&obligation.obligation_id),
        );

        assert!(evidence.is_unbounded_proof());
        assert!(!accepts_trust_vc_proof_evidence_shape(&obligation, &evidence));

        let diagnostics = trust_vc_proof_evidence_shape_diagnostics(&obligation, &evidence);
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("trust_vc.condition_origin=TypedTrustVcExpr")),
            "missing typed condition-origin diagnostic: {diagnostics:?}"
        );
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic
                    .contains("trust_vc.proof_obligation=TypedProofObligation")),
            "missing typed proof-obligation diagnostic: {diagnostics:?}"
        );
        assert!(
            diagnostics.iter().any(|diagnostic| diagnostic.contains("ownership_context=typed")),
            "missing typed ownership-context diagnostic: {diagnostics:?}"
        );
    }

    #[test]
    fn rejects_typed_trust_vc_shape_without_replay_or_check_artifact() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, "memory");
        let evidence = proved_trust_vc_evidence(
            &engine,
            &obligation,
            vec![
                trust_vc_artifact(EvidenceArtifactKind::NormalizedObligation, "typed-obligation"),
                trust_vc_artifact(EvidenceArtifactKind::EngineInput, "native-input"),
            ],
        );

        assert!(!evidence.is_unbounded_proof());
        assert!(!accepts_trust_vc_proof_evidence_shape(&obligation, &evidence));
        assert!(
            trust_vc_proof_evidence_shape_diagnostics(&obligation, &evidence)
                .iter()
                .any(|diagnostic| diagnostic.contains(TRUST_VC_PROOF_ARTIFACTS_REQUIRED))
        );
    }

    #[test]
    fn rejects_typed_trust_vc_shape_with_generic_check_report_but_no_certificate_link() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, "memory");
        let evidence = proved_trust_vc_evidence(&engine, &obligation, proof_check_artifacts());

        assert!(!evidence.satisfies_proof_artifact_policy());
        assert!(!accepts_trust_vc_proof_evidence_shape(&obligation, &evidence));
        assert!(
            trust_vc_proof_evidence_shape_diagnostics(&obligation, &evidence)
                .iter()
                .any(|diagnostic| diagnostic.contains(TRUST_VC_PROOF_ARTIFACT_ID_REQUIRED))
        );
    }

    #[test]
    fn rejects_typed_trust_vc_shape_with_mismatched_certificate_link() {
        let engine = TrustVcVerificationEngine::new();
        let obligation = typed_trust_vc_obligation(ObligationKind::MemorySafety, "memory");
        let evidence = proved_trust_vc_evidence(
            &engine,
            &obligation,
            mismatched_replayable_certificate_artifacts(&obligation.obligation_id),
        );

        assert!(evidence.satisfies_proof_artifact_policy());
        assert!(!accepts_trust_vc_proof_evidence_shape(&obligation, &evidence));
        assert!(
            trust_vc_proof_evidence_shape_diagnostics(&obligation, &evidence)
                .iter()
                .any(|diagnostic| diagnostic.contains(TRUST_VC_PROOF_ARTIFACT_ID_REQUIRED))
        );
    }

    #[test]
    fn non_owned_obligation_still_fails_closed_when_called_directly() {
        let engine = TrustVcVerificationEngine::new();
        let bundle = bundle_with(vec![obligation(ObligationKind::ArithmeticSafety, "arith")]);

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].proof_strength.is_none());
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("not ArithmeticSafety"))
        );
    }
}
