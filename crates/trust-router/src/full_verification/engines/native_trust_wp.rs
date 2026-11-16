//! Deductive fallback over the exact typed program and postcondition.
//!
//! The first-party engine derives its own WP from TrustIR. This adapter only
//! binds requests and publishes independently replayed evidence; it does not
//! translate program instructions or infer contract assumptions.

use trust_ir::{
    NativeVerificationBundle, NativeVerificationRequest, ProofId, TrustWpNativeRequest,
};
use trust_verifier_api::{
    API_VERSION, EngineCapability, EngineKind, EngineManifest, EvidenceArtifact,
    EvidenceArtifactKind, EvidenceArtifactMaterialization, EvidencePublicationMetadata,
    EvidenceStatus, ObligationEvidence, ObligationKind, ProofStrength, ReasoningKind, SupportLevel,
    TrustContractBundle, TrustObligation, ValidatedVerificationRequest, VerificationEngine,
};

pub struct NativeTrustWpTrustIrEngine {
    manifest: EngineManifest,
    timeout_ms: u64,
}

impl NativeTrustWpTrustIrEngine {
    pub fn new() -> Self {
        Self::with_timeout_ms(super::DEFAULT_PER_OBLIGATION_TIMEOUT_MS)
    }

    pub fn with_timeout_ms(timeout_ms: u64) -> Self {
        let mut manifest = EngineManifest::new("trust-wp", API_VERSION, EngineKind::Deductive);
        manifest.repository = Some("trust-wp".into());
        manifest.proof_modes = vec![ReasoningKind::Deductive];
        manifest.capabilities = vec![EngineCapability {
            obligation_kind: ObligationKind::Postcondition,
            support: SupportLevel::Supported,
        }];
        Self { manifest, timeout_ms }
    }

    pub(crate) fn native_trust_ir_bundle_unsupported_evidence(
        &self,
        _bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        reason: impl Into<String>,
    ) -> ObligationEvidence {
        ObligationEvidence {
            evidence_id: format!("trust-wp:body:{}", obligation.obligation_id),
            obligation_id: obligation.obligation_id.clone(),
            engine: self.manifest.clone(),
            status: EvidenceStatus::Unsupported,
            decline: None,
            proof_strength: None,
            artifacts: Vec::new(),
            counterexample: None,
            publication: EvidencePublicationMetadata::default(),
            diagnostics: vec![reason.into()],
        }
    }

    #[cfg(feature = "trust-build")]
    pub(crate) fn verify_obligation_with_native_trust_ir_request(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        native: &NativeVerificationBundle,
        request: &TrustWpNativeRequest,
        proof_id: ProofId,
    ) -> ObligationEvidence {
        use trust_wp_lib::trust_ir_body::{
            TRUST_IR_BODY_WP_SCHEMA, replay_trust_ir_body_contracts_validated,
            verify_trust_ir_body_contracts_validated,
        };

        let mut row = self.native_trust_ir_bundle_unsupported_evidence(
            bundle,
            obligation,
            "body-aware WP has not produced checked evidence",
        );
        let started = std::time::Instant::now();
        let expired = || started.elapsed() >= std::time::Duration::from_millis(self.timeout_ms);
        if expired() {
            row.status = EvidenceStatus::Timeout;
            row.diagnostics = vec!["body-aware WP per-obligation budget expired".into()];
            return row;
        }
        // Scope solving to this exact request. The module, source identities,
        // original contract and lineage stay byte-for-byte unchanged.
        if request.obligations != [proof_id]
            || !native.requests.iter().any(|candidate| {
                matches!(candidate, NativeVerificationRequest::TrustWp(value) if value == request)
            })
        {
            row.diagnostics = vec!["WP request is not the exact single-obligation native request".into()];
            return row;
        }
        let proof = native.module.proof_obligations.iter().find(|proof| proof.id == proof_id);
        if let Err(reason) = super::super::native_trust_ir::validate_public_claim(
            &native.module,
            proof,
            bundle,
            obligation,
        ) {
            row.diagnostics = vec![reason];
            return row;
        }
        let mut scoped = native.clone();
        scoped.requests.retain(|candidate| {
            matches!(candidate, NativeVerificationRequest::TrustWp(value) if value == request)
        });
        // Admission belongs to this exact scoped input, not the full original
        // bundle. Keep it immutably borrowed through solving and independent
        // output replay; neither operation gains source-generation authority.
        let admitted = match trust_ir::ValidatedNativeBundle::new(&scoped) {
            Ok(admitted) => admitted,
            Err(errors) => {
                row.diagnostics = vec![
                    trust_wp_lib::trust_ir_native::TrustIrNativeBundleError::InvalidNativeBundle {
                        errors: errors.into_iter().map(|error| error.to_string()).collect(),
                    }
                    .to_string(),
                ];
                return row;
            }
        };
        let results = match verify_trust_ir_body_contracts_validated(&admitted) {
            Ok(results) => results,
            Err(error) => {
                row.diagnostics = vec![error.to_string()];
                return row;
            }
        };
        if expired() {
            row.status = EvidenceStatus::Timeout;
            row.diagnostics = vec!["body-aware WP per-obligation budget expired".into()];
            return row;
        }
        if results.len() == 1
            && results[0].status == trust_wp_lib::VerifyBundleStatus::Failed
            && results[0].obligation_results.len() == 1
            && matches!(
                results[0].obligation_results[0].status,
                trust_wp_lib::BundleObligationStatus::Failed { .. }
            )
        {
            row.status = EvidenceStatus::Failed;
            row.diagnostics = vec![
                "body-aware WP refuted the original postcondition over the supported body fragment"
                    .into(),
            ];
            return row;
        }
        if results.len() != 1
            || results[0].status != trust_wp_lib::VerifyBundleStatus::Verified
            || results[0].obligation_results.len() != 1
            || !matches!(
                results[0].obligation_results[0].status,
                trust_wp_lib::BundleObligationStatus::Verified { .. }
            )
        {
            row.status = if results
                .iter()
                .any(|result| result.status == trust_wp_lib::VerifyBundleStatus::Unknown)
            {
                EvidenceStatus::Unknown
            } else {
                EvidenceStatus::Unsupported
            };
            row.diagnostics = vec!["body-aware WP did not prove the original postcondition".into()];
            return row;
        }
        if let Err(error) = replay_trust_ir_body_contracts_validated(&admitted, &results) {
            row.diagnostics = vec![format!("body-aware WP replay rejected evidence: {error}")];
            return row;
        }
        if expired() {
            row.status = EvidenceStatus::Timeout;
            row.diagnostics =
                vec!["body-aware WP per-obligation budget expired during replay".into()];
            return row;
        }
        let statement = serde_json::json!({
            "schema": TRUST_IR_BODY_WP_SCHEMA,
            "bundle_id": bundle.bundle_id,
            "obligation_id": obligation.obligation_id,
            "request": request,
            "module_digest": native.trust_ir_module_digest,
            "source_digest": native.provenance.source_digest,
            "results": results,
        });
        let certificate = serde_json::json!({
            "statement": statement,
            "replay": "rederive WP from original typed body and contract; replay native pure evidence",
            "accepted": true,
            "authority": "Trusted; not Clean-kernel certified",
        }).to_string();
        row.status = EvidenceStatus::Proved;
        row.proof_strength = Some(ProofStrength::deductive());
        let artifacts = [artifact(
            EvidenceArtifactKind::ProofCertificate,
            "certificate",
            &row.obligation_id,
            certificate,
        )]
        .into_iter()
        .collect::<Option<Vec<_>>>();
        let Some(artifacts) = artifacts else {
            return self.native_trust_ir_bundle_unsupported_evidence(
                bundle,
                obligation,
                "body-aware WP evidence exceeds artifact limits",
            );
        };
        if expired() {
            row.status = EvidenceStatus::Timeout;
            row.proof_strength = None;
            row.diagnostics =
                vec!["body-aware WP per-obligation budget expired before publication".into()];
            return row;
        }
        row.artifacts = artifacts;
        row.diagnostics = vec!["body-aware WP proved the postcondition and replay checked the exact original body and claim; authority remains Trusted".into()];
        row
    }
}

impl Default for NativeTrustWpTrustIrEngine {
    fn default() -> Self {
        Self::new()
    }
}

impl VerificationEngine for NativeTrustWpTrustIrEngine {
    fn manifest(&self) -> &EngineManifest {
        &self.manifest
    }

    fn supports(&self, obligation: &TrustObligation) -> SupportLevel {
        if obligation.kind == ObligationKind::Postcondition {
            SupportLevel::Supported
        } else {
            SupportLevel::Unsupported {
                reason: "body-aware WP currently handles postconditions".into(),
            }
        }
    }

    fn verify_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
    ) -> Vec<ObligationEvidence> {
        let (bundle, obligations) = request.into_parts();
        obligations
            .iter()
            .map(|obligation| {
                self.native_trust_ir_bundle_unsupported_evidence(
                    bundle,
                    obligation,
                    "body-aware WP requires the exact native TrustIR bundle",
                )
            })
            .collect()
    }
}

#[cfg(feature = "trust-build")]
fn artifact(
    kind: EvidenceArtifactKind,
    role: &str,
    obligation_id: &str,
    data: String,
) -> Option<EvidenceArtifact> {
    let bytes = data.into_bytes();
    let (materialization, hash) = EvidenceArtifactMaterialization::new_bound(
        kind,
        &bytes,
        &format!("trust-wp-body:{obligation_id}"),
        obligation_id,
        Vec::new(),
    )?;
    Some(EvidenceArtifact {
        kind,
        uri: format!("trust-wp-body://{obligation_id}/{role}/sha256/{}", hash.value),
        hash,
        materialization: Some(materialization),
    })
}
