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
            TRUST_IR_BODY_WP_SCHEMA, replay_trust_ir_body_request_validated,
            verify_trust_ir_body_request_validated,
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
        // Select solving work without changing the original native input.
        // The complete bundle, including unselected requests, binds the WP.
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
        // Reuse this exact full-input admission through solving and independent
        // replay. Selection never reconstructs a smaller replacement bundle,
        // and neither operation gains source-generation authority.
        let admitted = match trust_ir::ValidatedNativeBundle::new(native) {
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
        let verification = match verify_trust_ir_body_request_validated(&admitted, request.id) {
            Ok(verification) => verification,
            Err(error) => {
                row.diagnostics = vec![error.to_string()];
                return row;
            }
        };
        // Both values came from the same first-party derivation. The witness
        // is diagnostic data until independent replay checks it below.
        let results = std::slice::from_ref(verification.result());
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
            // The native body question is the bare postcondition: the module
            // carries no function precondition, and trust-wp's fragment has
            // none. For a function that declares `requires` (or an authored
            // assumption) the public claim is the postcondition UNDER that
            // precondition, so a body state that falsifies the bare clause may
            // be one the precondition excludes. Such a counterexample refutes
            // nothing. A proof of the bare clause is still a proof of the
            // conditional one, so only the refutation is withheld.
            if bundle.contracts.iter().any(|contract| {
                matches!(
                    contract.kind,
                    trust_verifier_api::ContractKind::Requires
                        | trust_verifier_api::ContractKind::Assumes
                )
            }) {
                row.diagnostics = vec![
                    "body-aware WP counterexample withheld: the body question omits this \
                     function's `requires`, so it does not refute the conditional postcondition"
                        .into(),
                ];
                return row;
            }
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
            // Retain the actual attempted question's reasons. These are data,
            // never proof evidence or a reason to change the outcome above.
            for result in results {
                for diagnostic in &result.diagnostics {
                    row.diagnostics
                        .push(
                            format!("body-aware WP {}: {}", diagnostic.code, diagnostic.message,),
                        );
                }
                for leaf in &result.obligation_results {
                    let reason = match &leaf.status {
                        trust_wp_lib::BundleObligationStatus::Failed { reason }
                        | trust_wp_lib::BundleObligationStatus::Unknown { reason }
                        | trust_wp_lib::BundleObligationStatus::Unsupported { reason } => {
                            Some(reason)
                        }
                        _ => None,
                    };
                    if let Some(reason) = reason {
                        row.diagnostics.push(format!(
                            "body-aware WP obligation `{}` is {}: {reason}",
                            leaf.obligation_id,
                            leaf.status.as_str(),
                        ));
                    }
                    for diagnostic in &leaf.diagnostics {
                        row.diagnostics.push(format!(
                            "body-aware WP obligation `{}` {}: {}",
                            leaf.obligation_id, diagnostic.code, diagnostic.message,
                        ));
                    }
                }
            }
            return row;
        }
        if let Err(error) = replay_trust_ir_body_request_validated(
            &admitted,
            request.id,
            verification.result(),
            Some(verification.witness()),
        ) {
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
            "translation_witness": verification.witness(),
        });
        let mut certificate = serde_json::json!({
            "statement": statement,
            "replay": "rederive WP from original typed body and contract; replay native pure evidence",
            "accepted": true,
            "authority": "Trusted; not Clean-kernel certified",
        });
        let mut certificate_bytes = certificate.to_string();
        if !super::super::native_trust_ir::native_wp_certificate_is_decodable(
            certificate_bytes.as_bytes(),
        ) {
            // A recursive diagnostic plan can exceed the unchanged normal
            // certificate decoder's bounds even when native replay remains
            // representable. Preserve that proof without a mathematical
            // witness; never relax the decoder or materialization limits.
            certificate["statement"]
                .as_object_mut()
                .expect("the producer constructed the statement object")
                .remove("translation_witness");
            certificate_bytes = certificate.to_string();
            if !super::super::native_trust_ir::native_wp_certificate_is_decodable(
                certificate_bytes.as_bytes(),
            ) {
                return self.native_trust_ir_bundle_unsupported_evidence(
                    bundle,
                    obligation,
                    "body-aware WP certificate exceeds decoder bounds",
                );
            }
        }
        row.status = EvidenceStatus::Proved;
        row.proof_strength = Some(ProofStrength::deductive());
        let artifacts = [artifact(
            EvidenceArtifactKind::ProofCertificate,
            "certificate",
            &row.obligation_id,
            certificate_bytes,
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
