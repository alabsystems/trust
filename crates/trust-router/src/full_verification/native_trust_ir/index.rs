//! Typed TrustIr native verification bundle indexing for the full verifier.

use std::collections::BTreeMap;

use serde::Serialize;
use trust_ir::request::transport::native_bundle_transport_payload;
use trust_ir_bridge::{NativeVerificationBundle, NativeVerificationRequest};
use trust_verifier_api::{
    ArtifactHash, EvidenceArtifact, EvidenceArtifactKind, EvidenceArtifactMaterialization,
    EvidenceArtifactReference, TrustObligation,
};

use super::super::policy::{
    TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
    TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY,
    TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY,
};
use super::super::routing::{ObligationRoute, PrimaryEngine, fallback_route, obligation_route};
use super::super::util::artifact_hash_label;

#[derive(Debug, Clone)]
pub(crate) struct NativeTrustIrEvidenceIndex {
    pub(super) bundle_artifact: EvidenceArtifact,
    pub(super) validation_errors: Vec<String>,
    pub(super) requests: Vec<NativeTrustIrRequestEvidence>,
    pub(crate) diagnostics: Vec<String>,
    #[cfg(feature = "trust-build")]
    wp_replay: Option<std::sync::Arc<super::wp_replay::NativeWpReplay>>,
}

#[derive(Debug, Clone)]
pub(super) struct NativeTrustIrRequestEvidence {
    pub(super) primary: PrimaryEngine,
    pub(super) request_id: u32,
    pub(super) proof_obligations: BTreeMap<u32, EvidenceArtifact>,
    pub(super) public_obligation_ids: BTreeMap<u32, String>,
    pub(super) request_artifact: EvidenceArtifact,
    pub(super) diagnostic: String,
}

#[derive(Debug, Clone)]
pub(crate) struct NativeTrustIrArtifactMatch {
    pub(crate) artifacts: Vec<EvidenceArtifact>,
    pub(crate) diagnostic: String,
    pub(crate) request_id: u32,
    pub(crate) proof_id: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NativeTrustIrObligationIdentity {
    pub(crate) suite: Option<String>,
    pub(crate) request_id: Option<u32>,
    pub(crate) proof_obligation_id: u32,
}

impl NativeTrustIrEvidenceIndex {
    pub(crate) fn from_bundle(bundle: &NativeVerificationBundle) -> Self {
        let bundle_bytes_result = native_bundle_transport_payload(bundle).and_then(|payload| {
            native_artifact_envelope_bytes("bundle", None, None, None, &payload)
        });
        let bundle_serialization_error = bundle_bytes_result.as_ref().err().cloned();
        let bundle_bytes = bundle_bytes_result.unwrap_or_default();
        let bundle_hash = sha256_artifact_hash(&bundle_bytes);
        let bundle_digest_hex = bundle_hash.value.clone();
        let bundle_materialization = EvidenceArtifactMaterialization::new(
            bundle_bytes,
            format!("trust-ir-native-bundle:{bundle_digest_hex}"),
            Vec::new(),
        );
        let bundle_artifact = EvidenceArtifact {
            kind: EvidenceArtifactKind::EngineInput,
            uri: format!("trust_ir-native://verification-bundle/{bundle_digest_hex}"),
            hash: bundle_hash.clone(),
            materialization: bundle_materialization,
        };
        let mut validation_errors = bundle
            .validate()
            .err()
            .unwrap_or_default()
            .into_iter()
            .map(|error| format!("{error:?}"))
            .collect::<Vec<_>>();
        if bundle_artifact.materialization.is_none() {
            validation_errors.push(
                "canonical TrustIr bundle payload is empty or exceeds inline transport limit"
                    .to_string(),
            );
        }
        if let Some(error) = bundle_serialization_error {
            validation_errors.push(error);
        }

        let mut requests = bundle
            .requests
            .iter()
            .filter_map(|request| {
                NativeTrustIrRequestEvidence::from_request(
                    &bundle_digest_hex,
                    &bundle_hash,
                    bundle,
                    request,
                )
            })
            .collect::<Vec<_>>();
        requests.sort_by_key(|request| (request.primary.name(), request.request_id));

        let mut diagnostics = vec![format!(
            "typed TrustIr NativeVerificationBundle indexed: schema_version={} bundle_digest={} requests={}",
            bundle.schema_version,
            artifact_hash_label(&bundle_artifact.hash),
            requests.len()
        )];
        diagnostics.extend(requests.iter().map(|request| {
            format!("typed TrustIr native request indexed: {}", request.diagnostic)
        }));
        if !validation_errors.is_empty() {
            diagnostics.push(format!(
                "typed TrustIr NativeVerificationBundle validation failed: {}",
                validation_errors.join("; ")
            ));
        }

        #[cfg(feature = "trust-build")]
        let wp_replay = (validation_errors.is_empty()
            && bundle
                .requests
                .iter()
                .any(|request| matches!(request, NativeVerificationRequest::TrustWp(_))))
        .then(|| std::sync::Arc::new(super::wp_replay::NativeWpReplay::new(bundle)));
        Self {
            bundle_artifact,
            validation_errors,
            requests,
            diagnostics,
            #[cfg(feature = "trust-build")]
            wp_replay,
        }
    }

    pub(crate) fn accepts_wp_certificate(
        &self,
        bundle: &trust_verifier_api::TrustContractBundle,
        obligation: &TrustObligation,
        evidence: &trust_verifier_api::ObligationEvidence,
        request_id: u32,
        proof_id: u32,
    ) -> bool {
        #[cfg(feature = "trust-build")]
        {
            self.wp_replay.as_ref().is_some_and(|replay| {
                replay.accepts(bundle, obligation, evidence, request_id, proof_id)
            })
        }
        #[cfg(not(feature = "trust-build"))]
        {
            let _ = (bundle, obligation, evidence, request_id, proof_id);
            false
        }
    }

    pub(crate) fn checked_wp_proof(
        &self,
        bundle: &trust_verifier_api::TrustContractBundle,
        obligation: &TrustObligation,
        evidence: &trust_verifier_api::ObligationEvidence,
    ) -> Option<super::CheckedNativeWpProof> {
        if evidence.status != trust_verifier_api::EvidenceStatus::Proved
            || evidence.proof_strength != Some(trust_verifier_api::ProofStrength::deductive())
        {
            return None;
        }
        let route = fallback_route(obligation)?.0;
        let binding = self.artifact_match(route, obligation).ok()??;
        #[cfg(feature = "trust-build")]
        {
            self.wp_replay.as_ref()?.checked_proof(
                bundle,
                obligation,
                evidence,
                binding.request_id,
                binding.proof_id,
            )
        }
        #[cfg(not(feature = "trust-build"))]
        {
            let _ = (bundle, binding);
            None
        }
    }

    #[cfg(test)]
    pub(crate) fn bundle_artifact_for_test(&self) -> &EvidenceArtifact {
        &self.bundle_artifact
    }

    #[cfg(test)]
    pub(crate) fn validation_errors_for_test(&self) -> &[String] {
        &self.validation_errors
    }

    /// `Some(reason)` when no proof on `route` can be accepted against this
    /// bundle, whatever the engine returns: the bundle failed validation or
    /// could not be materialized inline. Exactly the refusal
    /// [`Self::artifact_match`] gives every such proof, so callers can know it
    /// before dispatch.
    pub(crate) fn proof_authority_refusal(&self, route: ObligationRoute) -> Option<String> {
        if !route.primary.requires_trust_ir_native_bundle() || self.validation_errors.is_empty() {
            return None;
        }
        Some(format!(
            "proved {} evidence is missing a valid typed TrustIr NativeVerificationBundle: {}",
            route.primary.name(),
            self.validation_errors.join("; ")
        ))
    }

    pub(crate) fn artifact_match(
        &self,
        route: ObligationRoute,
        obligation: &TrustObligation,
    ) -> Result<Option<NativeTrustIrArtifactMatch>, String> {
        if !route.primary.requires_trust_ir_native_bundle() {
            return Ok(None);
        }
        if let Some(refusal) = self.proof_authority_refusal(route) {
            return Err(refusal);
        }

        let identity =
            match NativeTrustIrObligationIdentity::from_obligation(obligation, route.primary) {
                Ok(identity) => identity,
                Err(primary_error) if route.primary == PrimaryEngine::TrustWp => {
                    // A designated alternative strategy keeps the original public
                    // identity. First authenticate that primary request, then find
                    // its unique WP request for the same native proof obligation.
                    // Never erase or relabel caller-supplied suite/request metadata.
                    if fallback_route(obligation).is_none_or(|fallback| fallback.0 != route) {
                        return Err(primary_error);
                    }
                    let primary = obligation_route(obligation).ok_or(primary_error)?;
                    self.artifact_match(primary, obligation)?;
                    let original = NativeTrustIrObligationIdentity::from_obligation(
                        obligation,
                        primary.primary,
                    )?;
                    let mut alternatives = self.requests.iter().filter(|request| {
                        request.primary == route.primary
                            && request.proof_obligations.contains_key(&original.proof_obligation_id)
                    });
                    let request = alternatives.next().ok_or_else(|| {
                        "missing native WP request for the original proof obligation".to_string()
                    })?;
                    if alternatives.next().is_some() {
                        return Err(
                            "ambiguous native WP requests for the original proof obligation".into(),
                        );
                    }
                    NativeTrustIrObligationIdentity {
                        suite: Some(route.primary.name().into()),
                        request_id: Some(request.request_id),
                        proof_obligation_id: original.proof_obligation_id,
                    }
                }
                Err(error) => return Err(error),
            };
        let mut candidates = self.requests.iter().filter(|request| {
            request.primary == route.primary
                && identity.request_id.is_none_or(|request_id| request.request_id == request_id)
                && request.proof_obligations.contains_key(&identity.proof_obligation_id)
        });
        let request = candidates.next().ok_or_else(|| {
                format!(
                    "proved {} evidence is missing typed TrustIr native request artifact for request_id={} proof_obligation_id={}",
                    route.primary.name(),
                    identity
                        .request_id
                        .map_or_else(|| "any".to_string(), |request_id| request_id.to_string()),
                    identity.proof_obligation_id
                )
            })?;

        if candidates.next().is_some() {
            return Err(format!(
                "proved {} evidence has ambiguous typed TrustIr native requests for request_id={} proof_obligation_id={}",
                route.primary.name(),
                identity.request_id.map_or_else(|| "any".to_string(), |id| id.to_string()),
                identity.proof_obligation_id,
            ));
        }

        let proof_artifact = request
            .proof_obligation_artifact(identity.proof_obligation_id)
            .expect("indexed proof obligation exists");
        let bound_public_obligation_id = request
            .public_obligation_ids
            .get(&identity.proof_obligation_id)
            .ok_or_else(|| {
                format!(
                    "proved {} evidence is missing the typed public-obligation binding for request_id={} proof_obligation_id={}",
                    route.primary.name(),
                    request.request_id,
                    identity.proof_obligation_id
                )
            })?;
        if bound_public_obligation_id != &obligation.obligation_id {
            return Err(format!(
                "proved {} evidence public obligation id mismatch for request_id={} proof_obligation_id={}: typed native source binds {:?}, public verifier requested {:?}",
                route.primary.name(),
                request.request_id,
                identity.proof_obligation_id,
                bound_public_obligation_id,
                obligation.obligation_id
            ));
        }
        let proof_binding_id = format!(
            "trust_ir-native-{}-request-{}-proof-{}",
            route.primary.name(),
            request.request_id,
            identity.proof_obligation_id
        );
        let mut artifacts =
            vec![self.bundle_artifact.clone(), request.request_artifact.clone(), proof_artifact];
        for artifact in &mut artifacts {
            artifact.materialization =
                artifact.materialization.take().and_then(|materialization| {
                    materialization.with_proof_binding_id(proof_binding_id.clone())
                });
        }
        Ok(Some(NativeTrustIrArtifactMatch {
            request_id: request.request_id,
            proof_id: identity.proof_obligation_id,
            artifacts,
            diagnostic: format!(
                "typed TrustIr native request identity accepted: suite={} request_id={} proof_obligation_id={} public_obligation_id={:?} request_digest={} bundle_digest={}",
                route.primary.name(),
                request.request_id,
                identity.proof_obligation_id,
                bound_public_obligation_id,
                artifact_hash_label(&request.request_artifact.hash),
                artifact_hash_label(&self.bundle_artifact.hash)
            ),
        }))
    }
}

impl NativeTrustIrRequestEvidence {
    fn from_request(
        bundle_digest_hex: &str,
        bundle_hash: &ArtifactHash,
        bundle: &NativeVerificationBundle,
        request: &NativeVerificationRequest,
    ) -> Option<Self> {
        let raw_suite = request.verifier_suite().to_string();
        let primary = PrimaryEngine::from_trust_ir_suite_name(&raw_suite)?;
        // Trust: emit the canonical hyphenated suite name in URIs and
        // diagnostics so consumers (tests, audit logs, downstream tools)
        // see a single normalized identity regardless of whether the
        // upstream TrustIr `NativeVerifierSuite` Display happened to use
        // underscores or hyphens.
        let suite = primary.name();
        let request_id = request.id().0;
        let request_id_string = request_id.to_string();
        let request_bytes = native_artifact_envelope_bytes(
            "request",
            Some(suite),
            Some(&request_id_string),
            None,
            request,
        )
        .ok()?;
        let request_hash = sha256_artifact_hash(&request_bytes);
        let request_digest_hex = request_hash.value.as_str();
        let request_uri = format!(
            "trust_ir-native://verification-bundle/{bundle_digest_hex}/{suite}/request/{request_id}/{request_digest_hex}"
        );
        let request_materialization = EvidenceArtifactMaterialization::new(
            request_bytes,
            format!("trust-ir-native-request:{suite}:{request_id}"),
            vec![EvidenceArtifactReference {
                kind: EvidenceArtifactKind::EngineInput,
                hash: bundle_hash.clone(),
            }],
        )?;
        let request_artifact = EvidenceArtifact {
            kind: EvidenceArtifactKind::EngineInput,
            uri: request_uri.clone(),
            hash: request_hash.clone(),
            materialization: Some(request_materialization),
        };
        let proof_obligations = request
            .obligations()
            .iter()
            .filter_map(|obligation| {
                let proof_obligation_id = obligation.index();
                let proof_obligation_id_string = proof_obligation_id.to_string();
                let proof_bytes = native_artifact_envelope_bytes(
                    "normalized_obligation",
                    Some(suite),
                    Some(&request_id_string),
                    Some(&proof_obligation_id_string),
                    obligation,
                )
                .ok()?;
                let proof_hash = sha256_artifact_hash(&proof_bytes);
                let proof_digest_hex = proof_hash.value.as_str();
                let materialization = EvidenceArtifactMaterialization::new(
                    proof_bytes,
                    format!(
                        "trust-ir-native-obligation:{suite}:{request_id}:{proof_obligation_id}"
                    ),
                    vec![EvidenceArtifactReference {
                        kind: EvidenceArtifactKind::EngineInput,
                        hash: request_hash.clone(),
                    }],
                )?;
                let artifact = EvidenceArtifact {
                    kind: EvidenceArtifactKind::NormalizedObligation,
                    uri: format!("{request_uri}/proof/{proof_obligation_id}/{proof_digest_hex}"),
                    hash: proof_hash,
                    materialization: Some(materialization),
                };
                Some((proof_obligation_id, artifact))
            })
            .collect::<BTreeMap<_, _>>();
        let public_obligation_ids = request
            .obligations()
            .iter()
            .filter_map(|obligation| {
                bundle
                    .obligation_source(*obligation)
                    .map(|source| (obligation.index(), source.public_obligation_id.clone()))
            })
            .collect::<BTreeMap<_, _>>();
        let proof_ids = request
            .obligations()
            .iter()
            .map(|obligation| obligation.index().to_string())
            .collect::<Vec<_>>()
            .join(",");
        let diagnostic = format!(
            "suite={suite} request_id={request_id} proof_obligations=[{proof_ids}] request_digest={}",
            artifact_hash_label(&request_artifact.hash)
        );
        Some(Self {
            primary,
            request_id,
            proof_obligations,
            public_obligation_ids,
            request_artifact,
            diagnostic,
        })
    }

    fn proof_obligation_artifact(&self, proof_obligation_id: u32) -> Option<EvidenceArtifact> {
        self.proof_obligations.get(&proof_obligation_id).cloned()
    }
}

fn native_artifact_envelope_bytes<T: Serialize>(
    role: &str,
    suite: Option<&str>,
    request_id: Option<&str>,
    proof_id: Option<&str>,
    payload: &T,
) -> Result<Vec<u8>, String> {
    let payload = serde_json::to_value(payload).map_err(|error| {
        format!("typed TrustIr native transport JSON serialization failed: {error}")
    })?;
    let mut value = serde_json::json!({
        "schema": trust_types::NATIVE_TRUST_IR_MATERIALIZATION_SCHEMA,
        "role": role,
        "suite": suite,
        "request_id": request_id,
        "proof_id": proof_id,
        "payload": payload,
    });
    trust_types::digest::canonicalize_json_in_place(&mut value);
    serde_json::to_vec(&value).map_err(|error| {
        format!("canonical TrustIr native transport JSON encoding failed: {error}")
    })
}

fn sha256_artifact_hash(bytes: &[u8]) -> ArtifactHash {
    ArtifactHash { algorithm: "sha256".to_string(), value: trust_types::stable_sha256_hex(bytes) }
}

impl NativeTrustIrObligationIdentity {
    pub(crate) fn from_obligation(
        obligation: &TrustObligation,
        expected_primary: PrimaryEngine,
    ) -> Result<Self, String> {
        use trust_verifier_api::native_routing_identity::{
            NativeRoutingIdentityError as Error, NativeRoutingIdentityPolicy, SuiteComparison,
            parse_native_routing_identity,
        };
        let identity = parse_native_routing_identity(obligation, NativeRoutingIdentityPolicy {
            canonical_id_fallback: true,
            canonical_metadata_numbers: false,
            suite_comparison: SuiteComparison::Exact,
        }).map_err(|error| match error {
            Error::DuplicateMetadata { key } => format!(
                "proved {} evidence has ambiguous duplicate TrustIr native identity metadata `{key}`",
                expected_primary.name()
            ),
            Error::InvalidNumber { key, value } => format!(
                "metadata `{key}` must be an unsigned 32-bit integer, got `{value}`"
            ),
            Error::Conflict { key, metadata, canonical } => {
                let (field, id_field) = if key == TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY {
                    ("suite", "suite")
                } else if key == TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY {
                    ("request", "request")
                } else {
                    ("proof-obligation", "proof")
                };
                format!(
                    "proved {} evidence has TrustIr native {field} metadata `{metadata}` that disagrees with canonical obligation id `{}` {id_field} `{canonical}`",
                    expected_primary.name(), obligation.obligation_id
                )
            }
        })?;
        let proof_obligation_id = identity.proof_obligation_id.ok_or_else(|| format!(
            "proved {} evidence is missing TrustIr native proof-obligation identity; expected obligation metadata `{}` or id form `trust_ir-native-<suite>-request-<id>-proof-<proof_id>`",
            expected_primary.name(), TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY
        ))?;
        let request_id = identity.request_id;
        let suite = identity.suite;

        if let Some(suite) = suite.as_deref()
            && PrimaryEngine::from_trust_ir_suite_name(suite) != Some(expected_primary)
        {
            return Err(format!(
                "proved {} evidence names TrustIr native verifier suite `{suite}`",
                expected_primary.name()
            ));
        }

        Ok(Self { suite, request_id, proof_obligation_id })
    }
}

pub(crate) fn native_trust_ir_artifact_match(
    native_trust_ir: Option<&NativeTrustIrEvidenceIndex>,
    route: ObligationRoute,
    obligation: &TrustObligation,
) -> Result<Option<NativeTrustIrArtifactMatch>, String> {
    if !route.primary.requires_trust_ir_native_bundle() {
        return Ok(None);
    }

    let Some(native_trust_ir) = native_trust_ir else {
        return Err(format!(
            "proved {} evidence requires typed TrustIr native request/proof artifacts, but no typed TrustIr NativeVerificationBundle was supplied",
            route.primary.name()
        ));
    };
    native_trust_ir.artifact_match(route, obligation)
}

#[cfg(test)]
mod tests {
    use trust_verifier_api::{MetadataEntry, ObligationKind, SourceLocation};

    use super::*;
    use crate::full_verification::routing::{
        ObligationRoute, PrimaryEngine, ProofFamily, RequiredAssurance,
    };

    fn artifact(kind: EvidenceArtifactKind, uri: &str) -> EvidenceArtifact {
        EvidenceArtifact {
            kind,
            uri: uri.to_string(),
            hash: ArtifactHash { algorithm: "sha256".to_string(), value: "a".repeat(64) },
            materialization: None,
        }
    }

    #[test]
    fn artifact_match_rejects_native_proof_bound_to_a_different_public_obligation() {
        let proof = artifact(EvidenceArtifactKind::NormalizedObligation, "proof");
        let request = NativeTrustIrRequestEvidence {
            primary: PrimaryEngine::TrustMc,
            request_id: 7,
            proof_obligations: BTreeMap::from([(0, proof)]),
            public_obligation_ids: BTreeMap::from([(0, "public:original-obligation".to_string())]),
            request_artifact: artifact(EvidenceArtifactKind::EngineInput, "request"),
            diagnostic: String::new(),
        };
        let index = NativeTrustIrEvidenceIndex {
            bundle_artifact: artifact(EvidenceArtifactKind::EngineInput, "bundle"),
            validation_errors: Vec::new(),
            requests: vec![request],
            diagnostics: Vec::new(),
            #[cfg(feature = "trust-build")]
            wp_replay: None,
        };
        let obligation = TrustObligation {
            obligation_id: "public:aliased-obligation".to_string(),
            kind: ObligationKind::Assertion,
            contract_id: None,
            proof_item_id: None,
            source: SourceLocation::default(),
            description: "must not reuse another public obligation's native proof".to_string(),
            required_strength: None,
            summary_facts: Vec::new(),
            metadata: vec![
                MetadataEntry {
                    key: TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY.to_string(),
                    value: "trust-mc".to_string(),
                },
                MetadataEntry {
                    key: TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY.to_string(),
                    value: "7".to_string(),
                },
                MetadataEntry {
                    key: TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY.to_string(),
                    value: "0".to_string(),
                },
            ],
        };
        let route = ObligationRoute {
            obligation_kind: "assertion",
            primary: PrimaryEngine::TrustMc,
            proof_family: ProofFamily::TrustMcReachability,
            minimum_assurance: RequiredAssurance::SmtBacked,
        };

        let error = index
            .artifact_match(route, &obligation)
            .expect_err("public obligation alias must fail closed");
        assert!(error.contains("public obligation id mismatch"), "{error}");
        assert!(error.contains("public:original-obligation"), "{error}");
        assert!(error.contains("public:aliased-obligation"), "{error}");
    }

    fn canonical_native_identity_obligation() -> TrustObligation {
        TrustObligation {
            obligation_id: "trust_ir-native-trust-mc-request-7-proof-0".to_string(),
            kind: ObligationKind::Assertion,
            contract_id: None,
            proof_item_id: None,
            source: SourceLocation::default(),
            description: "canonical native identity fixture".to_string(),
            required_strength: None,
            summary_facts: Vec::new(),
            metadata: vec![
                MetadataEntry {
                    key: TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY.to_string(),
                    value: "trust-mc".to_string(),
                },
                MetadataEntry {
                    key: TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY.to_string(),
                    value: "7".to_string(),
                },
                MetadataEntry {
                    key: TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY.to_string(),
                    value: "0".to_string(),
                },
            ],
        }
    }

    #[test]
    fn native_identity_rejects_suite_request_and_proof_metadata_substitution() {
        for (key, substituted_value, expected_field) in [
            (TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY, "trust-vc", "suite"),
            (TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY, "8", "request"),
            (TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY, "1", "proof-obligation"),
        ] {
            let mut obligation = canonical_native_identity_obligation();
            obligation
                .metadata
                .iter_mut()
                .find(|entry| entry.key == key)
                .expect("fixture identity metadata")
                .value = substituted_value.to_string();

            let error = NativeTrustIrObligationIdentity::from_obligation(
                &obligation,
                PrimaryEngine::TrustMc,
            )
            .expect_err("metadata must not substitute a parsed canonical-id component");
            assert!(error.contains(expected_field), "{error}");
            assert!(error.contains("disagrees with canonical obligation id"), "{error}");
        }
    }

    #[test]
    fn native_identity_rejects_duplicate_suite_request_and_proof_metadata() {
        for key in [
            TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY,
            TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY,
            TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
        ] {
            let mut obligation = canonical_native_identity_obligation();
            let duplicate = obligation
                .metadata
                .iter()
                .find(|entry| entry.key == key)
                .expect("fixture identity metadata")
                .clone();
            obligation.metadata.push(duplicate);

            let error = NativeTrustIrObligationIdentity::from_obligation(
                &obligation,
                PrimaryEngine::TrustMc,
            )
            .expect_err("duplicate identity metadata must fail closed even when values agree");
            assert!(error.contains("ambiguous duplicate"), "{error}");
            assert!(error.contains(key), "{error}");
        }
    }

    #[test]
    fn native_identity_accepts_either_canonical_id_or_unique_metadata_channel() {
        let mut canonical_only = canonical_native_identity_obligation();
        canonical_only.metadata.clear();
        let from_id = NativeTrustIrObligationIdentity::from_obligation(
            &canonical_only,
            PrimaryEngine::TrustMc,
        )
        .expect("canonical id remains a complete identity channel");
        assert_eq!(from_id.request_id, Some(7));
        assert_eq!(from_id.proof_obligation_id, 0);
        assert_eq!(from_id.suite.as_deref(), Some("trust-mc"));

        let mut metadata_only = canonical_native_identity_obligation();
        metadata_only.obligation_id = "public:metadata-only".to_string();
        let from_metadata = NativeTrustIrObligationIdentity::from_obligation(
            &metadata_only,
            PrimaryEngine::TrustMc,
        )
        .expect("unique metadata remains a complete identity channel");
        assert_eq!(from_metadata, from_id);
    }

    #[test]
    fn native_routing_regression_requires_unique_inferred_request() {
        let mut obligation = canonical_native_identity_obligation();
        obligation.obligation_id = "public:shared-proof".into();
        obligation
            .metadata
            .retain(|entry| entry.key != TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY);
        let mut index = NativeTrustIrEvidenceIndex {
            bundle_artifact: artifact(EvidenceArtifactKind::EngineInput, "bundle"),
            validation_errors: Vec::new(),
            requests: [7, 8]
                .into_iter()
                .map(|request_id| NativeTrustIrRequestEvidence {
                    primary: PrimaryEngine::TrustMc,
                    request_id,
                    proof_obligations: BTreeMap::from([(
                        0,
                        artifact(EvidenceArtifactKind::NormalizedObligation, "proof"),
                    )]),
                    public_obligation_ids: BTreeMap::from([(0, obligation.obligation_id.clone())]),
                    request_artifact: artifact(
                        EvidenceArtifactKind::EngineInput,
                        &format!("request-{request_id}"),
                    ),
                    diagnostic: String::new(),
                })
                .collect(),
            diagnostics: Vec::new(),
            #[cfg(feature = "trust-build")]
            wp_replay: None,
        };
        let route = ObligationRoute {
            obligation_kind: "assertion",
            primary: PrimaryEngine::TrustMc,
            proof_family: ProofFamily::TrustMcReachability,
            minimum_assurance: RequiredAssurance::SmtBacked,
        };
        // These are correspondence controls, with no claim that synthetic
        // artifact descriptors establish a proof.
        let mut one = index.clone();
        one.requests.truncate(1);
        assert_eq!(one.artifact_match(route, &obligation).unwrap().unwrap().request_id, 7);
        for _ in 0..2 {
            let error = index
                .artifact_match(route, &obligation)
                .expect_err("a missing request id must not select by vector order");
            assert!(error.contains("ambiguous"), "{error}");
            assert_eq!(index.requests.len(), 2);
            index.requests.reverse();
        }
        obligation.metadata.push(MetadataEntry {
            key: TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY.into(),
            value: "8".into(),
        });
        assert_eq!(index.artifact_match(route, &obligation).unwrap().unwrap().request_id, 8);
        obligation.metadata.last_mut().unwrap().value = "9".into();
        assert!(
            index
                .artifact_match(route, &obligation)
                .unwrap_err()
                .contains("missing typed TrustIr native request")
        );
    }
}
