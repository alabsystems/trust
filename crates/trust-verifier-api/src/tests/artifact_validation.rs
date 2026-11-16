// Native performance observations and refusal controls for call-local policy reuse.
use super::*;

#[test]
fn enabled_audit_preserves_nested_cap_observations() {
    use trust_types::audit_ledger::{self, AuditEntry, Scope};
    const CHILD: &str = "TRUST_API_ARTIFACT_AUDIT_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let directory =
            std::env::temp_dir().join(format!("trust-api-artifact-audit-{}", std::process::id()));
        std::fs::create_dir(&directory).expect("own isolated audit directory");
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "tests::artifact_validation::enabled_audit_preserves_nested_cap_observations",
                "--nocapture",
                "--test-threads=1",
            ])
            .env(CHILD, "1")
            .env("TRUST_ELIDE_AUDIT", &directory)
            .output()
            .unwrap();
        std::fs::remove_dir(&directory).expect("remove own audit directory");
        assert!(
            output.status.success(),
            "audit child: {}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        return;
    }
    assert!(audit_ledger::enabled());
    let mut result = fully_proved_result(VerifierInvocation::DpubReleaseGate);
    let owner = result.evidence[0].obligation_id.clone();
    let artifact = &mut result.evidence[0].artifacts[0];
    let materialization = artifact.materialization.as_ref().unwrap();
    let payload_len = materialization.bound_payload_bytes(artifact.kind, &owner).unwrap().len();
    let mut bytes = materialization.bytes().to_vec();
    let length_offset = bytes.len() - payload_len - 8;
    bytes[length_offset..length_offset + 8]
        .copy_from_slice(&((MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES + 1) as u64).to_be_bytes());
    artifact.materialization = Some(
        EvidenceArtifactMaterialization::new(bytes, materialization.proof_binding_id(), Vec::new())
            .unwrap(),
    );
    artifact.hash.value = stable_sha256_hex(artifact.materialization.as_ref().unwrap().bytes());
    artifact.uri = format!("artifact://nested-cap/{}", artifact.hash.value);
    result.validate_input_state().expect("actual bytes/hash remain valid");
    result.try_reconcile_derived_state().expect("malformed envelope is a policy refusal");

    let direct_scope = Scope::enter("direct-policy").unwrap();
    assert!(!result.evidence[0].satisfies_proof_artifact_policy());
    assert!(!result.evidence[0].satisfies_proof_artifact_policy());
    let expected = direct_scope.finish();
    assert_eq!(
        expected,
        vec![
            AuditEntry::Cap {
                site: "crates/trust-verifier-api/src/lib.rs:MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES"
            };
            2
        ]
    );
    let shared_scope = Scope::enter("shared-policy").unwrap();
    let view = RunEvidenceValidation::new(&result);
    assert!(!view.artifact_policy(0));
    assert!(!view.artifact_policy(0));
    assert_eq!(shared_scope.finish(), expected);
    let manifest_scope = Scope::enter("manifest-policy").unwrap();
    let manifest = result.to_manifest();
    assert!(manifest.accepted_evidence.is_empty());
    assert_eq!(
        manifest_scope.finish(),
        expected,
        "summary and classification both remain observable"
    );
}

#[test]
fn shared_policy_verdicts_preserve_direct_counts_decisions_and_audit() {
    let mut result = fully_proved_result(VerifierInvocation::DpubReleaseGate);
    let template_obligation = result.requested_obligations[0].clone();
    let template_evidence = result.evidence[0].clone();
    result.requested_obligations.clear();
    result.evidence.clear();
    result.diagnostics.push("engine-authored audit history".to_string());
    for index in 0..13 {
        let mut obligation = template_obligation.clone();
        obligation.obligation_id = format!("policy-obligation-{index}");
        let mut evidence = template_evidence.clone();
        evidence.evidence_id = format!("policy-evidence-{index}");
        evidence.obligation_id = obligation.obligation_id.clone();
        evidence.diagnostics = vec![format!("audit for evidence {index}")];
        evidence.artifacts = vec![certificate_artifact(&obligation.obligation_id, "policy-proof")];
        match index {
            1 => {
                evidence.artifacts =
                    pdr_proof_dag_artifacts(&obligation.obligation_id, "policy-proof")
            }
            2 => evidence.artifacts.extend(native_structural_timing_artifacts()),
            3 => evidence.artifacts = vec![certificate_artifact("another-owner", "policy-proof")],
            4 => evidence.artifacts[0].uri = "artifact://without-the-digest".to_string(),
            5 => {
                evidence.artifacts =
                    pdr_proof_dag_artifacts(&obligation.obligation_id, "policy-proof");
                evidence.artifacts.retain(|artifact| artifact.kind != EvidenceArtifactKind::Model);
            }
            6 => evidence.proof_strength = Some(ProofStrength::bounded(4)),
            7 => evidence.proof_strength = None,
            8 => evidence.status = EvidenceStatus::Unknown,
            9 => {
                evidence.engine =
                    EngineManifest::new("another-engine", "0.1.0", EngineKind::Deductive)
            }
            10 => evidence.artifacts.push(evidence.artifacts[0].clone()),
            11 => {
                evidence.artifacts =
                    pdr_proof_dag_artifacts(&obligation.obligation_id, "policy-proof");
                evidence
                    .artifacts
                    .iter_mut()
                    .find(|artifact| artifact.kind == EvidenceArtifactKind::ReplayLog)
                    .unwrap()
                    .materialization
                    .as_mut()
                    .unwrap()
                    .proof_binding_id = "different-proof".to_string();
            }
            12 => {
                obligation.required_strength =
                    Some(ProofStrength::certified(ReasoningKind::Deductive))
            }
            _ => {}
        }
        result.requested_obligations.push(obligation);
        result.evidence.push(evidence);
    }
    let mut skipped = template_obligation;
    skipped.obligation_id = "policy-skipped".to_string();
    result.requested_obligations.push(skipped);
    result.try_reconcile_derived_state().expect("mixed canonical input");
    let direct_summary = VerificationRunSummary::from_parts(
        &result.requested_obligations,
        &result.evidence,
        &result.skipped,
        1,
    );
    assert_eq!(result.summary, direct_summary);
    assert_eq!(result.summary.requested_obligations, 14);
    assert_eq!(result.summary.proved, 4);
    assert_eq!(result.summary.missing_proof_artifacts, 5);
    assert_eq!(result.summary.insufficient_strength, 2);

    let manifest = result.try_to_manifest().expect("mixed evidence remains auditable");
    assert_eq!(manifest.accepted_evidence.len(), 3);
    assert_eq!(manifest.rejected_evidence.len(), 10);
    let obligations = result
        .requested_obligations
        .iter()
        .map(|obligation| (obligation.obligation_id.as_str(), obligation))
        .collect();
    for evidence in &result.evidence {
        let direct = ManifestEvidenceDecision::classify(&result, evidence, &obligations, || {
            evidence.satisfies_proof_artifact_policy()
        });
        let actual = manifest
            .accepted_evidence
            .iter()
            .chain(&manifest.rejected_evidence)
            .find(|decision| decision.evidence_id == evidence.evidence_id)
            .unwrap();
        assert_eq!(actual, &direct, "every field, including diagnostics and exact artifacts");
    }
    assert_eq!(manifest.diagnostics, result.diagnostics);
    assert_eq!(manifest.skipped, result.skipped);
    assert_eq!(manifest, result.to_manifest());
    manifest.validate_derived_state().expect("standalone manifest revalidation");
    assert!(!manifest.is_release_actionable());
}

#[test]
fn equal_artifact_hashes_do_not_share_an_owner_or_row_verdict() {
    let mut result = fully_proved_result(VerifierInvocation::DpubReleaseGate);
    let mut obligation = result.requested_obligations[0].clone();
    obligation.obligation_id = "different-owner".to_string();
    result.requested_obligations.push(obligation);
    let mut transplanted = result.evidence[0].clone();
    transplanted.evidence_id = "transplanted-evidence".to_string();
    transplanted.obligation_id = "different-owner".to_string();
    result.evidence.push(transplanted);
    assert_eq!(result.evidence[0].artifacts, result.evidence[1].artifacts);
    result.try_reconcile_derived_state().expect("owner failure is derived, not structural");
    for _ in 0..2 {
        let manifest = result.try_to_manifest().expect("auditable owner failure");
        assert_eq!(manifest.summary.proved, 1);
        assert_eq!(manifest.summary.missing_proof_artifacts, 1);
        assert_eq!(manifest.accepted_evidence[0].evidence_id, "ev-fully-proved");
        assert_eq!(manifest.rejected_evidence[0].evidence_id, "transplanted-evidence");
        assert_eq!(
            manifest.rejected_evidence[0].disposition,
            EvidenceDisposition::RejectedMissingProofArtifacts
        );
        result.evidence.reverse();
    }

    // Even a primed private view must run structural validation; a verdict is
    // never a reusable admission token for duplicate identities.
    result.evidence[1].evidence_id = result.evidence[0].evidence_id.clone();
    let view = RunEvidenceValidation::new(&result);
    assert!(view.artifact_policy(0));
    assert!(view.validate_derived_state().unwrap_err().contains("duplicate evidence IDs"));
    assert!(result.try_to_manifest().is_err());
    assert_eq!(result.to_manifest().status, VerificationRunStatus::Inconclusive);
}

#[test]
fn source_mutations_and_manifest_mutations_get_fresh_validation() {
    let mut result = fully_proved_result(VerifierInvocation::DpubReleaseGate);
    result.evidence[0].artifacts.extend(native_structural_timing_artifacts());
    result.try_reconcile_derived_state().expect("valid native structural domain");
    let original = result.try_to_manifest().expect("valid native manifest");
    assert!(original.is_release_actionable());
    let uri = result.evidence[0].artifacts[0].uri.clone();
    result.evidence[0].artifacts[0].uri = "artifact://without-the-digest".to_string();
    assert!(result.try_to_manifest().is_err());
    let refused = result.to_manifest();
    assert!(refused.accepted_evidence.is_empty());
    assert_eq!(
        refused.rejected_evidence[0].disposition,
        EvidenceDisposition::RejectedMissingProofArtifacts
    );
    result.try_reconcile_derived_state().expect("policy failure remains auditable");
    assert!(!result.try_to_manifest().unwrap().is_release_actionable());
    result.evidence[0].artifacts[0].uri = uri;
    result.try_reconcile_derived_state().expect("repair revalidates rather than retaining false");
    assert_eq!(result.try_to_manifest().unwrap(), original);

    let valid = result.clone();
    // Preserve the public hash while corrupting bytes: input validation must
    // refuse before any cached policy or derived-summary comparison.
    Arc::make_mut(&mut result.evidence[0].artifacts[0].materialization.as_mut().unwrap().bytes)
        [0] ^= 1;
    let corrupted = result.clone();
    assert!(result.try_to_manifest().unwrap_err().contains("materialization does not match"));
    assert!(result.try_reconcile_derived_state().is_err());
    assert_eq!(result, corrupted, "failed reconciliation is transactional");

    for index in 1..4 {
        let mut mutation = valid.clone();
        mutation.evidence[0].artifacts[index].materialization.as_mut().unwrap().proof_binding_id =
            "another-binding".to_string();
        assert!(!mutation.evidence[0].satisfies_proof_artifact_policy());
        assert!(mutation.try_to_manifest().is_err());
        assert!(mutation.to_manifest().accepted_evidence.is_empty());
    }
    let mut manifest = original.clone();
    manifest.accepted_evidence[0].artifacts[0].uri = "artifact://without-the-digest".to_string();
    assert!(manifest.validate_derived_state().is_err());
    assert!(!manifest.is_release_actionable());
    assert!(
        VerificationRunManifest::from_json_slice(&serde_json::to_vec(&manifest).unwrap()).is_err()
    );
    assert_eq!(valid.try_to_manifest().unwrap(), original);
}

// Manual native timing probe: ignored in ordinary tests because wall time is
// observational evidence, never an acceptance threshold or a proof grade.
#[test]
#[ignore = "manual native artifact-validation timing probe"]
fn artifact_validation_timing_probe() {
    for route in ["pdr-dag", "large-certificate", "native-structural"] {
        let mut result = fully_proved_result(VerifierInvocation::DpubReleaseGate);
        let template_obligation = result.requested_obligations[0].clone();
        let template_evidence = result.evidence[0].clone();
        result.requested_obligations.clear();
        result.evidence.clear();
        for index in 0..64 {
            let mut obligation = template_obligation.clone();
            obligation.obligation_id = format!("timing-obligation-{index}");
            let mut evidence = template_evidence.clone();
            evidence.evidence_id = format!("timing-evidence-{index}");
            evidence.obligation_id = obligation.obligation_id.clone();
            evidence.artifacts = if route == "pdr-dag" {
                pdr_proof_dag_artifacts(&obligation.obligation_id, "timing-proof")
            } else {
                vec![bound_artifact(
                    EvidenceArtifactKind::ProofCertificate,
                    &obligation.obligation_id,
                    "timing-proof",
                    &vec![b'x'; 16 * 1024],
                    Vec::new(),
                )]
            };
            if route == "native-structural" {
                evidence.artifacts.extend(native_structural_timing_artifacts());
            }
            result.requested_obligations.push(obligation);
            result.evidence.push(evidence);
        }
        result.try_reconcile_derived_state().expect("canonical timing fixture");
        let expected = result.try_to_manifest().expect("validated timing fixture");
        assert_eq!(expected.accepted_evidence.len(), 64);
        assert!(expected.rejected_evidence.is_empty());
        println!(
            "artifact-timing fixture={route} evidence={} materialized_bytes={} manifest_sha256={}",
            result.evidence.len(),
            result
                .evidence
                .iter()
                .flat_map(|e| &e.artifacts)
                .filter_map(|a| a.materialization.as_ref())
                .map(|m| m.bytes().len())
                .sum::<usize>(),
            stable_sha256_hex(&serde_json::to_vec(&expected).expect("manifest JSON")),
        );
        for operation in ["validate", "to-manifest", "try-to-manifest"] {
            let mut elapsed = Vec::new();
            for _ in 0..7 {
                let started = Instant::now();
                for _ in 0..20 {
                    match operation {
                        "validate" => std::hint::black_box(result.validate_derived_state())
                            .expect("valid timing input"),
                        "to-manifest" => {
                            std::hint::black_box(result.to_manifest());
                        }
                        _ => {
                            std::hint::black_box(result.try_to_manifest())
                                .expect("valid timing manifest");
                        }
                    }
                }
                elapsed.push(started.elapsed().as_micros());
            }
            println!(
                "artifact-timing fixture={route} operation={operation} iterations=20 batch_us={elapsed:?}"
            );
        }
        assert_eq!(result.to_manifest(), expected);
    }
}

fn native_structural_timing_artifacts() -> Vec<EvidenceArtifact> {
    let binding = "trust_ir-native-trust-vc-request-1-proof-1";
    let mut artifacts: Vec<EvidenceArtifact> = Vec::new();
    for (role, kind, suite, request_id, proof_id) in [
        ("bundle", EvidenceArtifactKind::EngineInput, None, None, None),
        ("request", EvidenceArtifactKind::EngineInput, Some("trust-vc"), Some("1"), None),
        (
            "normalized_obligation",
            EvidenceArtifactKind::NormalizedObligation,
            Some("trust-vc"),
            Some("1"),
            Some("1"),
        ),
    ] {
        let mut value = serde_json::json!({
            "schema": "trust.native-trust-ir-materialization.v1",
            "role": role, "suite": suite, "request_id": request_id,
            "proof_id": proof_id, "payload": { "fixture": "x".repeat(8192) },
        });
        canonicalize_json_in_place(&mut value);
        let bytes = serde_json::to_vec(&value).expect("native structural fixture JSON");
        let hash =
            ArtifactHash { algorithm: "sha256".to_string(), value: stable_sha256_hex(&bytes) };
        let references = artifacts.last().map_or_else(Vec::new, |previous| {
            vec![EvidenceArtifactReference { kind: previous.kind, hash: previous.hash.clone() }]
        });
        let uri = match artifacts.as_slice() {
            [] => format!("trust_ir-native://verification-bundle/{}", hash.value),
            [bundle] => format!("{}/trust-vc/request/1/{}", bundle.uri, hash.value),
            [_, request] => format!("{}/proof/1/{}", request.uri, hash.value),
            _ => unreachable!("three native structural roles"),
        };
        artifacts.push(EvidenceArtifact {
            kind,
            uri,
            hash,
            materialization: Some(
                EvidenceArtifactMaterialization::new(bytes, binding, references)
                    .expect("canonical native structural materialization"),
            ),
        });
    }
    artifacts
}
