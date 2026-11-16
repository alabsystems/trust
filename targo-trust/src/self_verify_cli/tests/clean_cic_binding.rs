use trust_types::{
    AssuranceLevel, ProofEvidence, ProofStrength, ReasoningKind, TransportObligationResult,
    TransportProofEvidence, TransportProofStatus,
};

use super::*;

fn proof_mut(row: &mut TransportObligationResult) -> &mut TransportProofEvidence {
    row.proof_evidence.as_mut().expect("fixture proof")
}

fn rebind_certificate(row: &mut TransportObligationResult, domain: &str) {
    let proof = proof_mut(row);
    let artifact = &mut proof.artifacts[0];
    // Address the certificate the way the compiler does: its typed encoding,
    // fields in declaration order. A `Value`'s bytes are key-sorted in a build
    // of targo-trust alone and would not be the compiler's address
    // (CLEAN-CIC-TYPED-ADDRESS-1). Unknown JSON fields do not survive the
    // decode, so a rebound forged field is still caught by the round trip.
    let typed: trust_ir::ProofEvidence =
        serde_json::from_value(artifact.metadata.clone().expect("fixture metadata"))
            .expect("fixture metadata decodes as a typed certificate");
    let bytes = serde_json::to_vec(&typed).unwrap();
    let mut hash = Sha256::new();
    hash.update(b"trustc.digest-frame.v1");
    hash.update((domain.len() as u64).to_be_bytes());
    hash.update(domain.as_bytes());
    hash.update((bytes.len() as u64).to_be_bytes());
    hash.update(&bytes);
    let digest = format!("{:x}", hash.finalize());
    let proof_id = format!("clean-cic:v2:{digest}");
    artifact.digest = Some(trust_types::TransportArtifactDigest {
        algorithm: "sha256".into(),
        value: digest.clone(),
    });
    artifact.artifact_id = Some(proof_id.clone());
    artifact.uri = Some(format!("trust-certify://clean-cic/{digest}"));
    proof.proof_id = Some(proof_id);
}

fn edit_payload(
    row: &mut TransportObligationResult,
    edit: impl FnOnce(&mut trust_ir::ProofEvidence),
) {
    let artifact = &mut proof_mut(row).artifacts[0];
    let mut payload = serde_json::from_value(artifact.metadata.clone().unwrap()).unwrap();
    edit(&mut payload);
    artifact.metadata = Some(serde_json::to_value(payload).unwrap());
    rebind_certificate(row, "trustc.transport-clean-cic.v2");
}

pub(super) fn kernel_transport() -> TransportObligationResult {
    // This is the canonical compiler transport shape, not a claim that these
    // fixture bytes are a kernel proof. The live authenticated producer remains
    // the authority; this consumer only checks its structural publication contract.
    let payload = serde_json::to_value(trust_ir::ProofEvidence::CleanCic {
        term: vec![1, 2, 3, 5, 8],
        context: vec![13, 21],
        lineage: trust_ir::ProofDigest::sha256([0xab; 32]),
        kernel_recheck: None,
    })
    .unwrap();
    let strength = ProofStrength {
        reasoning: ReasoningKind::Constructive,
        assurance: AssuranceLevel::Certified,
    };
    let mut row = TransportObligationResult {
        assumes: Vec::new(),
        gap_class: None,
        obligation_id: Some("self-build:kernel:0".into()),
        claim_digest_sha256: Some("c".repeat(64)),
        kind: "assert".into(),
        original_vc_snapshot: None,
        typed_kind: None,
        description: "kernel-certified bounded compiler obligation".into(),
        location: None,
        outcome: trust_types::Outcome::Proved,
        solver: "clean-kernel".into(),
        time_ms: 1,
        counterexample: None,
        counterexample_model: None,
        reason: None,
        design_mandate: false,
        native_trust_ir: None,
        proof_evidence: Some(TransportProofEvidence {
            suite: "trust-certify".into(),
            backend: "clean-kernel".into(),
            request_id: None,
            proof_id: None,
            native_id: None,
            status: TransportProofStatus::Proved,
            strength: Some(strength.clone()),
            evidence: Some(ProofEvidence::from(strength).with_kernel_reference(
                trust_types::KernelTheoryId::LeanReferenceV1,
                trust_types::KernelEnvDigest([0x2a; 32]),
            )),
            artifacts: vec![trust_types::TransportEvidenceArtifact {
                kind: "clean_cic".into(),
                format: Some("trust-ir-cleancic-v2".into()),
                artifact_id: None,
                digest: None,
                uri: None,
                materialization: None,
                metadata: Some(payload),
            }],
            diagnostics: Vec::new(),
        }),
        monitor: None,
        grade: None,
    };
    rebind_certificate(&mut row, "trustc.transport-clean-cic.v2");
    row
}

#[test]
fn canonical_clean_cic_certificate_has_its_own_binding_class() {
    let root = tempfile::tempdir().unwrap();
    let row = kernel_transport();
    let binding = proof_binding_summary(&row, root.path());
    assert_eq!(binding["accepted"], true);
    assert_eq!(binding["publication_grade_clean_cic_proof"], true);
    assert_eq!(binding["publication_grade_native_proof"], false);
    assert_eq!(binding["canonical_sha256_digest_binding"], true);
    assert_eq!(binding["materialized_artifact_or_transcript_binding"], false);
    assert_eq!(binding["digest_matches_materialized_path"], false);
    assert_eq!(binding["digest_matches_inline_materialization"], false);
    assert_eq!(
        binding["required_artifact_materialization"]["mode"],
        "clean_cic_kernel_certificate"
    );
    assert_eq!(binding["required_artifact_materialization"]["complete"], true);
    assert_eq!(binding["artifact_evidence"][0]["canonical_clean_cic_certificate_binding"], true);
    assert_eq!(binding["artifact_evidence"][0]["metadata_materialization_credit"], false);
}

#[test]
fn clean_cic_binding_rejects_certificate_and_authority_forgeries() {
    type Mutation = (&'static str, fn(&mut TransportObligationResult));
    let mutations: &[Mutation] = &[
        ("missing-proof", |row| row.proof_evidence = None),
        ("unproved-row", |row| row.outcome = trust_types::Outcome::Unknown),
        ("unproved-proof", |row| proof_mut(row).status = TransportProofStatus::Unknown),
        ("wrong-suite", |row| proof_mut(row).suite = "trust-mc".into()),
        ("wrong-backend", |row| proof_mut(row).backend = "trust-mc".into()),
        ("native-request-id", |row| proof_mut(row).request_id = Some("1".into())),
        ("native-proof-id", |row| proof_mut(row).native_id = Some("native".into())),
        ("missing-strength", |row| proof_mut(row).strength = None),
        ("wrong-reasoning", |row| {
            proof_mut(row).strength.as_mut().unwrap().reasoning = ReasoningKind::Smt
        }),
        ("wrong-assurance", |row| {
            proof_mut(row).strength.as_mut().unwrap().assurance = AssuranceLevel::Trusted
        }),
        ("missing-evidence", |row| proof_mut(row).evidence = None),
        ("wrong-evidence-reasoning", |row| {
            proof_mut(row).evidence.as_mut().unwrap().reasoning = ReasoningKind::Smt
        }),
        ("wrong-evidence-assurance", |row| {
            proof_mut(row).evidence.as_mut().unwrap().assurance = AssuranceLevel::Trusted
        }),
        ("missing-theory", |row| proof_mut(row).evidence.as_mut().unwrap().kernel_theory = None),
        ("missing-environment", |row| proof_mut(row).evidence.as_mut().unwrap().env_digest = None),
        ("diagnostic", |row| {
            proof_mut(row).diagnostics.push(trust_types::TransportEvidenceDiagnostic {
                code: "unverified".into(),
                severity: trust_types::TransportEvidenceDiagnosticSeverity::Error,
                message: "not a published proof".into(),
                detail: None,
            });
        }),
        ("missing-artifact", |row| proof_mut(row).artifacts.clear()),
        ("duplicate-artifact", |row| {
            let duplicate = proof_mut(row).artifacts[0].clone();
            proof_mut(row).artifacts.push(duplicate);
        }),
        ("wrong-kind", |row| proof_mut(row).artifacts[0].kind = "certificate".into()),
        ("wrong-format", |row| proof_mut(row).artifacts[0].format = Some("other".into())),
        ("wrong-artifact-id", |row| proof_mut(row).artifacts[0].artifact_id = Some("other".into())),
        ("wrong-proof-id", |row| proof_mut(row).proof_id = Some("other".into())),
        ("wrong-uri", |row| proof_mut(row).artifacts[0].uri = Some("artifact://other".into())),
        ("missing-digest", |row| proof_mut(row).artifacts[0].digest = None),
        ("wrong-digest", |row| {
            proof_mut(row).artifacts[0].digest.as_mut().unwrap().value = "a".repeat(64)
        }),
        ("wrong-domain", |row| rebind_certificate(row, "trustc.transport-clean-cic.v1")),
        ("missing-payload", |row| proof_mut(row).artifacts[0].metadata = None),
        ("changed-payload", |row| {
            proof_mut(row).artifacts[0].metadata.as_mut().unwrap()["CleanCic"]["term"] = json!([9]);
        }),
        ("rebound-empty-term", |row| {
            edit_payload(row, |payload| {
                if let trust_ir::ProofEvidence::CleanCic { term, .. } = payload {
                    term.clear();
                }
            })
        }),
        ("rebound-empty-context", |row| {
            edit_payload(row, |payload| {
                if let trust_ir::ProofEvidence::CleanCic { context, .. } = payload {
                    context.clear();
                }
            })
        }),
        ("rebound-zero-lineage", |row| {
            edit_payload(row, |payload| {
                if let trust_ir::ProofEvidence::CleanCic { lineage, .. } = payload {
                    *lineage = trust_ir::ProofDigest::sha256([0; 32]);
                }
            })
        }),
        ("rebound-unknown-field", |row| {
            proof_mut(row).artifacts[0].metadata.as_mut().unwrap()["CleanCic"]["forged"] =
                json!(true);
            rebind_certificate(row, "trustc.transport-clean-cic.v2");
        }),
        ("materialization", |row| {
            proof_mut(row).artifacts[0].materialization = Some(
                trust_types::TransportArtifactMaterialization::from_exact_bytes(
                    b"unrelated",
                    "unrelated",
                    vec![],
                )
                .unwrap(),
            );
        }),
    ];
    assert_eq!(mutations.len(), 33);
    let root = tempfile::tempdir().unwrap();
    let original = kernel_transport();
    for (name, mutate) in mutations {
        let mut row = original.clone();
        mutate(&mut row);
        assert!(!transport_obligation_has_publishable_clean_cic_proof(&row), "{name}");
        let binding = proof_binding_summary(&row, root.path());
        assert_eq!(binding["publication_grade_clean_cic_proof"], false, "{name}");
        assert_eq!(binding["accepted"], false, "{name}");
    }
}

#[test]
fn clean_cic_binding_preserves_supplied_native_materialization_checks() {
    let root = tempfile::tempdir().unwrap();
    let mut original = kernel_transport();
    original.native_trust_ir = Some(trust_types::TransportNativeTrustIrEvidence {
        suite: "trust-mc".into(),
        backend: "trust-mc".into(),
        request_id: Some("1".into()),
        native_id: Some("trust_ir-native-trust-mc-request-1-proof-1".into()),
        present: true,
        artifacts: native_shape_artifacts("trust-mc", "1", "1"),
        diagnostics: Vec::new(),
    });
    let valid = proof_binding_summary(&original, root.path());
    assert_eq!(valid["accepted"], true);
    assert_eq!(valid["publication_grade_native_proof"], false);
    assert_eq!(valid["kernel_certificate_binding"], true);

    type Mutation = (&'static str, fn(&mut trust_types::TransportEvidenceArtifact));
    let mutations: &[Mutation] = &[
        ("escaped-path", |artifact| {
            let materialization = artifact.materialization.as_mut().unwrap();
            materialization.materialized_path = Some("../escaped-artifact".into());
            materialization.encoded_bytes.clear();
        }),
        ("wrong-digest", |artifact| artifact.digest.as_mut().unwrap().value = "a".repeat(64)),
        ("missing-digest", |artifact| artifact.digest = None),
        ("changed-inline-bytes", |artifact| {
            artifact.materialization.as_mut().unwrap().encoded_bytes.push_str("ff");
        }),
    ];
    for (name, mutate) in mutations {
        let mut row = original.clone();
        mutate(&mut row.native_trust_ir.as_mut().unwrap().artifacts[0]);
        let binding = proof_binding_summary(&row, root.path());
        assert_eq!(binding["publication_grade_clean_cic_proof"], true, "{name}");
        assert_eq!(binding["kernel_certificate_binding"], false, "{name}");
        assert_eq!(
            binding["required_artifact_materialization"]["native_materialization_paths_secure"],
            false,
            "{name}"
        );
        assert_eq!(binding["accepted"], false, "{name}");
    }
}

#[test]
fn retained_kernel_row_does_not_close_source_or_execution_provenance() {
    let root = tempfile::tempdir().unwrap();
    let mut summary = TransportSummary::default();
    let target = cargo_identity_fixture(0, "primary");
    let row = kernel_transport();
    ingest_result_rows(
        &mut summary,
        &target,
        &json!({"total": 1, "results": [row]}),
        root.path(),
        "authenticated-consumer-fixture",
        1,
        Some("compiler::checked"),
    );
    assert_eq!(summary.verification_rows.len(), 1);
    assert_eq!(summary.verification_rows[0]["complete"], true);
    assert_eq!(summary.obligation_evidence.len(), 1);
    assert_eq!(summary.obligation_evidence[0]["native_trust_ir"], Value::Null);
    assert_eq!(
        summary.obligation_evidence[0]["proof_evidence"],
        summary.verification_rows[0]["proof_evidence"]
    );
    assert!(summary.coverage_blockers.is_empty(), "{:?}", summary.coverage_blockers);
    assert!(!summary.source_provenance_bound);
    assert!(!summary.stage2_execution_identity_bound);
    let suite = solver_suite_json(&summary);
    let proof = evaluate_proof("passed", Some(0), false, &suite);
    assert_eq!(proof["complete"], false);
}
