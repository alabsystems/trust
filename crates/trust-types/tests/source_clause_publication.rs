use std::path::Path;

use trust_types::*;

fn fixture() -> (
    TransportProofEvidence,
    trust_types::obligation_identity::ObligationIdentity,
    OriginalVcSnapshot,
) {
    let proof: TransportProofEvidence =
        serde_json::from_str(include_str!("fixtures/source_clause_transport.json")).unwrap();
    let owner = "obligation:source_clause_fixture__constant_false:postcondition:0";
    #[derive(serde::Deserialize)]
    struct Certificate {
        source: Source,
    }
    #[derive(serde::Deserialize)]
    struct Source {
        source_vc: VerificationCondition,
        source_text_sha256: String,
        overflow_checks: bool,
        target: String,
    }
    let source = trust_types::json_depth::from_str_deep::<Certificate>(include_str!(
        "fixtures/source_clause_certificate.json"
    ))
    .unwrap()
    .source;
    // This is a structural-only fixture. Live Targo tests independently derive
    // the digest from the exact original typed source and callee inputs.
    let typed = "1".repeat(64);
    let digest = trust_types::original_vc_snapshot::exact_vc_claim_digest_with_typed_input_sha256(
        &source.source_vc,
        source.overflow_checks,
        Some(&source.target),
        Some(&typed),
    )
    .unwrap();
    let snapshot = OriginalVcSnapshot::capture_with_typed_input_digest(
        &source.source_vc,
        source.overflow_checks,
        &source.target,
        owner,
        &digest,
        Some(&typed),
    )
    .unwrap();
    let identity = trust_types::obligation_identity::ObligationIdentity {
        key: "source_clause_fixture::constant_false#0".into(),
        package: "source_clause_fixture".into(),
        function_source_sha256: Some(source.source_text_sha256),
        expanded_function_identity: None,
    };
    (proof, identity, snapshot)
}

fn check(
    proof: &TransportProofEvidence,
    identity: &trust_types::obligation_identity::ObligationIdentity,
    snapshot: &OriginalVcSnapshot,
    root: Option<&Path>,
) -> Result<Vec<u8>, String> {
    source_clause_certificate_payload(
        proof,
        Some(&snapshot.obligation_id),
        Some(identity),
        Some(&snapshot.claim_digest_sha256),
        Some(snapshot),
        root,
    )
}

#[test]
fn source_clause_bound_claim_cannot_add_remove_or_replace_original_input() {
    let (_, _, snapshot) = fixture();
    let vc =
        snapshot.decode_for_row(&snapshot.obligation_id, &snapshot.claim_digest_sha256).unwrap();
    let legacy = original_vc_snapshot::exact_vc_claim_digest_sha256(
        &vc,
        snapshot.overflow_checks,
        Some(&snapshot.target),
    )
    .unwrap();
    assert_eq!(
        original_vc_snapshot::exact_vc_claim_digest_with_typed_input_sha256(
            &vc,
            snapshot.overflow_checks,
            Some(&snapshot.target),
            None
        ),
        Some(legacy.clone())
    );
    let old = OriginalVcSnapshot::capture(
        &vc,
        snapshot.overflow_checks,
        &snapshot.target,
        &snapshot.obligation_id,
        &legacy,
    )
    .unwrap();
    assert!(!serde_json::to_string(&old).unwrap().contains("typed_input_digest_sha256"));
    let mut modified = old;
    modified.typed_input_digest_sha256 = Some("1".repeat(64));
    assert!(modified.decode_for_row(&snapshot.obligation_id, &legacy).is_err());
    for replacement in [None, Some("2".repeat(64))] {
        let mut modified = snapshot.clone();
        modified.typed_input_digest_sha256 = replacement;
        assert!(
            modified
                .decode_for_row(&snapshot.obligation_id, &snapshot.claim_digest_sha256)
                .is_err()
        );
    }
    assert!(
        original_vc_snapshot::exact_vc_claim_digest_with_typed_input_sha256(
            &vc,
            snapshot.overflow_checks,
            Some(&snapshot.target),
            Some("invalid")
        )
        .is_none()
    );
}

#[test]
fn actual_source_clause_structure_binds_exact_source_and_snapshot() {
    let (proof, identity, snapshot) = fixture();
    let payload = check(&proof, &identity, &snapshot, None).unwrap();
    assert_eq!(
        trust_types::stable_sha256_hex(&payload),
        "e8e513e0b475bac21f6083f4c48d2ab53451cb8d8d1bb739228b86f0459b67f9"
    );
    let mut other = identity.clone();
    other.function_source_sha256 = Some("0".repeat(64));
    assert!(check(&proof, &other, &snapshot, None).is_err());
    let mut other = snapshot.clone();
    other.overflow_checks = !other.overflow_checks;
    assert!(check(&proof, &identity, &other, None).is_err());
    let mut other = snapshot.clone();
    other.obligation_id.push('x');
    assert!(check(&proof, &identity, &other, None).is_err());
    let mut other = snapshot.clone();
    other.target.push('x');
    assert!(check(&proof, &identity, &other, None).is_err());
    let mut other = snapshot.clone();
    other.original_vc_json.push(' ');
    assert!(check(&proof, &identity, &other, None).is_err());
}

#[test]
fn actual_source_clause_structure_refuses_mixed_artifacts_and_stronger_grade() {
    let (proof, identity, snapshot) = fixture();
    for mutation in 0..12 {
        let mut changed = proof.clone();
        match mutation {
            0 => changed.artifacts.push(changed.artifacts[0].clone()),
            1 => changed.request_id = Some("0".into()),
            2 => changed.native_id = Some("forged".into()),
            3 => changed.backend = "clean-kernel".into(),
            4 => changed.strength.as_mut().unwrap().assurance = AssuranceLevel::Certified,
            5 => changed.evidence.as_mut().unwrap().assurance = AssuranceLevel::Certified,
            6 => changed.artifacts[0].uri.as_mut().unwrap().push('x'),
            7 => changed.artifacts[0]
                .materialization
                .as_mut()
                .unwrap()
                .encoded_bytes
                .replace_range(0..2, "00"),
            8 => changed.artifacts[0].format = Some("trust-wp.trust-ir-body-wp.v1".into()),
            9 => changed.proof_id = Some("source-clause:v1:forged".into()),
            10 => changed.artifacts[0].materialization.as_mut().unwrap().referenced_artifacts.push(
                TransportArtifactReference {
                    kind: "ProofCertificate".into(),
                    digest: TransportArtifactDigest {
                        algorithm: "sha256".into(),
                        value: "0".repeat(64),
                    },
                },
            ),
            _ => changed.artifacts[0].metadata = Some("unexpected".into()),
        }
        assert!(check(&changed, &identity, &snapshot, None).is_err(), "mutation {mutation}");
    }
}

#[test]
fn actual_source_clause_path_materialization_requires_trusted_root() {
    let (mut proof, identity, snapshot) = fixture();
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path().canonicalize().unwrap();
    let relative = format!(
        ".trust-proof-artifacts/sha256/{}",
        proof.artifacts[0].digest.as_ref().unwrap().value
    );
    let materialization = proof.artifacts[0].materialization.as_mut().unwrap();
    let bytes = materialization.decoded_bytes().unwrap();
    let path = root.join(&relative);
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(&path, &bytes).unwrap();
    materialization.materialized_path = Some(relative);
    materialization.encoded_bytes.clear();
    assert!(check(&proof, &identity, &snapshot, None).is_err());
    assert!(check(&proof, &identity, &snapshot, Some(&root)).is_ok());
    std::fs::write(&path, b"corrupt").unwrap();
    assert!(check(&proof, &identity, &snapshot, Some(&root)).is_err());
}
