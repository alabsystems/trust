#![cfg(unix)]

use std::os::unix::fs::PermissionsExt as _;
use std::path::Path;
use std::process::Command;

use trust_proof_cert::{
    BinaryCertificateCheckRequest, SolverProofExport, StructuralBinaryCertificateChecker,
    check_binary_certificate, persist_solver_proof_export_artifacts,
};
use trust_types::{
    BinaryArtifactDigest, BinaryArtifactDigestIdentity, BinaryOrigin, BinarySelectedImageIdentity,
    Formula, SerializableVc, SolverDispatchRecord, SolverDispatchStatus, SolverQuerySemantics,
    SourceSpan, VcKind, VerificationCondition,
};

const SUPERVISOR_SUBCOMMAND: &str = "__targo_checked_certificate_checker";

fn supervisor_args(root: &Path, checker_source: &[u8]) -> Vec<String> {
    let checker_path = root.join("checker.sh");
    std::fs::write(&checker_path, checker_source).expect("write checker");
    std::fs::set_permissions(&checker_path, std::fs::Permissions::from_mode(0o700))
        .expect("make checker executable");

    let digest = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "main".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
        obligation: None,
    };
    let serializable_vc = SerializableVc::from_vc(&vc);
    // Same canonical form the supervisor's production path uses
    // (`verify_binary_evidence::canonical_vc_bytes`): an additive
    // `#[serde(default)] Option<_>` VC field must not move a certificate digest,
    // and a raw `serde_json::to_vec` here would drift from the binding under test.
    let canonical_vc =
        trust_types::stable_model_json_bytes(&serializable_vc).expect("serialize VC");
    let dispatch = SolverDispatchRecord {
        id: "external-checker-integration:vc0".to_string(),
        function: Some("main".to_string()),
        origin: Some(BinaryOrigin {
            binary_path: Some("fixture.bin".to_string()),
            function_entry: Some(0x401000),
            instruction_address: 0x401010,
            instruction_size: Some(1),
            encoding: Some(0x90),
            instruction_bytes: vec![0x90],
            source: Some(SourceSpan::binary_address(0x401010)),
        }),
        vc_kind: Some(vc.kind),
        vc: Some(serializable_vc),
        solver: "fixture-solver".to_string(),
        backend: Some("fixture-backend".to_string()),
        status: SolverDispatchStatus::Unsat,
        query_semantics: SolverQuerySemantics::SatIsCounterexample,
        binary_artifact_digest_identity: Some(BinaryArtifactDigestIdentity {
            root_artifact_digest: Some(BinaryArtifactDigest::sha256(digest)),
            selected_image: Some(BinarySelectedImageIdentity {
                file_offset: 0,
                file_size: 64,
                sha256: digest.to_string(),
            }),
        }),
        ..Default::default()
    };
    let export = SolverProofExport::new(
        &dispatch,
        &canonical_vc,
        "lrat",
        b"external checker integration proof".to_vec(),
        Some("fixture-1".to_string()),
        1_777_070_400_000,
    );
    let structural_checker = StructuralBinaryCertificateChecker::new(
        "fixture-structural-checker",
        "1",
        vec!["lrat".to_string()],
        1_777_070_401_000,
    );
    let checked = check_binary_certificate(
        &structural_checker,
        BinaryCertificateCheckRequest::from_export(&dispatch, &canonical_vc, &export),
    );
    assert!(checked.accepted, "{:?}", checked.error);
    let certificate = checked.certificate.expect("checked certificate");
    let certificate_path = root.join("checked-certificate.json");
    std::fs::write(
        &certificate_path,
        certificate.to_json().expect("serialize checked certificate"),
    )
    .expect("write checked certificate");
    let proof_artifacts = persist_solver_proof_export_artifacts(root, &export)
        .expect("persist proof export artifacts");

    vec![
        checker_path.display().to_string(),
        trust_types::digest::stable_sha256_hex(checker_source),
        "--checked-certificate".to_string(),
        certificate_path.display().to_string(),
        "--solver-proof-export-metadata".to_string(),
        proof_artifacts.metadata_path.display().to_string(),
        "--solver-proof-payload".to_string(),
        proof_artifacts.proof_path.display().to_string(),
        "--vc-sha256".to_string(),
        certificate.vc_sha256,
        "--origin-sha256".to_string(),
        certificate.origin_sha256,
        "--assumption-digest".to_string(),
        certificate.assumption_digest,
        "--certificate-sha256".to_string(),
        certificate.certificate_sha256,
        "--proof-export-sha256".to_string(),
        certificate.proof_export_sha256,
        "--proof-sha256".to_string(),
        certificate.proof_sha256,
    ]
}

#[test]
fn binary_supervisor_accepts_bound_evidence_and_rejects_bare_exit_zero() {
    let root = tempfile::tempdir().expect("supervisor integration fixture");
    let accepting_checker = b"#!/bin/sh\nchallenge=\nwhile [ \"$#\" -gt 0 ]; do\n  if [ \"$1\" = \"--targo-evidence-challenge\" ]; then shift; challenge=$1; fi\n  shift\ndone\nprintf 'TRUST_CHECKED_CERTIFICATE_ACCEPTED:%s\\n' \"$challenge\"\n";
    let accepting_args = supervisor_args(root.path(), accepting_checker);
    let accepted = Command::new(env!("CARGO_BIN_EXE_targo-trust"))
        .arg(SUPERVISOR_SUBCOMMAND)
        .args(&accepting_args)
        .output()
        .expect("run non-test Targo checker supervisor");
    assert!(
        accepted.status.success(),
        "stdout={}\nstderr={}",
        String::from_utf8_lossy(&accepted.stdout),
        String::from_utf8_lossy(&accepted.stderr)
    );
    assert!(
        String::from_utf8_lossy(&accepted.stdout).contains("TRUST_CHECKED_CERTIFICATE_ACCEPTED:")
    );

    let rejecting_root = tempfile::tempdir().expect("bare checker integration fixture");
    let bare_args = supervisor_args(rejecting_root.path(), b"#!/bin/sh\nexit 0\n");
    let rejected = Command::new(env!("CARGO_BIN_EXE_targo-trust"))
        .arg(SUPERVISOR_SUBCOMMAND)
        .args(&bare_args)
        .output()
        .expect("run non-test Targo checker supervisor with bare checker");
    assert_eq!(rejected.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&rejected.stderr).contains("exactly one"));
}
