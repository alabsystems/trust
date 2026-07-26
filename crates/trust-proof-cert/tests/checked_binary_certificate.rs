// Test fixtures construct nested arrays of (label, closure, expectation) tuples
// to drive the certificate audit matrix. The inlined types make the fixture
// readable; a type alias would just push the same shape one indirection away.
#![allow(clippy::type_complexity)]

use trust_proof_cert::binary_decomp::{
    BinaryArtifactTrustLevel, BinaryReleaseGateRejection, BinaryVerificationCertificateSummary,
    UnsupportedLedgerSummary, digest_lifted_binary,
};
use trust_proof_cert::{
    AuditOnlyRawSolverProofBytes, BinaryCertificateCheckRequest, BinaryCertificateCheckResult,
    CertError, CheckError, CheckedBinaryCertificateArtifact,
    CheckedBinaryCertificateArtifactIdentity, CheckedBinaryCertificateArtifactRef,
    CheckedBinaryCertificateAuditExport, CheckedBinaryCertificateAuditExportBundleRejectionCode,
    CheckedBinaryCertificateAuditExportBundleValidationRow,
    CheckedBinaryCertificateCheckerInvocationKind, CheckedBinaryCertificateCheckerSelection,
    CheckedBinaryCertificateExternalCheckerRunner,
    CheckedBinaryCertificateExternalProcessProofArtifactArgument,
    CheckedBinaryCertificateExternalProcessTranscript, CheckedBinaryCertificateManifest,
    CheckedBinaryCertificateManifestAcceptanceRequest, CheckedBinaryCertificateManifestEntry,
    CheckedBinaryCertificateManifestIdentityEntry,
    CheckedBinaryCertificateProductionCheckerEvidence, CheckedBinaryCertificateProductionManifest,
    CheckedBinaryCertificateProductionManifestAcceptedRowInput,
    CheckedBinaryCertificateProductionManifestInput,
    CheckedBinaryCertificateProductionManifestRejection,
    CheckedBinaryCertificateReplayTranscriptBinding,
    CheckedBinaryCertificateSourceBackpropagationGate, SolverProofExport,
    StructuralBinaryCertificateChecker, accept_checked_certificate_manifest_entry,
    apply_checked_certificate_to_dispatch, check_binary_certificate,
    checked_certificate_audit_export_bundle_path, checked_certificate_manifest_path,
    checked_certificate_status_production_checker_evidence, digest_binary_origin,
    digest_model_assumptions, import_checked_certificate_artifact_for_dispatch,
    import_checked_certificate_for_dispatch,
    import_checked_certificate_for_dispatch_by_canonical_digests,
    import_checked_certificate_manifest_entry_for_dispatch,
    import_content_addressed_checked_certificate_for_dispatch,
    load_checked_certificate_artifact_ref, load_checked_certificate_audit_export,
    load_checked_certificate_audit_export_bundle,
    load_checked_certificate_audit_export_bundle_complete_vc_coverage,
    load_checked_certificate_audit_export_bundle_rows, load_checked_certificate_manifest,
    load_content_addressed_checked_certificate_artifact, persist_checked_certificate_artifact,
    persist_checked_certificate_audit_export, persist_checked_certificate_audit_export_bundle,
    produce_checked_certificate_artifact,
};
use trust_types::{
    BinaryArtifactDigest, BinaryArtifactDigestIdentity, BinaryOrigin, BinarySelectedImageIdentity,
    BinarySourceProvenanceSummary, ModelAssumption, ProofCertificateStatus, ReplayStatus,
    SolverDispatchRecord, SolverDispatchStatus, SolverQuerySemantics, SourceSpan,
    UnsupportedLedger, UnsupportedRecord, VerificationResult,
};

fn temp_artifact_dir(name: &str) -> std::path::PathBuf {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system time should be after Unix epoch")
        .as_nanos();
    std::env::temp_dir().join(format!("trust-proof-cert-{name}-{}-{unique}", std::process::id()))
}

fn proved_dispatch(id: &str) -> SolverDispatchRecord {
    SolverDispatchRecord {
        id: id.to_string(),
        function: Some("sym.main".to_string()),
        solver: "ay".to_string(),
        backend: Some("ay-lrat".to_string()),
        status: SolverDispatchStatus::Unsat,
        query_semantics: SolverQuerySemantics::SatIsCounterexample,
        replay: ReplayStatus::Replayed,
        origin: Some(binary_origin()),
        binary_artifact_digest_identity: Some(binary_artifact_digest_identity()),
        certificate: ProofCertificateStatus::Present {
            format: "lrat".to_string(),
            sha256: None,
            artifact_path: None,
        },
        ..Default::default()
    }
}

fn binary_origin() -> BinaryOrigin {
    BinaryOrigin {
        binary_path: Some("fixtures/tiny".to_string()),
        function_entry: Some(0x401000),
        instruction_address: 0x401010,
        instruction_size: Some(4),
        encoding: Some(0x90),
        instruction_bytes: vec![0x90, 0x90, 0x90, 0x90],
        source: None,
    }
}

fn binary_artifact_digest_identity() -> BinaryArtifactDigestIdentity {
    BinaryArtifactDigestIdentity {
        root_artifact_digest: Some(BinaryArtifactDigest::sha256(trust_types::stable_sha256_hex(
            b"fixtures/tiny root artifact",
        ))),
        selected_image: Some(BinarySelectedImageIdentity {
            file_offset: 0,
            file_size: 4,
            sha256: trust_types::stable_sha256_hex(&[0x90, 0x90, 0x90, 0x90]),
        }),
    }
}

fn checked_certificate_checker() -> StructuralBinaryCertificateChecker {
    StructuralBinaryCertificateChecker::new(
        "ay-lrat-binary-check",
        "0.1.0",
        vec!["lrat".to_string()],
        1_777_070_401_000,
    )
}

fn proof_export(dispatch: &SolverDispatchRecord, canonical_vc_bytes: &[u8]) -> SolverProofExport {
    SolverProofExport::new(
        dispatch,
        canonical_vc_bytes,
        "lrat",
        b"normalized lrat proof bytes bound to vc0".to_vec(),
        Some("4.13.0".to_string()),
        1_777_070_400_000,
    )
}

fn proof_grade_summary(
    dispatches: &[SolverDispatchRecord],
) -> BinaryVerificationCertificateSummary {
    proof_grade_summary_with_ledger(dispatches, &UnsupportedLedger::default())
}

fn proof_grade_summary_with_ledger(
    dispatches: &[SolverDispatchRecord],
    ledger: &UnsupportedLedger,
) -> BinaryVerificationCertificateSummary {
    BinaryVerificationCertificateSummary::from_solver_dispatch_records(
        digest_lifted_binary(b"checked-binary-certificate-test"),
        "trust_ir+binary",
        "x86_64-unknown-linux-gnu",
        ledger,
        dispatches,
        BinaryArtifactTrustLevel::ProofGrade,
    )
    .expect("binary certificate summary should build")
}

fn is_canonical_lowercase_sha256(value: &str) -> bool {
    value.len() == 64
        && value.bytes().all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

fn checked_manifest_fixture(name: &str) -> (std::path::PathBuf, CheckedBinaryCertificateManifest) {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("vc0");
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let dir = temp_artifact_dir(name);
    let artifact_ref = produce_checked_certificate_artifact(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export),
        &dir,
    )
    .expect("production helper should persist checked artifact");
    let artifact = load_checked_certificate_artifact_ref(&artifact_ref)
        .expect("manifest fixture artifact should reload");
    let relative_path = artifact_ref
        .path
        .strip_prefix(&dir)
        .expect("artifact path should be under fixture root")
        .to_path_buf();
    let mut manifest = CheckedBinaryCertificateManifest::new();
    manifest.add_certificate(CheckedBinaryCertificateManifestEntry::from_artifact(
        &artifact,
        relative_path,
    ));
    (dir, manifest)
}

fn checked_manifest_acceptance_fixture(
    name: &str,
) -> (std::path::PathBuf, CheckedBinaryCertificateManifest, SolverProofExport, String) {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("export-run:vc0");
    let mut export = proof_export(&dispatch, canonical_vc_bytes);
    export.stdout_digest = Some(trust_types::stable_sha256_hex(b"deterministic solver stdout"));
    export.stderr_digest = Some(trust_types::stable_sha256_hex(b"deterministic solver stderr"));
    let checker = checked_certificate_checker();
    let replay_transcript_digest = trust_types::stable_sha256_hex(b"deterministic replay transcript for acceptance");
    let dir = temp_artifact_dir(name);
    let mut request =
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export);
    request.replay_transcript_digest = Some(&replay_transcript_digest);

    let artifact_ref = produce_checked_certificate_artifact(&checker, request, &dir)
        .expect("production helper should persist checked artifact");
    let manifest = CheckedBinaryCertificateManifest::from_artifact_refs(&dir, &[artifact_ref])
        .expect("checked artifact ref should export into a manifest row");

    (dir, manifest, export, replay_transcript_digest)
}

fn production_checker_evidence(
    entry: &CheckedBinaryCertificateManifestEntry,
) -> CheckedBinaryCertificateProductionCheckerEvidence {
    let transcript = CheckedBinaryCertificateExternalProcessTranscript::new(
        "ay-lrat-binary-check",
        [
            "ay-lrat-binary-check".to_string(),
            "--format".to_string(),
            entry.format.clone(),
            "--certificate".to_string(),
            entry.certificate_path.display().to_string(),
        ],
        0,
        Some(trust_types::stable_sha256_hex(b"checker stdout: accepted")),
        Some(trust_types::stable_sha256_hex(b"")),
    );
    CheckedBinaryCertificateProductionCheckerEvidence::external_process_for_manifest_entry(
        entry,
        trust_types::stable_sha256_hex(b"ay-lrat-binary-check production executable"),
        Some(trust_types::stable_sha256_hex(b"ay-lrat production checker config")),
        transcript,
        1_777_070_401_000,
    )
    .expect("external checker process evidence should build")
}

fn production_acceptance_request(
    entry: &CheckedBinaryCertificateManifestEntry,
    export: &SolverProofExport,
) -> CheckedBinaryCertificateManifestAcceptanceRequest {
    CheckedBinaryCertificateManifestAcceptanceRequest::from_manifest_entry_and_solver_proof_export_metadata(
        entry,
        export.normalized_metadata(),
    )
    .expect("acceptance request should bind normalized solver proof export metadata")
    .with_production_checker_evidence(production_checker_evidence(entry))
    .expect("acceptance request should bind production checker evidence")
}

fn exact_source_provenance_summary() -> BinarySourceProvenanceSummary {
    BinarySourceProvenanceSummary {
        status: "exact".to_string(),
        exact_mapping_count: 1,
        ambiguous_mapping_count: 0,
        diagnostics: vec!["exact debug/source provenance accepted for entry".to_string()],
        source_backpropagation_allowed: true,
    }
}

fn unresolved_unsupported_ledger() -> UnsupportedLedger {
    UnsupportedLedger {
        records: vec![UnsupportedRecord {
            stage: "lift".to_string(),
            architecture: Some("x86_64".to_string()),
            origin: Some(binary_origin()),
            opcode: Some("syscall".to_string()),
            operand: None,
            feature: "system-call-side-effects".to_string(),
        }],
    }
}

fn complete_source_backpropagation_gate() -> CheckedBinaryCertificateSourceBackpropagationGate {
    CheckedBinaryCertificateSourceBackpropagationGate::evaluated(
        exact_source_provenance_summary(),
        true,
        true,
        true,
        true,
        true,
        true,
    )
}

fn complete_source_backpropagation_gate_for(
    label: &str,
) -> CheckedBinaryCertificateSourceBackpropagationGate {
    let mut source_provenance = exact_source_provenance_summary();
    source_provenance.diagnostics =
        vec![format!("exact debug/source provenance accepted for {label}")];
    CheckedBinaryCertificateSourceBackpropagationGate::evaluated(
        source_provenance,
        true,
        true,
        true,
        true,
        true,
        true,
    )
}

#[cfg(unix)]
fn write_checker_fixture_script(
    dir: &std::path::Path,
    name: &str,
    body: &str,
) -> std::path::PathBuf {
    use std::os::unix::fs::PermissionsExt;

    let path = dir.join(name);
    std::fs::write(&path, body.as_bytes()).expect("checker fixture script should be writable");
    let mut permissions = std::fs::metadata(&path)
        .expect("checker fixture script should have metadata")
        .permissions();
    permissions.set_mode(0o700);
    std::fs::set_permissions(&path, permissions)
        .expect("checker fixture script should be executable");
    path
}

fn checked_certificate_relative_path_for_digest(digest: &str) -> std::path::PathBuf {
    std::path::PathBuf::from("checked-binary-certificates")
        .join(&digest[..2])
        .join(format!("{digest}.checked-binary-certificate.json"))
}

fn assert_production_manifest_rejects_field(
    manifest: &CheckedBinaryCertificateProductionManifest,
    expected_field: &str,
) {
    let decision = manifest.evaluate();
    assert!(!decision.accepted);
    assert!(
        decision.rejections.iter().any(|rejection| matches!(
            rejection,
            CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                field,
                ..
            } if field == expected_field
        )),
        "{:?}",
        decision.rejections
    );
}

fn assert_production_manifest_rejects_after(
    base: &CheckedBinaryCertificateProductionManifest,
    mutate: impl FnOnce(&mut CheckedBinaryCertificateProductionManifest),
    mut expected_rejection: impl FnMut(&CheckedBinaryCertificateProductionManifestRejection) -> bool,
) {
    let mut manifest = base.clone();
    mutate(&mut manifest);
    let decision = manifest.evaluate();
    assert!(!decision.accepted);
    assert!(decision.rejections.iter().any(&mut expected_rejection), "{:?}", decision.rejections);
}

fn recompute_first_row_manifest_identity_sha256(
    manifest: &CheckedBinaryCertificateProductionManifest,
) -> String {
    let entry = manifest.entries.first().expect("production manifest should have one row");
    let evidence = entry.production_evidence.as_ref().expect("production evidence should exist");
    let row_acceptance =
        entry.manifest_row_acceptance.as_ref().expect("manifest row acceptance should exist");
    let gate_row = row_acceptance
        .source_backpropagation_gate_row
        .as_ref()
        .expect("source-backpropagation gate row should exist");
    CheckedBinaryCertificateManifestIdentityEntry {
        schema_version: "checked-binary-certificate-manifest-identity.v1".to_string(),
        manifest_schema_version: "binary-certificate-manifest.v2".to_string(),
        checker_selection: CheckedBinaryCertificateCheckerSelection {
            checker: evidence.checker.clone(),
            checker_version: evidence.checker_version.clone(),
            format: evidence.format.clone(),
        },
        replay_transcript: CheckedBinaryCertificateReplayTranscriptBinding {
            replay: gate_row.replay,
            replay_transcript_digest: gate_row.replay_transcript_digest.clone(),
        },
        artifact_identity: CheckedBinaryCertificateArtifactIdentity {
            dispatch_id: entry.dispatch_id.clone(),
            vc_sha256: gate_row.vc_sha256.clone(),
            origin_sha256: gate_row.origin_sha256.clone(),
            proof_sha256: evidence.proof_sha256.clone(),
            proof_export_sha256: evidence.proof_export_sha256.clone(),
            certificate_sha256: gate_row.certificate_sha256.clone(),
            content_sha256: gate_row.certificate_sha256.clone(),
            certificate_path: gate_row.certificate_path.clone(),
            binary_artifact_digest_identity: evidence.binary_artifact_digest_identity.clone(),
        },
        production_checker_evidence_sha256: row_acceptance
            .production_checker_evidence_sha256
            .clone(),
        source_backpropagation_gate: gate_row.source_backpropagation_gate.clone(),
    }
    .sha256()
    .expect("manifest identity should recompute")
}

#[test]
fn production_checker_evidence_from_external_process_binds_invocation_transcript() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("external-process-evidence");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let transcript = CheckedBinaryCertificateExternalProcessTranscript::new(
        "/usr/bin/ay-lrat-binary-check",
        [
            "/usr/bin/ay-lrat-binary-check".to_string(),
            "--proof-format".to_string(),
            entry.format.clone(),
            "--certificate".to_string(),
            entry.certificate_path.display().to_string(),
        ],
        0,
        Some(trust_types::stable_sha256_hex(b"external checker stdout: accepted")),
        Some(trust_types::stable_sha256_hex(b"external checker stderr: empty")),
    );
    let expected_invocation_sha256 =
        transcript.sha256().expect("successful external transcript should digest");

    let evidence =
        CheckedBinaryCertificateProductionCheckerEvidence::external_process_for_manifest_entry(
            entry,
            trust_types::stable_sha256_hex(b"ay-lrat-binary-check executable"),
            Some(trust_types::stable_sha256_hex(b"ay-lrat-binary-check config")),
            transcript,
            1_777_070_401_000,
        )
        .expect("external process evidence should build");

    evidence.validate_production().expect("evidence should be production-grade");
    assert_eq!(
        evidence.invocation_kind,
        CheckedBinaryCertificateCheckerInvocationKind::ExternalProcess
    );
    assert_eq!(evidence.invocation_sha256, expected_invocation_sha256);
    let expected_stdout_sha256 = trust_types::stable_sha256_hex(b"external checker stdout: accepted");
    let expected_stderr_sha256 = trust_types::stable_sha256_hex(b"external checker stderr: empty");
    assert_eq!(evidence.stdout_sha256.as_deref(), Some(expected_stdout_sha256.as_str()));
    assert_eq!(evidence.stderr_sha256.as_deref(), Some(expected_stderr_sha256.as_str()));
    assert_eq!(evidence.proof_export_sha256, entry.proof_export_sha256);
    assert_eq!(evidence.certificate_sha256, entry.certificate_sha256);

    let acceptance_request =
        CheckedBinaryCertificateManifestAcceptanceRequest::from_manifest_entry_and_solver_proof_export_metadata(
            entry,
            export.normalized_metadata(),
        )
        .expect("acceptance request should bind proof export metadata")
        .with_production_checker_evidence(evidence)
        .expect("acceptance request should accept external process evidence");
    let mut gate_dispatch = proved_dispatch("gate-run:vc0");
    import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect("external process evidence should import as checked production evidence");
    assert!(gate_dispatch.certificate.is_checked());

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn production_checker_evidence_from_external_process_rejects_failed_exit() {
    let (dir, manifest, _, _) = checked_manifest_acceptance_fixture("external-process-failed-exit");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let transcript = CheckedBinaryCertificateExternalProcessTranscript::new(
        "/usr/bin/ay-lrat-binary-check",
        ["/usr/bin/ay-lrat-binary-check".to_string()],
        2,
        Some(trust_types::stable_sha256_hex(b"checker stdout before failure")),
        Some(trust_types::stable_sha256_hex(b"checker stderr failure")),
    );

    let err =
        CheckedBinaryCertificateProductionCheckerEvidence::external_process_for_manifest_entry(
            entry,
            trust_types::stable_sha256_hex(b"ay-lrat-binary-check executable"),
            None,
            transcript,
            1_777_070_401_000,
        )
        .expect_err("nonzero checker exits must not become production evidence");

    assert!(
        matches!(err, CheckError::CheckerExternalProcessFailed { ref command, exit_status: 2 } if command == "/usr/bin/ay-lrat-binary-check"),
        "{err:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn production_checker_evidence_from_external_process_rejects_missing_transcript_digests() {
    let (dir, manifest, _, _) =
        checked_manifest_acceptance_fixture("external-process-missing-transcript-digests");
    let entry = manifest.certificates.first().expect("manifest should have one row");

    for (field, stdout_sha256, stderr_sha256) in [
        ("stdout_sha256", None, Some(trust_types::stable_sha256_hex(b"checker stderr"))),
        ("stderr_sha256", Some(trust_types::stable_sha256_hex(b"checker stdout")), None),
    ] {
        let transcript = CheckedBinaryCertificateExternalProcessTranscript::new(
            "/usr/bin/ay-lrat-binary-check",
            ["/usr/bin/ay-lrat-binary-check".to_string()],
            0,
            stdout_sha256,
            stderr_sha256,
        );
        let err =
            CheckedBinaryCertificateProductionCheckerEvidence::external_process_for_manifest_entry(
                entry,
                trust_types::stable_sha256_hex(b"ay-lrat-binary-check executable"),
                None,
                transcript,
                1_777_070_401_000,
            )
            .expect_err("missing transcript digests must not become production evidence");

        assert!(
            matches!(err, CheckError::MissingCheckerExternalProcessTranscriptDigest { field: ref missing } if missing == field),
            "{err:?}"
        );
    }

    let low_level_evidence =
        CheckedBinaryCertificateProductionCheckerEvidence::production_for_manifest_entry(
            entry,
            trust_types::stable_sha256_hex(b"ay-lrat-binary-check executable"),
            trust_types::stable_sha256_hex(b"legacy invocation digest without transcript digests"),
            1_777_070_401_000,
        );
    let legacy_err = low_level_evidence
        .validate_production()
        .expect_err("external process evidence without transcript digests must fail closed");
    assert!(
        matches!(legacy_err, CheckError::MissingCheckerExternalProcessTranscriptDigest { ref field } if field == "stdout_sha256"),
        "{legacy_err:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[cfg(unix)]
#[test]
fn external_checker_runner_invokes_fixture_and_returns_production_evidence() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("external-checker-runner-success");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let script_body = "#!/bin/sh\nprintf 'checker accepted\\n'\nprintf 'mode=%s\\n' \"$TRUST_CHECKER_MODE\"\nprintf 'certificate=%s\\n' \"$2\" >&2\nexit 0\n";
    let script = write_checker_fixture_script(&dir, "checker-fixture-success.sh", script_body);
    let certificate_path = dir.join(&entry.certificate_path).display().to_string();
    let config_sha256 = trust_types::stable_sha256_hex(b"runner fixture checker config");
    let runner = CheckedBinaryCertificateExternalCheckerRunner::from_command_path(
        &script,
        ["--certificate".to_string(), certificate_path.clone()],
        1_777_070_401_000,
    )
    .expect("checker fixture runner should hash command")
    .with_checker_config_sha256(config_sha256.clone())
    .with_current_dir(&dir)
    .with_env("TRUST_CHECKER_MODE", "production")
    .with_timeout_ms(5_000)
    .with_proof_artifact_arg(
        CheckedBinaryCertificateExternalProcessProofArtifactArgument::new(
            "checker_config",
            None,
            "runner fixture checker config",
            Some(config_sha256.clone()),
        ),
    );

    let evidence = runner
        .run_for_manifest_entry(entry)
        .expect("successful fixture checker should produce production evidence");

    assert_eq!(
        evidence.invocation_kind,
        CheckedBinaryCertificateCheckerInvocationKind::ExternalProcess
    );
    assert_eq!(evidence.checker_binary_sha256, trust_types::stable_sha256_hex(script_body.as_bytes()));
    assert_eq!(evidence.checker_config_sha256.as_deref(), Some(config_sha256.as_str()));
    let expected_stdout_sha256 = trust_types::stable_sha256_hex(b"checker accepted\nmode=production\n");
    assert_eq!(evidence.stdout_sha256.as_deref(), Some(expected_stdout_sha256.as_str()));
    let expected_stderr = format!("certificate={certificate_path}\n");
    let expected_stderr_sha256 = trust_types::stable_sha256_hex(expected_stderr.as_bytes());
    assert_eq!(evidence.stderr_sha256.as_deref(), Some(expected_stderr_sha256.as_str()));
    let transcript = evidence
        .external_process_transcript
        .as_ref()
        .expect("runner evidence should persist structured external transcript");
    assert_eq!(transcript.cwd.as_deref(), Some(dir.as_path()));
    assert_eq!(transcript.env.get("TRUST_CHECKER_MODE").map(String::as_str), Some("production"));
    assert_eq!(transcript.timeout_policy.as_ref().map(|policy| policy.timeout_ms), Some(5_000));
    assert!(!transcript.timed_out);
    assert_eq!(transcript.stdout_sha256.as_deref(), Some(expected_stdout_sha256.as_str()));
    assert_eq!(transcript.stderr_sha256.as_deref(), Some(expected_stderr_sha256.as_str()));
    assert_eq!(
        transcript.sha256().expect("structured transcript should digest"),
        evidence.invocation_sha256
    );
    let checked_certificate_arg = transcript
        .proof_artifact_args
        .iter()
        .find(|arg| arg.role == "checked_certificate")
        .expect("checked certificate artifact argument should be recorded");
    assert_eq!(checked_certificate_arg.argv_index, Some(2));
    assert_eq!(checked_certificate_arg.sha256.as_deref(), Some(entry.certificate_sha256.as_str()));
    assert!(
        transcript.proof_artifact_args.iter().any(|arg| arg.role == "checker_config"
            && arg.sha256.as_deref() == Some(config_sha256.as_str()))
    );
    evidence.validate_production().expect("runner evidence should validate as production");

    let acceptance_request =
        CheckedBinaryCertificateManifestAcceptanceRequest::from_manifest_entry_and_solver_proof_export_metadata(
            entry,
            export.normalized_metadata(),
        )
        .expect("acceptance request should bind proof export metadata")
        .with_production_checker_evidence(evidence)
        .expect("runner evidence should bind to manifest entry");
    let mut gate_dispatch = proved_dispatch("gate-run:runner-success");
    import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect("runner evidence should import as checked production evidence");
    assert!(gate_dispatch.certificate.is_checked());

    let _ = std::fs::remove_dir_all(&dir);
}

#[cfg(unix)]
#[test]
fn external_checker_runner_rejects_nonzero_fixture_exit_after_digesting_transcript() {
    let (dir, manifest, _, _) =
        checked_manifest_acceptance_fixture("external-checker-runner-failed-exit");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let script_body =
        "#!/bin/sh\nprintf 'before failure\\n'\nprintf 'fatal fixture\\n' >&2\nexit 7\n";
    let script = write_checker_fixture_script(&dir, "checker-fixture-failure.sh", script_body);
    let runner = CheckedBinaryCertificateExternalCheckerRunner::from_command_path(
        &script,
        ["--certificate".to_string(), dir.join(&entry.certificate_path).display().to_string()],
        1_777_070_401_000,
    )
    .expect("checker fixture runner should hash command");

    let transcript =
        runner.run_transcript().expect("failed process should still yield a transcript");
    assert_eq!(transcript.exit_status, 7);
    let expected_stdout_sha256 = trust_types::stable_sha256_hex(b"before failure\n");
    let expected_stderr_sha256 = trust_types::stable_sha256_hex(b"fatal fixture\n");
    assert_eq!(transcript.stdout_sha256.as_deref(), Some(expected_stdout_sha256.as_str()));
    assert_eq!(transcript.stderr_sha256.as_deref(), Some(expected_stderr_sha256.as_str()));

    let err = runner
        .run_for_manifest_entry(entry)
        .expect_err("nonzero checker exit must not produce production evidence");

    assert!(
        matches!(
            err,
            CheckError::CheckerExternalProcessFailed { ref command, exit_status: 7 }
                if command == &script.display().to_string()
        ),
        "{err:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[cfg(unix)]
#[test]
fn external_checker_runner_times_out_fail_closed_with_transcript_digests() {
    let (dir, manifest, _, _) =
        checked_manifest_acceptance_fixture("external-checker-runner-timeout");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let script_body = "#!/bin/sh\nprintf 'before timeout\\n'\nprintf 'timeout stderr\\n' >&2\nwhile :; do :; done\n";
    let script = write_checker_fixture_script(&dir, "checker-fixture-timeout.sh", script_body);
    let runner = CheckedBinaryCertificateExternalCheckerRunner::from_command_path(
        &script,
        ["--certificate".to_string(), dir.join(&entry.certificate_path).display().to_string()],
        1_777_070_401_000,
    )
    .expect("checker fixture runner should hash command")
    .with_timeout_ms(50);

    let transcript =
        runner.run_transcript().expect("timed out checker should still expose transcript digests");
    assert!(transcript.timed_out);
    assert_eq!(transcript.timeout_policy.as_ref().map(|policy| policy.timeout_ms), Some(50));
    assert!(transcript.stdout_sha256.as_deref().is_some_and(is_canonical_lowercase_sha256));
    assert!(transcript.stderr_sha256.as_deref().is_some_and(is_canonical_lowercase_sha256));
    let transcript_err = transcript
        .validate_success()
        .expect_err("timed out transcript must not validate as successful evidence");
    assert!(
        matches!(transcript_err, CheckError::CheckerExternalProcessTimedOut { ref command, timeout_ms: 50 } if command == &script.display().to_string()),
        "{transcript_err:?}"
    );

    let err = runner
        .run_for_manifest_entry(entry)
        .expect_err("timed out checker must not produce production evidence");
    assert!(
        matches!(err, CheckError::CheckerExternalProcessTimedOut { ref command, timeout_ms: 50 } if command == &script.display().to_string()),
        "{err:?}"
    );

    let invalid_timeout_runner = CheckedBinaryCertificateExternalCheckerRunner::from_command_path(
        &script,
        ["--certificate".to_string(), dir.join(&entry.certificate_path).display().to_string()],
        1_777_070_401_000,
    )
    .expect("checker fixture runner should hash command")
    .with_timeout_ms(0);
    let invalid_timeout_err = invalid_timeout_runner
        .run_transcript()
        .expect_err("zero timeout policy must fail closed before spawn");
    assert!(
        matches!(invalid_timeout_err, CheckError::MalformedProof { ref reason } if reason.contains("timeout policy")),
        "{invalid_timeout_err:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_artifact_without_production_checker_evidence_stays_out_of_gate_coverage() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let mut dispatch = proved_dispatch("vc0");
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();

    let request =
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export);
    let check = check_binary_certificate(&checker, request);
    assert!(check.accepted, "{:?}", check.error);

    let artifact = check.certificate.as_ref().expect("accepted check has certificate");
    assert_eq!(artifact.dispatch_id, "vc0");
    assert_eq!(artifact.format, "lrat");
    assert_eq!(artifact.checker, "ay-lrat-binary-check");
    assert_eq!(artifact.checker_version, "0.1.0");
    assert_eq!(artifact.proof_sha256, export.proof_sha256);
    assert_eq!(
        artifact.proof_export_sha256,
        export.normalized_metadata_sha256().expect("proof export metadata should digest")
    );
    assert_eq!(artifact.query_semantics, SolverQuerySemantics::SatIsCounterexample);
    assert_eq!(artifact.replay, ReplayStatus::Replayed);
    assert_eq!(artifact.replay_transcript_digest, None);
    assert_eq!(artifact.origin, binary_origin());
    assert_eq!(artifact.binary_artifact_digest_identity, binary_artifact_digest_identity());
    assert_eq!(artifact.assumption_digest, digest_model_assumptions(&dispatch.assumptions));
    assert_eq!(
        artifact.origin_sha256,
        digest_binary_origin(&artifact.origin).expect("artifact origin should digest")
    );
    assert_eq!(
        digest_binary_origin(&artifact.origin).expect("artifact origin should digest"),
        digest_binary_origin(dispatch.origin.as_ref().expect("fixture has origin"))
            .expect("dispatch origin should digest")
    );
    assert!(!artifact.normalized_payload.is_empty());

    apply_checked_certificate_to_dispatch(&mut dispatch, artifact);
    let summary = proof_grade_summary(&[dispatch]);
    let decision = summary.proof_grade_release_gate();

    assert_eq!(summary.certificate_checks.checked_certificates, 0);
    assert_eq!(summary.certificate_checks.raw_solver_proof_bytes, 0);
    assert!(
        summary.certificate_checks.records[0]
            .coherence_failures
            .iter()
            .any(|failure| failure == "missing production checker evidence")
    );
    assert!(decision.rejected());
    assert!(decision.rejections.iter().any(|reason| {
        matches!(reason, BinaryReleaseGateRejection::MissingProofCertificates { .. })
    }));
}

#[test]
fn solver_proof_export_validation_accepts_bound_normalized_export_metadata() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("vc0");
    let mut export = proof_export(&dispatch, canonical_vc_bytes);
    export.stdout_digest = Some(trust_types::stable_sha256_hex(b"deterministic solver stdout"));
    export.stderr_digest = Some(trust_types::stable_sha256_hex(b"deterministic solver stderr"));

    export
        .validate_for_dispatch(&dispatch, canonical_vc_bytes)
        .expect("bound normalized solver proof export should validate");
}

#[test]
fn checked_binary_certificate_rejects_malformed_solver_proof_export_metadata() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("vc0");
    let mut export = proof_export(&dispatch, canonical_vc_bytes);
    export.stdout_digest = Some("NOT-A-CANONICAL-SHA256".to_string());
    let checker = checked_certificate_checker();

    let check = check_binary_certificate(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export),
    );

    assert!(!check.accepted);
    assert!(check.certificate.is_none());
    assert!(
        matches!(check.error, Some(CheckError::MalformedProof { ref reason }) if reason.contains("solver proof export stdout_digest") && reason.contains("canonical lowercase sha256")),
        "{:?}",
        check.error
    );
}

#[test]
fn checked_binary_certificate_artifact_roundtrips_persists_and_imports_with_bound_identity() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let mut dispatch = proved_dispatch("vc0");
    dispatch.assumptions = vec![ModelAssumption {
        stage: "lift".to_string(),
        description: "stack pointer is canonical".to_string(),
    }];
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();

    let request =
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export);
    let check = check_binary_certificate(&checker, request);
    assert!(check.accepted, "{:?}", check.error);
    let artifact = check.certificate.expect("accepted check has certificate");

    let json = artifact.to_json().expect("checked artifact should serialize");
    let restored =
        CheckedBinaryCertificateArtifact::from_json(&json).expect("checked artifact should reload");
    assert_eq!(restored, artifact);

    let root = unique_temp_dir("checked-binary-certificate-roundtrip");
    let path = persist_checked_certificate_artifact(&root, &restored)
        .expect("checked artifact should persist content-addressed");
    assert_eq!(
        path,
        restored.content_addressed_path(&root).expect("content-addressed path should compute")
    );
    assert!(
        path.ends_with(format!("{}.checked-binary-certificate.json", restored.certificate_sha256))
    );

    let loaded =
        load_content_addressed_checked_certificate_artifact(&root, &restored.certificate_sha256)
            .expect("content-addressed checked artifact should load");
    assert_eq!(loaded, restored);

    let mut reloaded_dispatch = proved_dispatch("vc0");
    reloaded_dispatch.assumptions = dispatch.assumptions.clone();
    let imported = import_content_addressed_checked_certificate_for_dispatch(
        &mut reloaded_dispatch,
        canonical_vc_bytes,
        &root,
        &restored.certificate_sha256,
    )
    .expect("restored checked artifact should bind to the same dispatch");
    assert_eq!(imported, restored);

    let summary = proof_grade_summary(&[reloaded_dispatch]);
    let decision = summary.proof_grade_release_gate();

    assert_eq!(summary.certificate_checks.checked_certificates, 0);
    assert_eq!(summary.raw_solver_proof_bytes, 0);
    assert!(decision.rejected());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn checked_binary_certificate_production_helper_persists_content_addressed_roundtrip() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let mut dispatch = proved_dispatch("vc0");
    dispatch.assumptions = vec![ModelAssumption {
        stage: "lift".to_string(),
        description: "stack pointer is canonical".to_string(),
    }];
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let dir = temp_artifact_dir("content-addressed-roundtrip");

    let artifact_ref = produce_checked_certificate_artifact(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export),
        &dir,
    )
    .expect("production helper should persist checked artifact");

    assert!(artifact_ref.path.exists());
    assert!(
        artifact_ref
            .path
            .file_name()
            .and_then(|name| name.to_str())
            .expect("artifact filename should be UTF-8")
            .starts_with(&artifact_ref.content_sha256)
    );
    assert_eq!(artifact_ref.content_sha256.len(), 64);
    assert!(is_canonical_lowercase_sha256(&artifact_ref.content_sha256));

    let restored = load_checked_certificate_artifact_ref(&artifact_ref)
        .expect("content-addressed checked artifact should reload");
    assert_eq!(restored.vc_sha256, trust_types::stable_sha256_hex(canonical_vc_bytes));
    assert_eq!(restored.replay, ReplayStatus::Replayed);
    assert_eq!(restored.origin, binary_origin());
    assert_eq!(restored.binary_artifact_digest_identity, binary_artifact_digest_identity());
    assert_eq!(restored.assumptions, dispatch.assumptions);
    assert_eq!(restored.checker, "ay-lrat-binary-check");
    assert_eq!(restored.checker_version, "0.1.0");

    let mut imported_dispatch = proved_dispatch("vc0");
    imported_dispatch.assumptions = dispatch.assumptions.clone();
    let imported = import_checked_certificate_artifact_for_dispatch(
        &mut imported_dispatch,
        canonical_vc_bytes,
        &artifact_ref,
    )
    .expect("content-addressed checked artifact should import");

    assert_eq!(imported, restored);
    assert!(imported_dispatch.certificate.is_checked());

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_binds_replay_transcript_digest_in_normalized_payload() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("vc0");
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let replay_transcript_digest = trust_types::stable_sha256_hex(b"deterministic replay transcript for vc0");
    let mut request =
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export);
    request.replay_transcript_digest = Some(&replay_transcript_digest);

    let check = check_binary_certificate(&checker, request);
    assert!(check.accepted, "{:?}", check.error);
    let artifact = check.certificate.expect("accepted check has certificate");
    let payload: serde_json::Value = serde_json::from_slice(&artifact.normalized_payload)
        .expect("normalized payload should decode");

    assert_eq!(
        artifact.replay_transcript_digest.as_deref(),
        Some(replay_transcript_digest.as_str())
    );
    assert_eq!(payload["replay_transcript_digest"], serde_json::json!(&replay_transcript_digest));
    assert_eq!(artifact.certificate_sha256, trust_types::stable_sha256_hex(&artifact.normalized_payload));
    artifact.validate_integrity().expect("replay transcript digest should validate");

    let baseline = check_binary_certificate(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export),
    )
    .certificate
    .expect("baseline checked certificate should exist");
    assert_ne!(artifact.certificate_sha256, baseline.certificate_sha256);
}

#[test]
fn checked_binary_certificate_rejects_noncanonical_replay_transcript_digest() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("vc0");
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let mut request =
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export);
    request.replay_transcript_digest = Some("not-a-canonical-sha256");

    let check = check_binary_certificate(&checker, request);

    assert!(!check.accepted);
    assert!(check.certificate.is_none());
    assert!(
        matches!(check.error, Some(CheckError::MalformedProof { ref reason }) if reason.contains("replay_transcript_digest") && reason.contains("canonical lowercase sha256")),
        "{:?}",
        check.error
    );
}

#[test]
fn checked_binary_certificate_rejects_missing_or_non_replay_grade_binary_artifact_identity() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let mut missing_identity = proved_dispatch("vc0");
    missing_identity.binary_artifact_digest_identity = None;
    let missing_export = proof_export(&missing_identity, canonical_vc_bytes);
    let checker = checked_certificate_checker();

    let missing_check = check_binary_certificate(
        &checker,
        BinaryCertificateCheckRequest::from_export(
            &missing_identity,
            canonical_vc_bytes,
            &missing_export,
        ),
    );

    assert!(!missing_check.accepted);
    assert!(
        matches!(missing_check.error, Some(CheckError::BinaryArtifactDigestIdentityInvalid { ref reason }) if reason.contains("missing dispatch binary artifact digest identity")),
        "{:?}",
        missing_check.error
    );

    let mut missing_selected_image = proved_dispatch("vc0");
    missing_selected_image
        .binary_artifact_digest_identity
        .as_mut()
        .expect("fixture has digest identity")
        .selected_image = None;
    let missing_selected_export = proof_export(&missing_selected_image, canonical_vc_bytes);
    let missing_selected_check = check_binary_certificate(
        &checker,
        BinaryCertificateCheckRequest::from_export(
            &missing_selected_image,
            canonical_vc_bytes,
            &missing_selected_export,
        ),
    );

    assert!(!missing_selected_check.accepted);
    assert!(
        matches!(missing_selected_check.error, Some(CheckError::BinaryArtifactDigestIdentityInvalid { ref reason }) if reason.contains("missing selected image digest/range")),
        "{:?}",
        missing_selected_check.error
    );
}

#[test]
fn checked_binary_certificate_manifest_accepts_complete_artifact_index() {
    let (dir, manifest) = checked_manifest_fixture("manifest-complete");

    let json = manifest.to_json().expect("manifest should serialize");
    let restored =
        CheckedBinaryCertificateManifest::from_json(&json).expect("manifest JSON should reload");
    restored
        .validate_files(&dir)
        .expect("complete manifest should validate against stored artifacts");

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_manifest_export_ref_satisfies_proof_grade_gate() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let export_dispatch = proved_dispatch("export-run:vc0");
    let export = proof_export(&export_dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let dir = temp_artifact_dir("manifest-export-ref-gate");
    let artifact_ref = produce_checked_certificate_artifact(
        &checker,
        BinaryCertificateCheckRequest::from_export(&export_dispatch, canonical_vc_bytes, &export),
        &dir,
    )
    .expect("export ref should persist a checked artifact");
    assert!(is_canonical_lowercase_sha256(&artifact_ref.content_sha256));

    let manifest = CheckedBinaryCertificateManifest::from_artifact_refs(
        &dir,
        std::slice::from_ref(&artifact_ref),
    )
    .expect("artifact refs should build a checked certificate manifest");
    manifest.validate_files(&dir).expect("manifest row should validate against exported artifact");
    let entry = manifest.certificates.first().expect("manifest should have one checked row");
    assert!(is_canonical_lowercase_sha256(&entry.vc_sha256));
    assert!(is_canonical_lowercase_sha256(&entry.origin_sha256));
    assert!(is_canonical_lowercase_sha256(&entry.proof_sha256));
    assert!(is_canonical_lowercase_sha256(&entry.proof_export_sha256));
    assert!(is_canonical_lowercase_sha256(&entry.certificate_sha256));
    assert!(is_canonical_lowercase_sha256(&entry.assumption_digest));
    assert_eq!(entry.binary_artifact_digest_identity, binary_artifact_digest_identity());

    let manifest_ref = CheckedBinaryCertificateArtifactRef {
        content_sha256: entry.certificate_sha256.clone(),
        path: dir.join(&entry.certificate_path),
    };
    let artifact = load_checked_certificate_artifact_ref(&manifest_ref)
        .expect("manifest artifact ref should reload checked certificate");
    entry
        .validate_production_bindings(
            &artifact,
            canonical_vc_bytes,
            &export,
            "ay-lrat-binary-check",
            "0.1.0",
            None,
        )
        .expect("manifest row should bind production inputs");
    let acceptance_request = production_acceptance_request(entry, &export);
    let mut gate_dispatch = proved_dispatch("gate-run:vc0");
    import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect("manifest acceptance should import checked artifact with production evidence");

    match &gate_dispatch.certificate {
        ProofCertificateStatus::Checked { sha256: Some(digest), .. } => {
            assert_eq!(digest, &entry.certificate_sha256);
            assert!(is_canonical_lowercase_sha256(digest));
        }
        certificate => panic!("expected checked certificate status, got {certificate:?}"),
    }

    let summary = proof_grade_summary(&[gate_dispatch]);
    let decision = summary.proof_grade_release_gate();

    assert_eq!(summary.certificate_checks.checked_certificates, 1);
    assert_eq!(summary.raw_solver_proof_bytes, 0);
    assert!(decision.accepted, "{:?}", decision.rejections);

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_manifest_row_binds_vc_replay_export_and_checker() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("vc0");
    let mut export = proof_export(&dispatch, canonical_vc_bytes);
    export.stdout_digest = Some(trust_types::stable_sha256_hex(b"deterministic solver stdout"));
    export.stderr_digest = Some(trust_types::stable_sha256_hex(b"deterministic solver stderr"));
    let checker = checked_certificate_checker();
    let replay_transcript_digest = trust_types::stable_sha256_hex(b"deterministic replay transcript for manifest row");
    let dir = temp_artifact_dir("manifest-production-row");
    let mut request =
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export);
    request.replay_transcript_digest = Some(&replay_transcript_digest);

    let artifact_ref = produce_checked_certificate_artifact(&checker, request, &dir)
        .expect("production helper should persist checked artifact");
    let manifest =
        CheckedBinaryCertificateManifest::from_artifact_refs(&dir, std::slice::from_ref(&artifact_ref))
            .expect("checked artifact ref should export into a manifest row");
    manifest
        .validate_files(&dir)
        .expect("manifest row should validate against the checked artifact");
    let entry = manifest.certificates.first().expect("manifest should have one checked row");
    let artifact = load_checked_certificate_artifact_ref(&artifact_ref)
        .expect("manifest-backed artifact should reload");

    assert_eq!(entry.vc_sha256, trust_types::stable_sha256_hex(canonical_vc_bytes));
    assert_eq!(
        entry.origin_sha256,
        digest_binary_origin(dispatch.origin.as_ref().expect("fixture has origin"))
            .expect("origin should digest")
    );
    assert_eq!(entry.replay_transcript_digest.as_deref(), Some(replay_transcript_digest.as_str()));
    assert_eq!(entry.proof_sha256, export.proof_sha256);
    assert_eq!(
        entry.proof_export_sha256,
        export.normalized_metadata_sha256().expect("proof export metadata should digest")
    );
    assert_eq!(entry.checker, "ay-lrat-binary-check");
    assert_eq!(entry.checker_version, "0.1.0");

    entry
        .validate_production_bindings(
            &artifact,
            canonical_vc_bytes,
            &export,
            "ay-lrat-binary-check",
            "0.1.0",
            Some(&replay_transcript_digest),
        )
        .expect("manifest row should bind VC bytes, replay digest, proof export, and checker");

    let acceptance_request = production_acceptance_request(entry, &export);
    let mut gate_dispatch = proved_dispatch("gate-run:vc0");
    import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect("accepted manifest-backed artifact should import with production evidence");
    let summary = proof_grade_summary(&[gate_dispatch]);
    let decision = summary.proof_grade_release_gate();

    assert_eq!(summary.certificate_checks.checked_certificates, 1);
    assert!(decision.accepted, "{:?}", decision.rejections);

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_manifest_acceptance_loads_imports_structured_production_bindings() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, replay_transcript_digest) =
        checked_manifest_acceptance_fixture("manifest-acceptance-positive");
    let manifest_json = manifest.to_json().expect("manifest should serialize");
    let restored = CheckedBinaryCertificateManifest::from_json(&manifest_json)
        .expect("manifest JSON should reload before acceptance");
    let entry = restored.certificates.first().expect("manifest should have one row");
    let acceptance_request = production_acceptance_request(entry, &export);
    let mut gate_dispatch = proved_dispatch("gate-run:vc0");

    let record = import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect("manifest acceptance should load and import the checked artifact");

    record.validate_structure().expect("acceptance record should be structurally valid");
    assert_eq!(record.schema_version, "checked-binary-certificate-acceptance.v1");
    assert_eq!(record.manifest_schema_version, "binary-certificate-manifest.v2");
    assert_eq!(record.checker_selection.checker, "ay-lrat-binary-check");
    assert_eq!(record.checker_selection.checker_version, "0.1.0");
    assert_eq!(record.checker_selection.format, "lrat");
    let production_evidence = record
        .production_checker_evidence
        .as_ref()
        .expect("production checker evidence should be recorded");
    assert_eq!(production_evidence.checker, "ay-lrat-binary-check");
    assert_eq!(production_evidence.checker_version, "0.1.0");
    assert_eq!(production_evidence.format, "lrat");
    assert_eq!(production_evidence.certificate_sha256, entry.certificate_sha256);
    assert_eq!(record.solver_proof_export.metadata, export.normalized_metadata());
    assert_eq!(
        record.solver_proof_export.metadata_sha256,
        export.normalized_metadata_sha256().expect("proof export metadata should digest")
    );
    let stdout_digest = trust_types::stable_sha256_hex(b"deterministic solver stdout");
    let stderr_digest = trust_types::stable_sha256_hex(b"deterministic solver stderr");
    assert_eq!(
        record.solver_proof_export.metadata.stdout_digest.as_deref(),
        Some(stdout_digest.as_str())
    );
    assert_eq!(
        record.solver_proof_export.metadata.stderr_digest.as_deref(),
        Some(stderr_digest.as_str())
    );
    assert_eq!(record.replay_transcript.replay, ReplayStatus::Replayed);
    assert_eq!(
        record.replay_transcript.replay_transcript_digest.as_deref(),
        Some(replay_transcript_digest.as_str())
    );
    assert_eq!(record.artifact_identity.vc_sha256, trust_types::stable_sha256_hex(canonical_vc_bytes));
    assert_eq!(
        record.artifact_identity.content_sha256,
        record.artifact_identity.certificate_sha256
    );
    assert_eq!(record.artifact_identity.certificate_sha256, entry.certificate_sha256);
    assert_eq!(record.artifact_identity.certificate_path, entry.certificate_path);

    match &gate_dispatch.certificate {
        ProofCertificateStatus::Checked { checker, format, sha256: Some(digest) } => {
            assert!(checker.contains("production_checker_evidence_sha256="));
            let typed_evidence = checked_certificate_status_production_checker_evidence(checker)
                .expect("checked status should expose typed production checker evidence");
            assert_eq!(typed_evidence.checker, "ay-lrat-binary-check");
            assert_eq!(typed_evidence.checker_version, "0.1.0");
            assert_eq!(
                typed_evidence.production_checker_evidence_sha256,
                production_evidence.sha256().expect("production evidence should digest")
            );
            assert_eq!(format, "lrat");
            assert_eq!(digest, &entry.certificate_sha256);
        }
        certificate => panic!("expected checked certificate status, got {certificate:?}"),
    }

    let summary = proof_grade_summary(&[gate_dispatch]);
    let decision = summary.proof_grade_release_gate();
    assert_eq!(summary.certificate_checks.checked_certificates, 1);
    assert_eq!(summary.certificate_checks.raw_solver_proof_bytes, 0);
    assert!(decision.accepted, "{:?}", decision.rejections);

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_manifest_acceptance_rejects_missing_production_checker_evidence() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("manifest-acceptance-missing-production-evidence");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let acceptance_request =
        CheckedBinaryCertificateManifestAcceptanceRequest::from_manifest_entry_and_solver_proof_export_metadata(
            entry,
            export.normalized_metadata(),
        )
        .expect("readback-only acceptance request should build but not import");
    let mut gate_dispatch = proved_dispatch("gate-run:vc0");

    let err = import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect_err("readback-only manifest row must not import as proof-grade checked");

    assert!(
        matches!(err, CertError::InvalidCertificate { ref reason } if reason.contains("missing production checker evidence")),
        "{err:?}"
    );
    assert!(!gate_dispatch.certificate.is_checked());

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_manifest_acceptance_rejects_mismatched_production_checker_evidence() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("manifest-acceptance-mismatched-production-evidence");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let mut invocation_mismatch = production_acceptance_request(entry, &export);
    invocation_mismatch
        .production_checker_evidence
        .as_mut()
        .expect("production evidence should be present")
        .invocation_sha256 = trust_types::stable_sha256_hex(b"different checker invocation transcript");
    let mut gate_dispatch = proved_dispatch("gate-run:vc0-invocation-mismatch");

    let err = import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &invocation_mismatch,
    )
    .expect_err("mismatched checker invocation evidence must fail closed");

    assert!(
        matches!(err, CertError::InvalidCertificate { ref reason } if reason.contains("production_checker_evidence.invocation_sha256")),
        "{err:?}"
    );
    assert!(!gate_dispatch.certificate.is_checked());

    let mut acceptance_request = production_acceptance_request(entry, &export);
    acceptance_request
        .production_checker_evidence
        .as_mut()
        .expect("production evidence should be present")
        .certificate_sha256 = trust_types::stable_sha256_hex(b"different checked artifact");
    let mut gate_dispatch = proved_dispatch("gate-run:vc0-certificate-mismatch");

    let err = import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect_err("mismatched production checker evidence must fail closed");

    assert!(
        matches!(err, CertError::InvalidCertificate { ref reason } if reason.contains("production_checker_evidence.certificate_sha256")),
        "{err:?}"
    );
    assert!(!gate_dispatch.certificate.is_checked());

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_manifest_acceptance_rejects_synthetic_invocation_evidence() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("manifest-acceptance-synthetic-invocation-evidence");
    let entry = manifest.certificates.first().expect("manifest should have one row");

    for invocation_kind in [
        CheckedBinaryCertificateCheckerInvocationKind::SyntheticFixture,
        CheckedBinaryCertificateCheckerInvocationKind::ReadbackOnly,
    ] {
        let mut acceptance_request = production_acceptance_request(entry, &export);
        acceptance_request
            .production_checker_evidence
            .as_mut()
            .expect("production evidence should be present")
            .invocation_kind = invocation_kind;
        let mut gate_dispatch = proved_dispatch("gate-run:vc0");

        let err = import_checked_certificate_manifest_entry_for_dispatch(
            &mut gate_dispatch,
            canonical_vc_bytes,
            &dir,
            entry,
            &acceptance_request,
        )
        .expect_err("synthetic/readback invocation evidence must fail closed");

        assert!(
            matches!(err, CertError::InvalidCertificate { ref reason } if reason.contains("external production checker invocation")),
            "{err:?}"
        );
        assert!(!gate_dispatch.certificate.is_checked());
    }

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_audit_export_roundtrips_persisted_json_and_reimports() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, replay_transcript_digest) =
        checked_manifest_acceptance_fixture("audit-export-roundtrip");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let acceptance_request = production_acceptance_request(entry, &export);
    let mut gate_dispatch = proved_dispatch("gate-run:vc0");
    let record = import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect("manifest acceptance should import before audit export");

    let audit_export =
        CheckedBinaryCertificateAuditExport::from_manifest_entry_and_record(entry.clone(), record)
            .expect("audit export should bind manifest row to accepted record");
    let json = audit_export.to_json().expect("audit export should serialize");
    assert!(!json.contains("proof_bytes"));
    assert!(!json.contains("normalized lrat proof bytes bound to vc0"));
    let restored_from_json =
        CheckedBinaryCertificateAuditExport::from_json(&json).expect("audit export should reload");
    assert_eq!(restored_from_json, audit_export);

    let path = dir.join("accepted-checked-certificate.audit.json");
    persist_checked_certificate_audit_export(&path, &audit_export)
        .expect("audit export should persist as JSON");
    let restored =
        load_checked_certificate_audit_export(&path).expect("persisted audit export should reload");

    assert_eq!(restored.manifest_entry, entry.clone());
    assert_eq!(restored.acceptance_record.checker_selection.checker, "ay-lrat-binary-check");
    assert_eq!(restored.acceptance_record.checker_selection.checker_version, "0.1.0");
    assert_eq!(restored.acceptance_record.checker_selection.format, "lrat");
    assert_eq!(
        restored.acceptance_record.artifact_identity.certificate_sha256.as_str(),
        entry.certificate_sha256.as_str()
    );
    assert_eq!(
        restored.acceptance_record.artifact_identity.certificate_path.as_path(),
        entry.certificate_path.as_path()
    );
    assert_eq!(
        restored.acceptance_record.solver_proof_export.metadata,
        export.normalized_metadata()
    );
    assert_eq!(
        restored.acceptance_record.replay_transcript.replay_transcript_digest.as_deref(),
        Some(replay_transcript_digest.as_str())
    );

    let restored_request =
        restored.acceptance_request().expect("audit export should reconstruct acceptance request");
    let mut readback_dispatch = proved_dispatch("readback-gate-run:vc0");
    let readback_record = import_checked_certificate_manifest_entry_for_dispatch(
        &mut readback_dispatch,
        canonical_vc_bytes,
        &dir,
        &restored.manifest_entry,
        &restored_request,
    )
    .expect("reconstructed request should re-import the checked artifact");
    assert_eq!(readback_record, restored.acceptance_record);
    assert!(readback_dispatch.certificate.is_checked());

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_manifest_audit_export_bundle_persists_and_reimports_without_raw_proof_bytes()
 {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, replay_transcript_digest) =
        checked_manifest_acceptance_fixture("audit-export-bundle-roundtrip");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let acceptance_request = production_acceptance_request(entry, &export);
    let mut gate_dispatch = proved_dispatch("gate-run:vc0");
    let record = import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect("manifest acceptance should import before bundle export");
    let audit_export =
        CheckedBinaryCertificateAuditExport::from_manifest_entry_and_record(entry.clone(), record)
            .expect("audit export should bind manifest row to accepted record");

    let bundle = persist_checked_certificate_audit_export_bundle(
        &dir,
        &manifest,
        std::slice::from_ref(&audit_export),
    )
    .expect("manifest plus audit export bundle should persist");
    let manifest_path = checked_certificate_manifest_path(&dir);
    let bundle_path = checked_certificate_audit_export_bundle_path(&dir);
    assert!(manifest_path.is_file());
    assert!(bundle_path.is_file());
    assert_eq!(
        bundle.manifest_path,
        manifest_path.strip_prefix(&dir).expect("manifest path should be under root").to_path_buf()
    );
    assert!(!bundle.manifest_path.is_absolute());
    assert!(bundle.manifest_path.starts_with("checked-binary-certificates"));
    assert!(is_canonical_lowercase_sha256(&bundle.manifest_sha256));

    let bundle_entry = bundle.audit_exports.first().expect("bundle should have one audit row");
    assert!(!bundle_entry.audit_export_path.is_absolute());
    assert!(bundle_entry.audit_export_path.starts_with("checked-binary-certificates"));
    assert!(is_canonical_lowercase_sha256(&bundle_entry.vc_sha256));
    assert!(is_canonical_lowercase_sha256(&bundle_entry.origin_sha256));
    assert!(is_canonical_lowercase_sha256(&bundle_entry.proof_sha256));
    assert!(is_canonical_lowercase_sha256(&bundle_entry.proof_export_sha256));
    assert!(is_canonical_lowercase_sha256(&bundle_entry.certificate_sha256));
    assert!(is_canonical_lowercase_sha256(&bundle_entry.audit_export_sha256));
    assert_eq!(bundle_entry.vc_sha256, trust_types::stable_sha256_hex(canonical_vc_bytes));
    assert_eq!(bundle_entry.origin_sha256, entry.origin_sha256);
    assert_eq!(bundle_entry.binary_artifact_digest_identity, binary_artifact_digest_identity());
    assert_eq!(bundle_entry.proof_sha256, export.proof_sha256);
    assert_eq!(
        bundle_entry.proof_export_sha256,
        export.normalized_metadata_sha256().expect("proof export metadata should digest")
    );
    assert_eq!(bundle_entry.checker, "ay-lrat-binary-check");
    assert_eq!(bundle_entry.checker_version, "0.1.0");
    assert_eq!(
        bundle_entry.replay_transcript_digest.as_deref(),
        Some(replay_transcript_digest.as_str())
    );

    let manifest_json =
        std::fs::read_to_string(&manifest_path).expect("manifest JSON should be readable");
    let bundle_json =
        std::fs::read_to_string(&bundle_path).expect("bundle JSON should be readable");
    let audit_json = std::fs::read_to_string(dir.join(&bundle_entry.audit_export_path))
        .expect("audit export JSON should be readable");
    for json in [&manifest_json, &bundle_json, &audit_json] {
        assert!(!json.contains("proof_bytes"));
        assert!(!json.contains("normalized lrat proof bytes bound to vc0"));
    }

    let restored_manifest =
        load_checked_certificate_manifest(&dir).expect("persisted manifest should reload");
    assert_eq!(restored_manifest, manifest);
    let readback =
        load_checked_certificate_audit_export_bundle(&dir).expect("bundle should reload");
    assert_eq!(readback.bundle, bundle);
    assert_eq!(readback.manifest, manifest);
    assert_eq!(readback.audit_exports, vec![audit_export.clone()]);

    let restored_audit = readback.audit_exports.first().expect("readback should have audit row");
    assert_eq!(
        restored_audit.acceptance_record.solver_proof_export.metadata,
        export.normalized_metadata()
    );
    assert_eq!(
        restored_audit.acceptance_record.solver_proof_export.metadata_sha256,
        export.normalized_metadata_sha256().expect("proof export metadata should digest")
    );
    assert_eq!(
        restored_audit.acceptance_record.replay_transcript.replay_transcript_digest.as_deref(),
        Some(replay_transcript_digest.as_str())
    );

    let restored_request =
        restored_audit.acceptance_request().expect("audit export should rebuild request");
    let restored_entry = readback.manifest.certificates.first().expect("manifest row should load");
    let mut readback_dispatch = proved_dispatch("readback-bundle-run:vc0");
    let readback_record = import_checked_certificate_manifest_entry_for_dispatch(
        &mut readback_dispatch,
        canonical_vc_bytes,
        &dir,
        restored_entry,
        &restored_request,
    )
    .expect("readback bundle should import the checked artifact");
    assert_eq!(readback_record, restored_audit.acceptance_record);
    assert!(readback_dispatch.certificate.is_checked());

    let summary = proof_grade_summary(&[readback_dispatch]);
    let decision = summary.proof_grade_release_gate();
    assert_eq!(summary.certificate_checks.checked_certificates, 1);
    assert_eq!(summary.certificate_checks.raw_solver_proof_bytes, 0);
    assert!(decision.accepted, "{:?}", decision.rejections);

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_certificate_audit_bundle_roundtrips_complete_source_backpropagation_gate() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("audit-export-source-backprop-complete");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let source_gate = complete_source_backpropagation_gate();
    assert!(source_gate.source_backpropagation_allowed);
    assert!(source_gate.blockers.is_empty());

    let acceptance_request = production_acceptance_request(entry, &export)
        .with_source_backpropagation_gate(source_gate.clone())
        .expect("complete source-backprop gate should bind to acceptance request");
    let mut gate_dispatch = proved_dispatch("gate-run:source-backprop-complete");
    let record = import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect("complete source-backprop gate should not block checked import");
    assert_eq!(record.source_backpropagation_gate, source_gate);

    let audit_export =
        CheckedBinaryCertificateAuditExport::from_manifest_entry_and_record(entry.clone(), record)
            .expect("audit export should carry source-backprop gate");
    let json = audit_export.to_json().expect("audit export should serialize source gate");
    assert!(json.contains("source_backpropagation_gate"));
    assert!(json.contains("replay_grade_artifact_identity"));
    assert!(json.contains("checked_certificate_identity"));
    assert!(json.contains("exact_replay_identity"));
    assert!(json.contains("accepted_reconstruction_validation"));
    assert!(json.contains("accepted_target_validation"));
    assert!(json.contains("exact_source_provenance"));
    assert!(json.contains("source_backpropagation_allowed"));
    let restored =
        CheckedBinaryCertificateAuditExport::from_json(&json).expect("audit export should reload");
    assert_eq!(restored.acceptance_record.source_backpropagation_gate, source_gate);

    let bundle = persist_checked_certificate_audit_export_bundle(
        &dir,
        &manifest,
        std::slice::from_ref(&restored),
    )
    .expect("bundle should persist source-backprop gate summary");
    assert_eq!(bundle.audit_exports[0].source_backpropagation_gate, source_gate);
    let readback =
        load_checked_certificate_audit_export_bundle(&dir).expect("bundle should reload");
    assert_eq!(readback.bundle.audit_exports[0].source_backpropagation_gate, source_gate);
    assert_eq!(
        readback.audit_exports[0].acceptance_record.source_backpropagation_gate,
        source_gate
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_certificate_audit_bundle_readback_accepts_distinct_source_backprop_vcs() {
    let checker = checked_certificate_checker();
    let dir = temp_artifact_dir("audit-export-distinct-source-backprop-readback");

    let vc_a: &[u8] = br#"{"vc":"main memory safety A"}"#;
    let dispatch_a = proved_dispatch("export-run:readback-vc-a");
    let mut export_a = SolverProofExport::new(
        &dispatch_a,
        vc_a,
        "lrat",
        b"normalized lrat proof bytes bound to readback vc-a".to_vec(),
        Some("4.13.0".to_string()),
        1_777_070_400_000,
    );
    export_a.stdout_digest = Some(trust_types::stable_sha256_hex(b"deterministic solver stdout for readback vc-a"));
    export_a.stderr_digest = Some(trust_types::stable_sha256_hex(b"deterministic solver stderr for readback vc-a"));
    let replay_a = trust_types::stable_sha256_hex(b"deterministic replay transcript for readback vc-a");
    let mut request_a = BinaryCertificateCheckRequest::from_export(&dispatch_a, vc_a, &export_a);
    request_a.replay_transcript_digest = Some(&replay_a);
    let artifact_ref_a = produce_checked_certificate_artifact(&checker, request_a, &dir)
        .expect("first checked artifact should persist");

    let vc_b: &[u8] = br#"{"vc":"stack bounds safety B"}"#;
    let dispatch_b = proved_dispatch("export-run:readback-vc-b");
    let mut export_b = SolverProofExport::new(
        &dispatch_b,
        vc_b,
        "lrat",
        b"normalized lrat proof bytes bound to readback vc-b".to_vec(),
        Some("4.13.0".to_string()),
        1_777_070_400_100,
    );
    export_b.stdout_digest = Some(trust_types::stable_sha256_hex(b"deterministic solver stdout for readback vc-b"));
    export_b.stderr_digest = Some(trust_types::stable_sha256_hex(b"deterministic solver stderr for readback vc-b"));
    let replay_b = trust_types::stable_sha256_hex(b"deterministic replay transcript for readback vc-b");
    let mut request_b = BinaryCertificateCheckRequest::from_export(&dispatch_b, vc_b, &export_b);
    request_b.replay_transcript_digest = Some(&replay_b);
    let artifact_ref_b = produce_checked_certificate_artifact(&checker, request_b, &dir)
        .expect("second checked artifact should persist");

    let manifest = CheckedBinaryCertificateManifest::from_artifact_refs(
        &dir,
        &[artifact_ref_a, artifact_ref_b],
    )
    .expect("two checked artifacts should build a manifest");
    manifest.validate_files(&dir).expect("manifest should validate checked artifacts");
    assert_eq!(manifest.certificates.len(), 2);

    let distinct_vcs = manifest
        .certificates
        .iter()
        .map(|entry| entry.vc_sha256.clone())
        .collect::<std::collections::BTreeSet<_>>();
    let distinct_certificates = manifest
        .certificates
        .iter()
        .map(|entry| entry.certificate_sha256.clone())
        .collect::<std::collections::BTreeSet<_>>();
    let distinct_proofs = manifest
        .certificates
        .iter()
        .map(|entry| entry.proof_sha256.clone())
        .collect::<std::collections::BTreeSet<_>>();
    let distinct_proof_exports = manifest
        .certificates
        .iter()
        .map(|entry| entry.proof_export_sha256.clone())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(distinct_vcs.len(), 2);
    assert_eq!(distinct_certificates.len(), 2);
    assert_eq!(distinct_proofs.len(), 2);
    assert_eq!(distinct_proof_exports.len(), 2);

    let mut imported_dispatches = Vec::new();
    let mut audit_exports = Vec::new();
    for (label, canonical_vc_bytes, export, replay_digest, source_gate) in [
        (
            "vc-a",
            vc_a,
            &export_a,
            &replay_a,
            complete_source_backpropagation_gate_for("readback vc-a"),
        ),
        (
            "vc-b",
            vc_b,
            &export_b,
            &replay_b,
            complete_source_backpropagation_gate_for("readback vc-b"),
        ),
    ] {
        let entry = manifest
            .certificates
            .iter()
            .find(|entry| entry.dispatch_id == export.dispatch_id)
            .expect("manifest should contain exported dispatch row");
        let acceptance_request = production_acceptance_request(entry, export)
            .with_source_backpropagation_gate(source_gate.clone())
            .expect("source-backprop gate should bind to acceptance request");
        let mut gate_dispatch = proved_dispatch(&format!("gate-run:{label}"));
        let record = import_checked_certificate_manifest_entry_for_dispatch(
            &mut gate_dispatch,
            canonical_vc_bytes,
            &dir,
            entry,
            &acceptance_request,
        )
        .expect("manifest-backed checked row should import");

        assert_eq!(record.source_backpropagation_gate, source_gate);
        assert!(record.source_backpropagation_gate.source_backpropagation_allowed);
        assert_eq!(record.solver_proof_export.metadata, export.normalized_metadata());
        assert_eq!(
            record.solver_proof_export.metadata_sha256,
            export.normalized_metadata_sha256().expect("proof export metadata should digest")
        );
        assert_eq!(
            record.replay_transcript.replay_transcript_digest.as_deref(),
            Some(replay_digest.as_str())
        );

        audit_exports.push(
            CheckedBinaryCertificateAuditExport::from_manifest_entry_and_record(
                entry.clone(),
                record,
            )
            .expect("audit export should bind accepted manifest row"),
        );
        imported_dispatches.push(gate_dispatch);
    }

    let imported_summary = proof_grade_summary(&imported_dispatches);
    let imported_decision = imported_summary.proof_grade_release_gate();
    assert_eq!(imported_summary.solver_results.proved_with_certificates, 2);
    assert_eq!(imported_summary.certificate_checks.checked_certificates, 2);
    assert!(imported_decision.accepted, "{:?}", imported_decision.rejections);

    let bundle = persist_checked_certificate_audit_export_bundle(&dir, &manifest, &audit_exports)
        .expect("manifest plus audit exports should persist");
    assert_eq!(bundle.audit_exports.len(), 2);
    let readback = load_checked_certificate_audit_export_bundle(&dir)
        .expect("bundle should reload with both checked rows");
    assert_eq!(readback.manifest, manifest);
    assert_eq!(readback.bundle, bundle);

    let validation = load_checked_certificate_audit_export_bundle_rows(&dir)
        .expect("row validation should load both checked rows");
    assert_eq!(validation.accepted_count(), 2);
    assert_eq!(validation.rejected_count(), 0);
    let required_vc_sha256 = vec![trust_types::stable_sha256_hex(vc_a), trust_types::stable_sha256_hex(vc_b)];
    let coverage = validation
        .validate_complete_checked_vc_coverage(&required_vc_sha256)
        .expect("readback rows should cover every required VC");
    assert!(coverage.complete);
    assert_eq!(coverage.accepted_vcs, 2);
    let loader_coverage = load_checked_certificate_audit_export_bundle_complete_vc_coverage(
        &dir,
        &required_vc_sha256,
    )
    .expect("complete-coverage loader should accept both required VCs");
    assert!(loader_coverage.complete);

    let accepted_rows = validation.accepted_rows().collect::<Vec<_>>();
    let manifest_identity_digests = accepted_rows
        .iter()
        .map(|row| row.bundle_entry.manifest_identity_sha256.clone())
        .collect::<std::collections::BTreeSet<_>>();
    let source_gate_digests = accepted_rows
        .iter()
        .map(|row| {
            let bytes = serde_json::to_vec(&row.bundle_entry.source_backpropagation_gate)
                .expect("source-backprop gate should serialize");
            trust_types::stable_sha256_hex(&bytes)
        })
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(manifest_identity_digests.len(), 2);
    assert!(manifest_identity_digests.iter().all(|digest| is_canonical_lowercase_sha256(digest)));
    assert_eq!(source_gate_digests.len(), 2);

    let mut readback_dispatches = Vec::new();
    for row in accepted_rows {
        let (label, canonical_vc_bytes, export, replay_digest) =
            if row.manifest_entry.dispatch_id == dispatch_a.id {
                ("vc-a", vc_a, &export_a, &replay_a)
            } else if row.manifest_entry.dispatch_id == dispatch_b.id {
                ("vc-b", vc_b, &export_b, &replay_b)
            } else {
                panic!("unexpected readback dispatch id {}", row.manifest_entry.dispatch_id);
            };

        assert_eq!(row.bundle_entry.vc_sha256, trust_types::stable_sha256_hex(canonical_vc_bytes));
        assert_eq!(row.bundle_entry.proof_sha256, export.proof_sha256);
        assert_eq!(
            row.bundle_entry.proof_export_sha256,
            export.normalized_metadata_sha256().expect("proof export metadata should digest")
        );
        assert_eq!(
            row.bundle_entry.replay_transcript_digest.as_deref(),
            Some(replay_digest.as_str())
        );
        assert_eq!(
            row.bundle_entry.source_backpropagation_gate,
            row.acceptance_record.source_backpropagation_gate
        );
        assert!(row.bundle_entry.source_backpropagation_gate.source_backpropagation_allowed);
        assert!(
            row.bundle_entry
                .source_backpropagation_gate
                .source_provenance
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains(&format!("readback {label}")))
        );
        assert_eq!(
            row.acceptance_record.solver_proof_export.metadata,
            export.normalized_metadata()
        );
        assert_eq!(
            row.acceptance_record.solver_proof_export.metadata_sha256,
            row.bundle_entry.proof_export_sha256
        );

        let restored_request =
            row.audit_export.acceptance_request().expect("readback row should rebuild request");
        let mut readback_dispatch = proved_dispatch(&format!("readback-bundle-run:{label}"));
        let readback_record = import_checked_certificate_manifest_entry_for_dispatch(
            &mut readback_dispatch,
            canonical_vc_bytes,
            &dir,
            &row.manifest_entry,
            &restored_request,
        )
        .expect("readback bundle row should re-import the checked artifact");
        assert_eq!(readback_record, row.acceptance_record);
        readback_dispatches.push(readback_dispatch);
    }

    let readback_summary = proof_grade_summary(&readback_dispatches);
    let readback_decision = readback_summary.proof_grade_release_gate();
    assert_eq!(readback_summary.solver_results.proved, 2);
    assert_eq!(readback_summary.solver_results.proved_with_certificates, 2);
    assert_eq!(readback_summary.certificate_checks.checked_certificates, 2);
    assert_eq!(readback_summary.raw_solver_proof_bytes, 0);
    assert!(readback_decision.accepted, "{:?}", readback_decision.rejections);

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_certificate_audit_bundle_rejects_stale_source_backpropagation_identity() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("audit-export-source-backprop-stale-identity");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let source_gate = complete_source_backpropagation_gate();
    let acceptance_request = production_acceptance_request(entry, &export)
        .with_source_backpropagation_gate(source_gate)
        .expect("complete source-backprop gate should bind to acceptance request");
    let mut gate_dispatch = proved_dispatch("gate-run:source-backprop-stale-identity");
    let record = import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect("complete source-backprop gate should import");
    let audit_export =
        CheckedBinaryCertificateAuditExport::from_manifest_entry_and_record(entry.clone(), record)
            .expect("audit export should carry source-backprop gate");
    let mut bundle = persist_checked_certificate_audit_export_bundle(
        &dir,
        &manifest,
        std::slice::from_ref(&audit_export),
    )
    .expect("bundle should persist source-backprop identity");
    let original_manifest_identity = bundle.audit_exports[0].manifest_identity_sha256.clone();
    assert!(is_canonical_lowercase_sha256(&original_manifest_identity));

    let mut stale_audit_export = audit_export;
    let stale_gate = CheckedBinaryCertificateSourceBackpropagationGate::closed_with_blockers(
        exact_source_provenance_summary(),
        ["source_backpropagation_gate_spliced_from_stale_release_row"],
    );
    stale_audit_export.acceptance_record.source_backpropagation_gate = stale_gate.clone();
    let stale_audit_json =
        stale_audit_export.to_json().expect("stale but self-consistent audit should serialize");
    let audit_path = dir.join(&bundle.audit_exports[0].audit_export_path);
    std::fs::write(&audit_path, stale_audit_json.as_bytes())
        .expect("stale audit export should be writable");
    bundle.audit_exports[0].source_backpropagation_gate = stale_gate;
    bundle.audit_exports[0].audit_export_sha256 = trust_types::stable_sha256_hex(stale_audit_json.as_bytes());
    assert_eq!(bundle.audit_exports[0].manifest_identity_sha256, original_manifest_identity);
    let bundle_json = bundle.to_json().expect("stale bundle should remain structurally valid");
    std::fs::write(checked_certificate_audit_export_bundle_path(&dir), bundle_json.as_bytes())
        .expect("stale bundle should be writable");

    let validation = load_checked_certificate_audit_export_bundle_rows(&dir)
        .expect("row-oriented loader should classify stale source-backprop identity");
    assert_eq!(validation.accepted_count(), 0);
    assert_eq!(validation.rejected_count(), 1);
    let rejected = validation.rejected_rows().next().expect("stale row should reject");
    assert_eq!(
        rejected.code,
        CheckedBinaryCertificateAuditExportBundleRejectionCode::ValidationFailed
    );
    assert!(
        rejected.reason.contains("audit_export_bundle.manifest_identity_sha256"),
        "{}",
        rejected.reason
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_certificate_audit_bundle_rejects_dropped_source_backpropagation_gate() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("audit-export-source-backprop-dropped");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let source_gate = complete_source_backpropagation_gate();
    let acceptance_request = production_acceptance_request(entry, &export)
        .with_source_backpropagation_gate(source_gate.clone())
        .expect("complete source-backprop gate should bind to acceptance request");
    let mut gate_dispatch = proved_dispatch("gate-run:source-backprop-dropped");
    let record = import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect("complete source-backprop gate should import");
    let audit_export =
        CheckedBinaryCertificateAuditExport::from_manifest_entry_and_record(entry.clone(), record)
            .expect("audit export should carry source-backprop gate");
    let bundle = persist_checked_certificate_audit_export_bundle(
        &dir,
        &manifest,
        std::slice::from_ref(&audit_export),
    )
    .expect("bundle should persist source-backprop gate");
    assert_eq!(bundle.audit_exports[0].source_backpropagation_gate, source_gate);

    let bundle_path = checked_certificate_audit_export_bundle_path(&dir);
    let mut bundle_json: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(&bundle_path).expect("bundle json should be readable"),
    )
    .expect("bundle json should parse");
    bundle_json["audit_exports"][0]
        .as_object_mut()
        .expect("bundle row should be an object")
        .remove("source_backpropagation_gate");
    std::fs::write(
        &bundle_path,
        serde_json::to_string_pretty(&bundle_json).expect("mutated bundle should serialize"),
    )
    .expect("mutated bundle should be writable");

    let err = load_checked_certificate_audit_export_bundle(&dir)
        .expect_err("dropping the bundle source-backprop gate must fail closed");
    assert!(
        matches!(err, CertError::InvalidCertificate { ref reason } if reason.contains("audit_export_bundle.source_backpropagation_gate")),
        "{err:?}"
    );

    let validation = load_checked_certificate_audit_export_bundle_rows(&dir)
        .expect("row validation should classify the dropped-gate bundle row");
    match &validation.rows[0] {
        CheckedBinaryCertificateAuditExportBundleValidationRow::Rejected(row) => {
            assert_eq!(
                row.code,
                CheckedBinaryCertificateAuditExportBundleRejectionCode::ValidationFailed
            );
            assert!(
                row.reason.contains("audit_export_bundle.source_backpropagation_gate"),
                "{}",
                row.reason
            );
        }
        other => panic!("dropped source-backprop gate should reject row, got {other:?}"),
    }

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_certificate_source_backpropagation_gate_fails_closed_when_prerequisites_missing() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("audit-export-source-backprop-incomplete");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let mut incomplete_gate = complete_source_backpropagation_gate();
    incomplete_gate.accepted_target_validation = false;
    incomplete_gate.source_backpropagation_allowed = true;
    incomplete_gate.blockers.clear();

    let err = production_acceptance_request(entry, &export)
        .with_source_backpropagation_gate(incomplete_gate)
        .expect_err("source_backpropagation_allowed=true must require target validation");
    assert!(
        matches!(err, CheckError::SourceBackpropagationGateIncomplete { ref reason } if reason.contains("accepted_target_validation_missing")),
        "{err:?}"
    );

    let mut missing_replay_digest = complete_source_backpropagation_gate();
    missing_replay_digest.source_backpropagation_allowed = true;
    let mut acceptance_request = production_acceptance_request(entry, &export);
    acceptance_request.replay_transcript.replay_transcript_digest = None;
    acceptance_request.source_backpropagation_gate = missing_replay_digest;
    let mut gate_dispatch = proved_dispatch("gate-run:source-backprop-missing-replay-digest");
    let err = import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect_err("source backpropagation must require exact replay transcript identity");
    assert!(
        matches!(err, CertError::InvalidCertificate { ref reason } if reason.contains("exact replay identity requires replay transcript digest")),
        "{err:?}"
    );
    assert!(!gate_dispatch.certificate.is_checked());

    let legacy_json = serde_json::json!({
        "schema_version": "checked-binary-certificate-acceptance.v1",
        "checker_selection": acceptance_request.checker_selection,
        "production_checker_evidence": acceptance_request.production_checker_evidence,
        "solver_proof_export": acceptance_request.solver_proof_export,
        "replay_transcript": CheckedBinaryCertificateManifestAcceptanceRequest::from_manifest_entry_and_solver_proof_export_metadata(
            entry,
            export.normalized_metadata(),
        )
        .expect("legacy request fixture should build")
        .replay_transcript,
        "artifact_identity": acceptance_request.artifact_identity,
    });
    let legacy_request: CheckedBinaryCertificateManifestAcceptanceRequest =
        serde_json::from_value(legacy_json).expect("legacy request should deserialize");
    assert!(!legacy_request.source_backpropagation_gate.source_backpropagation_allowed);
    assert!(
        legacy_request
            .source_backpropagation_gate
            .blockers
            .iter()
            .any(|blocker| blocker == "source_backpropagation_gate_not_evaluated")
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_certificate_source_backpropagation_requires_unsupported_ledger_elimination() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("audit-export-source-backprop-unsupported-ledger");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let unsupported_ledger = unresolved_unsupported_ledger();
    let unsupported_summary = UnsupportedLedgerSummary::from_ledger(&unsupported_ledger);

    let blocked_gate = complete_source_backpropagation_gate()
        .with_unsupported_ledger_summary(unsupported_summary.clone());
    assert!(!blocked_gate.source_backpropagation_allowed);
    assert!(
        blocked_gate
            .blockers
            .iter()
            .any(|blocker| blocker == "unsupported_ledger_entries_unconsumed")
    );

    let acceptance_request = production_acceptance_request(entry, &export)
        .with_source_backpropagation_gate(blocked_gate.clone())
        .expect("closed source-backprop gate should still carry checked audit evidence");
    let mut blocked_dispatch = proved_dispatch("gate-run:source-backprop-unsupported-ledger");
    let record = import_checked_certificate_manifest_entry_for_dispatch(
        &mut blocked_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect("closed source-backprop gate should not reject checked certificate import");
    assert_eq!(record.source_backpropagation_gate, blocked_gate);
    assert!(!record.source_backpropagation_gate.source_backpropagation_allowed);
    assert!(blocked_dispatch.certificate.is_checked());

    let blocked_summary = proof_grade_summary_with_ledger(&[blocked_dispatch], &unsupported_ledger);
    let blocked_decision = blocked_summary.proof_grade_release_gate();
    assert_eq!(blocked_summary.certificate_checks.checked_certificates, 1);
    assert!(blocked_decision.rejected());
    assert!(blocked_decision.rejections.iter().any(|reason| {
        matches!(reason, BinaryReleaseGateRejection::UnsupportedRecordsPresent { count: 1, .. })
    }));
    assert!(!blocked_decision.rejections.iter().any(|reason| {
        matches!(reason, BinaryReleaseGateRejection::MissingProofCertificates { .. })
    }));

    let mut forged_open_gate = complete_source_backpropagation_gate();
    forged_open_gate.unsupported_ledger_summary = unsupported_summary;
    forged_open_gate.source_backpropagation_allowed = true;
    forged_open_gate.blockers.clear();
    let err = production_acceptance_request(entry, &export)
        .with_source_backpropagation_gate(forged_open_gate)
        .expect_err("unsupported ledger rows must keep source backpropagation closed");
    assert!(
        matches!(err, CheckError::SourceBackpropagationGateIncomplete { ref reason } if reason.contains("unsupported_ledger_entries_unconsumed")),
        "{err:?}"
    );

    let eliminated_gate = complete_source_backpropagation_gate()
        .with_unsupported_ledger_summary(UnsupportedLedgerSummary::default());
    assert!(eliminated_gate.source_backpropagation_allowed);
    assert!(eliminated_gate.blockers.is_empty());
    let acceptance_request = production_acceptance_request(entry, &export)
        .with_source_backpropagation_gate(eliminated_gate.clone())
        .expect("eliminated unsupported ledger should allow source backpropagation when other gates pass");
    let mut allowed_dispatch = proved_dispatch("gate-run:source-backprop-eliminated-ledger");
    let record = import_checked_certificate_manifest_entry_for_dispatch(
        &mut allowed_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect("complete source-backprop gate should import when unsupported ledger is eliminated");
    assert_eq!(record.source_backpropagation_gate, eliminated_gate);
    assert!(record.source_backpropagation_gate.source_backpropagation_allowed);

    let allowed_summary =
        proof_grade_summary_with_ledger(&[allowed_dispatch], &UnsupportedLedger::default());
    let allowed_decision = allowed_summary.proof_grade_release_gate();
    assert!(allowed_decision.accepted, "{:?}", allowed_decision.rejections);

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_certificate_source_backpropagation_requires_symbolic_formula_consumer() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("audit-export-source-backprop-symbolic-formula");
    let entry = manifest.certificates.first().expect("manifest should have one row");

    let blocked_gate =
        complete_source_backpropagation_gate().with_symbolic_formula_consumer_evidence(1, false);
    assert!(!blocked_gate.source_backpropagation_allowed);
    assert!(
        blocked_gate
            .blockers
            .iter()
            .any(|blocker| blocker == "trust_symbolic_formula_entries_unconsumed")
    );

    let mut direct_gate_without_consumer = complete_source_backpropagation_gate();
    assert!(direct_gate_without_consumer.source_backpropagation_allowed);
    direct_gate_without_consumer.preserved_symbolic_formulas = 1;
    assert!(!direct_gate_without_consumer.symbolic_formula_consumer_accepted);
    let err = production_acceptance_request(entry, &export)
        .with_source_backpropagation_gate(direct_gate_without_consumer)
        .expect_err(
            "direct gate with preserved formulas but no consumer evidence must fail closed",
        );
    assert!(
        matches!(err, CheckError::SourceBackpropagationGateIncomplete { ref reason } if reason.contains("trust_symbolic_formula_entries_unconsumed")),
        "{err:?}"
    );

    let acceptance_request = production_acceptance_request(entry, &export)
        .with_source_backpropagation_gate(blocked_gate.clone())
        .expect("closed source-backprop gate should still carry checked audit evidence");
    let mut blocked_dispatch = proved_dispatch("gate-run:source-backprop-symbolic-unconsumed");
    let record = import_checked_certificate_manifest_entry_for_dispatch(
        &mut blocked_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect("closed source-backprop gate should not reject checked certificate import");
    assert_eq!(record.source_backpropagation_gate, blocked_gate);
    assert!(!record.source_backpropagation_gate.source_backpropagation_allowed);
    assert!(blocked_dispatch.certificate.is_checked());

    let mut forged_open_gate =
        complete_source_backpropagation_gate().with_symbolic_formula_consumer_evidence(1, false);
    forged_open_gate.source_backpropagation_allowed = true;
    forged_open_gate.blockers.clear();
    let err = production_acceptance_request(entry, &export)
        .with_source_backpropagation_gate(forged_open_gate)
        .expect_err("unconsumed symbolic formulas must keep source backpropagation closed");
    assert!(
        matches!(err, CheckError::SourceBackpropagationGateIncomplete { ref reason } if reason.contains("trust_symbolic_formula_entries_unconsumed")),
        "{err:?}"
    );

    let consumed_gate =
        complete_source_backpropagation_gate().with_symbolic_formula_consumer_evidence(1, true);
    assert!(consumed_gate.source_backpropagation_allowed);
    assert!(consumed_gate.blockers.is_empty());
    let acceptance_request = production_acceptance_request(entry, &export)
        .with_source_backpropagation_gate(consumed_gate.clone())
        .expect("symbolic formula consumer evidence should allow source backpropagation");
    let mut allowed_dispatch = proved_dispatch("gate-run:source-backprop-symbolic-consumed");
    let record = import_checked_certificate_manifest_entry_for_dispatch(
        &mut allowed_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect("consumed symbolic formula gate should import");
    assert_eq!(record.source_backpropagation_gate, consumed_gate);
    assert!(record.source_backpropagation_gate.source_backpropagation_allowed);

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn proof_grade_release_requires_manifest_identity_for_every_source_backprop_vc() {
    let checker = checked_certificate_checker();
    let dir = temp_artifact_dir("manifest-identity-per-vc-coverage");

    let vc_a: &[u8] = br#"{"vc":"main memory safety A"}"#;
    let export_dispatch_a = proved_dispatch("export-run:vc-a");
    let export_a = proof_export(&export_dispatch_a, vc_a);
    let replay_a = trust_types::stable_sha256_hex(b"deterministic replay transcript for vc-a");
    let mut request_a =
        BinaryCertificateCheckRequest::from_export(&export_dispatch_a, vc_a, &export_a);
    request_a.replay_transcript_digest = Some(&replay_a);
    let artifact_ref_a = produce_checked_certificate_artifact(&checker, request_a, &dir)
        .expect("first checked artifact should persist");

    let vc_b: &[u8] = br#"{"vc":"stack bounds safety B"}"#;
    let export_dispatch_b = proved_dispatch("export-run:vc-b");
    let export_b = proof_export(&export_dispatch_b, vc_b);
    let replay_b = trust_types::stable_sha256_hex(b"deterministic replay transcript for vc-b");
    let mut request_b =
        BinaryCertificateCheckRequest::from_export(&export_dispatch_b, vc_b, &export_b);
    request_b.replay_transcript_digest = Some(&replay_b);
    let artifact_ref_b = produce_checked_certificate_artifact(&checker, request_b, &dir)
        .expect("second checked artifact should persist");

    let manifest = CheckedBinaryCertificateManifest::from_artifact_refs(
        &dir,
        &[artifact_ref_a, artifact_ref_b],
    )
    .expect("two checked artifacts should build a manifest");
    manifest.validate_files(&dir).expect("manifest should validate against checked artifacts");
    let entry_a = manifest
        .certificates
        .iter()
        .find(|entry| entry.dispatch_id == export_dispatch_a.id)
        .expect("manifest should contain vc-a");
    let entry_b = manifest
        .certificates
        .iter()
        .find(|entry| entry.dispatch_id == export_dispatch_b.id)
        .expect("manifest should contain vc-b");

    let request_a = production_acceptance_request(entry_a, &export_a)
        .with_source_backpropagation_gate(complete_source_backpropagation_gate())
        .expect("source-backprop gate should bind to vc-a acceptance");
    let request_b = production_acceptance_request(entry_b, &export_b)
        .with_source_backpropagation_gate(complete_source_backpropagation_gate())
        .expect("source-backprop gate should bind to vc-b acceptance");

    let mut covered_a = proved_dispatch("gate-run:vc-a");
    let record_a = import_checked_certificate_manifest_entry_for_dispatch(
        &mut covered_a,
        vc_a,
        &dir,
        entry_a,
        &request_a,
    )
    .expect("vc-a should import with manifest identity");
    assert!(record_a.source_backpropagation_gate.source_backpropagation_allowed);

    let acceptance_b = accept_checked_certificate_manifest_entry(&dir, vc_b, entry_b, &request_b)
        .expect("vc-b manifest row should accept before dispatch import");
    let mut status_only_b = proved_dispatch("gate-run:vc-b-status-only");
    status_only_b.certificate = acceptance_b
        .record
        .proof_certificate_status()
        .expect("accepted manifest record should produce checked status");

    let partial_summary = proof_grade_summary(&[covered_a.clone(), status_only_b]);
    let partial_decision = partial_summary.proof_grade_release_gate();
    assert!(partial_decision.rejected());
    assert_eq!(partial_summary.solver_results.proved, 2);
    assert_eq!(partial_summary.solver_results.proved_with_certificates, 1);
    assert_eq!(partial_summary.certificate_checks.checked_certificates, 1);
    assert_eq!(partial_summary.certificate_checks.missing_checked_certificates, 1);
    assert!(
        partial_summary.certificate_checks.records[1]
            .coherence_failures
            .iter()
            .any(|failure| failure == "missing manifest-backed checked certificate identity"),
        "{:?}",
        partial_summary.certificate_checks.records[1]
    );
    assert!(partial_decision.rejections.iter().any(|reason| {
        matches!(
            reason,
            BinaryReleaseGateRejection::MissingProofCertificates {
                vc_count: 2,
                proved: 2,
                proved_with_certificates: 1,
                missing_certificates: 1,
            }
        )
    }));

    let mut covered_b = proved_dispatch("gate-run:vc-b");
    let record_b = import_checked_certificate_manifest_entry_for_dispatch(
        &mut covered_b,
        vc_b,
        &dir,
        entry_b,
        &request_b,
    )
    .expect("vc-b should import with manifest identity");
    assert!(record_b.source_backpropagation_gate.source_backpropagation_allowed);

    let covered_summary = proof_grade_summary(&[covered_a, covered_b]);
    let covered_decision = covered_summary.proof_grade_release_gate();
    assert_eq!(covered_summary.solver_results.proved_with_certificates, 2);
    assert_eq!(covered_summary.certificate_checks.checked_certificates, 2);
    assert_eq!(covered_summary.certificate_checks.missing_checked_certificates, 0);
    assert!(
        covered_summary
            .certificate_checks
            .records
            .iter()
            .all(|record| record.checked && record.coherence_failures.is_empty())
    );
    assert!(covered_decision.accepted, "{:?}", covered_decision.rejections);

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_manifest_audit_export_bundle_rejects_stale_audit_row() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("audit-export-bundle-stale-audit");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let acceptance_request = production_acceptance_request(entry, &export);
    let mut gate_dispatch = proved_dispatch("gate-run:vc0");
    let record = import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect("manifest acceptance should import before bundle export");
    let audit_export =
        CheckedBinaryCertificateAuditExport::from_manifest_entry_and_record(entry.clone(), record)
            .expect("audit export should bind manifest row to accepted record");
    let mut bundle = persist_checked_certificate_audit_export_bundle(
        &dir,
        &manifest,
        std::slice::from_ref(&audit_export),
    )
    .expect("bundle should persist before stale readback test");

    let mut stale_audit_export = audit_export;
    stale_audit_export.manifest_entry.checker_version = "0.2.0".to_string();
    stale_audit_export.acceptance_record.checker_selection.checker_version = "0.2.0".to_string();
    stale_audit_export
        .acceptance_record
        .production_checker_evidence
        .as_mut()
        .expect("production evidence should be present")
        .checker_version = "0.2.0".to_string();
    let stale_audit_json =
        stale_audit_export.to_json().expect("self-consistent stale audit should serialize");
    let audit_path = dir.join(&bundle.audit_exports[0].audit_export_path);
    std::fs::write(&audit_path, stale_audit_json.as_bytes())
        .expect("stale audit export should be writable");
    bundle.audit_exports[0].audit_export_sha256 = trust_types::stable_sha256_hex(stale_audit_json.as_bytes());
    let bundle_json = bundle.to_json().expect("updated bundle digest should serialize");
    std::fs::write(checked_certificate_audit_export_bundle_path(&dir), bundle_json.as_bytes())
        .expect("updated bundle should be writable");

    let err = load_checked_certificate_audit_export_bundle(&dir)
        .expect_err("stale audit export row must fail closed against manifest");

    assert!(
        matches!(err, CertError::InvalidCertificate { ref reason } if reason.contains("audit_export.manifest_entry")),
        "{err:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_audit_export_bundle_rows_reject_stale_proof_export_and_import_valid_rows()
 {
    let checker = checked_certificate_checker();
    let dir = temp_artifact_dir("audit-export-bundle-row-rejections");

    let vc_a: &[u8] = br#"{"vc":"main memory safety A"}"#;
    let dispatch_a = proved_dispatch("export-run:vc-a");
    let export_a = proof_export(&dispatch_a, vc_a);
    let artifact_ref_a = produce_checked_certificate_artifact(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch_a, vc_a, &export_a),
        &dir,
    )
    .expect("first checked artifact should persist");

    let vc_b: &[u8] = br#"{"vc":"main memory safety B"}"#;
    let dispatch_b = proved_dispatch("export-run:vc-b");
    let export_b = proof_export(&dispatch_b, vc_b);
    let artifact_ref_b = produce_checked_certificate_artifact(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch_b, vc_b, &export_b),
        &dir,
    )
    .expect("second checked artifact should persist");

    let manifest = CheckedBinaryCertificateManifest::from_artifact_refs(
        &dir,
        &[artifact_ref_a, artifact_ref_b],
    )
    .expect("two checked artifact refs should build a manifest");

    let mut audit_exports = Vec::new();
    for (dispatch, canonical_vc_bytes, export) in
        [(&dispatch_a, vc_a, &export_a), (&dispatch_b, vc_b, &export_b)]
    {
        let entry = manifest
            .certificates
            .iter()
            .find(|entry| entry.dispatch_id == dispatch.id)
            .expect("manifest should contain exported dispatch");
        let acceptance_request = production_acceptance_request(entry, export);
        let mut gate_dispatch = proved_dispatch(format!("gate-run:{}", dispatch.id).as_str());
        let record = import_checked_certificate_manifest_entry_for_dispatch(
            &mut gate_dispatch,
            canonical_vc_bytes,
            &dir,
            entry,
            &acceptance_request,
        )
        .expect("manifest row should import before audit export");
        audit_exports.push(
            CheckedBinaryCertificateAuditExport::from_manifest_entry_and_record(
                entry.clone(),
                record,
            )
            .expect("audit export should bind accepted manifest row"),
        );
    }

    let bundle = persist_checked_certificate_audit_export_bundle(&dir, &manifest, &audit_exports)
        .expect("bundle should persist before row rejection test");
    let stale_certificate_sha256 = audit_exports[0].manifest_entry.certificate_sha256.clone();
    let stale_bundle_entry = bundle
        .audit_exports
        .iter()
        .find(|entry| entry.certificate_sha256 == stale_certificate_sha256)
        .expect("bundle should contain stale test row");
    let mut stale_audit_export = audit_exports[0].clone();
    stale_audit_export.acceptance_record.solver_proof_export.metadata.proof_sha256 =
        trust_types::stable_sha256_hex(b"stale proof payload digest");
    stale_audit_export.acceptance_record.solver_proof_export.metadata_sha256 = stale_audit_export
        .acceptance_record
        .solver_proof_export
        .metadata
        .sha256()
        .expect("tampered proof export metadata should still be digestible");
    stale_audit_export
        .acceptance_record
        .production_checker_evidence
        .as_mut()
        .expect("production evidence should be present")
        .proof_export_sha256 =
        stale_audit_export.acceptance_record.solver_proof_export.metadata_sha256.clone();
    let stale_audit_json = serde_json::to_string_pretty(&stale_audit_export)
        .expect("tampered audit export should serialize");
    std::fs::write(dir.join(&stale_bundle_entry.audit_export_path), stale_audit_json.as_bytes())
        .expect("tampered audit export should be writable");

    let mut stale_bundle = bundle;
    stale_bundle
        .audit_exports
        .iter_mut()
        .find(|entry| entry.certificate_sha256 == stale_certificate_sha256)
        .expect("bundle should contain stale test row")
        .audit_export_sha256 = trust_types::stable_sha256_hex(stale_audit_json.as_bytes());
    let stale_bundle_json = stale_bundle.to_json().expect("updated bundle digest should serialize");
    std::fs::write(
        checked_certificate_audit_export_bundle_path(&dir),
        stale_bundle_json.as_bytes(),
    )
    .expect("updated bundle should be writable");

    let validation = load_checked_certificate_audit_export_bundle_rows(&dir)
        .expect("row-oriented bundle loader should keep valid rows");
    assert_eq!(validation.accepted_count(), 1);
    assert_eq!(validation.rejected_count(), 1);
    let rejected = validation.rejected_rows().collect::<Vec<_>>();
    assert_eq!(rejected[0].certificate_sha256, stale_certificate_sha256);
    assert_eq!(
        rejected[0].code,
        CheckedBinaryCertificateAuditExportBundleRejectionCode::ProofExportMismatch
    );
    assert_eq!(rejected[0].code.as_str(), "proof_export_mismatch");
    assert!(rejected[0].reason.contains("solver_proof_export.proof_sha256"), "{:?}", rejected[0]);

    let accepted = validation.accepted_rows().collect::<Vec<_>>();
    let accepted_row = accepted[0];
    assert_ne!(accepted_row.manifest_entry.certificate_sha256, stale_certificate_sha256);
    let accepted_vc =
        if accepted_row.manifest_entry.dispatch_id == dispatch_a.id { vc_a } else { vc_b };
    let mut current_dispatch = proved_dispatch("current-run:valid-row");
    import_checked_certificate_for_dispatch_by_canonical_digests(
        &mut current_dispatch,
        accepted_vc,
        &accepted_row.artifact,
    )
    .expect("accepted bundle row should still import by canonical VC and origin digests");
    assert!(current_dispatch.certificate.is_checked());

    let required_vc_sha256 = vec![trust_types::stable_sha256_hex(vc_a), trust_types::stable_sha256_hex(vc_b)];
    let coverage_err = validation
        .validate_complete_checked_vc_coverage(&required_vc_sha256)
        .expect_err("stale rejected rows must not satisfy per-VC checked coverage");
    assert!(
        matches!(coverage_err, CheckError::CheckedVcCoverageIncomplete { ref reason } if reason.contains("rejected_rows=1") && reason.contains(&stale_audit_export.manifest_entry.vc_sha256)),
        "{coverage_err:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_certificate_production_manifest_readback_rejects_stale_checker_identity() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("production-manifest-readback-stale-checker");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let acceptance_request = production_acceptance_request(entry, &export);
    let mut gate_dispatch = proved_dispatch("gate-run:stale-checker-readback");
    let record = import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect("manifest row should import before stale checker readback test");
    let audit_export =
        CheckedBinaryCertificateAuditExport::from_manifest_entry_and_record(entry.clone(), record)
            .expect("audit export should bind accepted manifest row");
    let mut bundle = persist_checked_certificate_audit_export_bundle(
        &dir,
        &manifest,
        std::slice::from_ref(&audit_export),
    )
    .expect("bundle should persist before stale checker readback test");

    bundle.audit_exports[0].checker = "stale-ay-lrat-binary-check".to_string();
    let bundle_json =
        bundle.to_json().expect("stale checker bundle should remain structurally valid");
    std::fs::write(checked_certificate_audit_export_bundle_path(&dir), bundle_json.as_bytes())
        .expect("stale checker bundle should be writable");

    let validation = load_checked_certificate_audit_export_bundle_rows(&dir)
        .expect("row-oriented loader should classify stale checker identity");
    assert_eq!(validation.accepted_count(), 0);
    assert_eq!(validation.rejected_count(), 1);
    let rejected = validation.rejected_rows().next().expect("stale checker row should reject");
    assert_eq!(
        rejected.code,
        CheckedBinaryCertificateAuditExportBundleRejectionCode::CheckerMismatch
    );
    assert!(rejected.reason.contains("audit_export_bundle.checker"), "{}", rejected.reason);

    let accepted_rows = validation.accepted_rows().collect::<Vec<_>>();
    let accepted_inputs = accepted_rows
        .iter()
        .map(|row| CheckedBinaryCertificateProductionManifestAcceptedRowInput {
            manifest_entry: &row.manifest_entry,
            acceptance_record: &row.acceptance_record,
        })
        .collect::<Vec<_>>();
    let production_manifest =
        CheckedBinaryCertificateProductionManifest::from_manifest_acceptance_records(
            1,
            &accepted_inputs,
        )
        .expect("empty accepted readback should still build a rejectable production manifest");
    let decision = production_manifest.evaluate();
    assert!(!decision.accepted);
    assert!(
        decision.rejections.iter().any(|rejection| matches!(
            rejection,
            CheckedBinaryCertificateProductionManifestRejection::RequiredVcCoverageIncomplete {
                required_vcs: 1,
                entries: 0
            }
        )),
        "{:?}",
        decision.rejections
    );

    let required_vc_sha256 = vec![trust_types::stable_sha256_hex(canonical_vc_bytes)];
    let coverage_err = validation
        .validate_complete_checked_vc_coverage(&required_vc_sha256)
        .expect_err("stale checker row must not satisfy checked VC coverage");
    assert!(
        matches!(coverage_err, CheckError::CheckedVcCoverageIncomplete { ref reason } if reason.contains("rejected_rows=1") && reason.contains(&required_vc_sha256[0])),
        "{coverage_err:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_certificate_production_manifest_readback_rejects_noncanonical_manifest_identity_digest()
{
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("production-manifest-readback-noncanonical-identity");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let acceptance_request = production_acceptance_request(entry, &export);
    let mut gate_dispatch = proved_dispatch("gate-run:noncanonical-manifest-identity");
    let record = import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect("manifest row should import before noncanonical readback test");
    let audit_export =
        CheckedBinaryCertificateAuditExport::from_manifest_entry_and_record(entry.clone(), record)
            .expect("audit export should bind accepted manifest row");
    persist_checked_certificate_audit_export_bundle(
        &dir,
        &manifest,
        std::slice::from_ref(&audit_export),
    )
    .expect("bundle should persist before noncanonical readback test");

    let bundle_path = checked_certificate_audit_export_bundle_path(&dir);
    let mut bundle_json: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(&bundle_path).expect("bundle JSON should be readable"),
    )
    .expect("bundle JSON should parse");
    let manifest_identity = bundle_json["audit_exports"][0]["manifest_identity_sha256"]
        .as_str()
        .expect("bundle row should carry manifest identity digest")
        .to_ascii_uppercase();
    bundle_json["audit_exports"][0]["manifest_identity_sha256"] =
        serde_json::Value::String(manifest_identity);
    std::fs::write(
        &bundle_path,
        serde_json::to_string_pretty(&bundle_json).expect("mutated bundle should serialize"),
    )
    .expect("mutated bundle should be writable");

    let err = load_checked_certificate_audit_export_bundle_rows(&dir)
        .expect_err("noncanonical manifest identity digest must fail closed before row acceptance");
    assert!(
        matches!(err, CertError::InvalidCertificate { ref reason } if reason.contains("audit export bundle manifest_identity_sha256") && reason.contains("canonical lowercase sha256")),
        "{err:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_audit_export_bundle_coverage_rejects_missing_required_vc() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let missing_vc_bytes = br#"{"vc":"stack bounds safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("audit-export-bundle-missing-vc-coverage");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let acceptance_request = production_acceptance_request(entry, &export);
    let mut gate_dispatch = proved_dispatch("gate-run:vc0");
    let record = import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect("single manifest row should import before coverage accounting");
    let audit_export =
        CheckedBinaryCertificateAuditExport::from_manifest_entry_and_record(entry.clone(), record)
            .expect("audit export should bind accepted manifest row");
    persist_checked_certificate_audit_export_bundle(&dir, &manifest, &[audit_export])
        .expect("single-row checked audit bundle should persist");

    let present_required = vec![trust_types::stable_sha256_hex(canonical_vc_bytes)];
    let present_coverage =
        load_checked_certificate_audit_export_bundle_complete_vc_coverage(&dir, &present_required)
            .expect("bundle should satisfy the single required VC");
    assert!(present_coverage.complete);
    assert_eq!(present_coverage.required_vcs, 1);
    assert_eq!(present_coverage.accepted_vcs, 1);
    assert_eq!(present_coverage.rejected_rows, 0);

    let missing_vc_sha256 = trust_types::stable_sha256_hex(missing_vc_bytes);
    let required = vec![trust_types::stable_sha256_hex(canonical_vc_bytes), missing_vc_sha256.clone()];
    let validation = load_checked_certificate_audit_export_bundle_rows(&dir)
        .expect("row validation should load the single accepted row");
    let coverage =
        validation.checked_vc_coverage_for(&required).expect("coverage accounting should run");
    assert!(!coverage.complete);
    assert_eq!(coverage.required_vcs, 2);
    assert_eq!(coverage.accepted_vcs, 1);
    assert_eq!(coverage.missing_vc_sha256, vec![missing_vc_sha256.clone()]);

    let coverage_err = validation
        .validate_complete_checked_vc_coverage(&required)
        .expect_err("accepted bundle missing a required VC must fail closed");
    assert!(
        matches!(coverage_err, CheckError::CheckedVcCoverageIncomplete { ref reason } if reason.contains(&missing_vc_sha256) && reason.contains("required_vcs=2")),
        "{coverage_err:?}"
    );

    let load_err =
        load_checked_certificate_audit_export_bundle_complete_vc_coverage(&dir, &required)
            .expect_err("complete-coverage loader must reject missing required VC coverage");
    assert!(
        matches!(load_err, CertError::InvalidCertificate { ref reason } if reason.contains("checked certificate audit bundle coverage incomplete") && reason.contains(&missing_vc_sha256)),
        "{load_err:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_audit_export_readback_rejects_checker_selection_mismatch() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("audit-export-checker-mismatch");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let acceptance_request = production_acceptance_request(entry, &export);
    let mut gate_dispatch = proved_dispatch("gate-run:vc0");
    let record = import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect("manifest acceptance should import before audit export");
    let mut audit_export =
        CheckedBinaryCertificateAuditExport::from_manifest_entry_and_record(entry.clone(), record)
            .expect("audit export should bind manifest row to accepted record");
    audit_export.acceptance_record.checker_selection.checker_version = "0.2.0".to_string();
    audit_export
        .acceptance_record
        .production_checker_evidence
        .as_mut()
        .expect("production evidence should be present")
        .checker_version = "0.2.0".to_string();
    let json = serde_json::to_string_pretty(&audit_export)
        .expect("tampered audit export should serialize for readback test");

    let err = CheckedBinaryCertificateAuditExport::from_json(&json)
        .expect_err("checker selection mismatch must fail closed on JSON readback");

    assert!(
        matches!(err, CertError::InvalidCertificate { ref reason } if reason.contains("checker_selection.checker_version")),
        "{err:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_audit_export_readback_rejects_proof_export_metadata_mismatch() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("audit-export-proof-export-mismatch");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let acceptance_request = production_acceptance_request(entry, &export);
    let mut gate_dispatch = proved_dispatch("gate-run:vc0");
    let record = import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect("manifest acceptance should import before audit export");
    let mut audit_export =
        CheckedBinaryCertificateAuditExport::from_manifest_entry_and_record(entry.clone(), record)
            .expect("audit export should bind manifest row to accepted record");
    audit_export.manifest_entry.proof_export_sha256 =
        trust_types::stable_sha256_hex(b"different proof export metadata");
    let json = serde_json::to_string_pretty(&audit_export)
        .expect("tampered audit export should serialize for readback test");

    let err = CheckedBinaryCertificateAuditExport::from_json(&json)
        .expect_err("proof export metadata mismatch must fail closed on JSON readback");

    assert!(
        matches!(err, CertError::InvalidCertificate { ref reason } if reason.contains("solver_proof_export.metadata_sha256")),
        "{err:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_manifest_acceptance_rejects_checker_identity_mismatch() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("manifest-acceptance-checker-mismatch");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let mut acceptance_request = production_acceptance_request(entry, &export);
    acceptance_request.checker_selection.checker = "shadow-checker".to_string();
    acceptance_request
        .production_checker_evidence
        .as_mut()
        .expect("production evidence should be present")
        .checker = "shadow-checker".to_string();
    let mut gate_dispatch = proved_dispatch("gate-run:vc0");

    let err = import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect_err("checker identity mismatch must fail closed");

    assert!(
        matches!(err, CertError::InvalidCertificate { ref reason } if reason.contains("checker_selection.checker")),
        "{err:?}"
    );
    assert!(!gate_dispatch.certificate.is_checked());

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_manifest_acceptance_rejects_artifact_identity_mismatch() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("manifest-acceptance-artifact-mismatch");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let mut acceptance_request = production_acceptance_request(entry, &export);
    let wrong_digest = trust_types::stable_sha256_hex(b"different checked certificate artifact identity");
    acceptance_request.artifact_identity.certificate_sha256 = wrong_digest.clone();
    acceptance_request.artifact_identity.content_sha256 = wrong_digest.clone();
    acceptance_request.artifact_identity.certificate_path =
        checked_certificate_relative_path_for_digest(&wrong_digest);
    acceptance_request
        .production_checker_evidence
        .as_mut()
        .expect("production evidence should be present")
        .certificate_sha256 = wrong_digest.clone();
    let mut gate_dispatch = proved_dispatch("gate-run:vc0");

    let err = import_checked_certificate_manifest_entry_for_dispatch(
        &mut gate_dispatch,
        canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect_err("artifact identity mismatch must fail closed");

    assert!(
        matches!(err, CertError::InvalidCertificate { ref reason } if reason.contains("artifact_identity.certificate_sha256")),
        "{err:?}"
    );
    assert!(!gate_dispatch.certificate.is_checked());

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_manifest_rejects_replay_transcript_digest_mismatch() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("vc0");
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let replay_transcript_digest = trust_types::stable_sha256_hex(b"deterministic replay transcript for manifest row");
    let dir = temp_artifact_dir("manifest-replay-digest-mismatch");
    let mut request =
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export);
    request.replay_transcript_digest = Some(&replay_transcript_digest);
    let artifact_ref = produce_checked_certificate_artifact(&checker, request, &dir)
        .expect("checked artifact should persist");
    let mut manifest = CheckedBinaryCertificateManifest::from_artifact_refs(&dir, &[artifact_ref])
        .expect("manifest should build from checked artifact refs");
    manifest.certificates[0].replay_transcript_digest =
        Some(trust_types::stable_sha256_hex(b"different replay transcript"));

    let err = manifest
        .validate_files(&dir)
        .expect_err("manifest replay transcript digest mismatch must fail closed");

    assert!(
        matches!(err, CertError::InvalidCertificate { ref reason } if reason.contains("manifest.replay_transcript_digest")),
        "{err:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_manifest_rejects_proof_export_digest_mismatch() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("vc0");
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let dir = temp_artifact_dir("manifest-proof-export-digest-mismatch");
    let artifact_ref = produce_checked_certificate_artifact(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export),
        &dir,
    )
    .expect("checked artifact should persist");
    let mut manifest = CheckedBinaryCertificateManifest::from_artifact_refs(&dir, &[artifact_ref])
        .expect("manifest should build from checked artifact refs");
    manifest.certificates[0].proof_export_sha256 = trust_types::stable_sha256_hex(b"different proof export metadata");

    let err = manifest
        .validate_files(&dir)
        .expect_err("manifest proof export digest mismatch must fail closed");

    assert!(
        matches!(err, CertError::InvalidCertificate { ref reason } if reason.contains("manifest.proof_export_sha256")),
        "{err:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_manifest_rejects_noncanonical_digest_rows() {
    let (dir, mut manifest) = checked_manifest_fixture("manifest-noncanonical-digest");
    manifest.certificates[0].certificate_sha256 =
        manifest.certificates[0].certificate_sha256.to_ascii_uppercase();

    let err = manifest
        .validate_files(&dir)
        .expect_err("noncanonical manifest digest row must fail closed");

    assert!(
        matches!(err, CertError::InvalidCertificate { ref reason } if reason.contains("manifest certificate_sha256") && reason.contains("canonical lowercase sha256")),
        "{err:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_manifest_from_artifact_refs_is_stable_and_rejects_duplicates() {
    let dir = temp_artifact_dir("manifest-artifact-ref-order");
    let checker = checked_certificate_checker();

    let vc_a = br#"{"vc":"main memory safety A"}"#;
    let dispatch_a = proved_dispatch("vc-stable-b");
    let export_a = proof_export(&dispatch_a, vc_a);
    let artifact_ref_a = produce_checked_certificate_artifact(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch_a, vc_a, &export_a),
        &dir,
    )
    .expect("first checked artifact should persist");

    let vc_b = br#"{"vc":"main memory safety B"}"#;
    let dispatch_b = proved_dispatch("vc-stable-a");
    let export_b = proof_export(&dispatch_b, vc_b);
    let artifact_ref_b = produce_checked_certificate_artifact(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch_b, vc_b, &export_b),
        &dir,
    )
    .expect("second checked artifact should persist");

    let manifest_ab = CheckedBinaryCertificateManifest::from_artifact_refs(
        &dir,
        &[artifact_ref_a.clone(), artifact_ref_b.clone()],
    )
    .expect("artifact refs should build a manifest");
    let manifest_ba = CheckedBinaryCertificateManifest::from_artifact_refs(
        &dir,
        &[artifact_ref_b.clone(), artifact_ref_a.clone()],
    )
    .expect("reordered artifact refs should build the same manifest");

    assert_eq!(manifest_ab, manifest_ba);
    let mut expected_digests =
        vec![artifact_ref_a.content_sha256.clone(), artifact_ref_b.content_sha256.clone()];
    expected_digests.sort();
    let manifest_digests = manifest_ab
        .certificates
        .iter()
        .map(|entry| entry.certificate_sha256.clone())
        .collect::<Vec<_>>();
    assert_eq!(manifest_digests, expected_digests);
    manifest_ab
        .validate_files(&dir)
        .expect("manifest from artifact refs should validate against stored artifacts");

    let duplicate_err = CheckedBinaryCertificateManifest::from_artifact_refs(
        &dir,
        &[artifact_ref_a.clone(), artifact_ref_a.clone()],
    )
    .expect_err("duplicate artifact refs must fail closed");
    assert!(
        matches!(duplicate_err, CertError::InvalidCertificate { ref reason } if reason.contains("duplicate checked certificate artifact ref")),
        "{duplicate_err:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_manifest_from_artifact_refs_rejects_paths_outside_root() {
    let manifest_root = temp_artifact_dir("manifest-root");
    let artifact_root = temp_artifact_dir("manifest-outside-root");
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("vc0");
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let artifact_ref = produce_checked_certificate_artifact(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export),
        &artifact_root,
    )
    .expect("checked artifact should persist outside the manifest root");

    let err = CheckedBinaryCertificateManifest::from_artifact_refs(&manifest_root, &[artifact_ref])
        .expect_err("manifest artifact refs must stay under the manifest root");
    assert!(
        matches!(err, CertError::InvalidCertificate { ref reason } if reason.contains("outside manifest root")),
        "{err:?}"
    );

    let _ = std::fs::remove_dir_all(&manifest_root);
    let _ = std::fs::remove_dir_all(&artifact_root);
}

#[test]
fn checked_binary_certificate_manifest_rejects_duplicate_dispatch_or_vc_entries() {
    let (dir, manifest) = checked_manifest_fixture("manifest-duplicates");
    let entry = manifest.certificates[0].clone();

    let mut duplicate_dispatch = CheckedBinaryCertificateManifest::new();
    duplicate_dispatch.add_certificate(entry.clone());
    duplicate_dispatch.add_certificate(entry.clone());
    let dispatch_err = duplicate_dispatch
        .validate_files(&dir)
        .expect_err("duplicate dispatch ids must fail closed");
    assert!(
        matches!(dispatch_err, CertError::InvalidCertificate { ref reason } if reason.contains("duplicate checked certificate manifest dispatch_id")),
        "{dispatch_err:?}"
    );

    let mut duplicate_vc = CheckedBinaryCertificateManifest::new();
    duplicate_vc.add_certificate(entry.clone());
    let mut same_vc_different_dispatch = entry;
    same_vc_different_dispatch.dispatch_id = "vc1".to_string();
    duplicate_vc.add_certificate(same_vc_different_dispatch);
    let vc_err =
        duplicate_vc.validate_files(&dir).expect_err("duplicate VC digests must fail closed");
    assert!(
        matches!(vc_err, CertError::InvalidCertificate { ref reason } if reason.contains("duplicate checked certificate manifest vc_sha256")),
        "{vc_err:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_manifest_rejects_missing_certificate_files() {
    let (dir, mut manifest) = checked_manifest_fixture("manifest-missing-file");
    let missing_digest = trust_types::stable_sha256_hex(b"missing checked certificate");
    manifest.certificates[0].certificate_sha256 = missing_digest.clone();
    manifest.certificates[0].certificate_path =
        std::path::PathBuf::from("checked-binary-certificates")
            .join(&missing_digest[..2])
            .join(format!("{missing_digest}.checked-binary-certificate.json"));

    let err = manifest
        .validate_files(&dir)
        .expect_err("missing checked certificate files must fail closed");
    assert!(
        matches!(err, CertError::InvalidCertificate { ref reason } if reason.contains("missing certificate file")),
        "{err:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_manifest_rejects_non_content_addressed_certificate_paths() {
    let (dir, mut manifest) = checked_manifest_fixture("manifest-path-alias");
    let certificate_sha256 = manifest.certificates[0].certificate_sha256.clone();
    manifest.certificates[0].certificate_path =
        std::path::PathBuf::from("checked-binary-certificates/alias")
            .join(format!("{certificate_sha256}.checked-binary-certificate.json"));

    let err = manifest
        .validate_files(&dir)
        .expect_err("manifest certificate path must be bound to certificate digest");
    assert!(
        matches!(err, CertError::InvalidCertificate { ref reason } if reason.contains("certificate_path must match content-addressed path")),
        "{err:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_manifest_rejects_path_traversal_and_absolute_certificate_paths() {
    let (dir, manifest) = checked_manifest_fixture("manifest-path-escape");

    let mut traversal = manifest.clone();
    traversal.certificates[0].certificate_path =
        std::path::PathBuf::from("checked-binary-certificates/../escaped.checked.json");
    let traversal_err = traversal
        .validate_files(&dir)
        .expect_err("manifest certificate paths must not traverse outside the certificate store");
    assert!(
        matches!(traversal_err, CertError::InvalidCertificate { ref reason } if reason.contains("certificate_path must not escape")),
        "{traversal_err:?}"
    );

    let mut absolute = manifest;
    absolute.certificates[0].certificate_path =
        std::env::temp_dir().join("escaped.checked-binary-certificate.json");
    let absolute_err = absolute
        .validate_files(&dir)
        .expect_err("manifest certificate paths must be relative to the certificate store");
    assert!(
        matches!(absolute_err, CertError::InvalidCertificate { ref reason } if reason.contains("certificate_path must be relative")),
        "{absolute_err:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_manifest_rejects_artifact_digest_mismatches() {
    let (dir, manifest) = checked_manifest_fixture("manifest-digest-mismatch");

    let mut vc_mismatch = manifest.clone();
    vc_mismatch.certificates[0].vc_sha256 = trust_types::stable_sha256_hex(b"different VC digest");
    let vc_err =
        vc_mismatch.validate_files(&dir).expect_err("manifest VC digest mismatch must fail closed");
    assert!(
        matches!(vc_err, CertError::InvalidCertificate { ref reason } if reason.contains("manifest.vc_sha256")),
        "{vc_err:?}"
    );

    let mut certificate_mismatch = manifest;
    certificate_mismatch.certificates[0].certificate_sha256 =
        trust_types::stable_sha256_hex(b"different checked certificate digest");
    let certificate_err = certificate_mismatch
        .validate_files(&dir)
        .expect_err("manifest certificate digest mismatch must fail closed");
    assert!(
        matches!(certificate_err, CertError::InvalidCertificate { ref reason } if reason.contains("manifest.certificate_sha256")),
        "{certificate_err:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_content_addressed_import_rejects_bound_identity_mismatches() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("vc0");
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let dir = temp_artifact_dir("identity-mismatch");
    let artifact_ref = produce_checked_certificate_artifact(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export),
        &dir,
    )
    .expect("production helper should persist checked artifact");

    let mut vc_mismatch = proved_dispatch("vc0");
    let vc_err = import_checked_certificate_artifact_for_dispatch(
        &mut vc_mismatch,
        br#"{"vc":"different VC"}"#,
        &artifact_ref,
    )
    .expect_err("canonical VC digest mismatch should be rejected");
    assert!(
        matches!(vc_err, CertError::InvalidCertificate { ref reason } if reason.contains("VC digest mismatch")),
        "{vc_err:?}"
    );
    assert!(!vc_mismatch.certificate.is_checked());

    let mut origin_mismatch = proved_dispatch("vc0");
    origin_mismatch.origin.as_mut().expect("fixture has origin").instruction_address += 4;
    let origin_err = import_checked_certificate_artifact_for_dispatch(
        &mut origin_mismatch,
        canonical_vc_bytes,
        &artifact_ref,
    )
    .expect_err("origin digest mismatch should be rejected");
    assert!(
        matches!(origin_err, CertError::InvalidCertificate { ref reason } if reason.contains("binary_origin_digest")),
        "{origin_err:?}"
    );
    assert!(!origin_mismatch.certificate.is_checked());

    let mut source_claim_mismatch = proved_dispatch("vc0");
    source_claim_mismatch.origin.as_mut().expect("fixture has origin").source = Some(SourceSpan {
        file: "src/forged.rs".to_string(),
        line_start: 1,
        col_start: 1,
        line_end: 1,
        col_end: 10,
    });
    let source_claim_err = import_checked_certificate_artifact_for_dispatch(
        &mut source_claim_mismatch,
        canonical_vc_bytes,
        &artifact_ref,
    )
    .expect_err("source provenance claim changes must change the binary origin digest");
    assert!(
        matches!(source_claim_err, CertError::InvalidCertificate { ref reason } if reason.contains("binary_origin_digest")),
        "{source_claim_err:?}"
    );
    assert!(!source_claim_mismatch.certificate.is_checked());

    let mut root_digest_mismatch = proved_dispatch("vc0");
    root_digest_mismatch
        .binary_artifact_digest_identity
        .as_mut()
        .expect("fixture has digest identity")
        .root_artifact_digest =
        Some(BinaryArtifactDigest::sha256(trust_types::stable_sha256_hex(b"different root artifact")));
    let root_digest_err = import_checked_certificate_artifact_for_dispatch(
        &mut root_digest_mismatch,
        canonical_vc_bytes,
        &artifact_ref,
    )
    .expect_err("root artifact digest mismatch should be rejected");
    assert!(
        matches!(root_digest_err, CertError::InvalidCertificate { ref reason } if reason.contains("binary_artifact_digest_identity")),
        "{root_digest_err:?}"
    );
    assert!(!root_digest_mismatch.certificate.is_checked());

    let mut selected_image_digest_mismatch = proved_dispatch("vc0");
    selected_image_digest_mismatch
        .binary_artifact_digest_identity
        .as_mut()
        .and_then(|identity| identity.selected_image.as_mut())
        .expect("fixture has selected image")
        .sha256 = trust_types::stable_sha256_hex(b"different selected image");
    let selected_digest_err = import_checked_certificate_artifact_for_dispatch(
        &mut selected_image_digest_mismatch,
        canonical_vc_bytes,
        &artifact_ref,
    )
    .expect_err("selected image digest mismatch should be rejected");
    assert!(
        matches!(selected_digest_err, CertError::InvalidCertificate { ref reason } if reason.contains("binary_artifact_digest_identity")),
        "{selected_digest_err:?}"
    );
    assert!(!selected_image_digest_mismatch.certificate.is_checked());

    let mut selected_image_range_mismatch = proved_dispatch("vc0");
    selected_image_range_mismatch
        .binary_artifact_digest_identity
        .as_mut()
        .and_then(|identity| identity.selected_image.as_mut())
        .expect("fixture has selected image")
        .file_offset = 1;
    let selected_range_err = import_checked_certificate_artifact_for_dispatch(
        &mut selected_image_range_mismatch,
        canonical_vc_bytes,
        &artifact_ref,
    )
    .expect_err("selected image range mismatch should be rejected");
    assert!(
        matches!(selected_range_err, CertError::InvalidCertificate { ref reason } if reason.contains("binary_artifact_digest_identity")),
        "{selected_range_err:?}"
    );
    assert!(!selected_image_range_mismatch.certificate.is_checked());

    let mut missing_digest_identity = proved_dispatch("vc0");
    missing_digest_identity.binary_artifact_digest_identity = None;
    let missing_digest_identity_err = import_checked_certificate_artifact_for_dispatch(
        &mut missing_digest_identity,
        canonical_vc_bytes,
        &artifact_ref,
    )
    .expect_err("missing dispatch artifact digest identity should be rejected");
    assert!(
        matches!(missing_digest_identity_err, CertError::InvalidCertificate { ref reason } if reason.contains("binary artifact digest identity")),
        "{missing_digest_identity_err:?}"
    );
    assert!(!missing_digest_identity.certificate.is_checked());

    let mut replay_mismatch = proved_dispatch("vc0");
    replay_mismatch.replay = ReplayStatus::NotAttempted;
    let replay_err = import_checked_certificate_artifact_for_dispatch(
        &mut replay_mismatch,
        canonical_vc_bytes,
        &artifact_ref,
    )
    .expect_err("replay status mismatch should be rejected");
    assert!(
        matches!(replay_err, CertError::InvalidCertificate { ref reason } if reason.contains("replay")),
        "{replay_err:?}"
    );
    assert!(!replay_mismatch.certificate.is_checked());

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn raw_present_proof_bytes_do_not_import_as_checked_artifacts() {
    let raw_bytes = b"raw solver proof bytes, not a checked artifact";
    let dir = temp_artifact_dir("raw-present");
    std::fs::create_dir_all(&dir).expect("artifact dir should be creatable");
    let content_sha256 = trust_types::stable_sha256_hex(raw_bytes);
    let path = dir.join(format!("{content_sha256}.checked-binary-certificate.json"));
    std::fs::write(&path, raw_bytes).expect("raw proof fixture should be writable");
    let raw_ref = CheckedBinaryCertificateArtifactRef { content_sha256, path };
    let mut dispatch = proved_dispatch("vc0");

    let err = import_checked_certificate_artifact_for_dispatch(
        &mut dispatch,
        br#"{"vc":"main memory safety"}"#,
        &raw_ref,
    )
    .expect_err("raw Present proof bytes must not deserialize as checked artifacts");

    assert!(
        matches!(err, CertError::SerializationFailed { .. } | CertError::InvalidCertificate { .. }),
        "{err:?}"
    );
    assert!(matches!(dispatch.certificate, ProofCertificateStatus::Present { .. }));

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_import_rejects_summary_only_metadata() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let summary_only = serde_json::json!({
        "dispatch_id": "vc0",
        "vc_sha256": trust_types::stable_sha256_hex(canonical_vc_bytes),
        "origin_sha256": digest_binary_origin(&binary_origin()).expect("origin should digest"),
        "proof_sha256": trust_types::stable_sha256_hex(b"normalized lrat proof bytes bound to vc0"),
        "proof_export_sha256": trust_types::stable_sha256_hex(b"normalized solver proof export metadata"),
        "certificate_sha256": trust_types::stable_sha256_hex(b""),
        "format": "lrat",
        "checker": "ay-lrat-binary-check",
        "checker_version": "0.1.0",
        "query_semantics": "SatIsCounterexample",
        "replay": "Replayed",
        "replay_transcript_digest": null,
        "origin": binary_origin(),
        "normalized_payload": [],
        "dependencies": [],
        "assumption_digest": digest_model_assumptions(&[]),
        "assumptions": [],
        "checked_at_unix_ms": 1_777_070_401_000_u64,
        "diagnostics": [],
    });

    let err = CheckedBinaryCertificateArtifact::from_json(&summary_only.to_string())
        .expect_err("summary-only checked metadata must fail closed");

    assert!(matches!(err, CertError::InvalidCertificate { .. }), "{err:?}");
}

#[test]
fn checked_binary_certificate_import_rejects_noncanonical_digest_bindings() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("vc0");
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let check = check_binary_certificate(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export),
    );
    assert!(check.accepted, "{:?}", check.error);
    let artifact = check.certificate.expect("accepted check has certificate");
    let mut json = serde_json::to_value(&artifact).expect("checked artifact should serialize");

    let payload_bytes = json["normalized_payload"]
        .as_array()
        .expect("payload bytes should serialize as an array")
        .iter()
        .map(|byte| byte.as_u64().expect("payload byte should be numeric") as u8)
        .collect::<Vec<_>>();
    let mut payload: serde_json::Value =
        serde_json::from_slice(&payload_bytes).expect("payload metadata should deserialize");
    payload["proof_sha256"] = serde_json::json!("vc0-sha256");
    let payload_bytes =
        serde_json::to_vec(&payload).expect("payload metadata should serialize after tamper");

    json["proof_sha256"] = serde_json::json!("vc0-sha256");
    json["normalized_payload"] =
        serde_json::to_value(&payload_bytes).expect("payload bytes should serialize");
    json["certificate_sha256"] = serde_json::json!(trust_types::stable_sha256_hex(&payload_bytes));

    let err = CheckedBinaryCertificateArtifact::from_json(&json.to_string())
        .expect_err("non-canonical digest strings must fail closed");

    assert!(
        matches!(err, CertError::InvalidCertificate { ref reason } if reason.contains("proof_sha256") && reason.contains("canonical lowercase sha256")),
        "{err:?}"
    );
}

#[test]
fn checked_binary_certificate_import_rejects_noncanonical_normalized_payload_bytes() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("vc0");
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let check = check_binary_certificate(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export),
    );
    assert!(check.accepted, "{:?}", check.error);
    let mut artifact = check.certificate.expect("accepted check has certificate");

    let payload: serde_json::Value = serde_json::from_slice(&artifact.normalized_payload)
        .expect("payload metadata should deserialize");
    let noncanonical_payload = serde_json::to_string_pretty(&payload)
        .expect("payload metadata should pretty serialize")
        .into_bytes();
    assert_ne!(artifact.normalized_payload, noncanonical_payload);

    artifact.normalized_payload = noncanonical_payload;
    artifact.certificate_sha256 = trust_types::stable_sha256_hex(&artifact.normalized_payload);

    let err = artifact
        .validate_integrity()
        .expect_err("noncanonical normalized payload bytes must fail closed");

    assert!(
        matches!(err, CheckError::MalformedProof { ref reason } if reason.contains("normalized payload is not canonical")),
        "{err:?}"
    );
}

#[test]
fn checked_binary_certificate_import_rejects_noncanonical_replay_transcript_digest_payload() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("vc0");
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let replay_transcript_digest = trust_types::stable_sha256_hex(b"deterministic replay transcript for vc0");
    let mut request =
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export);
    request.replay_transcript_digest = Some(&replay_transcript_digest);
    let check = check_binary_certificate(&checker, request);
    assert!(check.accepted, "{:?}", check.error);
    let mut artifact = check.certificate.expect("accepted check has certificate");

    let payload = String::from_utf8(artifact.normalized_payload.clone())
        .expect("normalized payload should be UTF-8 JSON");
    let tampered_payload = payload.replace(&replay_transcript_digest, "not-a-canonical-sha256");
    assert_ne!(payload, tampered_payload);
    artifact.normalized_payload = tampered_payload.into_bytes();
    artifact.certificate_sha256 = trust_types::stable_sha256_hex(&artifact.normalized_payload);

    let err = artifact
        .validate_integrity()
        .expect_err("noncanonical replay transcript digest must fail closed");

    assert!(
        matches!(err, CheckError::MalformedProof { ref reason } if reason.contains("replay_transcript_digest") && reason.contains("canonical lowercase sha256")),
        "{err:?}"
    );
}

#[test]
fn checked_binary_certificate_import_rejects_tampered_persisted_bindings() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let mut dispatch = proved_dispatch("vc0");
    dispatch.assumptions = vec![ModelAssumption {
        stage: "lift".to_string(),
        description: "stack pointer is canonical".to_string(),
    }];
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let check = check_binary_certificate(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export),
    );
    assert!(check.accepted, "{:?}", check.error);
    let artifact = check.certificate.expect("accepted check has certificate");

    let mut replay_tampered = artifact.clone();
    replay_tampered.replay = ReplayStatus::NotAttempted;
    let replay_err = replay_tampered
        .validate_for_dispatch(&dispatch, canonical_vc_bytes)
        .expect_err("tampered replay status should fail");
    assert!(
        matches!(replay_err, CheckError::ArtifactBindingMismatch { ref field, .. } if field == "replay"),
        "{replay_err:?}"
    );

    let mut origin_tampered = artifact.clone();
    origin_tampered.origin.instruction_address += 4;
    let origin_err = origin_tampered
        .validate_for_dispatch(&dispatch, canonical_vc_bytes)
        .expect_err("tampered binary origin should fail");
    assert!(
        matches!(origin_err, CheckError::ArtifactBindingMismatch { ref field, .. } if field == "origin_sha256"),
        "{origin_err:?}"
    );

    let mut origin_digest_tampered = artifact.clone();
    origin_digest_tampered.origin_sha256 = trust_types::stable_sha256_hex(b"different binary origin");
    let origin_digest_err = origin_digest_tampered
        .validate_for_dispatch(&dispatch, canonical_vc_bytes)
        .expect_err("tampered binary origin digest should fail");
    assert!(
        matches!(origin_digest_err, CheckError::ArtifactBindingMismatch { ref field, .. } if field == "origin_sha256"),
        "{origin_digest_err:?}"
    );

    let mut artifact_digest_tampered = artifact.clone();
    artifact_digest_tampered.binary_artifact_digest_identity.root_artifact_digest =
        Some(BinaryArtifactDigest::sha256(trust_types::stable_sha256_hex(b"different root artifact")));
    let artifact_digest_err = artifact_digest_tampered
        .validate_for_dispatch(&dispatch, canonical_vc_bytes)
        .expect_err("tampered binary artifact digest identity should fail");
    assert!(
        matches!(artifact_digest_err, CheckError::ArtifactBindingMismatch { ref field, .. } if field == "binary_artifact_digest_identity"),
        "{artifact_digest_err:?}"
    );

    let mut selected_image_tampered = artifact.clone();
    selected_image_tampered
        .binary_artifact_digest_identity
        .selected_image
        .as_mut()
        .expect("fixture has selected image")
        .file_size = 3;
    let selected_image_err = selected_image_tampered
        .validate_for_dispatch(&dispatch, canonical_vc_bytes)
        .expect_err("tampered selected image range should fail");
    assert!(
        matches!(selected_image_err, CheckError::ArtifactBindingMismatch { ref field, .. } if field == "binary_artifact_digest_identity"),
        "{selected_image_err:?}"
    );

    let mut checker_version_tampered = artifact.clone();
    checker_version_tampered.checker_version = "attacker-checker".to_string();
    let checker_version_err = checker_version_tampered
        .validate_for_dispatch(&dispatch, canonical_vc_bytes)
        .expect_err("tampered checker metadata should fail");
    assert!(
        matches!(checker_version_err, CheckError::ArtifactBindingMismatch { ref field, .. } if field == "checker_version"),
        "{checker_version_err:?}"
    );

    let mut assumptions_tampered = artifact.clone();
    assumptions_tampered.assumptions[0].description =
        "stack pointer is attacker-controlled".to_string();
    let assumption_err = assumptions_tampered
        .validate_for_dispatch(&dispatch, canonical_vc_bytes)
        .expect_err("tampered assumptions should fail");
    assert!(matches!(assumption_err, CheckError::AssumptionDigestMismatch { .. }));

    let mut proof_tampered = artifact.clone();
    proof_tampered.proof_sha256 = trust_types::stable_sha256_hex(b"different proof payload");
    let proof_err = proof_tampered
        .validate_for_dispatch(&dispatch, canonical_vc_bytes)
        .expect_err("tampered proof payload digest should fail");
    assert!(
        matches!(proof_err, CheckError::ArtifactBindingMismatch { ref field, .. } if field == "proof_sha256"),
        "{proof_err:?}"
    );

    let mut checker_tampered = artifact;
    checker_tampered.checker_version = "0.2.0".to_string();
    let checker_err = checker_tampered
        .validate_for_dispatch(&dispatch, canonical_vc_bytes)
        .expect_err("tampered checker metadata should fail");
    assert!(
        matches!(checker_err, CheckError::ArtifactBindingMismatch { ref field, .. } if field == "checker_version"),
        "{checker_err:?}"
    );
}

#[test]
fn checked_binary_certificate_content_addressed_load_rejects_wrong_digest() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("vc0");
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let check = check_binary_certificate(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export),
    );
    assert!(check.accepted, "{:?}", check.error);
    let artifact = check.certificate.expect("accepted check has certificate");

    let root = unique_temp_dir("checked-binary-certificate-digest-mismatch");
    persist_checked_certificate_artifact(&root, &artifact)
        .expect("checked artifact should persist content-addressed");
    let err =
        load_content_addressed_checked_certificate_artifact(&root, &trust_types::stable_sha256_hex(b"wrong digest"))
            .expect_err("wrong content address should fail");

    assert!(matches!(err, CertError::IoError { .. }), "{err:?}");

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn checked_binary_certificate_artifact_ref_rejects_non_content_addressed_alias_paths() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("vc0");
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let dir = temp_artifact_dir("artifact-ref-path-alias");
    let artifact_ref = produce_checked_certificate_artifact(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export),
        &dir,
    )
    .expect("production helper should persist checked artifact");

    let alias_dir = dir.join("alias");
    std::fs::create_dir_all(&alias_dir).expect("alias dir should be creatable");
    let alias_path =
        alias_dir.join(format!("{}.checked-binary-certificate.json", artifact_ref.content_sha256));
    std::fs::copy(&artifact_ref.path, &alias_path)
        .expect("checked artifact should be copyable into alias path");
    let alias_ref = CheckedBinaryCertificateArtifactRef {
        content_sha256: artifact_ref.content_sha256,
        path: alias_path,
    };

    let err = load_checked_certificate_artifact_ref(&alias_ref)
        .expect_err("artifact refs must use deterministic content-addressed paths");
    assert!(
        matches!(err, CertError::InvalidCertificate { ref reason } if reason.contains("content-addressed artifact path") && reason.contains("must end with")),
        "{err:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn checked_binary_certificate_rejects_vc_identity_mismatch() {
    let dispatch = proved_dispatch("vc0");
    let export = proof_export(&dispatch, br#"{"vc":"main memory safety"}"#);
    let checker = checked_certificate_checker();
    let request =
        BinaryCertificateCheckRequest::from_export(&dispatch, br#"{"vc":"different VC"}"#, &export);

    let check = check_binary_certificate(&checker, request);

    assert!(!check.accepted);
    assert!(check.certificate.is_none());
    assert!(matches!(check.error, Some(CheckError::VcDigestMismatch { .. })));
}

#[test]
fn checked_binary_certificate_rejects_dispatch_identity_mismatch() {
    let dispatch = proved_dispatch("vc0");
    let mut export = proof_export(&dispatch, br#"{"vc":"main memory safety"}"#);
    export.dispatch_id = "vc-from-another-binary".to_string();
    let checker = checked_certificate_checker();
    let request = BinaryCertificateCheckRequest::from_export(
        &dispatch,
        br#"{"vc":"main memory safety"}"#,
        &export,
    );

    let check = check_binary_certificate(&checker, request);

    assert!(!check.accepted);
    assert!(check.certificate.is_none());
    assert!(matches!(check.error, Some(CheckError::CheckerInternalError { .. })));
}

#[test]
fn checked_binary_certificate_rejects_solver_identity_mismatch() {
    let dispatch = proved_dispatch("vc0");
    let mut export = proof_export(&dispatch, br#"{"vc":"main memory safety"}"#);
    export.solver = "different-solver".to_string();
    let checker = checked_certificate_checker();
    let request = BinaryCertificateCheckRequest::from_export(
        &dispatch,
        br#"{"vc":"main memory safety"}"#,
        &export,
    );

    let check = check_binary_certificate(&checker, request);

    assert!(!check.accepted);
    assert!(check.certificate.is_none());
    assert!(
        matches!(check.error, Some(CheckError::ArtifactBindingMismatch { ref field, .. }) if field == "solver"),
        "{:?}",
        check.error
    );
}

#[test]
fn checked_binary_certificate_rejects_backend_identity_mismatch() {
    let dispatch = proved_dispatch("vc0");
    let mut export = proof_export(&dispatch, br#"{"vc":"main memory safety"}"#);
    export.backend = Some("different-backend".to_string());
    let checker = checked_certificate_checker();
    let request = BinaryCertificateCheckRequest::from_export(
        &dispatch,
        br#"{"vc":"main memory safety"}"#,
        &export,
    );

    let check = check_binary_certificate(&checker, request);

    assert!(!check.accepted);
    assert!(check.certificate.is_none());
    assert!(
        matches!(check.error, Some(CheckError::ArtifactBindingMismatch { ref field, .. }) if field == "backend"),
        "{:?}",
        check.error
    );
}

#[test]
fn checked_binary_certificate_rejects_assumption_identity_mismatch() {
    let mut dispatch = proved_dispatch("vc0");
    dispatch.assumptions = vec![ModelAssumption {
        stage: "lift".to_string(),
        description: "stack pointer is canonical".to_string(),
    }];
    let export = proof_export(&dispatch, br#"{"vc":"main memory safety"}"#);
    dispatch.assumptions[0].description = "stack pointer is attacker-controlled".to_string();
    let checker = checked_certificate_checker();
    let request = BinaryCertificateCheckRequest::from_export(
        &dispatch,
        br#"{"vc":"main memory safety"}"#,
        &export,
    );

    let check = check_binary_certificate(&checker, request);

    assert!(!check.accepted);
    assert!(check.certificate.is_none());
    assert!(matches!(check.error, Some(CheckError::AssumptionDigestMismatch { .. })));
}

#[test]
fn checked_binary_certificate_rejects_tampered_proof_payload() {
    let dispatch = proved_dispatch("vc0");
    let mut export = proof_export(&dispatch, br#"{"vc":"main memory safety"}"#);
    export.proof_bytes.extend_from_slice(b" after export");
    let checker = checked_certificate_checker();
    let request = BinaryCertificateCheckRequest::from_export(
        &dispatch,
        br#"{"vc":"main memory safety"}"#,
        &export,
    );

    let check = check_binary_certificate(&checker, request);

    assert!(!check.accepted);
    assert!(check.certificate.is_none());
    assert!(matches!(check.error, Some(CheckError::MalformedProof { .. })));
}

#[test]
fn raw_solver_bytes_are_audit_only_and_do_not_create_checked_gate_coverage() {
    let raw_bytes = b"raw solver proof bytes";
    let audit_only = AuditOnlyRawSolverProofBytes::new("ay", Some("lrat".to_string()), raw_bytes);
    let check = BinaryCertificateCheckResult::raw_solver_bytes_are_audit_only("vc0", &audit_only);

    assert!(!check.accepted);
    assert!(matches!(check.error, Some(CheckError::RawSolverBytesAuditOnly { .. })));

    let dispatch = SolverDispatchRecord {
        id: "vc0".to_string(),
        function: Some("sym.main".to_string()),
        solver: "ay".to_string(),
        status: SolverDispatchStatus::Unsat,
        query_semantics: SolverQuerySemantics::SatIsCounterexample,
        replay: ReplayStatus::Replayed,
        result: Some(VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 1,
            strength: trust_types::ProofStrength::smt_unsat(),
            proof_certificate: Some(raw_bytes.to_vec()),
            solver_warnings: None,
            native_proof_envelope: None,
        }),
        certificate: ProofCertificateStatus::Present {
            format: "lrat".to_string(),
            sha256: Some(audit_only.bytes_sha256),
            artifact_path: None,
        },
        ..Default::default()
    };

    let summary = proof_grade_summary(&[dispatch]);
    let decision = summary.proof_grade_release_gate();

    assert_eq!(summary.certificate_checks.checked_certificates, 0);
    assert_eq!(summary.certificate_checks.raw_solver_proof_bytes, 1);
    assert!(decision.rejected());
    assert!(decision.rejections.iter().any(|reason| {
        matches!(reason, BinaryReleaseGateRejection::MissingProofCertificates { .. })
    }));
    assert!(decision.rejections.iter().any(|reason| {
        matches!(reason, BinaryReleaseGateRejection::RawSolverProofBytesPresent { count: 1 })
    }));
}

#[test]
fn raw_present_solver_proof_bytes_do_not_upgrade_to_checked_on_import() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("vc0");
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let check = check_binary_certificate(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export),
    );
    assert!(check.accepted, "{:?}", check.error);
    let artifact = check.certificate.expect("accepted check has certificate");

    let raw_bytes = b"raw solver proof bytes";
    let mut raw_dispatch = proved_dispatch("vc0");
    raw_dispatch.result = Some(VerificationResult::Proved {
        solver: "ay".into(),
        time_ms: 1,
        strength: trust_types::ProofStrength::smt_unsat(),
        proof_certificate: Some(raw_bytes.to_vec()),
        solver_warnings: None,
        native_proof_envelope: None,
    });
    raw_dispatch.certificate = ProofCertificateStatus::Present {
        format: "lrat".to_string(),
        sha256: Some(trust_types::stable_sha256_hex(raw_bytes)),
        artifact_path: None,
    };

    let err =
        import_checked_certificate_for_dispatch(&mut raw_dispatch, canonical_vc_bytes, &artifact)
            .expect_err("raw Present proof bytes must stay audit-only");

    assert!(matches!(err, CheckError::RawSolverBytesCannotUpgradeToChecked { .. }), "{err:?}");
    assert!(!raw_dispatch.certificate.is_checked());
}

#[test]
fn checked_binary_certificate_import_can_match_by_canonical_vc_and_origin_digest() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let previous_dispatch = proved_dispatch("previous-run:vc0");
    let export = proof_export(&previous_dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let check = check_binary_certificate(
        &checker,
        BinaryCertificateCheckRequest::from_export(&previous_dispatch, canonical_vc_bytes, &export),
    );
    assert!(check.accepted, "{:?}", check.error);
    let artifact = check.certificate.expect("accepted check has certificate");

    let mut current_dispatch = proved_dispatch("current-run:vc0");
    import_checked_certificate_for_dispatch_by_canonical_digests(
        &mut current_dispatch,
        canonical_vc_bytes,
        &artifact,
    )
    .expect("same VC and binary origin digests should import across dispatch ids");

    assert!(current_dispatch.certificate.is_checked());
    assert_ne!(artifact.dispatch_id, current_dispatch.id);
}

#[test]
fn canonical_digest_import_rejects_replay_status_mismatch() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let previous_dispatch = proved_dispatch("previous-run:vc0");
    let export = proof_export(&previous_dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let check = check_binary_certificate(
        &checker,
        BinaryCertificateCheckRequest::from_export(&previous_dispatch, canonical_vc_bytes, &export),
    );
    assert!(check.accepted, "{:?}", check.error);
    let artifact = check.certificate.expect("accepted check has certificate");

    let mut current_dispatch = proved_dispatch("current-run:vc0");
    current_dispatch.replay = ReplayStatus::NotAttempted;

    let err = import_checked_certificate_for_dispatch_by_canonical_digests(
        &mut current_dispatch,
        canonical_vc_bytes,
        &artifact,
    )
    .expect_err("canonical import must reject replay status mismatch");

    assert!(
        matches!(err, CheckError::ArtifactBindingMismatch { ref field, .. } if field == "replay"),
        "{err:?}"
    );
    assert!(!current_dispatch.certificate.is_checked());
}

#[test]
fn canonical_digest_import_still_rejects_raw_solver_bytes() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let previous_dispatch = proved_dispatch("previous-run:vc0");
    let export = proof_export(&previous_dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let check = check_binary_certificate(
        &checker,
        BinaryCertificateCheckRequest::from_export(&previous_dispatch, canonical_vc_bytes, &export),
    );
    assert!(check.accepted, "{:?}", check.error);
    let artifact = check.certificate.expect("accepted check has certificate");

    let raw_bytes = b"raw solver proof bytes";
    let mut raw_dispatch = proved_dispatch("current-run:vc0");
    raw_dispatch.result = Some(VerificationResult::Proved {
        solver: "ay".into(),
        time_ms: 1,
        strength: trust_types::ProofStrength::smt_unsat(),
        proof_certificate: Some(raw_bytes.to_vec()),
        solver_warnings: None,
        native_proof_envelope: None,
    });

    let err = import_checked_certificate_for_dispatch_by_canonical_digests(
        &mut raw_dispatch,
        canonical_vc_bytes,
        &artifact,
    )
    .expect_err("raw proof bytes cannot be upgraded even with matching persisted artifact");

    assert!(matches!(err, CheckError::RawSolverBytesCannotUpgradeToChecked { .. }), "{err:?}");
    assert!(!raw_dispatch.certificate.is_checked());
}

#[test]
fn proof_grade_production_manifest_accepts_real_manifest_row_readback_bindings() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, replay_transcript_digest) =
        checked_manifest_acceptance_fixture("production-manifest-real-row-positive");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let source_gate = complete_source_backpropagation_gate();
    let acceptance_request = production_acceptance_request(entry, &export)
        .with_source_backpropagation_gate(source_gate.clone())
        .expect("source-backprop gate should bind to accepted row");
    let acceptance = accept_checked_certificate_manifest_entry(
        &dir,
        canonical_vc_bytes,
        entry,
        &acceptance_request,
    )
    .expect("real manifest row should accept before production manifest export");
    let audit_export =
        CheckedBinaryCertificateAuditExport::from_manifest_acceptance(entry, &acceptance)
            .expect("accepted manifest row should produce readback audit export");
    persist_checked_certificate_audit_export_bundle(
        &dir,
        &manifest,
        std::slice::from_ref(&audit_export),
    )
    .expect("accepted row bundle should persist for readback");
    let validation = load_checked_certificate_audit_export_bundle_rows(&dir)
        .expect("readback rows should validate");
    let accepted_rows = validation.accepted_rows().collect::<Vec<_>>();
    assert_eq!(accepted_rows.len(), 1);
    let accepted_row = accepted_rows[0];

    let production_manifest =
        CheckedBinaryCertificateProductionManifest::from_manifest_acceptance_records(
            1,
            &[CheckedBinaryCertificateProductionManifestAcceptedRowInput {
                manifest_entry: &accepted_row.manifest_entry,
                acceptance_record: &accepted_row.acceptance_record,
            }],
        )
        .expect("accepted readback row should build a production manifest");
    let decision = production_manifest.evaluate();
    assert!(decision.accepted, "{:?}", decision.rejections);
    assert!(production_manifest.require_manifest_row_acceptance);

    let production_entry = production_manifest.entries.first().expect("one production row");
    let row_acceptance = production_entry
        .manifest_row_acceptance
        .as_ref()
        .expect("real production row should carry manifest-row acceptance");
    assert_eq!(row_acceptance.vc_sha256, trust_types::stable_sha256_hex(canonical_vc_bytes));
    assert_eq!(row_acceptance.certificate_sha256, entry.certificate_sha256);
    assert_eq!(
        row_acceptance.proof_metadata_sha256,
        export.normalized_metadata_sha256().expect("proof metadata should digest")
    );
    assert_eq!(row_acceptance.replay, ReplayStatus::Replayed);
    assert_eq!(
        row_acceptance.replay_transcript_digest.as_deref(),
        Some(replay_transcript_digest.as_str())
    );
    assert_eq!(row_acceptance.binary_artifact_digest_identity, binary_artifact_digest_identity());
    let expected_source_gate_sha256 =
        trust_types::stable_sha256_hex(&serde_json::to_vec(&source_gate).expect("source gate should serialize"));
    assert_eq!(row_acceptance.source_backpropagation_gate_sha256, expected_source_gate_sha256);
    let source_gate_row = row_acceptance
        .source_backpropagation_gate_row
        .as_ref()
        .expect("real production row should carry schema-versioned source gate row");
    assert_eq!(
        source_gate_row.schema_version,
        "checked-binary-certificate-source-backpropagation-gate-row.v1"
    );
    assert_eq!(source_gate_row.manifest_identity_sha256, row_acceptance.manifest_identity_sha256);
    assert_eq!(source_gate_row.source_backpropagation_gate_sha256, expected_source_gate_sha256);
    assert_eq!(source_gate_row.vc_sha256, row_acceptance.vc_sha256);
    assert_eq!(source_gate_row.certificate_sha256, row_acceptance.certificate_sha256);
    assert_eq!(source_gate_row.origin_sha256, entry.origin_sha256);
    assert_eq!(source_gate_row.assumption_digest, entry.assumption_digest);
    assert_eq!(source_gate_row.replay, ReplayStatus::Replayed);
    assert_eq!(
        source_gate_row.replay_transcript_digest.as_deref(),
        Some(replay_transcript_digest.as_str())
    );
    assert_eq!(
        Some(&source_gate_row.selected_image_identity),
        binary_artifact_digest_identity().selected_image.as_ref()
    );
    assert_eq!(source_gate_row.source_backpropagation_gate, source_gate);
    let expected_checker_evidence_sha256 = acceptance
        .record
        .production_checker_evidence
        .as_ref()
        .expect("accepted row should carry external checker evidence")
        .sha256()
        .expect("production checker evidence should digest");
    assert_eq!(row_acceptance.production_checker_evidence_sha256, expected_checker_evidence_sha256);
    assert_eq!(
        production_entry
            .production_evidence
            .as_ref()
            .expect("accepted row should carry production evidence")
            .production_checker_evidence_sha256
            .as_deref(),
        Some(expected_checker_evidence_sha256.as_str())
    );
    assert_eq!(
        row_acceptance.manifest_identity_sha256,
        accepted_row.bundle_entry.manifest_identity_sha256
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn proof_grade_production_manifest_requires_complete_runner_contract_bindings() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("production-manifest-complete-runner-contract");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let source_gate = complete_source_backpropagation_gate();
    let acceptance_request = production_acceptance_request(entry, &export)
        .with_source_backpropagation_gate(source_gate)
        .expect("source-backprop gate should bind to accepted row");
    let acceptance = accept_checked_certificate_manifest_entry(
        &dir,
        canonical_vc_bytes,
        entry,
        &acceptance_request,
    )
    .expect("real manifest row should accept before production manifest export");
    let production_manifest =
        CheckedBinaryCertificateProductionManifest::from_manifest_acceptance_records(
            1,
            &[CheckedBinaryCertificateProductionManifestAcceptedRowInput {
                manifest_entry: entry,
                acceptance_record: &acceptance.record,
            }],
        )
        .expect("accepted row should build a production manifest");
    assert!(production_manifest.evaluate().accepted);

    assert_production_manifest_rejects_after(
        &production_manifest,
        |manifest| {
            manifest.entries[0]
                .production_evidence
                .as_mut()
                .expect("production evidence should exist")
                .production_checker_evidence_sha256 = None;
        },
        |rejection| {
            matches!(
                rejection,
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    field,
                    ..
                } if field == "production_evidence.production_checker_evidence_sha256"
            )
        },
    );

    assert_production_manifest_rejects_after(
        &production_manifest,
        |manifest| {
            manifest.entries[0].manifest_row_acceptance = None;
        },
        |rejection| {
            matches!(
                rejection,
                CheckedBinaryCertificateProductionManifestRejection::MissingManifestRowAcceptance {
                    dispatch_id
                } if dispatch_id == &entry.dispatch_id
            )
        },
    );

    assert_production_manifest_rejects_after(
        &production_manifest,
        |manifest| {
            manifest.entries[0]
                .manifest_row_acceptance
                .as_mut()
                .expect("row acceptance should exist")
                .source_backpropagation_gate_row = None;
        },
        |rejection| {
            matches!(
                rejection,
                CheckedBinaryCertificateProductionManifestRejection::MissingSourceBackpropagationGateRow {
                    dispatch_id
                } if dispatch_id == &entry.dispatch_id
            )
        },
    );

    assert_production_manifest_rejects_after(
        &production_manifest,
        |manifest| {
            manifest.entries[0]
                .manifest_row_acceptance
                .as_mut()
                .expect("row acceptance should exist")
                .production_checker_evidence_sha256 =
                trust_types::stable_sha256_hex(b"stale external checker evidence digest");
        },
        |rejection| {
            matches!(
                rejection,
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    field,
                    ..
                } if field == "manifest_row_acceptance.production_checker_evidence_sha256"
            )
        },
    );

    assert_production_manifest_rejects_after(
        &production_manifest,
        |manifest| {
            manifest.entries[0]
                .manifest_row_acceptance
                .as_mut()
                .expect("row acceptance should exist")
                .vc_sha256 = trust_types::stable_sha256_hex(b"stale VC identity");
        },
        |rejection| {
            matches!(
                rejection,
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    field,
                    ..
                } if field == "manifest_row_acceptance.vc_sha256"
            )
        },
    );

    assert_production_manifest_rejects_after(
        &production_manifest,
        |manifest| {
            manifest.entries[0]
                .manifest_row_acceptance
                .as_mut()
                .expect("row acceptance should exist")
                .binary_artifact_digest_identity
                .root_artifact_digest = None;
        },
        |rejection| {
            matches!(
                rejection,
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    field,
                    ..
                } if field == "manifest_row_acceptance.binary_artifact_digest_identity"
            )
        },
    );

    assert_production_manifest_rejects_after(
        &production_manifest,
        |manifest| {
            manifest.entries[0]
                .manifest_row_acceptance
                .as_mut()
                .expect("row acceptance should exist")
                .replay_transcript_digest = None;
        },
        |rejection| {
            matches!(
                rejection,
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    field,
                    ..
                } if field == "manifest_row_acceptance.replay_transcript_digest"
            )
        },
    );

    assert_production_manifest_rejects_after(
        &production_manifest,
        |manifest| {
            manifest.entries[0]
                .manifest_row_acceptance
                .as_mut()
                .expect("row acceptance should exist")
                .source_backpropagation_gate_sha256 = trust_types::stable_sha256_hex(b"stale source gate identity");
        },
        |rejection| {
            matches!(
                rejection,
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    field,
                    ..
                } if field == "manifest_row_acceptance.source_backpropagation_gate_sha256"
            )
        },
    );

    assert_production_manifest_rejects_after(
        &production_manifest,
        |manifest| {
            manifest.entries[0]
                .manifest_row_acceptance
                .as_mut()
                .expect("row acceptance should exist")
                .proof_metadata_sha256 = trust_types::stable_sha256_hex(b"stale proof metadata digest");
        },
        |rejection| {
            matches!(
                rejection,
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    field,
                    ..
                } if field == "manifest_row_acceptance.proof_metadata_sha256"
            )
        },
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn proof_grade_production_manifest_rejects_each_stale_manifest_row_binding_independently() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("production-manifest-stale-row-binding-matrix");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let source_gate = complete_source_backpropagation_gate();
    let acceptance_request = production_acceptance_request(entry, &export)
        .with_source_backpropagation_gate(source_gate)
        .expect("source-backprop gate should bind to accepted row");
    let acceptance = accept_checked_certificate_manifest_entry(
        &dir,
        canonical_vc_bytes,
        entry,
        &acceptance_request,
    )
    .expect("real manifest row should accept before production manifest export");
    let production_manifest =
        CheckedBinaryCertificateProductionManifest::from_manifest_acceptance_records(
            1,
            &[CheckedBinaryCertificateProductionManifestAcceptedRowInput {
                manifest_entry: entry,
                acceptance_record: &acceptance.record,
            }],
        )
        .expect("accepted row should build a production manifest");
    assert!(production_manifest.evaluate().accepted);

    let stale_cases: [(&str, &str, fn(&mut CheckedBinaryCertificateProductionManifest)); 6] = [
        (
            "checker evidence digest",
            "manifest_row_acceptance.production_checker_evidence_sha256",
            |manifest| {
                manifest.entries[0]
                    .manifest_row_acceptance
                    .as_mut()
                    .expect("row acceptance should exist")
                    .production_checker_evidence_sha256 =
                    trust_types::stable_sha256_hex(b"stale external checker evidence digest");
            },
        ),
        ("VC identity", "manifest_row_acceptance.vc_sha256", |manifest| {
            manifest.entries[0]
                .manifest_row_acceptance
                .as_mut()
                .expect("row acceptance should exist")
                .vc_sha256 = trust_types::stable_sha256_hex(b"stale VC identity");
        }),
        ("binary digest", "manifest_row_acceptance.binary_artifact_digest_identity", |manifest| {
            manifest.entries[0]
                .manifest_row_acceptance
                .as_mut()
                .expect("row acceptance should exist")
                .binary_artifact_digest_identity
                .root_artifact_digest =
                Some(BinaryArtifactDigest::sha256(trust_types::stable_sha256_hex(b"stale root artifact digest")));
        }),
        ("replay digest", "manifest_row_acceptance.replay_transcript_digest", |manifest| {
            manifest.entries[0]
                .manifest_row_acceptance
                .as_mut()
                .expect("row acceptance should exist")
                .replay_transcript_digest = Some(trust_types::stable_sha256_hex(b"stale replay transcript digest"));
        }),
        (
            "source gate identity",
            "manifest_row_acceptance.source_backpropagation_gate_sha256",
            |manifest| {
                manifest.entries[0]
                    .manifest_row_acceptance
                    .as_mut()
                    .expect("row acceptance should exist")
                    .source_backpropagation_gate_sha256 = trust_types::stable_sha256_hex(b"stale source gate identity");
            },
        ),
        ("proof metadata digest", "manifest_row_acceptance.proof_metadata_sha256", |manifest| {
            manifest.entries[0]
                .manifest_row_acceptance
                .as_mut()
                .expect("row acceptance should exist")
                .proof_metadata_sha256 = trust_types::stable_sha256_hex(b"stale proof metadata digest");
        }),
    ];

    for (case, expected_field, mutate) in stale_cases {
        let mut stale_manifest = production_manifest.clone();
        mutate(&mut stale_manifest);

        let decision = stale_manifest.evaluate();

        assert!(!decision.accepted, "{case}: {:?}", decision.rejections);
        assert!(
            matches!(
                &decision.rejections[0],
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    field,
                    ..
                } if field == expected_field
            ),
            "{case}: {:?}",
            decision.rejections
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn proof_grade_production_manifest_rejects_missing_stale_or_wrong_source_gate_rows() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("production-manifest-source-gate-row-negative");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let acceptance_request = production_acceptance_request(entry, &export)
        .with_source_backpropagation_gate(complete_source_backpropagation_gate())
        .expect("source-backprop gate should bind to accepted row");
    let acceptance = accept_checked_certificate_manifest_entry(
        &dir,
        canonical_vc_bytes,
        entry,
        &acceptance_request,
    )
    .expect("real manifest row should accept before source gate row checks");
    let production_manifest =
        CheckedBinaryCertificateProductionManifest::from_manifest_acceptance_records(
            1,
            &[CheckedBinaryCertificateProductionManifestAcceptedRowInput {
                manifest_entry: entry,
                acceptance_record: &acceptance.record,
            }],
        )
        .expect("accepted row should build a production manifest");
    assert!(production_manifest.evaluate().accepted);

    let mut missing_row = production_manifest.clone();
    missing_row.entries[0]
        .manifest_row_acceptance
        .as_mut()
        .expect("row acceptance should exist")
        .source_backpropagation_gate_row = None;
    let missing_decision = missing_row.evaluate();
    assert!(!missing_decision.accepted);
    assert!(
        missing_decision.rejections.iter().any(|rejection| matches!(
            rejection,
            CheckedBinaryCertificateProductionManifestRejection::MissingSourceBackpropagationGateRow {
                dispatch_id
            } if dispatch_id == &entry.dispatch_id
        )),
        "{:?}",
        missing_decision.rejections
    );

    let mut stale_gate = production_manifest.clone();
    stale_gate.entries[0]
        .manifest_row_acceptance
        .as_mut()
        .expect("row acceptance should exist")
        .source_backpropagation_gate_row
        .as_mut()
        .expect("source gate row should exist")
        .source_backpropagation_gate =
        complete_source_backpropagation_gate_for("stale production source gate row");
    assert_production_manifest_rejects_field(
        &stale_gate,
        "manifest_row_acceptance.source_backpropagation_gate_row.source_backpropagation_gate_sha256",
    );

    let wrong_identity_cases: [(&str, &str, fn(&mut CheckedBinaryCertificateProductionManifest));
        9] = [
        (
            "schema version",
            "manifest_row_acceptance.source_backpropagation_gate_row.schema_version",
            |manifest| {
                manifest.entries[0]
                    .manifest_row_acceptance
                    .as_mut()
                    .expect("row acceptance should exist")
                    .source_backpropagation_gate_row
                    .as_mut()
                    .expect("source gate row should exist")
                    .schema_version =
                    "checked-binary-certificate-source-backpropagation-gate-row.v0".to_string();
            },
        ),
        (
            "manifest identity",
            "manifest_row_acceptance.source_backpropagation_gate_row.manifest_identity_sha256",
            |manifest| {
                manifest.entries[0]
                    .manifest_row_acceptance
                    .as_mut()
                    .expect("row acceptance should exist")
                    .source_backpropagation_gate_row
                    .as_mut()
                    .expect("source gate row should exist")
                    .manifest_identity_sha256 = trust_types::stable_sha256_hex(b"wrong manifest identity");
            },
        ),
        (
            "certificate identity",
            "manifest_row_acceptance.source_backpropagation_gate_row.certificate_sha256",
            |manifest| {
                manifest.entries[0]
                    .manifest_row_acceptance
                    .as_mut()
                    .expect("row acceptance should exist")
                    .source_backpropagation_gate_row
                    .as_mut()
                    .expect("source gate row should exist")
                    .certificate_sha256 = trust_types::stable_sha256_hex(b"wrong checked certificate");
            },
        ),
        (
            "VC identity",
            "manifest_row_acceptance.source_backpropagation_gate_row.vc_sha256",
            |manifest| {
                manifest.entries[0]
                    .manifest_row_acceptance
                    .as_mut()
                    .expect("row acceptance should exist")
                    .source_backpropagation_gate_row
                    .as_mut()
                    .expect("source gate row should exist")
                    .vc_sha256 = trust_types::stable_sha256_hex(b"wrong VC digest");
            },
        ),
        (
            "binary origin",
            "manifest_row_acceptance.source_backpropagation_gate_row.origin_sha256",
            |manifest| {
                manifest.entries[0]
                    .manifest_row_acceptance
                    .as_mut()
                    .expect("row acceptance should exist")
                    .source_backpropagation_gate_row
                    .as_mut()
                    .expect("source gate row should exist")
                    .origin_sha256 = trust_types::stable_sha256_hex(b"wrong binary origin digest");
            },
        ),
        (
            "assumptions",
            "manifest_row_acceptance.source_backpropagation_gate_row.assumption_digest",
            |manifest| {
                manifest.entries[0]
                    .manifest_row_acceptance
                    .as_mut()
                    .expect("row acceptance should exist")
                    .source_backpropagation_gate_row
                    .as_mut()
                    .expect("source gate row should exist")
                    .assumption_digest = trust_types::stable_sha256_hex(b"wrong assumptions digest");
            },
        ),
        ("replay", "manifest_row_acceptance.source_backpropagation_gate_row.replay", |manifest| {
            manifest.entries[0]
                .manifest_row_acceptance
                .as_mut()
                .expect("row acceptance should exist")
                .source_backpropagation_gate_row
                .as_mut()
                .expect("source gate row should exist")
                .replay = ReplayStatus::Failed;
        }),
        (
            "replay transcript",
            "manifest_row_acceptance.source_backpropagation_gate_row.replay_transcript_digest",
            |manifest| {
                manifest.entries[0]
                    .manifest_row_acceptance
                    .as_mut()
                    .expect("row acceptance should exist")
                    .source_backpropagation_gate_row
                    .as_mut()
                    .expect("source gate row should exist")
                    .replay_transcript_digest = Some(trust_types::stable_sha256_hex(b"wrong replay transcript"));
            },
        ),
        (
            "selected image",
            "manifest_row_acceptance.source_backpropagation_gate_row.selected_image_identity",
            |manifest| {
                manifest.entries[0]
                    .manifest_row_acceptance
                    .as_mut()
                    .expect("row acceptance should exist")
                    .source_backpropagation_gate_row
                    .as_mut()
                    .expect("source gate row should exist")
                    .selected_image_identity
                    .sha256 = trust_types::stable_sha256_hex(b"wrong selected image identity");
            },
        ),
    ];

    for (case, expected_field, mutate) in wrong_identity_cases {
        let mut wrong_identity = production_manifest.clone();
        mutate(&mut wrong_identity);
        let decision = wrong_identity.evaluate();
        assert!(!decision.accepted, "{case}: {:?}", decision.rejections);
        assert!(
            decision.rejections.iter().any(|rejection| matches!(
                rejection,
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    field,
                    ..
                } if field == expected_field
            )),
            "{case}: {:?}",
            decision.rejections
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn proof_grade_production_manifest_rejects_self_consistent_replay_downgrade() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("production-manifest-replay-downgrade");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let acceptance_request = production_acceptance_request(entry, &export)
        .with_source_backpropagation_gate(complete_source_backpropagation_gate())
        .expect("source-backprop gate should bind to accepted row");
    let acceptance = accept_checked_certificate_manifest_entry(
        &dir,
        canonical_vc_bytes,
        entry,
        &acceptance_request,
    )
    .expect("real manifest row should accept before replay-downgrade check");
    let production_manifest =
        CheckedBinaryCertificateProductionManifest::from_manifest_acceptance_records(
            1,
            &[CheckedBinaryCertificateProductionManifestAcceptedRowInput {
                manifest_entry: entry,
                acceptance_record: &acceptance.record,
            }],
        )
        .expect("accepted row should build a production manifest");
    assert!(production_manifest.evaluate().accepted);

    let mut replay_downgrade = production_manifest.clone();
    let production_entry = &mut replay_downgrade.entries[0];
    production_entry
        .production_evidence
        .as_mut()
        .expect("production evidence should exist")
        .replay = ReplayStatus::Failed;
    production_entry
        .production_evidence
        .as_mut()
        .expect("production evidence should exist")
        .replay_transcript_digest = None;
    let row_acceptance = production_entry
        .manifest_row_acceptance
        .as_mut()
        .expect("manifest row acceptance should exist");
    row_acceptance.replay = ReplayStatus::Failed;
    row_acceptance.replay_transcript_digest = None;
    let gate_row = row_acceptance
        .source_backpropagation_gate_row
        .as_mut()
        .expect("source gate row should exist");
    gate_row.replay = ReplayStatus::Failed;
    gate_row.replay_transcript_digest = None;
    let recomputed_identity = recompute_first_row_manifest_identity_sha256(&replay_downgrade);
    let row_acceptance = replay_downgrade.entries[0]
        .manifest_row_acceptance
        .as_mut()
        .expect("manifest row acceptance should exist");
    row_acceptance.manifest_identity_sha256 = recomputed_identity.clone();
    row_acceptance
        .source_backpropagation_gate_row
        .as_mut()
        .expect("source gate row should exist")
        .manifest_identity_sha256 = recomputed_identity;

    let decision = replay_downgrade.evaluate();

    assert!(!decision.accepted);
    for expected_field in [
        "production_evidence.replay",
        "production_evidence.replay_transcript_digest",
        "manifest_row_acceptance.replay",
        "manifest_row_acceptance.source_backpropagation_gate_row.replay",
        "manifest_row_acceptance.source_backpropagation_gate_row.replay_transcript_digest",
    ] {
        assert!(
            decision.rejections.iter().any(|rejection| matches!(
                rejection,
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    field,
                    ..
                } if field == expected_field
            )),
            "{expected_field}: {:?}",
            decision.rejections
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn proof_grade_production_manifest_rejects_missing_or_mismatched_real_manifest_row() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("production-manifest-real-row-negative");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let acceptance_request = production_acceptance_request(entry, &export)
        .with_source_backpropagation_gate(complete_source_backpropagation_gate())
        .expect("source-backprop gate should bind to accepted row");
    let acceptance = accept_checked_certificate_manifest_entry(
        &dir,
        canonical_vc_bytes,
        entry,
        &acceptance_request,
    )
    .expect("real manifest row should accept before negative production checks");
    let production_manifest =
        CheckedBinaryCertificateProductionManifest::from_manifest_acceptance_records(
            1,
            &[CheckedBinaryCertificateProductionManifestAcceptedRowInput {
                manifest_entry: entry,
                acceptance_record: &acceptance.record,
            }],
        )
        .expect("accepted row should build a production manifest");
    assert!(production_manifest.evaluate().accepted);

    let mut missing = production_manifest.clone();
    missing.entries[0].manifest_row_acceptance = None;
    let missing_decision = missing.evaluate();
    assert!(!missing_decision.accepted);
    assert!(
        missing_decision.rejections.iter().any(|rejection| matches!(
            rejection,
            CheckedBinaryCertificateProductionManifestRejection::MissingManifestRowAcceptance {
                dispatch_id
            } if dispatch_id == &entry.dispatch_id
        )),
        "{:?}",
        missing_decision.rejections
    );

    let mut vc_mismatch = production_manifest.clone();
    vc_mismatch.entries[0]
        .manifest_row_acceptance
        .as_mut()
        .expect("row acceptance should exist")
        .vc_sha256 = trust_types::stable_sha256_hex(b"different VC identity");
    assert_production_manifest_rejects_field(&vc_mismatch, "manifest_row_acceptance.vc_sha256");

    let mut proof_metadata_mismatch = production_manifest.clone();
    proof_metadata_mismatch.entries[0]
        .manifest_row_acceptance
        .as_mut()
        .expect("row acceptance should exist")
        .proof_metadata_sha256 = trust_types::stable_sha256_hex(b"different proof metadata digest");
    assert_production_manifest_rejects_field(
        &proof_metadata_mismatch,
        "manifest_row_acceptance.proof_metadata_sha256",
    );

    let mut replay_mismatch = production_manifest.clone();
    replay_mismatch.entries[0]
        .manifest_row_acceptance
        .as_mut()
        .expect("row acceptance should exist")
        .replay_transcript_digest = Some(trust_types::stable_sha256_hex(b"different replay transcript digest"));
    assert_production_manifest_rejects_field(
        &replay_mismatch,
        "manifest_row_acceptance.replay_transcript_digest",
    );

    let mut binary_digest_mismatch = production_manifest.clone();
    binary_digest_mismatch.entries[0]
        .manifest_row_acceptance
        .as_mut()
        .expect("row acceptance should exist")
        .binary_artifact_digest_identity
        .root_artifact_digest =
        Some(BinaryArtifactDigest::sha256(trust_types::stable_sha256_hex(b"different root artifact digest")));
    assert_production_manifest_rejects_field(
        &binary_digest_mismatch,
        "manifest_row_acceptance.binary_artifact_digest_identity",
    );

    let mut source_gate_mismatch = production_manifest;
    source_gate_mismatch.entries[0]
        .manifest_row_acceptance
        .as_mut()
        .expect("row acceptance should exist")
        .source_backpropagation_gate_sha256 =
        trust_types::stable_sha256_hex(b"different source-backprop gate identity");
    assert_production_manifest_rejects_field(
        &source_gate_mismatch,
        "manifest_row_acceptance.source_backpropagation_gate_sha256",
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn proof_grade_production_manifest_rejects_checked_artifact_shortcut_without_manifest_row() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("vc0");
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let check = check_binary_certificate(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export),
    );
    assert!(check.accepted, "{:?}", check.error);
    let artifact = check.certificate.expect("accepted check has certificate");

    let manifest = CheckedBinaryCertificateProductionManifest::from_checked_artifacts(
        1,
        &[CheckedBinaryCertificateProductionManifestInput {
            dispatch: &dispatch,
            canonical_vc_bytes,
            artifact: &artifact,
        }],
    )
    .expect("validated checked artifact should build production manifest");

    let decision = manifest.evaluate();
    assert!(!decision.accepted);
    assert_eq!(manifest.entries.len(), 1);
    let entry = &manifest.entries[0];
    assert_eq!(entry.dispatch_id, dispatch.id);
    assert_eq!(entry.vc_sha256, trust_types::stable_sha256_hex(canonical_vc_bytes));
    assert_eq!(entry.origin_sha256, artifact.origin_sha256);
    assert_eq!(entry.proof_sha256, artifact.proof_sha256);
    assert_eq!(entry.proof_export_sha256, artifact.proof_export_sha256);
    assert_eq!(entry.replay, artifact.replay);
    assert_eq!(entry.binary_artifact_digest_identity, artifact.binary_artifact_digest_identity);
    assert_eq!(entry.assumption_digest, artifact.assumption_digest);
    let evidence = entry.production_evidence.as_ref().expect("per-VC evidence");
    assert_eq!(evidence.vc_sha256, entry.vc_sha256);
    assert_eq!(evidence.certificate_sha256, entry.certificate_sha256);
    assert_eq!(evidence.query_semantics, SolverQuerySemantics::SatIsCounterexample);
    assert!(
        decision.rejections.iter().any(|rejection| matches!(
            rejection,
            CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                field,
                ..
            } if field == "require_manifest_row_acceptance"
        )),
        "{:?}",
        decision.rejections
    );
    assert!(
        decision.rejections.iter().any(|rejection| matches!(
            rejection,
            CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                field,
                ..
            } if field == "production_evidence.production_checker_evidence_sha256"
        )),
        "{:?}",
        decision.rejections
    );
    assert!(
        decision.rejections.iter().any(|rejection| matches!(
            rejection,
            CheckedBinaryCertificateProductionManifestRejection::MissingManifestRowAcceptance {
                dispatch_id
            } if dispatch_id == &entry.dispatch_id
        )),
        "{:?}",
        decision.rejections
    );
}

#[test]
fn proof_grade_production_manifest_rejects_raw_solver_bytes_on_checked_artifact_input() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("vc0");
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let check = check_binary_certificate(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export),
    );
    assert!(check.accepted, "{:?}", check.error);
    let artifact = check.certificate.expect("accepted check has certificate");

    let raw_bytes = b"raw solver proof bytes must not satisfy production evidence";
    let mut raw_dispatch = proved_dispatch("vc0");
    raw_dispatch.result = Some(VerificationResult::Proved {
        solver: "ay".into(),
        time_ms: 1,
        strength: trust_types::ProofStrength::smt_unsat(),
        proof_certificate: Some(raw_bytes.to_vec()),
        solver_warnings: None,
        native_proof_envelope: None,
    });

    let err = CheckedBinaryCertificateProductionManifest::from_checked_artifacts(
        1,
        &[CheckedBinaryCertificateProductionManifestInput {
            dispatch: &raw_dispatch,
            canonical_vc_bytes,
            artifact: &artifact,
        }],
    )
    .expect_err("raw solver proof bytes must not satisfy checked certificate evidence");

    assert!(
        matches!(err, CheckError::RawSolverBytesCannotUpgradeToChecked { ref dispatch_id } if dispatch_id == "vc0"),
        "{err:?}"
    );
}

#[test]
fn proof_grade_production_manifest_rejects_wrong_origin_checked_artifact_input_by_name() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("vc0");
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let check = check_binary_certificate(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export),
    );
    assert!(check.accepted, "{:?}", check.error);
    let artifact = check.certificate.expect("accepted check has certificate");

    let mut wrong_origin_dispatch = proved_dispatch("vc0");
    wrong_origin_dispatch
        .origin
        .as_mut()
        .expect("fixture has binary origin")
        .instruction_address += 4;

    let err = CheckedBinaryCertificateProductionManifest::from_checked_artifacts(
        1,
        &[CheckedBinaryCertificateProductionManifestInput {
            dispatch: &wrong_origin_dispatch,
            canonical_vc_bytes,
            artifact: &artifact,
        }],
    )
    .expect_err("wrong-origin checked artifact must not satisfy checked certificate evidence");

    assert!(
        matches!(err, CheckError::ArtifactBindingMismatch { ref field, .. } if field == "binary_origin_digest"),
        "{err:?}"
    );
}

#[test]
fn proof_grade_production_manifest_rejects_stale_row_bindings_by_name() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let (dir, manifest, export, _) =
        checked_manifest_acceptance_fixture("production-manifest-stale-row-bindings-by-name");
    let entry = manifest.certificates.first().expect("manifest should have one row");
    let source_gate = complete_source_backpropagation_gate();
    let acceptance_request = production_acceptance_request(entry, &export)
        .with_source_backpropagation_gate(source_gate)
        .expect("source-backprop gate should bind to accepted row");
    let acceptance = accept_checked_certificate_manifest_entry(
        &dir,
        canonical_vc_bytes,
        entry,
        &acceptance_request,
    )
    .expect("real manifest row should accept before production manifest export");
    let production_manifest =
        CheckedBinaryCertificateProductionManifest::from_manifest_acceptance_records(
            1,
            &[CheckedBinaryCertificateProductionManifestAcceptedRowInput {
                manifest_entry: entry,
                acceptance_record: &acceptance.record,
            }],
        )
        .expect("accepted row should build a production manifest");
    assert!(production_manifest.evaluate().accepted);

    let stale_cases: [(&str, &str, fn(&mut CheckedBinaryCertificateProductionManifest)); 3] = [
        ("origin", "origin_sha256", |manifest| {
            manifest.entries[0]
                .production_evidence
                .as_mut()
                .expect("production evidence should exist")
                .origin_sha256 = trust_types::stable_sha256_hex(b"stale binary origin digest");
        }),
        ("proof", "proof_sha256", |manifest| {
            manifest.entries[0]
                .production_evidence
                .as_mut()
                .expect("production evidence should exist")
                .proof_sha256 = trust_types::stable_sha256_hex(b"stale solver proof digest");
        }),
        ("assumptions", "assumption_digest", |manifest| {
            manifest.entries[0]
                .production_evidence
                .as_mut()
                .expect("production evidence should exist")
                .assumption_digest = trust_types::stable_sha256_hex(b"stale assumption digest");
        }),
    ];

    for (case, expected_field, mutate) in stale_cases {
        let mut stale_manifest = production_manifest.clone();
        mutate(&mut stale_manifest);

        let decision = stale_manifest.evaluate();

        assert!(!decision.accepted, "{case}: {:?}", decision.rejections);
        assert!(
            decision.rejections.iter().any(|rejection| matches!(
                rejection,
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    field,
                    ..
                } if field == expected_field
            )),
            "{case}: {:?}",
            decision.rejections
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn proof_grade_production_manifest_rejects_missing_or_mismatched_evidence() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("vc0");
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let check = check_binary_certificate(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export),
    );
    assert!(check.accepted, "{:?}", check.error);
    let artifact = check.certificate.expect("accepted check has certificate");
    let manifest = CheckedBinaryCertificateProductionManifest::from_checked_artifacts(
        2,
        &[CheckedBinaryCertificateProductionManifestInput {
            dispatch: &dispatch,
            canonical_vc_bytes,
            artifact: &artifact,
        }],
    )
    .expect("validated checked artifact should build production manifest");

    let coverage_decision = manifest.evaluate();
    assert!(!coverage_decision.accepted);
    assert!(
        coverage_decision.rejections.iter().any(|rejection| matches!(
            rejection,
            CheckedBinaryCertificateProductionManifestRejection::RequiredVcCoverageIncomplete {
                required_vcs: 2,
                entries: 1
            }
        )),
        "{:?}",
        coverage_decision.rejections
    );

    let mut missing = manifest.clone();
    missing.required_vcs = 1;
    missing.entries[0].production_evidence = None;
    let missing_decision = missing.evaluate();
    assert!(!missing_decision.accepted);
    assert!(
        missing_decision.rejections.iter().any(|rejection| matches!(
            rejection,
            CheckedBinaryCertificateProductionManifestRejection::MissingProductionEvidence {
                dispatch_id
            } if dispatch_id == "vc0"
        )),
        "{:?}",
        missing_decision.rejections
    );

    let mut mismatched = manifest;
    mismatched.required_vcs = 1;
    mismatched.entries[0]
        .production_evidence
        .as_mut()
        .expect("evidence should exist")
        .certificate_sha256 = trust_types::stable_sha256_hex(b"forged certificate");
    let mismatched_decision = mismatched.evaluate();
    assert!(!mismatched_decision.accepted);
    assert!(
        mismatched_decision.rejections.iter().any(|rejection| matches!(
            rejection,
            CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                field,
                ..
            } if field == "certificate_sha256"
        )),
        "{:?}",
        mismatched_decision.rejections
    );
}

#[test]
fn proof_grade_production_manifest_rejects_noncanonical_digest_identities() {
    let canonical_vc_bytes = br#"{"vc":"main memory safety"}"#;
    let dispatch = proved_dispatch("vc0");
    let export = proof_export(&dispatch, canonical_vc_bytes);
    let checker = checked_certificate_checker();
    let check = check_binary_certificate(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch, canonical_vc_bytes, &export),
    );
    assert!(check.accepted, "{:?}", check.error);
    let artifact = check.certificate.expect("accepted check has certificate");
    let mut manifest = CheckedBinaryCertificateProductionManifest::from_checked_artifacts(
        1,
        &[CheckedBinaryCertificateProductionManifestInput {
            dispatch: &dispatch,
            canonical_vc_bytes,
            artifact: &artifact,
        }],
    )
    .expect("validated checked artifact should build production manifest");

    manifest.entries[0].vc_sha256 = "NOT-A-CANONICAL-DIGEST".to_string();
    manifest.entries[0]
        .production_evidence
        .as_mut()
        .expect("production evidence should exist")
        .proof_sha256 = "also-not-a-canonical-digest".to_string();

    let decision = manifest.evaluate();

    assert!(!decision.accepted);
    assert!(
        decision.rejections.iter().any(|rejection| matches!(
            rejection,
            CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                field,
                expected,
                ..
            } if field == "vc_sha256"
                && expected == "canonical lowercase sha256 hex digest"
        )),
        "{:?}",
        decision.rejections
    );
    assert!(
        decision.rejections.iter().any(|rejection| matches!(
            rejection,
            CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                field,
                expected,
                ..
            } if field == "production_evidence.proof_sha256"
                && expected == "canonical lowercase sha256 hex digest"
        )),
        "{:?}",
        decision.rejections
    );
}

fn unique_temp_dir(label: &str) -> std::path::PathBuf {
    let mut dir = std::env::temp_dir();
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system time should be after epoch")
        .as_nanos();
    dir.push(format!("{label}-{}-{unique}", std::process::id()));
    dir
}
