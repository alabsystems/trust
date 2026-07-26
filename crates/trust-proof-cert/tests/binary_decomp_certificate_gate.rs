use trust_proof_cert::binary_decomp::{
    BinaryArtifactTrustLevel, BinaryReleaseGateRejection, BinaryVerificationCertificateSummary,
    digest_lifted_binary, summarize_binary_certificate_proof_grade_gate,
};
use trust_proof_cert::{
    BinaryCertificateCheckRequest, CheckedBinaryCertificateExternalProcessTranscript,
    CheckedBinaryCertificateManifest, CheckedBinaryCertificateManifestAcceptanceRequest,
    CheckedBinaryCertificateProductionCheckerEvidence, SolverProofExport,
    StructuralBinaryCertificateChecker, import_checked_certificate_manifest_entry_for_dispatch,
    produce_checked_certificate_artifact,
};
use trust_types::{
    BinaryArtifactDigest, BinaryArtifactDigestIdentity, BinaryOrigin, BinarySelectedImageIdentity,
    BinaryVerificationSummary, CompilerClaim, Counterexample, CounterexampleValue, DecompileTarget,
    ExploitWitness, Formula, ProofCertificateStatus, ProofStrength, RefutationKind, ReplayStatus,
    SerializableVc, SolverDispatchRecord, SolverDispatchStatus, SolverQuerySemantics, SourceSpan,
    Symbol, UnsupportedLedger, UnsupportedRecord, VcKind, VerificationResult,
};

fn checked_dispatch(id: &str) -> SolverDispatchRecord {
    let canonical_vc_bytes = canonical_vc_bytes(id);
    let export_dispatch = SolverDispatchRecord {
        id: format!("export-run:{id}"),
        solver: "ay".to_string(),
        backend: Some("ay-lfsc".to_string()),
        status: SolverDispatchStatus::Unsat,
        query_semantics: SolverQuerySemantics::SatIsCounterexample,
        replay: ReplayStatus::Replayed,
        origin: Some(binary_origin()),
        binary_artifact_digest_identity: Some(binary_artifact_digest_identity()),
        certificate: ProofCertificateStatus::Present {
            format: "lfsc".to_string(),
            sha256: None,
            artifact_path: None,
        },
        ..Default::default()
    };
    let export = SolverProofExport::new(
        &export_dispatch,
        &canonical_vc_bytes,
        "lfsc",
        format!("normalized lfsc proof bytes for {id}").into_bytes(),
        Some("4.13.0".to_string()),
        1_777_070_400_000,
    );
    let checker = checked_certificate_checker();
    let dir = temp_artifact_dir(format!("manifest-backed-{}", id.replace(':', "-")).as_str());
    let artifact_ref = produce_checked_certificate_artifact(
        &checker,
        BinaryCertificateCheckRequest::from_export(&export_dispatch, &canonical_vc_bytes, &export),
        &dir,
    )
    .expect("checked artifact should persist for manifest-backed dispatch");
    let manifest = CheckedBinaryCertificateManifest::from_artifact_refs(&dir, &[artifact_ref])
        .expect("manifest should build from checked artifact");
    let entry = manifest.certificates.first().expect("manifest should contain checked artifact");
    let acceptance_request =
        CheckedBinaryCertificateManifestAcceptanceRequest::from_manifest_entry_and_solver_proof_export_metadata(
            entry,
            export.normalized_metadata(),
        )
        .expect("acceptance request should bind solver proof export")
        .with_production_checker_evidence(production_checker_evidence(entry))
        .expect("acceptance request should bind production checker evidence");

    let mut dispatch = SolverDispatchRecord {
        id: id.to_string(),
        solver: "ay".to_string(),
        backend: Some("ay-lfsc".to_string()),
        status: SolverDispatchStatus::Unsat,
        query_semantics: SolverQuerySemantics::SatIsCounterexample,
        replay: ReplayStatus::Replayed,
        origin: Some(binary_origin()),
        binary_artifact_digest_identity: Some(binary_artifact_digest_identity()),
        certificate: ProofCertificateStatus::Present {
            format: "lfsc".to_string(),
            sha256: None,
            artifact_path: None,
        },
        ..Default::default()
    };
    import_checked_certificate_manifest_entry_for_dispatch(
        &mut dispatch,
        &canonical_vc_bytes,
        &dir,
        entry,
        &acceptance_request,
    )
    .expect("manifest-backed checked dispatch should import");
    let _ = std::fs::remove_dir_all(&dir);
    dispatch
}

fn test_sha256_hex(value: impl AsRef<[u8]>) -> String {
    trust_types::stable_sha256_hex(value.as_ref())
}

fn canonical_vc_bytes(id: &str) -> Vec<u8> {
    format!(r#"{{"vc":"binary safety {id}"}}"#).into_bytes()
}

fn temp_artifact_dir(name: &str) -> std::path::PathBuf {
    static COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system time should be after Unix epoch")
        .as_nanos();
    let counter = COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    std::env::temp_dir()
        .join(format!("trust-proof-cert-{name}-{}-{unique}-{counter}", std::process::id()))
}

fn checked_certificate_checker() -> StructuralBinaryCertificateChecker {
    StructuralBinaryCertificateChecker::new(
        "ay-cert-check",
        "1.0.0",
        vec!["lfsc".to_string()],
        1_777_070_401_000,
    )
}

fn production_checker_evidence(
    entry: &trust_proof_cert::CheckedBinaryCertificateManifestEntry,
) -> CheckedBinaryCertificateProductionCheckerEvidence {
    let transcript = CheckedBinaryCertificateExternalProcessTranscript::new(
        "ay-cert-check",
        [
            "ay-cert-check".to_string(),
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
        trust_types::stable_sha256_hex(b"ay-cert-check production executable"),
        Some(trust_types::stable_sha256_hex(b"ay-cert-check production config")),
        transcript,
        1_777_070_401_000,
    )
    .expect("production checker evidence should build")
}

fn serializable_vc(function: &str) -> SerializableVc {
    SerializableVc {
        kind: VcKind::Assertion { message: "binary safety".to_string() },
        function: Symbol::intern(function),
        location: SourceSpan::binary_address(0x401010),
        formula: Formula::Bool(true),
        contract_metadata: None,
    }
}

fn present_unchecked_dispatch(id: &str) -> SolverDispatchRecord {
    SolverDispatchRecord {
        certificate: ProofCertificateStatus::Present {
            format: "lfsc".to_string(),
            sha256: Some(test_sha256_hex(format!("{id}-present"))),
            artifact_path: None,
        },
        ..checked_dispatch(id)
    }
}

fn raw_solver_proved_result() -> VerificationResult {
    VerificationResult::Proved {
        solver: "ay".into(),
        time_ms: 1,
        strength: ProofStrength::smt_unsat(),
        proof_certificate: Some(b"raw solver proof bytes".to_vec()),
        solver_warnings: None,
        native_proof_envelope: None,
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

fn unsupported_ledger(feature: &str, origin: Option<BinaryOrigin>) -> UnsupportedLedger {
    UnsupportedLedger {
        records: vec![UnsupportedRecord {
            stage: "lift".to_string(),
            architecture: Some("x86_64".to_string()),
            origin,
            opcode: Some("syscall".to_string()),
            operand: None,
            feature: feature.to_string(),
        }],
    }
}

fn summary_from_dispatches(
    dispatches: &[SolverDispatchRecord],
) -> BinaryVerificationCertificateSummary {
    BinaryVerificationCertificateSummary::from_solver_dispatch_records(
        digest_lifted_binary(b"integration-lifted-trust_ir"),
        "trust_ir+binary",
        "x86_64",
        &UnsupportedLedger::default(),
        dispatches,
        BinaryArtifactTrustLevel::ProofGrade,
    )
    .expect("binary certificate summary should build")
}

fn summary_from_dispatches_with_ledger(
    dispatches: &[SolverDispatchRecord],
    ledger: &UnsupportedLedger,
) -> BinaryVerificationCertificateSummary {
    BinaryVerificationCertificateSummary::from_solver_dispatch_records(
        digest_lifted_binary(b"integration-lifted-trust_ir"),
        "trust_ir+binary",
        "x86_64",
        ledger,
        dispatches,
        BinaryArtifactTrustLevel::ProofGrade,
    )
    .expect("binary certificate summary should build")
}

fn summary_from_verification(
    verification: &BinaryVerificationSummary,
) -> BinaryVerificationCertificateSummary {
    BinaryVerificationCertificateSummary::from_binary_verification_summary(
        digest_lifted_binary(b"integration-lifted-trust_ir"),
        "trust_ir+binary",
        "x86_64",
        &UnsupportedLedger::default(),
        verification,
        BinaryArtifactTrustLevel::ProofGrade,
    )
    .expect("binary certificate summary should build")
}

fn verification_from_dispatches(
    dispatches: Vec<SolverDispatchRecord>,
) -> BinaryVerificationSummary {
    let mut verification = BinaryVerificationSummary::from_solver_dispatch(dispatches);
    verification.trust_level = BinaryArtifactTrustLevel::ProofGrade;
    verification
}

fn exploit_witness(replay: ReplayStatus, model: Option<Counterexample>) -> ExploitWitness {
    ExploitWitness {
        claim: CompilerClaim {
            component: "external-audit".to_string(),
            claim: "argv[1] reaches unchecked memcpy".to_string(),
            location: Some(SourceSpan::binary_address(0x401010)),
            assumptions: Vec::new(),
        },
        refutation: RefutationKind::ReplayMismatch,
        function: "sym.main".to_string(),
        location: Some(SourceSpan::binary_address(0x401010)),
        model,
        replay,
        attribution: Some("regression-fixture".to_string()),
    }
}

fn concrete_exploit_input() -> Counterexample {
    Counterexample::new(vec![("argv_len".to_string(), CounterexampleValue::Uint(4))])
}

#[test]
fn manifest_backed_checked_certificate_dispatches_are_the_local_proof_grade_path() {
    let dispatches = vec![checked_dispatch("vc0"), checked_dispatch("vc1")];
    let summary = summary_from_dispatches(&dispatches);
    let decision = summary.proof_grade_release_gate();
    let gate_summary = summarize_binary_certificate_proof_grade_gate(&summary);

    assert_eq!(summary.solver_results.proved, 2);
    assert_eq!(summary.solver_results.proved_with_certificates, 2);
    assert_eq!(summary.raw_solver_proof_bytes, 0);
    assert!(summary.certificate_checks.records.iter().all(|record| {
        record.production_checker_evidence.as_ref().is_some_and(|evidence| {
            evidence.checker == "ay-cert-check" && evidence.checker_version == "1.0.0"
        })
    }));
    assert!(decision.accepted, "{:?}", decision.rejections);

    assert!(gate_summary.accepted);
    assert_eq!(gate_summary.required_vcs, 2);
    assert_eq!(gate_summary.checked_certificates, 2);
    assert_eq!(gate_summary.raw_solver_proof_bytes, 0);
}

#[test]
fn duplicated_manifest_backed_checked_identity_does_not_cover_another_required_vc() {
    let covered = checked_dispatch("vc0");
    let mut duplicate_identity = covered.clone();
    duplicate_identity.id = "vc1".to_string();

    let summary = summary_from_dispatches(&[covered, duplicate_identity]);
    let decision = summary.proof_grade_release_gate();

    assert_eq!(summary.solver_results.proved, 2);
    assert_eq!(summary.solver_results.proved_with_certificates, 1);
    assert_eq!(summary.certificate_checks.checked_certificates, 1);
    assert_eq!(summary.certificate_checks.missing_checked_certificates, 1);
    assert!(
        summary.certificate_checks.records[1]
            .coherence_failures
            .iter()
            .any(|failure| failure
                .contains("duplicate manifest-backed checked certificate VC identity")),
        "{:?}",
        summary.certificate_checks.records[1]
    );
    assert!(decision.rejected());
    assert!(decision.rejections.iter().any(|reason| {
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
}

#[test]
fn direct_summary_preserved_symbolic_formulas_require_consumer_evidence() {
    let mut summary = summary_from_dispatches(&[checked_dispatch("vc0")]);
    summary.preserved_symbolic_formulas = 1;

    let decision = summary.proof_grade_release_gate();

    assert!(!summary.symbolic_formula_consumer_accepted);
    assert!(decision.rejected());
    assert_eq!(decision.rejections.len(), 1, "{:?}", decision.rejections);
    assert!(matches!(
        decision.rejections.as_slice(),
        [BinaryReleaseGateRejection::SymbolicFormulasNotConsumed {
            target: DecompileTarget::TrustIr,
            count: 1,
        }]
    ));

    let consumed_summary = summary_from_dispatches(&[checked_dispatch("vc0")])
        .with_symbolic_formula_consumer_evidence(1, true);
    let consumed_decision = consumed_summary.proof_grade_release_gate();

    assert!(consumed_decision.accepted, "{:?}", consumed_decision.rejections);
}

#[test]
fn malformed_checked_certificate_digest_rows_fail_closed() {
    let mut dispatch = checked_dispatch("vc0");
    dispatch.certificate = ProofCertificateStatus::Checked {
        checker: "ay-cert-check".to_string(),
        format: "lfsc".to_string(),
        sha256: Some("VC0-CHECKED".to_string()),
    };

    let summary = summary_from_dispatches(&[dispatch]);
    let decision = summary.proof_grade_release_gate();

    assert_eq!(summary.solver_results.proved, 1);
    assert_eq!(summary.solver_results.proved_with_certificates, 0);
    assert_eq!(summary.certificate_checks.checked_certificates, 0);
    assert_eq!(summary.certificate_checks.records[0].status, "checked-invalid");
    assert!(
        summary.certificate_checks.records[0].coherence_failures.contains(
            &"checked certificate digest is not canonical lowercase sha256 hex".to_string()
        )
    );
    assert!(decision.rejected());
    assert!(decision.rejections.iter().any(|reason| {
        matches!(
            reason,
            BinaryReleaseGateRejection::MissingProofCertificates {
                vc_count: 1,
                proved: 1,
                proved_with_certificates: 0,
                missing_certificates: 1,
            }
        )
    }));
}

#[test]
fn malformed_production_checker_evidence_marker_fails_closed() {
    let mut dispatch = checked_dispatch("vc0");
    dispatch.certificate = ProofCertificateStatus::Checked {
        checker: "ay-cert-check@1.0.0;production_checker_evidence_sha256=NOTHEX".to_string(),
        format: "lfsc".to_string(),
        sha256: Some(test_sha256_hex("vc0-checked")),
    };

    let summary = summary_from_dispatches(&[dispatch]);
    let decision = summary.proof_grade_release_gate();

    assert_eq!(summary.solver_results.proved, 1);
    assert_eq!(summary.solver_results.proved_with_certificates, 0);
    assert_eq!(summary.certificate_checks.checked_certificates, 0);
    assert_eq!(summary.certificate_checks.records[0].status, "checked-invalid");
    assert_eq!(summary.certificate_checks.records[0].production_checker_evidence, None);
    assert!(summary.certificate_checks.records[0].coherence_failures.iter().any(|failure| {
        failure.contains("malformed production checker evidence")
            && failure.contains("canonical lowercase sha256 hex")
    }));
    assert!(decision.rejected());
    assert!(decision.rejections.iter().any(|reason| {
        matches!(reason, BinaryReleaseGateRejection::MissingProofCertificates { .. })
    }));
}

#[test]
fn checked_vc_certificate_replay_does_not_independently_refute_uncaptured_exploit() {
    let mut verification = verification_from_dispatches(vec![checked_dispatch("vc0")]);
    verification.witnesses = vec![exploit_witness(ReplayStatus::NotAttempted, None)];

    let summary = summary_from_verification(&verification);
    let decision = summary.proof_grade_release_gate();

    assert_eq!(summary.solver_results.proved, 1);
    assert_eq!(summary.solver_results.proved_with_certificates, 1);
    assert_eq!(summary.replay_status.replayed, 1);
    assert_eq!(summary.certificate_checks.checked_certificates, 1);
    assert_eq!(summary.exploit_refutations.total_refutations, 1);
    assert_eq!(summary.exploit_refutations.captured_and_replayed, 0);
    assert_eq!(summary.exploit_refutations.missing_exact_inputs, 1);
    assert_eq!(summary.exploit_refutations.not_replayed, 1);
    assert!(decision.rejected());
    assert!(decision.rejections.iter().any(|reason| {
        matches!(
            reason,
            BinaryReleaseGateRejection::ExploitRefutationReplayIncomplete {
                refutations: 1,
                captured_and_replayed: 0,
                missing_exact_inputs: 1,
                not_replayed: 1,
                unknown_refutations: 0,
            }
        )
    }));
    assert!(!decision.rejections.iter().any(|reason| {
        matches!(
            reason,
            BinaryReleaseGateRejection::MissingProofCertificates { .. }
                | BinaryReleaseGateRejection::ReplayCoverageIncomplete { .. }
                | BinaryReleaseGateRejection::ReplayStatusUnknown { .. }
        )
    }));
}

#[test]
fn checked_vc_certificate_can_coexist_with_exact_replayed_exploit_refutation() {
    let mut verification = verification_from_dispatches(vec![checked_dispatch("vc0")]);
    verification.witnesses =
        vec![exploit_witness(ReplayStatus::Replayed, Some(concrete_exploit_input()))];

    let summary = summary_from_verification(&verification);
    let decision = summary.proof_grade_release_gate();

    assert_eq!(summary.certificate_checks.checked_certificates, 1);
    assert_eq!(summary.exploit_refutations.total_refutations, 1);
    assert_eq!(summary.exploit_refutations.captured_and_replayed, 1);
    assert!(decision.accepted, "{:?}", decision.rejections);
}

#[test]
fn raw_solver_proof_bytes_are_audit_artifacts_even_with_checked_status() {
    let mut dispatch = checked_dispatch("vc0");
    dispatch.result = Some(raw_solver_proved_result());
    let summary = summary_from_dispatches(&[dispatch]);
    let decision = summary.proof_grade_release_gate();
    let gate_summary = summarize_binary_certificate_proof_grade_gate(&summary);

    assert_eq!(summary.solver_results.proved, 1);
    assert_eq!(summary.solver_results.proved_with_certificates, 1);
    assert_eq!(summary.raw_solver_proof_bytes, 1);
    assert!(decision.rejected());
    assert!(decision.rejections.iter().any(|reason| {
        matches!(reason, BinaryReleaseGateRejection::RawSolverProofBytesPresent { count: 1 })
    }));
    assert!(!decision.rejections.iter().any(|reason| {
        matches!(reason, BinaryReleaseGateRejection::MissingProofCertificates { .. })
    }));

    assert!(!gate_summary.accepted);
    assert_eq!(gate_summary.checked_certificates, 1);
    assert_eq!(gate_summary.raw_solver_proof_bytes, 1);
}

#[test]
fn raw_solver_result_certificates_do_not_count_as_checked_local_certificates() {
    let summary = BinaryVerificationCertificateSummary::from_results(
        digest_lifted_binary(b"integration-lifted-trust_ir"),
        "trust_ir+binary",
        "x86_64",
        &UnsupportedLedger::default(),
        1,
        &[raw_solver_proved_result()],
        &[ReplayStatus::Replayed],
        BinaryArtifactTrustLevel::ProofGrade,
    )
    .expect("binary certificate summary should build");
    let decision = summary.proof_grade_release_gate();
    let gate_summary = summarize_binary_certificate_proof_grade_gate(&summary);

    assert_eq!(summary.solver_results.proved, 1);
    assert_eq!(summary.solver_results.proved_with_certificates, 0);
    assert_eq!(summary.raw_solver_proof_bytes, 1);
    assert!(decision.rejected());
    assert!(decision.rejections.iter().any(|reason| {
        matches!(
            reason,
            BinaryReleaseGateRejection::MissingProofCertificates {
                vc_count: 1,
                proved: 1,
                proved_with_certificates: 0,
                missing_certificates: 1,
            }
        )
    }));
    assert!(decision.rejections.iter().any(|reason| {
        matches!(reason, BinaryReleaseGateRejection::RawSolverProofBytesPresent { count: 1 })
    }));

    assert_eq!(gate_summary.checked_certificates, 0);
    assert_eq!(gate_summary.raw_solver_proof_bytes, 1);
}

#[test]
fn checked_certificate_coverage_does_not_mask_missing_replay_status() {
    let mut summary = summary_from_dispatches(&[checked_dispatch("vc0")]);
    summary.replay_status = Default::default();

    let decision = summary.proof_grade_release_gate();
    let gate_summary = summarize_binary_certificate_proof_grade_gate(&summary);

    assert_eq!(summary.solver_results.proved_with_certificates, 1);
    assert_eq!(summary.certificate_checks.checked_certificates, 1);
    assert_eq!(summary.raw_solver_proof_bytes, 0);
    assert!(decision.rejected());
    assert!(
        decision
            .rejections
            .iter()
            .any(|reason| matches!(reason, BinaryReleaseGateRejection::ReplayStatusMissing))
    );
    assert!(!decision.rejections.iter().any(|reason| {
        matches!(reason, BinaryReleaseGateRejection::MissingProofCertificates { .. })
    }));
    assert!(!decision.rejections.iter().any(|reason| {
        matches!(reason, BinaryReleaseGateRejection::RawSolverProofBytesPresent { .. })
    }));

    assert!(!gate_summary.accepted);
    assert_eq!(gate_summary.checked_certificates, 1);
    assert_eq!(gate_summary.replayed_vcs, 0);
    assert_eq!(gate_summary.raw_solver_proof_bytes, 0);
}

#[test]
fn checked_certificate_coverage_does_not_mask_unattempted_replay() {
    let mut dispatch = checked_dispatch("vc0");
    dispatch.replay = ReplayStatus::NotAttempted;
    let summary = summary_from_dispatches(&[dispatch]);

    let decision = summary.proof_grade_release_gate();

    assert_eq!(summary.solver_results.proved_with_certificates, 0);
    assert_eq!(summary.certificate_checks.checked_certificates, 0);
    assert_eq!(summary.raw_solver_proof_bytes, 0);
    assert!(decision.rejected());
    assert!(decision.rejections.iter().any(|reason| {
        matches!(reason, BinaryReleaseGateRejection::ReplayStatusUnknown { not_attempted: 1 })
    }));
    assert!(decision.rejections.iter().any(|reason| {
        matches!(reason, BinaryReleaseGateRejection::MissingProofCertificates { .. })
    }));
}

#[test]
fn checked_certificate_coverage_does_not_mask_unsupported_binary_ledger() {
    let ledger = unsupported_ledger("system-call-side-effects", Some(binary_origin()));
    let summary = summary_from_dispatches_with_ledger(&[checked_dispatch("vc0")], &ledger);

    let decision = summary.proof_grade_release_gate();

    assert_eq!(summary.solver_results.proved_with_certificates, 1);
    assert_eq!(summary.raw_solver_proof_bytes, 0);
    assert_eq!(summary.unsupported_ledger_summary.total_records, 1);
    assert_eq!(
        summary.unsupported_ledger_summary.by_feature.get("system-call-side-effects"),
        Some(&1)
    );
    assert!(decision.rejected());
    assert!(decision.rejections.iter().any(|reason| {
        matches!(reason, BinaryReleaseGateRejection::UnsupportedRecordsPresent { count: 1, .. })
    }));
    assert!(!decision.rejections.iter().any(|reason| {
        matches!(reason, BinaryReleaseGateRejection::MissingProofCertificates { .. })
    }));
    assert!(!decision.rejections.iter().any(|reason| {
        matches!(reason, BinaryReleaseGateRejection::RawSolverProofBytesPresent { .. })
    }));
}

#[test]
fn checked_certificate_coverage_does_not_mask_missing_binary_origin_record() {
    let ledger = unsupported_ledger("missing-binary-origin", None);
    let summary = summary_from_dispatches_with_ledger(&[checked_dispatch("vc0")], &ledger);

    let decision = summary.proof_grade_release_gate();

    assert_eq!(summary.solver_results.proved_with_certificates, 1);
    assert_eq!(summary.raw_solver_proof_bytes, 0);
    assert_eq!(summary.unsupported_ledger_summary.total_records, 1);
    assert_eq!(summary.unsupported_ledger_summary.by_stage.get("lift"), Some(&1));
    assert_eq!(
        summary.unsupported_ledger_summary.by_feature.get("missing-binary-origin"),
        Some(&1)
    );
    assert!(decision.rejected());
    assert!(decision.rejections.iter().any(|reason| {
        matches!(reason, BinaryReleaseGateRejection::UnsupportedRecordsPresent { count: 1, .. })
    }));
    assert!(!decision.rejections.iter().any(|reason| {
        matches!(reason, BinaryReleaseGateRejection::MissingProofCertificates { .. })
    }));
}

#[test]
fn unchecked_certificate_candidates_do_not_satisfy_binary_gate_coverage() {
    let summary =
        summary_from_dispatches(&[checked_dispatch("vc0"), present_unchecked_dispatch("vc1")]);

    let decision = summary.proof_grade_release_gate();
    let gate_summary = summarize_binary_certificate_proof_grade_gate(&summary);

    assert_eq!(summary.solver_results.proved, 2);
    assert_eq!(summary.solver_results.proved_with_certificates, 1);
    assert_eq!(summary.certificate_checks.certificate_candidates, 2);
    assert_eq!(summary.certificate_checks.checked_certificates, 1);
    assert_eq!(summary.certificate_checks.missing_checked_certificates, 1);
    assert_eq!(summary.raw_solver_proof_bytes, 0);
    assert!(decision.rejected());
    assert!(decision.rejections.iter().any(|reason| {
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
    assert!(!decision.rejections.iter().any(|reason| {
        matches!(reason, BinaryReleaseGateRejection::RawSolverProofBytesPresent { .. })
    }));

    assert!(!gate_summary.accepted);
    assert_eq!(gate_summary.required_vcs, 2);
    assert_eq!(gate_summary.checked_certificates, 1);
    assert_eq!(gate_summary.raw_solver_proof_bytes, 0);
}

#[test]
fn checked_certificate_status_without_binary_origin_does_not_count_as_gate_coverage() {
    let mut dispatch = checked_dispatch("vc0");
    dispatch.origin = None;

    let summary = summary_from_dispatches(&[dispatch]);
    let decision = summary.proof_grade_release_gate();

    assert_eq!(summary.solver_results.proved, 1);
    assert_eq!(summary.solver_results.proved_with_certificates, 0);
    assert_eq!(summary.certificate_checks.checked_certificates, 0);
    assert_eq!(
        summary.certificate_checks.records[0].coherence_failures,
        vec!["missing binary origin"]
    );
    assert!(decision.rejected());
    assert!(decision.rejections.iter().any(|reason| {
        matches!(reason, BinaryReleaseGateRejection::MissingProofCertificates { .. })
    }));
}

#[test]
fn checked_certificate_status_with_incoherent_origin_does_not_count_as_gate_coverage() {
    let mut dispatch = checked_dispatch("vc0");
    let origin = dispatch.origin.as_mut().expect("fixture has origin");
    origin.instruction_size = Some(4);
    origin.instruction_bytes = vec![0x90, 0x90];

    let summary = summary_from_dispatches(&[dispatch]);
    let decision = summary.proof_grade_release_gate();

    assert_eq!(summary.solver_results.proved_with_certificates, 0);
    assert_eq!(summary.certificate_checks.checked_certificates, 0);
    assert!(
        summary.certificate_checks.records[0]
            .coherence_failures
            .iter()
            .any(|failure| failure.contains("checked_certificate_manifest_identity.origin_sha256")),
        "{:?}",
        summary.certificate_checks.records[0].coherence_failures
    );
    assert!(
        summary.certificate_checks.records[0]
            .coherence_failures
            .iter()
            .any(|failure| failure == "instruction bytes length does not match instruction size"),
        "{:?}",
        summary.certificate_checks.records[0].coherence_failures
    );
    assert!(decision.rejected());
}

#[test]
fn checked_certificate_status_with_mismatched_vc_function_does_not_count_as_gate_coverage() {
    let mut dispatch = checked_dispatch("vc0");
    dispatch.function = Some("sym.main".to_string());
    dispatch.vc = Some(serializable_vc("sym.helper"));

    let summary = summary_from_dispatches(&[dispatch]);
    let decision = summary.proof_grade_release_gate();

    assert_eq!(summary.solver_results.proved, 1);
    assert_eq!(summary.solver_results.proved_with_certificates, 0);
    assert_eq!(summary.certificate_checks.checked_certificates, 0);
    assert_eq!(
        summary.certificate_checks.records[0].coherence_failures,
        vec!["VC function does not match dispatch function"]
    );
    assert!(decision.rejected());
}
