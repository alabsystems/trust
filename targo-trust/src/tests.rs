use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::time::{SystemTime, UNIX_EPOCH};

use trust_decompile::DecompileOutputKind;
use trust_lift::{LiftError, LiftProofMode};
use trust_proof_cert::{
    BinaryCertificateCheckRequest, CheckedBinaryCertificateArtifact,
    CheckedBinaryCertificateAuditExport, CheckedBinaryCertificateExternalCheckerRunner,
    CheckedBinaryCertificateManifest, CheckedBinaryCertificateManifestAcceptanceRequest,
    CheckedBinaryCertificateManifestEntry, CheckedBinaryCertificateSourceBackpropagationGate,
    SolverProofExport, StructuralBinaryCertificateChecker, check_binary_certificate,
    checked_certificate_audit_export_bundle_path, digest_binary_origin, digest_model_assumptions,
    import_checked_certificate_manifest_entry_for_dispatch,
    load_checked_certificate_audit_export_bundle_rows, persist_checked_certificate_artifact,
    persist_checked_certificate_audit_export_bundle, produce_checked_certificate_artifact,
};
use trust_router::{Router, VerificationBackend};
use trust_types::{
    BinaryAddressRange, BinaryArtifactDigest, BinaryArtifactDigestIdentity, BinaryOrigin,
    BinarySegment, BinarySegmentPermissions, BinarySelectedImageIdentity,
    BinarySourceProvenanceSummary, Endianness, Formula, HardenedVcCategory, MemoryAccessFact,
    MemoryAccessKind, MemoryRegionKind, PreservedSymbolicFormula, ProofCertificateStatus,
    ReplayStatus, SerializableVc, SolverDispatchRecord, SolverDispatchStatus, SolverQuerySemantics,
    Sort, SourceSpan, TargetValidationBlocker, VcKind, VerificationCondition,
};

use super::{
    BinaryReplayAttempt, BinaryReplayContext, BinarySolverRoute, DoctorBackendSource,
    DoctorBackendStatus, DoctorCheckReportMode, DoctorCompilerStatus, DoctorConfigSourceKind,
    DoctorConfigStatus, DoctorDailyDriverStatus, DoctorReport, DoctorSolverStatus,
    ExactReplayInstructionAttestationSummary, LiftReportInput, LiftedTrustIrFunctionSummary,
    ProofGradeReleaseTranscriptRowInput, TargetConsumerDigestBinding,
    VerifiedBinaryFunctionSummary, VerifyBinaryReportInput, apply_configured_trust_profile,
    backend_status, binary_replay_fields_from_report, binary_solver_result_report,
    binary_solver_result_report_with_replay, binary_verify_shared_verification_summary,
    bounded_machine_architecture, build_binary_cli_proof_grade_gate, build_convert_cli_gate,
    build_convert_cli_gate_with_loader, build_decompile_report, build_exploit_evidence_gate,
    build_exploit_find_report, build_lift_report, build_verify_binary_report,
    checked_certificate_import_proof_grade_release_transcript_row_with_target_consumer,
    checked_certificate_import_release_transcript_binding,
    convert_checked_certificate_blocker_code, convert_checked_certificate_loader_failure_report,
    convert_checked_certificate_release_blocker,
    convert_checked_certificate_source_backpropagation_gate_for_decompilation_artifact,
    convert_should_fail, convert_usage_text, count_vc_kinds, decompile_output_kind,
    decompile_should_fail, decompile_target_validation_blocker_code, decompile_usage_text,
    describe_capability, describe_config_source, dispatch_binary_vcs_with_replay_evidence,
    exploit_analyzer_stage_records, exploit_claim_capture_records, exploit_find_should_fail,
    exploit_find_usage_text, lift_report_input_from_result, lift_should_fail, lift_usage_text,
    load_convert_checked_certificate_loader_report,
    load_convert_checked_certificate_loader_report_with_external_checker,
    load_convert_checked_certificate_loader_report_with_production_export, load_doctor_config,
    load_proof_grade_release_transcript_report, parse_convert_target, parse_decompile_target,
    parse_exploit_find_args, parse_lift_entry,
    produce_convert_checked_certificate_artifacts_for_decompilation,
    proof_grade_release_transcript_report, proof_grade_release_transcript_row_binding_digest,
    proof_grade_release_transcript_row_report, release_transcript_candidate_commit,
    release_transcript_candidate_commit_in, render_convert_terminal,
    render_convert_terminal_with_checked_certificate_loader, render_decompile_terminal,
    render_exploit_find_terminal, render_lift_terminal, render_verify_binary_terminal,
    rewrite_request_error, run_convert_subcommand, run_decompile_subcommand,
    run_exploit_find_subcommand, run_lift_subcommand, run_subcommand, run_verify_binary_subcommand,
    scan_decompilation_proof_export_candidates, select_verify_binary_solver,
    serialize_convert_json, serialize_convert_json_with_checked_certificate_loader,
    serialize_decompile_json_with_checked_certificate_loader, serialize_exploit_find_json,
    serialize_verify_binary_json, serialize_verify_binary_json_with_route, solver_route_diagnostic,
    target_blocker_mentions_checked_certificate, target_consumer_digest_binding_for_report,
    target_proof_consumer_evidence_from_output, verifier_suite_statuses,
    verify_binary_report_input_from_result, verify_binary_should_fail, verify_binary_usage_text,
    write_and_readback_proof_grade_release_transcript_artifact,
    write_and_readback_proof_grade_release_transcript_rows,
    write_proof_grade_release_transcript_report,
};
use crate::cli::{parse_subcommand_args, usage_text};
use crate::config::{DEFAULT_CODEGEN_BACKEND, DEFAULT_TRUST_PROFILE, TrustConfig};
use crate::pipeline::{
    CargoRustflags, LinkedTrustCargoSurfaceKind, LinkedTrustSurfaceToolStatus,
    LinkedTrustSurfaceToolStatusKind, LinkedTrustToolchainStatus, LinkedTrustToolchainStatusKind,
    NativeRustcDiscovery, NativeRustcDiscoverySource, build_native_command,
    build_native_command_with_json_transport, compiler_help_supports_option,
    find_trust_verify_disable_arg, find_trust_verify_disable_in_rustflags, has_output_path_flag,
    is_cargo_program, level_to_num, merged_cargo_rustflags_with_options, merged_rustflags,
    merged_rustflags_with_backend, merged_rustflags_with_json_transport,
    merged_rustflags_with_options, parse_compiler_stderr, select_native_rustc_discovery,
    trust_verify_disable_diagnostic,
};
use crate::project_root::resolve_project_root_from;
use crate::report::{ReportConfig, VerificationReport, html_escape, parse_vc_kind};
use crate::types::{
    BinaryLiftStatus, BinarySolverResultReport, BinaryVcKindCount, DecompileBinaryEvidenceReport,
    DecompileFunctionReport, DecompileProofGradeEvidenceReport, DecompileReport, DecompileTarget,
    ExploitFindStatus, ExploitFindTarget, OutputFormat, ProofGradeReleaseTranscriptRowReport,
    Subcommand, VerificationOutcome, VerificationResult, parse_trust_note,
    transport_to_verification_result,
};
use crate::unicode_command_arguments;
use crate::verify_binary_evidence::{
    CheckedCertificateImportReport, EXACT_REPLAY_BYTE_RANGE_FACT_DIAGNOSTIC_PREFIX,
    EXACT_REPLAY_CONTROL_FLOW_FACT_DIAGNOSTIC_PREFIX,
    EXACT_REPLAY_MEMORY_EFFECT_FACT_DIAGNOSTIC_PREFIX,
    EXACT_REPLAY_SLICE_ATTESTATION_ACCEPTED_DIAGNOSTIC,
    EXACT_REPLAY_TRANSCRIPT_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX,
    EXACT_REPLAY_WITNESS_ARTIFACT_DIGEST_DIAGNOSTIC,
    EXACT_REPLAY_WITNESS_BINDING_ACCEPTED_DIAGNOSTIC,
    EXACT_REPLAY_WITNESS_CONTROL_FLOW_CAPABILITY_DIAGNOSTIC,
    EXACT_REPLAY_WITNESS_EXECUTED_RANGE_DIAGNOSTIC,
    EXACT_REPLAY_WITNESS_INSTRUCTION_BYTES_DIAGNOSTIC,
    EXACT_REPLAY_WITNESS_MEMORY_EFFECT_DIAGNOSTIC, EXACT_REPLAY_WITNESS_SELECTED_IMAGE_DIAGNOSTIC,
    NormalizedSolverProofExportArtifactInput, VerifyBinaryEvidence,
    build_normalized_solver_proof_export_artifact,
    checked_certificate_replay_digest_identity_record, dispatch_binary_vcs_with_evidence,
    dispatch_exact_replay_transcript_artifact_digest,
    persist_normalized_solver_proof_export_artifact,
};

struct TestEnvVar {
    key: &'static str,
    old: Option<std::ffi::OsString>,
}

impl TestEnvVar {
    #[allow(unknown_lints, env_mutation)] // lock-serialized env helper (see the acquired *_ENV_LOCK); the single audited boundary.
    fn set(key: &'static str, value: &str) -> Self {
        let old = std::env::var_os(key);
        std::env::set_var(key, value);
        Self { key, old }
    }

    #[allow(unknown_lints, env_mutation)] // lock-serialized env helper (see the acquired *_ENV_LOCK); the single audited boundary.
    fn unset(key: &'static str) -> Self {
        let old = std::env::var_os(key);
        std::env::remove_var(key);
        Self { key, old }
    }
}

impl Drop for TestEnvVar {
    #[allow(unknown_lints, env_mutation)] // lock-serialized env helper (see the acquired *_ENV_LOCK); the single audited boundary.
    fn drop(&mut self) {
        if let Some(old) = self.old.take() {
            std::env::set_var(self.key, old);
        } else {
            std::env::remove_var(self.key);
        }
    }
}

fn verify_binary_evidence_for_vcs(required_vcs: usize) -> VerifyBinaryEvidence {
    VerifyBinaryEvidence::from_solver_dispatch_records(required_vcs, Vec::new())
}

fn canonical_binary_dispatch_fields(record: &mut SolverDispatchRecord) {
    let vc = binary_vc(VcKind::DivisionByZero);
    record.origin = Some(BinaryOrigin {
        binary_path: Some("fixtures/tiny.bin".to_string()),
        function_entry: Some(0x401000),
        instruction_address: 0x401010,
        instruction_size: Some(1),
        encoding: Some(0x90),
        instruction_bytes: vec![0x90],
        source: Some(SourceSpan::binary_address(0x401010)),
    });
    record.vc_kind = Some(vc.kind.clone());
    record.vc = Some(SerializableVc::from_vc(&vc));
    record.binary_artifact_digest_identity = Some(fixture_binary_artifact_digest_identity());
}

fn checked_binary_dispatch(id: &str, function: &str) -> SolverDispatchRecord {
    let mut record = SolverDispatchRecord {
        id: id.to_string(),
        function: Some(function.to_string()),
        solver: "ay-incremental".to_string(),
        backend: Some("ay-incremental".to_string()),
        status: SolverDispatchStatus::Unsat,
        query_semantics: SolverQuerySemantics::SatIsCounterexample,
        replay: ReplayStatus::Replayed,
        certificate: ProofCertificateStatus::Checked {
            checker: "fixture-checker".to_string(),
            format: "lfsc".to_string(),
            sha256: Some("0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef".into()),
        },
        diagnostics: vec![EXACT_REPLAY_SLICE_ATTESTATION_ACCEPTED_DIAGNOSTIC.to_string()],
        ..Default::default()
    };
    canonical_binary_dispatch_fields(&mut record);
    record
}

fn canonical_sha_checked_binary_dispatch(id: &str, function: &str) -> SolverDispatchRecord {
    let mut record = checked_binary_dispatch(id, function);
    if let ProofCertificateStatus::Checked { sha256, .. } = &mut record.certificate {
        *sha256 = Some("0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef".into());
    }
    record
}

fn raw_solver_binary_dispatch(id: &str, function: &str) -> SolverDispatchRecord {
    let mut record = SolverDispatchRecord {
        id: id.to_string(),
        function: Some(function.to_string()),
        solver: "ay-incremental".to_string(),
        backend: Some("ay-incremental".to_string()),
        status: SolverDispatchStatus::Unsat,
        query_semantics: SolverQuerySemantics::SatIsCounterexample,
        replay: ReplayStatus::NotAttempted,
        certificate: ProofCertificateStatus::Present {
            format: "solver-native".to_string(),
            sha256: None,
            artifact_path: None,
        },
        result: Some(trust_types::VerificationResult::Proved {
            solver: "ay-incremental".into(),
            time_ms: 4,
            strength: trust_types::ProofStrength::smt_unsat(),
            proof_certificate: Some(vec![1, 2, 3, 4]),
            solver_warnings: None,
            native_proof_envelope: None,
        }),
        binary_artifact_digest_identity: Some(fixture_binary_artifact_digest_identity()),
        ..Default::default()
    };
    canonical_binary_dispatch_fields(&mut record);
    record
}

fn attach_normalized_proof_export_artifact(
    root: &Path,
    dispatch: &mut SolverDispatchRecord,
    canonical_vc_bytes: &[u8],
    proof_bytes: &[u8],
    replay_transcript_digest: Option<&str>,
    source_backpropagation_gate: &CheckedBinaryCertificateSourceBackpropagationGate,
) -> PathBuf {
    let artifact =
        build_normalized_solver_proof_export_artifact(NormalizedSolverProofExportArtifactInput {
            dispatch,
            canonical_vc_bytes,
            format: "lrat",
            proof_bytes: proof_bytes.to_vec(),
            solver_version: None,
            exported_at_unix_ms: 1_777_070_400_000,
            replay_transcript_digest,
            source_backpropagation_gate,
        })
        .expect("normalized proof export artifact should build");
    let path = persist_normalized_solver_proof_export_artifact(root, &artifact)
        .expect("normalized proof export artifact should persist");
    dispatch.certificate = ProofCertificateStatus::Present {
        format: "lrat".to_string(),
        sha256: Some(trust_types::digest::stable_sha256_hex(proof_bytes)),
        artifact_path: Some(path.display().to_string()),
    };
    path
}

fn attach_decompile_normalized_proof_export_artifact(
    root: &Path,
    artifact: &mut trust_types::DecompilationArtifact,
    proof_bytes: &[u8],
    replay_transcript_digest: Option<&str>,
) {
    let scan = scan_decompilation_proof_export_candidates(artifact);
    let source_gate =
        convert_checked_certificate_source_backpropagation_gate_for_decompilation_artifact(
            artifact, &scan,
        );
    let dispatch = artifact
        .verification
        .solver_dispatch
        .get_mut(0)
        .expect("fixture decompilation artifact should carry one dispatch");
    let canonical_vc_bytes =
        serde_json::to_vec(dispatch.vc.as_ref().expect("fixture dispatch has canonical VC"))
            .expect("fixture VC should serialize");
    attach_normalized_proof_export_artifact(
        root,
        dispatch,
        &canonical_vc_bytes,
        proof_bytes,
        replay_transcript_digest,
        &source_gate,
    );
}

fn checked_certificate_only_binary_dispatch(id: &str, function: &str) -> SolverDispatchRecord {
    let mut record = SolverDispatchRecord {
        id: id.to_string(),
        function: Some(function.to_string()),
        solver: "ay-incremental".to_string(),
        backend: Some("ay-incremental".to_string()),
        status: SolverDispatchStatus::Unsat,
        query_semantics: SolverQuerySemantics::SatIsCounterexample,
        replay: ReplayStatus::NotAttempted,
        certificate: ProofCertificateStatus::Checked {
            checker: "fixture-checker".to_string(),
            format: "lfsc".to_string(),
            sha256: Some("0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef".into()),
        },
        ..Default::default()
    };
    canonical_binary_dispatch_fields(&mut record);
    record
}

fn checked_binary_dispatch_without_canonical_binding(
    id: &str,
    function: &str,
) -> SolverDispatchRecord {
    let mut record = checked_certificate_only_binary_dispatch(id, function);
    record.origin = None;
    record.vc_kind = None;
    record.vc = None;
    record
}

fn missing_checker_identity_binary_dispatch(id: &str, function: &str) -> SolverDispatchRecord {
    SolverDispatchRecord {
        id: id.to_string(),
        function: Some(function.to_string()),
        solver: "ay-incremental".to_string(),
        backend: Some("ay-incremental".to_string()),
        status: SolverDispatchStatus::Unsat,
        query_semantics: SolverQuerySemantics::SatIsCounterexample,
        replay: ReplayStatus::NotAttempted,
        certificate: ProofCertificateStatus::Checked {
            checker: " ".to_string(),
            format: "lfsc".to_string(),
            sha256: Some(format!("{id}-sha256")),
        },
        ..Default::default()
    }
}

fn sat_unreplayed_binary_dispatch(id: &str, function: &str) -> SolverDispatchRecord {
    SolverDispatchRecord {
        id: id.to_string(),
        function: Some(function.to_string()),
        solver: "ay-incremental".to_string(),
        backend: Some("ay-incremental".to_string()),
        status: SolverDispatchStatus::Sat,
        query_semantics: SolverQuerySemantics::SatIsCounterexample,
        replay: ReplayStatus::NotAttempted,
        certificate: ProofCertificateStatus::NotRequested,
        ..Default::default()
    }
}

fn sat_replayed_binary_dispatch(id: &str, function: &str) -> SolverDispatchRecord {
    SolverDispatchRecord {
        id: id.to_string(),
        function: Some(function.to_string()),
        solver: "ay-incremental".to_string(),
        backend: Some("ay-incremental".to_string()),
        status: SolverDispatchStatus::Sat,
        query_semantics: SolverQuerySemantics::SatIsCounterexample,
        replay: ReplayStatus::Replayed,
        certificate: ProofCertificateStatus::NotRequested,
        ..Default::default()
    }
}

fn unsupported_binary_dispatch(id: &str, function: &str) -> SolverDispatchRecord {
    SolverDispatchRecord {
        id: id.to_string(),
        function: Some(function.to_string()),
        solver: "ay-incremental".to_string(),
        backend: Some("ay-incremental".to_string()),
        status: SolverDispatchStatus::Unsupported,
        query_semantics: SolverQuerySemantics::SatIsCounterexample,
        replay: ReplayStatus::NotAttempted,
        certificate: ProofCertificateStatus::NotRequested,
        ..Default::default()
    }
}

struct RawProofBackend;

impl VerificationBackend for RawProofBackend {
    fn name(&self) -> &str {
        "raw-proof-fixture"
    }

    fn can_handle(&self, _vc: &VerificationCondition) -> bool {
        true
    }

    fn verify(&self, _vc: &VerificationCondition) -> trust_types::VerificationResult {
        trust_types::VerificationResult::Proved {
            solver: "raw-proof-fixture".into(),
            time_ms: 7,
            strength: trust_types::ProofStrength::smt_unsat(),
            proof_certificate: Some(b"raw solver proof bytes".to_vec()),
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }
}

struct ReplaySatBackend;

impl VerificationBackend for ReplaySatBackend {
    fn name(&self) -> &str {
        "replay-sat-fixture"
    }

    fn can_handle(&self, _vc: &VerificationCondition) -> bool {
        true
    }

    fn verify(&self, _vc: &VerificationCondition) -> trust_types::VerificationResult {
        trust_types::VerificationResult::Failed {
            solver: "replay-sat-fixture".into(),
            time_ms: 13,
            counterexample: Some(replay_test_counterexample("bb0@0x401010")),
        }
    }
}

struct ReplaySatProgramPointBackend(&'static str);

impl VerificationBackend for ReplaySatProgramPointBackend {
    fn name(&self) -> &str {
        "replay-sat-program-point-fixture"
    }

    fn can_handle(&self, _vc: &VerificationCondition) -> bool {
        true
    }

    fn verify(&self, _vc: &VerificationCondition) -> trust_types::VerificationResult {
        trust_types::VerificationResult::Failed {
            solver: "replay-sat-program-point-fixture".into(),
            time_ms: 13,
            counterexample: Some(replay_test_counterexample(self.0)),
        }
    }
}

struct ReplaySatCallReturnBackend;

impl VerificationBackend for ReplaySatCallReturnBackend {
    fn name(&self) -> &str {
        "replay-sat-call-return-fixture"
    }

    fn can_handle(&self, _vc: &VerificationCondition) -> bool {
        true
    }

    fn verify(&self, _vc: &VerificationCondition) -> trust_types::VerificationResult {
        trust_types::VerificationResult::Failed {
            solver: "replay-sat-call-return-fixture".into(),
            time_ms: 17,
            counterexample: Some(replay_test_call_return_counterexample()),
        }
    }
}

fn binary_vc(kind: VcKind) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: "main".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    }
}

fn fixture_binary_artifact_digest_identity() -> BinaryArtifactDigestIdentity {
    let digest = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
    BinaryArtifactDigestIdentity {
        root_artifact_digest: Some(BinaryArtifactDigest::sha256(digest)),
        selected_image: Some(BinarySelectedImageIdentity {
            file_offset: 0,
            file_size: 64,
            sha256: digest.to_string(),
        }),
    }
}

fn current_release_candidate_commit() -> String {
    release_transcript_candidate_commit().expect("release transcript tests run in a git checkout")
}

#[test]
fn release_transcript_candidate_identity_is_not_stale_across_repositories_or_head_changes() {
    fn commit(repo: &Path, file: &str, contents: &str, message: &str) -> String {
        std::fs::write(repo.join(file), contents).expect("write repository fixture");
        let add = Command::new("git")
            .arg("-C")
            .arg(repo)
            .args(["add", file])
            .status()
            .expect("run git add");
        assert!(add.success());
        let commit = Command::new("git")
            .arg("-C")
            .arg(repo)
            .args([
                "-c",
                "user.name=Trust Test",
                "-c",
                "user.email=trust-test@example.invalid",
                "commit",
                "-m",
                message,
            ])
            .status()
            .expect("run git commit");
        assert!(commit.success());
        release_transcript_candidate_commit_in(repo).expect("read committed HEAD")
    }

    let root = temp_test_dir("release-transcript-multi-repo-identity");
    let first_repo = root.join("first");
    let second_repo = root.join("second");
    for repo in [&first_repo, &second_repo] {
        std::fs::create_dir_all(repo).expect("create repository fixture");
        let init =
            Command::new("git").arg("-C").arg(repo).arg("init").status().expect("run git init");
        assert!(init.success());
    }

    let first_head = commit(&first_repo, "identity.txt", "first\n", "first identity");
    let second_head = commit(&second_repo, "identity.txt", "second\n", "second identity");
    assert_ne!(first_head, second_head);
    assert_eq!(release_transcript_candidate_commit_in(&first_repo), Some(first_head.clone()));
    assert_eq!(release_transcript_candidate_commit_in(&second_repo), Some(second_head));

    let advanced_first = commit(&first_repo, "identity.txt", "advanced\n", "advance identity");
    assert_ne!(advanced_first, first_head);
    assert_eq!(
        release_transcript_candidate_commit_in(&first_repo),
        Some(advanced_first),
        "same-process release provenance must observe a later HEAD in the same repository"
    );
    assert_eq!(release_transcript_candidate_commit_in(&root.join("not-a-repo")), None);
    std::fs::remove_dir_all(root).expect("remove repository fixtures");
}

#[test]
fn test_proof_grade_release_transcript_row_accepts_fully_populated_typed_evidence() {
    let candidate_commit = current_release_candidate_commit();
    let vc_sha256 = trust_types::digest::stable_sha256_hex(b"release transcript vc");
    let certificate_sha256 = trust_types::digest::stable_sha256_hex(b"release transcript checked certificate");
    let replay_sha256 = trust_types::digest::stable_sha256_hex(b"release transcript machine replay");
    let provenance_sha256 = trust_types::digest::stable_sha256_hex(b"release transcript provenance");
    let target_evidence_sha256 = trust_types::digest::stable_sha256_hex(b"release transcript target evidence");
    let target_binding_sha256 = trust_types::digest::stable_sha256_hex(b"release transcript target binding");
    let exact_source_sha256 = trust_types::digest::stable_sha256_hex(b"release transcript exact source ownership");
    let type_ownership_sha256 = trust_types::digest::stable_sha256_hex(b"release transcript type ownership");
    let target_consumer = TargetConsumerDigestBinding {
        required: true,
        evidence_sha256: Some(target_evidence_sha256.clone()),
        binding_sha256: Some(target_binding_sha256.clone()),
    };

    let row = proof_grade_release_transcript_row_report(ProofGradeReleaseTranscriptRowInput {
        evidence_origin: "targo_trust_release_export",
        candidate_commit: Some(candidate_commit.clone()),
        binary_artifact_digest_identity: &fixture_binary_artifact_digest_identity(),
        vc_sha256s: vec![vc_sha256.clone()],
        checked_certificate_sha256s: vec![certificate_sha256.clone()],
        replay_transcript_sha256s: vec![replay_sha256.clone()],
        provenance_sha256s: vec![provenance_sha256.clone()],
        unsupported_ledgers_empty: true,
        target_consumer: &target_consumer,
        exact_source_ownership_sha256: Some(exact_source_sha256.clone()),
        type_ownership_sha256: Some(type_ownership_sha256.clone()),
        aarch64_ordering_monitor_evidence: Vec::new(),
    });

    assert!(row.accepted, "{:?}", row.blockers);
    assert_eq!(row.status, "accepted");
    assert_eq!(row.rejection_reason, None);
    assert_eq!(row.schema_version, "trust.proof-grade-row.v1");
    assert_eq!(row.row_type, "binary-decompilation-proof-grade");
    assert_eq!(row.candidate_commit.as_deref(), Some(candidate_commit.as_str()));
    assert_eq!(row.proof_required_vc_count, 1);
    assert_eq!(
        row.binary_digest.as_deref(),
        Some("sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef")
    );
    let selected_image = row.selected_image.as_ref().expect("selected image row");
    assert_eq!(selected_image.identity, "file_offset=0:file_size=64");
    assert_eq!(
        selected_image.digest,
        "sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
    );
    assert_eq!(row.vc_digests.len(), 1);
    assert_eq!(row.vc_digests[0].schema_version, "trust.vc-digest-entry.v1");
    assert_eq!(row.vc_digests[0].artifact_kind, "verification-condition");
    assert_eq!(row.vc_digests[0].digest_algorithm, "sha256");
    assert_eq!(row.vc_digests[0].digest, format!("sha256:{vc_sha256}"));
    assert_eq!(row.vc_digests[0].candidate_commit, candidate_commit);
    assert_eq!(
        row.vc_digests[0].binary_digest,
        "sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
    );
    assert_eq!(row.vc_digests[0].selected_image, selected_image.clone());
    assert_eq!(row.vc_digests[0].inventory_index, 0);
    assert_eq!(row.vc_digests[0].inventory_count, 1);
    assert_eq!(row.vc_digests[0].vc_id, "proof-required-vc-0");
    assert_eq!(row.checked_certificate_digests.len(), 1);
    assert_eq!(
        row.checked_certificate_digests[0].schema_version,
        "trust.checked-certificate-readback-digest-entry.v1"
    );
    assert_eq!(row.checked_certificate_digests[0].artifact_kind, "checked-certificate-readback");
    assert_eq!(row.checked_certificate_digests[0].digest_algorithm, "sha256");
    assert_eq!(row.checked_certificate_digests[0].digest, format!("sha256:{certificate_sha256}"));
    assert_eq!(row.checked_certificate_digests[0].vc_digest, row.vc_digests[0].digest);
    assert_eq!(row.checked_certificate_digests[0].certificate_role, "checked-certificate");
    assert_eq!(row.checked_certificate_digests[0].readback_status, "accepted");
    assert_eq!(row.replay_transcript_digests, vec![format!("sha256:{replay_sha256}")]);
    assert_eq!(row.provenance_artifact_digests, vec![format!("sha256:{provenance_sha256}")]);
    assert!(row.unsupported_ledgers_empty);
    assert_eq!(
        row.target_proof_consumer_artifact_digests,
        vec![format!("sha256:{target_evidence_sha256}"), format!("sha256:{target_binding_sha256}")]
    );
    assert_eq!(row.exact_source_ownership_evidence.status, "accepted");
    let expected_exact_source_digest = format!("sha256:{exact_source_sha256}");
    assert_eq!(
        row.exact_source_ownership_evidence.digest.as_deref(),
        Some(expected_exact_source_digest.as_str())
    );
    assert_eq!(row.type_ownership_evidence.status, "accepted");
    let expected_type_ownership_digest = format!("sha256:{type_ownership_sha256}");
    assert_eq!(
        row.type_ownership_evidence.digest.as_deref(),
        Some(expected_type_ownership_digest.as_str())
    );
    assert!(row.aarch64_ordering_monitor_evidence.is_empty());
    let expected_release_binding_digest = proof_grade_release_transcript_row_binding_digest(&row)
        .expect("accepted row should have canonical row binding digest");
    assert_eq!(
        row.release_transcript_binding_digest.as_deref(),
        Some(expected_release_binding_digest.as_str())
    );
    assert!(row.blockers.is_empty());

    let transcript = proof_grade_release_transcript_report(std::slice::from_ref(&row));
    assert_eq!(transcript.schema_version, "trust.proof-grade-release-transcript.v1");
    assert_eq!(transcript.accepted_proof_grade_rows, vec![row]);
    assert!(transcript.blocked_proof_grade_rows.is_empty());
}

#[test]
fn test_proof_grade_release_transcript_row_accepts_all_vc_checked_certificate_inventory() {
    let candidate_commit = current_release_candidate_commit();
    let vc_sha256s =
        vec![trust_types::digest::stable_sha256_hex(b"release transcript vc 0"), trust_types::digest::stable_sha256_hex(b"release transcript vc 1")];
    let certificate_sha256s = vec![
        trust_types::digest::stable_sha256_hex(b"release transcript checked certificate 0"),
        trust_types::digest::stable_sha256_hex(b"release transcript checked certificate 1"),
    ];
    let target_consumer = TargetConsumerDigestBinding {
        required: true,
        evidence_sha256: Some(trust_types::digest::stable_sha256_hex(b"release transcript all-vc target evidence")),
        binding_sha256: Some(trust_types::digest::stable_sha256_hex(b"release transcript all-vc target binding")),
    };

    let row = proof_grade_release_transcript_row_report(ProofGradeReleaseTranscriptRowInput {
        evidence_origin: "targo_trust_release_export",
        candidate_commit: Some(candidate_commit),
        binary_artifact_digest_identity: &fixture_binary_artifact_digest_identity(),
        vc_sha256s: vc_sha256s.clone(),
        checked_certificate_sha256s: certificate_sha256s.clone(),
        replay_transcript_sha256s: vec![trust_types::digest::stable_sha256_hex(b"release transcript all-vc replay")],
        provenance_sha256s: vec![trust_types::digest::stable_sha256_hex(b"release transcript all-vc provenance")],
        unsupported_ledgers_empty: true,
        target_consumer: &target_consumer,
        exact_source_ownership_sha256: Some(trust_types::digest::stable_sha256_hex(
            b"release transcript all-vc exact source ownership",
        )),
        type_ownership_sha256: Some(trust_types::digest::stable_sha256_hex(b"release transcript all-vc type ownership")),
        aarch64_ordering_monitor_evidence: Vec::new(),
    });

    assert!(row.accepted, "{:?}", row.blockers);
    assert_eq!(row.proof_required_vc_count, 2);
    assert_eq!(row.vc_digests.len(), 2);
    assert_eq!(row.checked_certificate_digests.len(), 2);
    for inventory_index in 0..2 {
        assert_eq!(row.vc_digests[inventory_index].inventory_index, inventory_index);
        assert_eq!(row.vc_digests[inventory_index].inventory_count, 2);
        assert_eq!(
            row.vc_digests[inventory_index].digest,
            format!("sha256:{}", vc_sha256s[inventory_index])
        );
        assert_eq!(
            row.checked_certificate_digests[inventory_index].inventory_index,
            inventory_index
        );
        assert_eq!(row.checked_certificate_digests[inventory_index].inventory_count, 2);
        assert_eq!(
            row.checked_certificate_digests[inventory_index].digest,
            format!("sha256:{}", certificate_sha256s[inventory_index])
        );
        assert_eq!(
            row.checked_certificate_digests[inventory_index].vc_digest,
            row.vc_digests[inventory_index].digest
        );
    }

    let transcript = proof_grade_release_transcript_report(std::slice::from_ref(&row));
    assert_eq!(transcript.accepted_proof_grade_rows, vec![row]);
    assert!(transcript.blocked_proof_grade_rows.is_empty());
}

#[test]
fn test_proof_grade_release_transcript_digest_tampering_rejects() {
    let target_consumer = TargetConsumerDigestBinding {
        required: true,
        evidence_sha256: Some(trust_types::digest::stable_sha256_hex(b"tamper target evidence")),
        binding_sha256: Some(trust_types::digest::stable_sha256_hex(b"tamper target binding")),
    };
    let mut row = proof_grade_release_transcript_row_report(ProofGradeReleaseTranscriptRowInput {
        evidence_origin: "targo_trust_release_export",
        candidate_commit: Some(current_release_candidate_commit()),
        binary_artifact_digest_identity: &fixture_binary_artifact_digest_identity(),
        vc_sha256s: vec![trust_types::digest::stable_sha256_hex(b"tamper vc")],
        checked_certificate_sha256s: vec![trust_types::digest::stable_sha256_hex(b"tamper checked certificate")],
        replay_transcript_sha256s: vec![trust_types::digest::stable_sha256_hex(b"tamper replay")],
        provenance_sha256s: vec![trust_types::digest::stable_sha256_hex(b"tamper provenance")],
        unsupported_ledgers_empty: true,
        target_consumer: &target_consumer,
        exact_source_ownership_sha256: Some(trust_types::digest::stable_sha256_hex(b"tamper exact source ownership")),
        type_ownership_sha256: Some(trust_types::digest::stable_sha256_hex(b"tamper type ownership")),
        aarch64_ordering_monitor_evidence: Vec::new(),
    });
    assert!(row.accepted, "{:?}", row.blockers);
    row.release_transcript_binding_digest = Some(format!("sha256:{}", "0".repeat(64)));

    let transcript = proof_grade_release_transcript_report(std::slice::from_ref(&row));

    assert!(transcript.accepted_proof_grade_rows.is_empty());
    assert_eq!(transcript.blocked_proof_grade_rows.len(), 1);
    let blocked = &transcript.blocked_proof_grade_rows[0];
    assert!(!blocked.accepted);
    assert!(
        blocked
            .blockers
            .iter()
            .any(|blocker| blocker
                .contains("does not match canonical trust.proof-grade-row-binding.v1")),
        "{:?}",
        blocked.blockers
    );
}

#[test]
fn test_proof_grade_release_transcript_row_blocks_non_empty_accepted_blockers() {
    let target_consumer = TargetConsumerDigestBinding {
        required: true,
        evidence_sha256: Some(trust_types::digest::stable_sha256_hex(b"blocker target evidence")),
        binding_sha256: Some(trust_types::digest::stable_sha256_hex(b"blocker target binding")),
    };
    let mut row = proof_grade_release_transcript_row_report(ProofGradeReleaseTranscriptRowInput {
        evidence_origin: "targo_trust_release_export",
        candidate_commit: Some(current_release_candidate_commit()),
        binary_artifact_digest_identity: &fixture_binary_artifact_digest_identity(),
        vc_sha256s: vec![trust_types::digest::stable_sha256_hex(b"blocker vc")],
        checked_certificate_sha256s: vec![trust_types::digest::stable_sha256_hex(b"blocker checked certificate")],
        replay_transcript_sha256s: vec![trust_types::digest::stable_sha256_hex(b"blocker replay")],
        provenance_sha256s: vec![trust_types::digest::stable_sha256_hex(b"blocker provenance")],
        unsupported_ledgers_empty: true,
        target_consumer: &target_consumer,
        exact_source_ownership_sha256: Some(trust_types::digest::stable_sha256_hex(b"blocker exact source ownership")),
        type_ownership_sha256: Some(trust_types::digest::stable_sha256_hex(b"blocker type ownership")),
        aarch64_ordering_monitor_evidence: Vec::new(),
    });
    assert!(row.accepted, "{:?}", row.blockers);
    row.blockers.push("injected release blocker".to_string());
    row.release_transcript_binding_digest = proof_grade_release_transcript_row_binding_digest(&row);

    let transcript = proof_grade_release_transcript_report(std::slice::from_ref(&row));

    assert!(transcript.accepted_proof_grade_rows.is_empty());
    let blocked = transcript.blocked_proof_grade_rows.first().expect("blocked row");
    assert!(
        blocked
            .blockers
            .iter()
            .any(|blocker| blocker == "accepted row blockers must be an empty list"),
        "{:?}",
        blocked.blockers
    );
}

#[test]
fn test_proof_grade_release_transcript_row_blocks_stale_candidate_commit() {
    let target_consumer = TargetConsumerDigestBinding {
        required: true,
        evidence_sha256: Some(trust_types::digest::stable_sha256_hex(b"stale target evidence")),
        binding_sha256: Some(trust_types::digest::stable_sha256_hex(b"stale target binding")),
    };

    let row = proof_grade_release_transcript_row_report(ProofGradeReleaseTranscriptRowInput {
        evidence_origin: "targo_trust_release_export",
        candidate_commit: Some("0".repeat(40)),
        binary_artifact_digest_identity: &fixture_binary_artifact_digest_identity(),
        vc_sha256s: vec![trust_types::digest::stable_sha256_hex(b"stale vc")],
        checked_certificate_sha256s: vec![trust_types::digest::stable_sha256_hex(b"stale checked certificate")],
        replay_transcript_sha256s: vec![trust_types::digest::stable_sha256_hex(b"stale replay")],
        provenance_sha256s: vec![trust_types::digest::stable_sha256_hex(b"stale provenance")],
        unsupported_ledgers_empty: true,
        target_consumer: &target_consumer,
        exact_source_ownership_sha256: Some(trust_types::digest::stable_sha256_hex(b"stale exact source ownership")),
        type_ownership_sha256: Some(trust_types::digest::stable_sha256_hex(b"stale type ownership")),
        aarch64_ordering_monitor_evidence: Vec::new(),
    });

    assert!(!row.accepted);
    assert_eq!(row.release_transcript_binding_digest, None);
    assert!(
        row.blockers.iter().any(|blocker| {
            blocker.contains("candidate_commit does not match the current release candidate commit")
        }),
        "{:?}",
        row.blockers
    );
}

#[test]
fn test_proof_grade_release_transcript_row_blocks_missing_target_consumer_fields() {
    let target_consumer = TargetConsumerDigestBinding {
        required: false,
        evidence_sha256: None,
        binding_sha256: None,
    };

    let row = proof_grade_release_transcript_row_report(ProofGradeReleaseTranscriptRowInput {
        evidence_origin: "targo_trust_release_export",
        candidate_commit: Some(current_release_candidate_commit()),
        binary_artifact_digest_identity: &fixture_binary_artifact_digest_identity(),
        vc_sha256s: vec![trust_types::digest::stable_sha256_hex(b"missing target consumer vc")],
        checked_certificate_sha256s: vec![trust_types::digest::stable_sha256_hex(
            b"missing target consumer checked certificate",
        )],
        replay_transcript_sha256s: vec![trust_types::digest::stable_sha256_hex(b"missing target consumer replay")],
        provenance_sha256s: vec![trust_types::digest::stable_sha256_hex(b"missing target consumer provenance")],
        unsupported_ledgers_empty: true,
        target_consumer: &target_consumer,
        exact_source_ownership_sha256: Some(trust_types::digest::stable_sha256_hex(
            b"missing target consumer exact source ownership",
        )),
        type_ownership_sha256: Some(trust_types::digest::stable_sha256_hex(b"missing target consumer type ownership")),
        aarch64_ordering_monitor_evidence: Vec::new(),
    });

    assert!(!row.accepted);
    assert_eq!(row.release_transcript_binding_digest, None);
    let blockers = row.blockers.join("\n");
    for expected in [
        "target proof-consumer evidence digest is missing",
        "target proof-consumer binding digest is missing",
        "target_proof_consumer_artifact_digests must be a non-empty list",
        "release_transcript_binding_digest cannot be computed",
    ] {
        assert!(blockers.contains(expected), "missing `{expected}` in {blockers}");
    }
}

#[test]
fn test_proof_grade_release_transcript_row_blocks_missing_artifact_binding() {
    let target_consumer = TargetConsumerDigestBinding {
        required: true,
        evidence_sha256: Some(trust_types::digest::stable_sha256_hex(b"missing binding target evidence")),
        binding_sha256: Some(trust_types::digest::stable_sha256_hex(b"missing binding target binding")),
    };
    let mut row = proof_grade_release_transcript_row_report(ProofGradeReleaseTranscriptRowInput {
        evidence_origin: "targo_trust_release_export",
        candidate_commit: Some(current_release_candidate_commit()),
        binary_artifact_digest_identity: &fixture_binary_artifact_digest_identity(),
        vc_sha256s: vec![trust_types::digest::stable_sha256_hex(b"missing binding vc")],
        checked_certificate_sha256s: vec![trust_types::digest::stable_sha256_hex(b"missing binding checked certificate")],
        replay_transcript_sha256s: vec![trust_types::digest::stable_sha256_hex(b"missing binding replay")],
        provenance_sha256s: vec![trust_types::digest::stable_sha256_hex(b"missing binding provenance")],
        unsupported_ledgers_empty: true,
        target_consumer: &target_consumer,
        exact_source_ownership_sha256: Some(trust_types::digest::stable_sha256_hex(b"missing binding exact source ownership")),
        type_ownership_sha256: Some(trust_types::digest::stable_sha256_hex(b"missing binding type ownership")),
        aarch64_ordering_monitor_evidence: Vec::new(),
    });
    assert!(row.accepted, "{:?}", row.blockers);
    row.release_transcript_binding_digest = None;

    let transcript = proof_grade_release_transcript_report(std::slice::from_ref(&row));

    assert!(transcript.accepted_proof_grade_rows.is_empty());
    let blocked = transcript.blocked_proof_grade_rows.first().expect("blocked row");
    assert!(
        blocked
            .blockers
            .iter()
            .any(|blocker| blocker == "release_transcript_binding_digest is missing"),
        "{:?}",
        blocked.blockers
    );
}

#[test]
fn test_proof_grade_release_transcript_row_blocks_missing_transcript_critical_fields() {
    let target_consumer =
        TargetConsumerDigestBinding { required: true, evidence_sha256: None, binding_sha256: None };

    let row = proof_grade_release_transcript_row_report(ProofGradeReleaseTranscriptRowInput {
        evidence_origin: "targo_trust_release_export",
        candidate_commit: None,
        binary_artifact_digest_identity: &BinaryArtifactDigestIdentity::default(),
        vc_sha256s: Vec::new(),
        checked_certificate_sha256s: Vec::new(),
        replay_transcript_sha256s: Vec::new(),
        provenance_sha256s: Vec::new(),
        unsupported_ledgers_empty: false,
        target_consumer: &target_consumer,
        exact_source_ownership_sha256: None,
        type_ownership_sha256: None,
        aarch64_ordering_monitor_evidence: Vec::new(),
    });

    assert!(!row.accepted);
    assert_eq!(row.status, "blocked");
    assert!(row.rejection_reason.is_some());
    assert_eq!(row.candidate_commit, None);
    assert_eq!(row.proof_required_vc_count, 0);
    assert_eq!(row.binary_digest, None);
    assert_eq!(row.selected_image, None);
    assert!(row.vc_digests.is_empty());
    assert!(row.checked_certificate_digests.is_empty());
    assert!(row.replay_transcript_digests.is_empty());
    assert!(row.provenance_artifact_digests.is_empty());
    assert!(!row.unsupported_ledgers_empty);
    assert!(row.target_proof_consumer_artifact_digests.is_empty());
    assert_eq!(row.exact_source_ownership_evidence.status, "missing");
    assert_eq!(row.type_ownership_evidence.status, "missing");
    assert_eq!(row.release_transcript_binding_digest, None);

    let blockers = row.blockers.join("\n");
    for expected in [
        "candidate_commit is missing",
        "binary_digest is missing",
        "selected_image must identify the replayed image",
        "vc_digests must be a non-empty typed digest inventory",
        "checked_certificate_digests must be a non-empty typed digest inventory",
        "replay_transcript_digests must be a non-empty list",
        "provenance_artifact_digests must be a non-empty list",
        "unsupported_ledgers_empty must be true",
        "target proof-consumer evidence digest is missing",
        "target proof-consumer binding digest is missing",
        "target_proof_consumer_artifact_digests must be a non-empty list",
        "exact_source_ownership_evidence.digest is missing",
        "type_ownership_evidence.digest is missing",
        "release_transcript_binding_digest cannot be computed",
    ] {
        assert!(blockers.contains(expected), "missing `{expected}` in {blockers}");
    }

    let transcript = proof_grade_release_transcript_report(std::slice::from_ref(&row));
    assert!(transcript.accepted_proof_grade_rows.is_empty());
    assert_eq!(transcript.blocked_proof_grade_rows, vec![row]);
}

#[cfg(unix)]
#[test]
fn test_proof_grade_release_transcript_writes_synthetic_unit_fixture_from_typed_import_row() {
    let (dispatch, canonical_vc_bytes) =
        importable_binary_dispatch("synthetic-unit-release-transcript:vc0");
    let artifact = checked_binary_artifact_for_dispatch(&dispatch, &canonical_vc_bytes);
    let root = temp_test_dir("proof-grade-release-transcript-synthetic-unit");
    let path = persist_checked_certificate_artifact(&root, &artifact)
        .expect("checked artifact should persist");

    let (current_dispatch, _) =
        importable_binary_dispatch("synthetic-unit-release-transcript-current:vc0");
    let mut proof_evidence =
        VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![current_dispatch]);
    let mut import_report = proof_evidence
        .load_and_import_checked_certificate_artifacts([path.as_path()])
        .expect("checked artifact should load into typed import rows");
    let mut import_row = import_report.artifacts.remove(0);
    let replay_transcript_digest =
        trust_types::digest::stable_sha256_hex(b"synthetic unit proof-grade release replay transcript");
    import_row.manifest_identity_sha256 =
        Some(trust_types::digest::stable_sha256_hex(b"synthetic unit checked certificate manifest identity"));
    import_row.source_backpropagation_gate_sha256 =
        Some(trust_types::digest::stable_sha256_hex(b"synthetic unit source backpropagation gate identity"));
    import_row.source_backpropagation_gate = accepted_checked_source_gate();
    import_row.production_checker_evidence_sha256 =
        Some(trust_types::digest::stable_sha256_hex(b"synthetic unit production checker evidence"));
    import_row.production_checker_evidence_status = "present".to_string();
    import_row.replay_transcript_digest = Some(replay_transcript_digest.clone());
    import_row.replay_digest_identity = checked_certificate_replay_digest_identity_record(
        ReplayStatus::Replayed,
        Some(replay_transcript_digest),
        Some(import_row.binary_artifact_digest_identity.clone()),
    );

    let mut report =
        proof_grade_convert_report_with_source_provenance(exact_binary_source_provenance_summary());
    report.output_content = Some(accepted_trust_cg_target_proof_consumer_output(&dispatch.id));
    let target_evidence = target_proof_consumer_evidence_from_output(&report)
        .expect("synthetic target proof-consumer evidence should parse");
    let target_consumer =
        target_consumer_digest_binding_for_report(&report, Some(&target_evidence));

    let row = checked_certificate_import_proof_grade_release_transcript_row_with_target_consumer(
        Some("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".to_string()),
        &import_row,
        true,
        &target_consumer,
    );
    assert!(!row.accepted);
    assert_eq!(row.evidence_origin, "synthetic_fixture");
    assert!(
        row.blockers.iter().any(
            |blocker| blocker.contains("evidence_origin must be `targo_trust_release_export`")
        ),
        "{:?}",
        row.blockers
    );
    assert!(row.release_transcript_binding_digest.is_none());

    let transcript = proof_grade_release_transcript_report(std::slice::from_ref(&row));
    assert!(transcript.accepted_proof_grade_rows.is_empty());
    assert_eq!(transcript.blocked_proof_grade_rows.len(), 1);
    let json = serde_json::to_string_pretty(&transcript).expect("serialize transcript") + "\n";
    let actual: serde_json::Value =
        serde_json::from_str(&json).expect("generated transcript should parse");
    let expected: serde_json::Value = serde_json::from_str(include_str!(
        "fixtures/proof_grade_release_transcript_synthetic_unit_golden.json"
    ))
    .expect("parse synthetic unit release transcript golden");
    assert_eq!(actual, expected, "generated synthetic unit transcript:\n{json}");

    let output_path = root.join("proof-grade-release-transcript.json");
    write_proof_grade_release_transcript_report(&output_path, &transcript)
        .expect("transcript writer should persist JSON");
    let written: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(&output_path).expect("written transcript should be readable"),
    )
    .expect("written transcript should parse");
    assert_eq!(written, expected);

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn test_convert_json_exports_real_accepted_proof_grade_release_transcript_row() {
    let root = temp_test_dir("real-proof-grade-release-transcript");
    let proof_bytes = b"normalized real release proof payload";
    let replay_transcript_digest = trust_types::digest::stable_sha256_hex(b"real proof-grade release replay transcript");

    let (mut dispatch, _) = importable_binary_dispatch("real-release:vc0");
    dispatch.replay = ReplayStatus::Replayed;
    dispatch.diagnostics.push(format!(
        "{EXACT_REPLAY_TRANSCRIPT_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX}{replay_transcript_digest}"
    ));
    dispatch.certificate = ProofCertificateStatus::Present {
        format: "lrat".to_string(),
        sha256: Some(trust_types::digest::stable_sha256_hex(proof_bytes)),
        artifact_path: Some(root.join("placeholder.lrat").display().to_string()),
    };
    let mut decompile_artifact = trust_types::DecompilationArtifact {
        verification: trust_types::BinaryVerificationSummary {
            total_vcs: 1,
            proved: 1,
            solver_dispatch: vec![dispatch.clone()],
            ..Default::default()
        },
        reconstruction: trust_types::ReconstructionSummary {
            target: trust_types::DecompileTarget::TrustCg,
            validation: trust_types::ReconstructionValidationStatus::Validated,
            trust_level: trust_types::TrustLevel::ProofGrade,
            outputs: vec![trust_types::DecompiledOutput {
                target: trust_types::DecompileTarget::TrustCg,
                validation: trust_types::ReconstructionValidationStatus::Validated,
                trust_level: trust_types::TrustLevel::ProofGrade,
                diagnostics: vec!["target proof-consumer accepted".to_string()],
                ..Default::default()
            }],
            ..Default::default()
        },
        source_provenance: exact_binary_source_provenance_summary(),
        ..Default::default()
    };
    attach_decompile_normalized_proof_export_artifact(
        &root,
        &mut decompile_artifact,
        proof_bytes,
        Some(replay_transcript_digest.as_str()),
    );
    let checker = write_checker_fixture_script(
        &root,
        "real-release-checker.sh",
        "#!/bin/sh\nprintf 'real release checker ok'\n",
    );

    let produced = produce_convert_checked_certificate_artifacts_for_decompilation(
        &decompile_artifact,
        &root.join("checked-certs"),
        Some(checker.as_path()),
        1_777_070_405_000,
    );
    assert_eq!(produced.report.status, "exported", "{:#?}", produced.report);
    assert_eq!(produced.report.exported_artifacts, 1);
    assert!(produced.report.source_backpropagation_gate.source_backpropagation_allowed);
    let manifest_path = produced.report.manifest_path.clone().expect("manifest should be exported");
    let loader = load_convert_checked_certificate_loader_report_with_production_export(
        &[],
        std::slice::from_ref(&manifest_path),
        None,
        1_777_070_405_001,
        Some(produced.report.clone()),
    )
    .expect("production manifest should import for real release transcript");
    assert_eq!(loader.status, "loaded");
    assert_eq!(loader.requested_manifests, 1);
    assert_eq!(loader.readback_records.len(), 1);
    assert!(loader.readback_records[0].production_checked);
    assert_eq!(loader.readback_records[0].replay_digest_identity.status, "accepted");
    assert_eq!(
        loader.readback_records[0].replay_transcript_digest.as_deref(),
        Some(replay_transcript_digest.as_str())
    );
    assert!(loader.readback_records[0].source_backpropagation_gate.source_backpropagation_allowed);

    let mut report =
        proof_grade_convert_report_with_source_provenance(exact_binary_source_provenance_summary());
    report.output_content = Some(accepted_trust_cg_target_proof_consumer_output(&dispatch.id));
    report.production_proof_grade_evidence = Some(DecompileProofGradeEvidenceReport {
        schema_version: "targo-trust-decompile-production-proof-grade-evidence.v1".to_string(),
        producer: "trust-decompile::binary-release-gate".to_string(),
        artifact_trust_level: "proof_grade".to_string(),
        binary_verification_trust_level: "proof_grade".to_string(),
        binary_verification_status: "proved".to_string(),
        binary_replay: "replayed".to_string(),
        required_vcs: 1,
        proved_vcs: 1,
        checked_certificate_identity: true,
        exact_replay_identity: true,
        binary_artifact_digest_identity: true,
        exact_source_provenance: true,
        reconstruction_accepted: true,
        target_validation_accepted: true,
        unsupported_ledger_empty: true,
    });

    let json = serialize_convert_json_with_checked_certificate_loader(&report, loader)
        .expect("serialize convert JSON with real release transcript");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse convert JSON");
    let transcript = &value["proof_grade_release_transcript"];
    assert_eq!(transcript["blocked_proof_grade_rows"], serde_json::Value::Null);
    let row = &transcript["accepted_proof_grade_rows"][0];

    assert_eq!(value["conversion_gate"]["accepted"], true, "{value}");
    assert_eq!(value["checked_certificate_readback"]["proof_grade_release_accepted"], true);
    assert_eq!(row["accepted"], true);
    assert_eq!(row["status"], "accepted");
    assert_eq!(row["rejection_reason"], serde_json::Value::Null);
    assert_eq!(row["evidence_origin"], "targo_trust_release_export");
    let expected_candidate_commit = current_release_candidate_commit();
    assert_eq!(row["candidate_commit"].as_str(), Some(expected_candidate_commit.as_str()));
    assert_eq!(row["proof_required_vc_count"], 1);
    assert_eq!(row["vc_digests"][0]["schema_version"], "trust.vc-digest-entry.v1");
    assert_eq!(row["vc_digests"][0]["artifact_kind"], "verification-condition");
    assert_eq!(row["vc_digests"][0]["digest_algorithm"], "sha256");
    assert_eq!(row["vc_digests"][0]["candidate_commit"], row["candidate_commit"]);
    assert_eq!(row["vc_digests"][0]["binary_digest"], row["binary_digest"]);
    assert_eq!(row["vc_digests"][0]["selected_image"], row["selected_image"]);
    assert_eq!(row["vc_digests"][0]["inventory_index"], 0);
    assert_eq!(row["vc_digests"][0]["inventory_count"], 1);
    assert_eq!(row["vc_digests"][0]["vc_id"], "proof-required-vc-0");
    assert_json_canonical_digest_uri(&row["vc_digests"][0]["digest"], "real release VC digest");
    assert_eq!(
        row["checked_certificate_digests"][0]["schema_version"],
        "trust.checked-certificate-readback-digest-entry.v1"
    );
    assert_eq!(
        row["checked_certificate_digests"][0]["artifact_kind"],
        "checked-certificate-readback"
    );
    assert_eq!(row["checked_certificate_digests"][0]["digest_algorithm"], "sha256");
    assert_eq!(row["checked_certificate_digests"][0]["candidate_commit"], row["candidate_commit"]);
    assert_eq!(row["checked_certificate_digests"][0]["binary_digest"], row["binary_digest"]);
    assert_eq!(row["checked_certificate_digests"][0]["selected_image"], row["selected_image"]);
    assert_eq!(row["checked_certificate_digests"][0]["inventory_index"], 0);
    assert_eq!(row["checked_certificate_digests"][0]["inventory_count"], 1);
    assert_eq!(row["checked_certificate_digests"][0]["vc_digest"], row["vc_digests"][0]["digest"]);
    assert_eq!(row["checked_certificate_digests"][0]["certificate_role"], "checked-certificate");
    assert_eq!(row["checked_certificate_digests"][0]["readback_status"], "accepted");
    assert_json_canonical_digest_uri(
        &row["checked_certificate_digests"][0]["digest"],
        "real release checked certificate digest",
    );
    assert_json_canonical_digest_uri(
        &row["release_transcript_binding_digest"],
        "real release row binding digest",
    );
    assert_json_canonical_digest_uri(
        &row["replay_transcript_digests"][0],
        "real release replay transcript digest",
    );
    assert_json_canonical_digest_uri(
        &row["provenance_artifact_digests"][0],
        "real release provenance artifact digest",
    );
    assert_json_canonical_digest_uri(
        &row["target_proof_consumer_artifact_digests"][0],
        "real release target proof-consumer evidence digest",
    );
    assert_json_canonical_digest_uri(
        &row["target_proof_consumer_artifact_digests"][1],
        "real release target proof-consumer binding digest",
    );
    assert_eq!(row["exact_source_ownership_evidence"]["status"], "accepted");
    assert_json_canonical_digest_uri(
        &row["exact_source_ownership_evidence"]["digest"],
        "real release exact source ownership digest",
    );
    assert_eq!(row["type_ownership_evidence"]["status"], "accepted");
    assert_json_canonical_digest_uri(
        &row["type_ownership_evidence"]["digest"],
        "real release type ownership digest",
    );
    assert_eq!(
        value["checked_certificate_readback"]["readback_records"][0]["proof_grade_release_transcript_row"],
        row.clone()
    );
    assert_eq!(row["aarch64_ordering_monitor_evidence"], serde_json::json!([]));

    let transcript_report: crate::types::ProofGradeReleaseTranscriptReport =
        serde_json::from_value(transcript.clone()).expect("real transcript should import typed");
    assert_eq!(transcript_report.accepted_proof_grade_rows.len(), 1);
    let transcript_path = root.join("real-proof-grade-release-transcript.json");
    let transcript_artifact_digest = write_and_readback_proof_grade_release_transcript_artifact(
        &transcript_path,
        &transcript_report,
    )
    .expect("real transcript artifact runner should persist and read back accepted JSON");
    assert_eq!(
        transcript_artifact_digest,
        format!(
            "sha256:{}",
            trust_types::digest::stable_sha256_hex(
                &std::fs::read(&transcript_path).expect("written transcript bytes should read")
            )
        )
    );
    let loaded_transcript = load_proof_grade_release_transcript_report(&transcript_path)
        .expect("real transcript artifact should load");
    assert_eq!(loaded_transcript, transcript_report);
    let written: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(&transcript_path).expect("written transcript should be readable"),
    )
    .expect("written real transcript should parse");
    assert_eq!(written, transcript.clone());
    let row_runner_path = root.join("real-proof-grade-release-transcript-from-rows.json");
    let row_runner_digest = write_and_readback_proof_grade_release_transcript_rows(
        &row_runner_path,
        &transcript_report.accepted_proof_grade_rows,
    )
    .expect("real transcript row runner should persist release artifact rows");
    assert_json_canonical_digest_uri(
        &serde_json::Value::String(row_runner_digest),
        "real release transcript artifact digest",
    );

    let _ = std::fs::remove_dir_all(root);
}

fn accepted_release_transcript_row_for_artifact_tests() -> ProofGradeReleaseTranscriptRowReport {
    let target_consumer = TargetConsumerDigestBinding {
        required: true,
        evidence_sha256: Some(trust_types::digest::stable_sha256_hex(b"release artifact target consumer evidence")),
        binding_sha256: Some(trust_types::digest::stable_sha256_hex(b"release artifact target consumer binding")),
    };
    proof_grade_release_transcript_row_report(ProofGradeReleaseTranscriptRowInput {
        evidence_origin: "targo_trust_release_export",
        candidate_commit: Some(current_release_candidate_commit()),
        binary_artifact_digest_identity: &fixture_binary_artifact_digest_identity(),
        vc_sha256s: vec![trust_types::digest::stable_sha256_hex(b"release artifact vc")],
        checked_certificate_sha256s: vec![trust_types::digest::stable_sha256_hex(b"release artifact checked certificate")],
        replay_transcript_sha256s: vec![trust_types::digest::stable_sha256_hex(b"release artifact replay transcript")],
        provenance_sha256s: vec![trust_types::digest::stable_sha256_hex(b"release artifact provenance")],
        unsupported_ledgers_empty: true,
        target_consumer: &target_consumer,
        exact_source_ownership_sha256: Some(trust_types::digest::stable_sha256_hex(b"release artifact exact source ownership")),
        type_ownership_sha256: Some(trust_types::digest::stable_sha256_hex(b"release artifact type ownership")),
        aarch64_ordering_monitor_evidence: Vec::new(),
    })
}

#[test]
fn test_release_transcript_artifact_runner_rejects_synthetic_or_unbound_rows() {
    let root = temp_test_dir("release-transcript-artifact-rejections");
    let base_row = accepted_release_transcript_row_for_artifact_tests();
    assert!(base_row.accepted, "{:?}", base_row.blockers);

    let mut synthetic_row = base_row.clone();
    synthetic_row.evidence_origin = "synthetic_fixture".to_string();
    let blocked_synthetic_row = synthetic_row.clone();

    let mut missing_target_consumer_row = base_row.clone();
    missing_target_consumer_row.target_proof_consumer_artifact_digests.clear();

    let mut stale_candidate_row = base_row.clone();
    stale_candidate_row.candidate_commit =
        Some("0000000000000000000000000000000000000000".to_string());

    let mut missing_selected_image_row = base_row;
    missing_selected_image_row.selected_image = None;

    for (name, row, expected) in [
        ("synthetic", synthetic_row, "evidence_origin"),
        (
            "missing-target-consumer",
            missing_target_consumer_row,
            "target_proof_consumer_artifact_digests",
        ),
        ("stale-candidate", stale_candidate_row, "candidate_commit does not match"),
        ("missing-selected-image", missing_selected_image_row, "selected_image"),
    ] {
        let report = crate::types::ProofGradeReleaseTranscriptReport {
            schema_version: "trust.proof-grade-release-transcript.v1".to_string(),
            accepted_proof_grade_rows: vec![row],
            blocked_proof_grade_rows: Vec::new(),
        };
        let error = write_and_readback_proof_grade_release_transcript_artifact(
            &root.join(format!("{name}.json")),
            &report,
        )
        .expect_err("release transcript artifact runner should reject tampered row");
        let error = format!("{error:?}");
        assert!(error.contains(expected), "{name} error: {error}");
    }

    let blocked_report = crate::types::ProofGradeReleaseTranscriptReport {
        schema_version: "trust.proof-grade-release-transcript.v1".to_string(),
        accepted_proof_grade_rows: Vec::new(),
        blocked_proof_grade_rows: vec![blocked_synthetic_row],
    };
    let error = write_and_readback_proof_grade_release_transcript_artifact(
        &root.join("blocked-synthetic.json"),
        &blocked_report,
    )
    .expect_err("blocked synthetic transcript must not be a release artifact");
    let error = format!("{error:?}");
    assert!(error.contains("accepted_proof_grade_rows must contain at least one row"), "{error}");
    assert!(error.contains("blocked_proof_grade_rows must be empty"), "{error}");

    let _ = std::fs::remove_dir_all(root);
}

fn exact_replay_witness_binding_diagnostics() -> Vec<String> {
    vec![
        EXACT_REPLAY_SLICE_ATTESTATION_ACCEPTED_DIAGNOSTIC.to_string(),
        EXACT_REPLAY_WITNESS_BINDING_ACCEPTED_DIAGNOSTIC.to_string(),
        EXACT_REPLAY_WITNESS_ARTIFACT_DIGEST_DIAGNOSTIC.to_string(),
        EXACT_REPLAY_WITNESS_SELECTED_IMAGE_DIAGNOSTIC.to_string(),
        EXACT_REPLAY_WITNESS_INSTRUCTION_BYTES_DIAGNOSTIC.to_string(),
        EXACT_REPLAY_WITNESS_EXECUTED_RANGE_DIAGNOSTIC.to_string(),
        EXACT_REPLAY_WITNESS_CONTROL_FLOW_CAPABILITY_DIAGNOSTIC.to_string(),
        EXACT_REPLAY_WITNESS_MEMORY_EFFECT_DIAGNOSTIC.to_string(),
    ]
}

fn exact_replay_dispatch_facts(record: &SolverDispatchRecord, prefix: &str) -> Vec<String> {
    let mut facts = record
        .diagnostics
        .iter()
        .filter_map(|diagnostic| diagnostic.trim().strip_prefix(prefix).map(str::to_string))
        .collect::<Vec<_>>();
    facts.sort();
    facts.dedup();
    facts
}

fn exact_replay_bound_sat_dispatch(id: &str) -> SolverDispatchRecord {
    let mut record = sat_replayed_binary_dispatch(id, "main");
    canonical_binary_dispatch_fields(&mut record);
    record.binary_artifact_digest_identity = Some(fixture_binary_artifact_digest_identity());
    record.result = Some(trust_types::VerificationResult::Failed {
        solver: "ay-smtlib".into(),
        time_ms: 17,
        counterexample: Some(replay_test_counterexample("bb0@0x401010")),
    });
    record.diagnostics = exact_replay_witness_binding_diagnostics();
    record
}

fn bind_exact_replay_dispatch_to_binary(
    record: &mut SolverDispatchRecord,
    binary_path: &Path,
    binary_bytes: &[u8],
) {
    let binary_sha256 = trust_types::digest::stable_sha256_hex(binary_bytes);
    record.origin.as_mut().expect("exact replay fixture has origin").binary_path =
        Some(binary_path.display().to_string());
    record.binary_artifact_digest_identity = Some(BinaryArtifactDigestIdentity {
        root_artifact_digest: Some(BinaryArtifactDigest::sha256(binary_sha256.clone())),
        selected_image: Some(BinarySelectedImageIdentity {
            file_offset: 0,
            file_size: u64::try_from(binary_bytes.len()).expect("fixture binary length fits u64"),
            sha256: binary_sha256,
        }),
    });
}

#[test]
fn test_verify_binary_readback_release_transcript_preserves_actual_digest_fields() {
    let root = temp_test_dir("verify-readback-release-transcript-actual-digests");
    std::fs::create_dir_all(&root).expect("test dir should be writable");
    let binary_path = root.join("selected-image.bin");
    let binary_bytes = b"\x7fELF release transcript selected image bytes".to_vec();
    std::fs::write(&binary_path, &binary_bytes).expect("test binary should be writable");
    let binary_sha256 = trust_types::digest::stable_sha256_hex(&binary_bytes);

    let (mut producer_dispatch, canonical_vc_bytes) =
        importable_binary_dispatch("release-transcript-digest-producer:vc0");
    bind_exact_replay_dispatch_to_binary(&mut producer_dispatch, &binary_path, &binary_bytes);
    let artifact = checked_binary_artifact_for_dispatch(&producer_dispatch, &canonical_vc_bytes);

    let (mut current_dispatch, _) =
        importable_binary_dispatch("release-transcript-digest-current:vc0");
    bind_exact_replay_dispatch_to_binary(&mut current_dispatch, &binary_path, &binary_bytes);
    let mut proof_evidence =
        VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![current_dispatch]);
    let mut import_report = proof_evidence.import_checked_certificate_artifacts(&[artifact]);
    assert_eq!(import_report.imported, 1, "{import_report:#?}");
    let import_row = import_report.artifacts.get_mut(0).expect("imported row");
    let replay_transcript_digest = trust_types::digest::stable_sha256_hex(b"actual digest readback replay transcript");
    import_row.manifest_identity_sha256 = Some(trust_types::digest::stable_sha256_hex(b"actual digest manifest identity"));
    import_row.source_backpropagation_gate_sha256 =
        Some(trust_types::digest::stable_sha256_hex(b"actual digest source gate identity"));
    import_row.production_checker_evidence_sha256 =
        Some(trust_types::digest::stable_sha256_hex(b"actual digest production checker evidence"));
    import_row.production_checker_evidence_status = "present".to_string();
    import_row.replay_transcript_digest = Some(replay_transcript_digest.clone());
    import_row.replay_digest_identity = checked_certificate_replay_digest_identity_record(
        ReplayStatus::Replayed,
        Some(replay_transcript_digest),
        Some(import_row.binary_artifact_digest_identity.clone()),
    );

    let binding = checked_certificate_import_release_transcript_binding(import_row);
    assert_eq!(binding.binary_sha256.as_deref(), Some(binary_sha256.as_str()));
    assert_eq!(binding.selected_image_sha256.as_deref(), Some(binary_sha256.as_str()));
    assert_eq!(binding.selected_image_file_offset, Some(0));
    assert_eq!(
        binding.selected_image_file_size,
        Some(u64::try_from(binary_bytes.len()).expect("fixture binary length fits u64"))
    );
    assert_eq!(binding.status, "accepted", "{:?}", binding.blockers);

    let row = checked_certificate_import_proof_grade_release_transcript_row_with_target_consumer(
        Some("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".to_string()),
        import_row,
        true,
        &TargetConsumerDigestBinding::default(),
    );
    assert!(
        !row.accepted,
        "checked-certificate import rows must preserve actual digest fields without masquerading as real release exports"
    );
    assert!(
        row.blockers.iter().any(
            |blocker| blocker.contains("evidence_origin must be `targo_trust_release_export`")
        ),
        "{:?}",
        row.blockers
    );
    assert_eq!(row.release_transcript_binding_digest, None);
    assert_eq!(row.binary_digest.as_deref(), Some(format!("sha256:{binary_sha256}").as_str()));
    let selected_image = row.selected_image.as_ref().expect("selected image transcript field");
    assert_eq!(selected_image.identity, format!("file_offset=0:file_size={}", binary_bytes.len()));
    assert_eq!(selected_image.digest, format!("sha256:{binary_sha256}"));

    let _ = std::fs::remove_dir_all(root);
}

fn importable_binary_dispatch(id: &str) -> (SolverDispatchRecord, Vec<u8>) {
    importable_binary_dispatch_with_kind(id, VcKind::DivisionByZero, 0x401010, 0x90)
}

fn importable_binary_dispatch_with_kind(
    id: &str,
    kind: VcKind,
    instruction_address: u64,
    instruction_byte: u8,
) -> (SolverDispatchRecord, Vec<u8>) {
    let vc = binary_vc(kind);
    let serializable_vc = SerializableVc::from_vc(&vc);
    let canonical_vc_bytes =
        serde_json::to_vec(&serializable_vc).expect("fixture VC should serialize");
    let dispatch = SolverDispatchRecord {
        id: id.to_string(),
        function: Some("main".to_string()),
        origin: Some(BinaryOrigin {
            binary_path: Some("fixtures/tiny.bin".to_string()),
            function_entry: Some(0x401000),
            instruction_address,
            instruction_size: Some(1),
            encoding: Some(instruction_byte.into()),
            instruction_bytes: vec![instruction_byte],
            source: Some(SourceSpan::binary_address(instruction_address)),
        }),
        vc_kind: Some(vc.kind.clone()),
        vc: Some(serializable_vc),
        solver: "ay-incremental".to_string(),
        backend: Some("ay-lrat".to_string()),
        status: SolverDispatchStatus::Unsat,
        query_semantics: SolverQuerySemantics::SatIsCounterexample,
        result: Some(trust_types::VerificationResult::Proved {
            solver: "ay-incremental".into(),
            time_ms: 4,
            strength: trust_types::ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }),
        binary_artifact_digest_identity: Some(fixture_binary_artifact_digest_identity()),
        replay: ReplayStatus::NotAttempted,
        certificate: ProofCertificateStatus::Unavailable {
            reason: Some("checked artifact not imported yet".to_string()),
        },
        ..Default::default()
    };
    (dispatch, canonical_vc_bytes)
}

fn checked_binary_artifact_for_dispatch(
    dispatch: &SolverDispatchRecord,
    canonical_vc_bytes: &[u8],
) -> CheckedBinaryCertificateArtifact {
    let export = SolverProofExport::new(
        dispatch,
        canonical_vc_bytes,
        "lrat",
        b"normalized checked proof payload".to_vec(),
        Some("4.13.0".to_string()),
        1_777_070_400_000,
    );
    let checker = StructuralBinaryCertificateChecker::new(
        "ay-lrat-binary-check",
        "0.1.0",
        vec!["lrat".to_string()],
        1_777_070_401_000,
    );
    let check = check_binary_certificate(
        &checker,
        BinaryCertificateCheckRequest::from_export(dispatch, canonical_vc_bytes, &export),
    );
    assert!(check.accepted, "{:?}", check.error);
    check.certificate.expect("accepted check should carry artifact")
}

fn assert_json_canonical_sha256(value: &serde_json::Value, context: &str) {
    let digest = value.as_str().unwrap_or_else(|| panic!("{context} should be a string"));
    assert_eq!(digest.len(), 64, "{context} should be 64 hex chars: {digest}");
    assert!(
        digest.bytes().all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase()),
        "{context} should be lowercase canonical SHA-256 hex: {digest}"
    );
}

fn assert_json_canonical_digest_uri(value: &serde_json::Value, context: &str) {
    let digest = value.as_str().unwrap_or_else(|| panic!("{context} should be a string"));
    let hex = digest
        .strip_prefix("sha256:")
        .unwrap_or_else(|| panic!("{context} should start with sha256:: {digest}"));
    assert_eq!(hex.len(), 64, "{context} should carry 64 hex chars: {digest}");
    assert!(
        hex.bytes().all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase()),
        "{context} should be lowercase canonical SHA-256 URI: {digest}"
    );
}

#[cfg(unix)]
fn accepted_trust_cg_target_proof_consumer_output(dispatch_id: &str) -> String {
    let target_output = "trust_cg-lir:function:entry:return:i32";
    let provenance_id = format!("binary_provenance:{dispatch_id}@0x401000");
    serde_json::json!({
        "functions": [{"name": "entry", "return_type": "i32"}],
        "typed": true,
        "target_proof_consumer_evidence": {
            "target": "trust-cg",
            "status": "accepted",
            "target_semantics_consumed": true,
            "records": [
                {
                    "kind": "target_semantics",
                    "identifier": "trust_cg-lir",
                    "accepted": true,
                    "detail": "trust-cg target semantics consumed conversion proof inputs"
                },
                {
                    "kind": "binary_provenance",
                    "identifier": provenance_id,
                    "accepted": true,
                    "detail": "binary provenance consumed by trust_cg target proof consumer"
                },
                {
                    "kind": "checked_certificate",
                    "identifier": dispatch_id,
                    "accepted": true,
                    "detail": "checked certificate identity consumed by trust_cg target proof consumer"
                },
                {
                    "kind": "proof_replay",
                    "identifier": dispatch_id,
                    "accepted": true,
                    "detail": "checked UNSAT certificate-only replay semantics consumed by trust_cg target proof consumer"
                }
            ],
            "binding": {
                "target": "trust-cg",
                "target_output": target_output,
                "status": "accepted",
                "target_semantics_consumed": true,
                "inputs": [
                    {
                        "kind": "binary_provenance",
                        "identifier": provenance_id,
                        "canonical_source": "trust_binary.provenance",
                        "target_output": target_output,
                        "consumed_by_target_semantics": true,
                        "detail": "binary provenance is bound to emitted trust_cg return value"
                    },
                    {
                        "kind": "checked_certificate",
                        "identifier": dispatch_id,
                        "canonical_source": "trust_proof.checked_certificate",
                        "target_output": target_output,
                        "consumed_by_target_semantics": true,
                        "detail": "checked certificate is bound to emitted trust_cg return value"
                    },
                    {
                        "kind": "proof_replay",
                        "identifier": dispatch_id,
                        "canonical_source": "trust_proof.proof_replay",
                        "target_output": target_output,
                        "consumed_by_target_semantics": true,
                        "detail": "proof replay identity is bound to emitted trust_cg return value"
                    }
                ],
                "blockers": []
            },
            "blockers": []
        }
    })
    .to_string()
}

fn accepted_wasm_scalar_target_proof_consumer_output() -> String {
    let target_output = "wat:emitted:guard:i32.const:1";
    let formula_id = "guard::bb0::stmt0::use";
    let provenance_id = "solver_dispatch:vc:guard@0x1004";
    let certificate_id = "checked_certificate:trust-proof-cert-check:lrat:abababababababababababababababababababababababababababababababab";
    let replay_id =
        "proof_replay:replayed:cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd";

    serde_json::json!({
        "functions": [{"name": "guard", "return_type": "i32"}],
        "typed": true,
        "target_proof_consumer_evidence": {
            "target": "wasm",
            "status": "accepted",
            "target_semantics_consumed": true,
            "records": [
                {
                    "kind": "target_semantics",
                    "identifier": "wasm32",
                    "accepted": true,
                    "detail": "Wasm target proof consumer accepted the non-empty scalar slice"
                },
                {
                    "kind": "symbolic_formula",
                    "identifier": formula_id,
                    "accepted": true,
                    "detail": "Bool(true) formula consumed by bridge-owned Wasm target proof-consumer evidence"
                },
                {
                    "kind": "binary_provenance",
                    "identifier": provenance_id,
                    "accepted": true,
                    "detail": "binary provenance consumed by bridge-owned Wasm target proof-consumer evidence"
                },
                {
                    "kind": "checked_certificate",
                    "identifier": certificate_id,
                    "accepted": true,
                    "detail": "checked certificate identity consumed by bridge-owned Wasm target proof-consumer evidence"
                },
                {
                    "kind": "proof_replay",
                    "identifier": replay_id,
                    "accepted": true,
                    "detail": "proof replay identity consumed by bridge-owned Wasm target proof-consumer evidence"
                }
            ],
            "binding": {
                "target": "wasm",
                "target_output": target_output,
                "status": "accepted",
                "target_semantics_consumed": true,
                "inputs": [
                    {
                        "kind": "canonical_trust_ir_formula",
                        "identifier": formula_id,
                        "canonical_source": "trust_symbolic.formula",
                        "target_output": target_output,
                        "consumed_by_target_semantics": true,
                        "detail": "formula is bound to emitted i32.const 1"
                    },
                    {
                        "kind": "binary_provenance",
                        "identifier": provenance_id,
                        "canonical_source": "trust_binary.provenance",
                        "target_output": target_output,
                        "consumed_by_target_semantics": true,
                        "detail": "exact instruction provenance is bound to emitted i32.const 1"
                    },
                    {
                        "kind": "checked_certificate",
                        "identifier": certificate_id,
                        "canonical_source": "trust_proof.checked_certificate",
                        "target_output": target_output,
                        "consumed_by_target_semantics": true,
                        "detail": "checked certificate is bound to emitted i32.const 1"
                    },
                    {
                        "kind": "proof_replay",
                        "identifier": replay_id,
                        "canonical_source": "trust_proof.proof_replay",
                        "target_output": target_output,
                        "consumed_by_target_semantics": true,
                        "detail": "exact replay identity is bound to emitted i32.const 1"
                    }
                ],
                "blockers": []
            },
            "blockers": []
        }
    })
    .to_string()
}

// -- Argument parsing tests --

#[test]
fn test_parse_args_default_format() {
    let args: Vec<String> = vec![];
    let result = parse_subcommand_args(&args).expect("should parse empty args");
    assert_eq!(result.format, OutputFormat::Terminal);
    assert!(!result.is_single_file);
    assert!(result.passthrough.is_empty());
}

#[test]
fn test_parse_args_format_json() {
    let args: Vec<String> = vec!["--format".into(), "json".into()];
    let result = parse_subcommand_args(&args).expect("should parse --format json");
    assert_eq!(result.format, OutputFormat::Json);
    assert!(result.passthrough.is_empty());
}

#[test]
fn test_parse_args_format_equals() {
    let args: Vec<String> = vec!["--format=html".into()];
    let result = parse_subcommand_args(&args).expect("should parse --format=html");
    assert_eq!(result.format, OutputFormat::Html);
}

#[test]
fn test_parse_args_invalid_format() {
    let args: Vec<String> = vec!["--format".into(), "csv".into()];
    assert!(parse_subcommand_args(&args).is_err());
}

#[test]
fn test_parse_args_rejects_removed_level0_gap_alias() {
    let args: Vec<String> = vec!["--allow-level0-gaps".into()];
    let error = parse_subcommand_args(&args).expect_err("removed gap alias should fail");

    assert!(error.to_string().contains("--allow-level0-gaps has been removed"));
    assert!(error.to_string().contains("--allow-l0-gaps"));
}

#[test]
fn test_parse_args_single_file() {
    let args: Vec<String> = vec!["test.rs".into()];
    let result = parse_subcommand_args(&args).expect("should parse single file");
    assert!(result.is_single_file);
    assert_eq!(result.single_file_path(), Some("test.rs"));
    assert_eq!(result.passthrough, vec!["test.rs"]);
}

#[test]
fn test_parse_args_manifest_path_is_preserved_for_passthrough() {
    let args: Vec<String> =
        vec!["--manifest-path".into(), "demo/Cargo.toml".into(), "--release".into()];
    let result = parse_subcommand_args(&args).expect("should parse --manifest-path");
    assert_eq!(result.manifest_path.as_deref(), Some("demo/Cargo.toml"));
    assert!(!result.is_single_file);
    assert_eq!(result.passthrough, vec!["--manifest-path", "demo/Cargo.toml", "--release"]);
}

#[test]
fn test_parse_args_passthrough_with_format() {
    let args: Vec<String> = vec!["--format".into(), "json".into(), "--release".into()];
    let result = parse_subcommand_args(&args).expect("should parse mixed args");
    assert_eq!(result.format, OutputFormat::Json);
    assert_eq!(result.passthrough, vec!["--release"]);
}

#[test]
fn test_parse_args_lift_options() {
    let args: Vec<String> = vec![
        "demo.bin".into(),
        "--entry".into(),
        "0x401000".into(),
        "--json".into(),
        "--strict".into(),
    ];
    let result = parse_subcommand_args(&args).expect("should parse lift args");
    assert_eq!(result.passthrough, vec!["demo.bin"]);
    assert_eq!(result.entry.as_deref(), Some("0x401000"));
    assert_eq!(result.format, OutputFormat::Json);
    assert!(!result.all_functions);
    assert!(result.strict);
}

#[test]
fn test_parse_args_lift_all_functions() {
    let args: Vec<String> = vec!["demo.bin".into(), "--all".into(), "--allow-unsupported".into()];
    let result = parse_subcommand_args(&args).expect("should parse lift --all");
    assert_eq!(result.passthrough, vec!["demo.bin"]);
    assert!(result.all_functions);
    assert!(!result.strict);
}

#[test]
fn test_parse_args_lift_strict_and_allow_unsupported_conflict_in_both_orders() {
    for args in [
        vec!["demo.bin", "--strict", "--allow-unsupported"],
        vec!["demo.bin", "--allow-unsupported", "--strict"],
    ] {
        let args = args.into_iter().map(String::from).collect::<Vec<_>>();
        let error = parse_subcommand_args(&args)
            .expect_err("strict and partial binary coverage must conflict");
        assert!(
            error.to_string().contains("--strict conflicts with --allow-unsupported"),
            "{error}"
        );
    }
}

#[test]
fn test_parse_args_checked_certificate_artifacts_do_not_passthrough() {
    let args: Vec<String> = vec![
        "demo.bin".into(),
        "--checked-cert-artifact".into(),
        "cert-a.json".into(),
        "--checked-cert-artifact=cert-b.json".into(),
    ];
    let result = parse_subcommand_args(&args).expect("should parse checked cert artifacts");
    assert_eq!(result.passthrough, vec!["demo.bin"]);
    assert_eq!(
        result.checked_certificate_artifacts,
        vec!["cert-a.json".to_string(), "cert-b.json".to_string()]
    );
}

#[test]
fn test_parse_args_checked_certificate_manifests_do_not_passthrough() {
    let args: Vec<String> = vec![
        "demo.bin".into(),
        "--checked-cert-manifest".into(),
        "manifest-a.json".into(),
        "--checked-cert-manifest=manifest-b.json".into(),
    ];
    let result = parse_subcommand_args(&args).expect("should parse checked cert manifests");
    assert_eq!(result.passthrough, vec!["demo.bin"]);
    assert_eq!(
        result.checked_certificate_manifests,
        vec!["manifest-a.json".to_string(), "manifest-b.json".to_string()]
    );
}

#[test]
fn test_parse_args_checked_certificate_export_dir_does_not_passthrough() {
    let args: Vec<String> =
        vec!["demo.bin".into(), "--checked-cert-export-dir".into(), "target/checked-certs".into()];
    let result = parse_subcommand_args(&args).expect("should parse checked cert export dir");
    assert_eq!(result.passthrough, vec!["demo.bin"]);
    assert_eq!(result.checked_certificate_export_dir.as_deref(), Some("target/checked-certs"));
}

#[test]
fn test_parse_args_checked_certificate_checker_does_not_passthrough() {
    let args: Vec<String> =
        vec!["demo.bin".into(), "--checked-cert-checker".into(), "bin/check-cert".into()];
    let result = parse_subcommand_args(&args).expect("should parse checked cert checker");
    assert_eq!(result.passthrough, vec!["demo.bin"]);
    assert_eq!(result.checked_certificate_checker.as_deref(), Some("bin/check-cert"));

    let args: Vec<String> = vec!["demo.bin".into(), "--checked-cert-checker=bin/check-cert".into()];
    let result = parse_subcommand_args(&args).expect("should parse checked cert checker equals");
    assert_eq!(result.passthrough, vec!["demo.bin"]);
    assert_eq!(result.checked_certificate_checker.as_deref(), Some("bin/check-cert"));
}

#[test]
fn test_parse_args_proof_grade_release_transcript_out_does_not_passthrough() {
    let args: Vec<String> = vec![
        "demo.bin".into(),
        "--proof-grade-release-transcript-out".into(),
        "target/release/proof-grade-release-transcript.json".into(),
    ];
    let result = parse_subcommand_args(&args).expect("should parse release transcript output");
    assert_eq!(result.passthrough, vec!["demo.bin"]);
    assert_eq!(
        result.proof_grade_release_transcript_out.as_deref(),
        Some("target/release/proof-grade-release-transcript.json")
    );

    let args: Vec<String> = vec![
        "demo.bin".into(),
        "--proof-grade-release-transcript-out=target/release/proof-grade-release-transcript.json"
            .into(),
    ];
    let result =
        parse_subcommand_args(&args).expect("should parse release transcript output equals");
    assert_eq!(result.passthrough, vec!["demo.bin"]);
    assert_eq!(
        result.proof_grade_release_transcript_out.as_deref(),
        Some("target/release/proof-grade-release-transcript.json")
    );
}

#[test]
fn test_parse_args_checked_certificate_artifact_requires_path() {
    let args: Vec<String> = vec!["demo.bin".into(), "--checked-cert-artifact".into()];
    assert!(parse_subcommand_args(&args).is_err());
}

#[test]
fn test_parse_args_checked_certificate_manifest_requires_path() {
    let args: Vec<String> = vec!["demo.bin".into(), "--checked-cert-manifest".into()];
    assert!(parse_subcommand_args(&args).is_err());
}

#[test]
fn test_parse_args_checked_certificate_export_dir_requires_path() {
    let args: Vec<String> = vec!["demo.bin".into(), "--checked-cert-export-dir".into()];
    assert!(parse_subcommand_args(&args).is_err());
}

#[test]
fn test_parse_args_checked_certificate_checker_requires_path() {
    let args: Vec<String> = vec!["demo.bin".into(), "--checked-cert-checker".into()];
    assert!(parse_subcommand_args(&args).is_err());
}

#[test]
fn test_parse_args_proof_grade_release_transcript_out_requires_path() {
    let args: Vec<String> = vec!["demo.bin".into(), "--proof-grade-release-transcript-out".into()];
    assert!(parse_subcommand_args(&args).is_err());
}

#[test]
fn test_parse_args_binary_source_provenance_artifacts_do_not_passthrough() {
    let args: Vec<String> = vec![
        "demo.bin".into(),
        "--binary-source-provenance-artifact".into(),
        "source-a.json".into(),
        "--binary-source-provenance-artifact=source-b.json".into(),
    ];
    let result = parse_subcommand_args(&args).expect("should parse source provenance artifacts");
    assert_eq!(result.passthrough, vec!["demo.bin"]);
    assert_eq!(
        result.binary_source_provenance_artifacts,
        vec!["source-a.json".to_string(), "source-b.json".to_string()]
    );
}

#[test]
fn test_parse_args_binary_source_provenance_artifact_requires_path() {
    let args: Vec<String> = vec!["demo.bin".into(), "--binary-source-provenance-artifact".into()];
    assert!(parse_subcommand_args(&args).is_err());
}

#[test]
fn test_lift_rejects_html_format() {
    let args: Vec<String> = vec!["--format=html".into()];
    assert_eq!(run_lift_subcommand(&args), ExitCode::from(2));
}

#[test]
fn test_lift_rejects_entry_and_all_conflict() {
    let args: Vec<String> =
        vec!["demo.bin".into(), "--entry".into(), "0x401000".into(), "--all".into()];
    assert_eq!(run_lift_subcommand(&args), ExitCode::from(2));
}

#[test]
fn test_parse_lift_entry_decimal_and_hex() {
    assert_eq!(parse_lift_entry(Some("4198400")).unwrap(), Some(4_198_400));
    assert_eq!(parse_lift_entry(Some("0x401000")).unwrap(), Some(0x401000));
    assert!(parse_lift_entry(Some("not-an-address")).is_err());
}

#[test]
fn test_lift_report_counts_and_strict_exit() {
    let report = build_lift_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        LiftReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![LiftedTrustIrFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 2,
                statements: 7,
                vcs: 3,
                instruction_provenance: Vec::new(),
            }],
            unsupported: vec!["unsupported opcode".into()],
            failures: Vec::new(),
        },
    );

    assert_eq!(report.status, BinaryLiftStatus::Incomplete);
    assert_eq!(report.functions_lifted, 1);
    assert_eq!(report.blocks, 2);
    assert_eq!(report.statements, 7);
    assert_eq!(report.vcs, 3);
    assert_eq!(report.unsupported, 1);
    assert!(lift_should_fail(&report));

    let rendered = render_lift_terminal(&report);
    assert!(rendered.contains("functions lifted: 1\n"));
    assert!(rendered.contains("status: incomplete\n"));
    assert!(rendered.contains("  - main @ 0x401000: blocks=2 statements=7 vcs=3\n"));
}

#[test]
fn test_lift_allow_unsupported_fails_when_zero_functions_lift() {
    let report = build_lift_report(
        Path::new("demo.bin"),
        None,
        false,
        false,
        LiftReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: Vec::new(),
            unsupported: vec!["unsupported control flow".into()],
            failures: Vec::new(),
        },
    );

    assert_eq!(report.status, BinaryLiftStatus::Incomplete);
    assert_eq!(report.functions_lifted, 0);
    assert!(lift_should_fail(&report));
}

#[test]
fn test_lift_allow_unsupported_permits_partial_coverage() {
    let report = build_lift_report(
        Path::new("demo.bin"),
        None,
        false,
        false,
        LiftReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![LiftedTrustIrFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 0,
                instruction_provenance: Vec::new(),
            }],
            unsupported: vec!["unsupported callee".into()],
            failures: Vec::new(),
        },
    );

    assert_eq!(report.status, BinaryLiftStatus::Incomplete);
    assert_eq!(report.functions_lifted, 1);
    assert!(!lift_should_fail(&report));
}

#[test]
fn test_structured_lift_errors_are_reported_as_unsupported() {
    let errors = [
        LiftError::UnsupportedSemantics {
            mode: LiftProofMode::SemanticLift,
            message: "unsupported opcode".into(),
        },
        LiftError::UnsupportedEffect {
            mode: LiftProofMode::SemanticLift,
            message: "unsupported flag effect".into(),
        },
        LiftError::UnresolvedControlFlow {
            mode: LiftProofMode::Cfg,
            message: "indirect jump".into(),
        },
        LiftError::MissingSuccessor { mode: LiftProofMode::Cfg, message: "missing edge".into() },
        LiftError::UnrepresentableCfg {
            mode: LiftProofMode::Cfg,
            message: "irreducible shape".into(),
        },
    ];

    for error in errors {
        let report_input = lift_report_input_from_result(Err(error));
        assert_eq!(report_input.unsupported.len(), 1);
        assert!(report_input.failures.is_empty());
    }
}

#[test]
fn test_verify_binary_rejects_html_format() {
    let args: Vec<String> = vec!["--format=html".into()];
    assert_eq!(run_verify_binary_subcommand(&args), ExitCode::from(2));
}

#[test]
fn test_verify_binary_rejects_entry_and_all_conflict() {
    let args: Vec<String> =
        vec!["demo.bin".into(), "--entry".into(), "0x401000".into(), "--all".into()];
    assert_eq!(run_verify_binary_subcommand(&args), ExitCode::from(2));
}

#[test]
fn test_verify_binary_rejects_unwired_solver_override() {
    let error = select_verify_binary_solver(Some("trust-mc")).expect_err("trust-mc is not wired");
    assert!(error.contains("verify-binary --solver trust-mc is unsupported for binary VCs"));
    assert!(error.contains("only `ay`"));
    assert!(error.contains("`ay-incremental`"));

    let args: Vec<String> = vec!["demo.bin".into(), "--solver".into(), "trust-mc".into()];
    assert_eq!(run_verify_binary_subcommand(&args), ExitCode::from(2));
}

#[test]
fn test_verify_binary_accepts_default_and_ay_solver_route() {
    assert_eq!(select_verify_binary_solver(None).unwrap(), BinarySolverRoute::AYIncremental);
    assert_eq!(select_verify_binary_solver(Some("ay")).unwrap(), BinarySolverRoute::AYIncremental);
}

#[test]
fn test_verify_binary_unknown_solver_is_distinct_from_unwired_route() {
    let error = select_verify_binary_solver(Some("not-a-solver"))
        .expect_err("unknown solver should be rejected");
    assert!(error.contains("unknown verify-binary solver `not-a-solver`"));
    assert!(error.contains("known source-level solvers"));
    assert!(error.contains("only `ay` is wired"));
    assert!(!error.contains("is unsupported for binary VCs"));
}

#[test]
fn test_verify_binary_solver_route_diagnostics_render_terminal_and_json() {
    let report = build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 0,
                vc_counts: Vec::new(),
            }],
            solver_results: Vec::new(),
            proof_evidence: verify_binary_evidence_for_vcs(0),
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );

    let route = solver_route_diagnostic(Some("ay"), BinarySolverRoute::AYIncremental);
    assert_eq!(route.requested, "ay");
    assert_eq!(route.selected, "ay-incremental");
    assert_eq!(route.status, "routed");
    assert!(route.detail.contains("only `ay` is wired"));

    let rendered = render_verify_binary_terminal(&report);
    assert!(rendered.contains("solver route: ay-incremental\n"));
    assert!(rendered.contains("solver route status: routed\n"));
    assert!(rendered.contains("solver route detail: verify-binary binary VCs are routed"));

    let json = serialize_verify_binary_json_with_route(
        &report,
        Some("ay"),
        BinarySolverRoute::AYIncremental,
    )
    .expect("serialize verify-binary JSON");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse JSON");
    assert_eq!(value["solver_route"]["requested"], "ay");
    assert_eq!(value["solver_route"]["selected"], "ay-incremental");
    assert_eq!(value["solver_route"]["status"], "routed");
}

#[test]
fn test_verify_binary_solver_ay_gets_past_argument_validation() {
    let root = temp_test_dir("verify-binary-ay-solver");
    std::fs::create_dir_all(&root).expect("should create temp dir");
    let binary = root.join("demo.bin");
    std::fs::write(&binary, &[] as &[u8]).expect("should write invalid binary fixture");

    let args: Vec<String> = vec![binary.display().to_string(), "--solver".into(), "ay".into()];
    assert_eq!(run_verify_binary_subcommand(&args), ExitCode::FAILURE);

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_verify_binary_report_counts_vc_kinds() {
    let report = build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 2,
                statements: 7,
                vcs: 3,
                vc_counts: vec![
                    BinaryVcKindCount { kind: "binary_memory_write_oob".into(), count: 1 },
                    BinaryVcKindCount { kind: "binary_stack_pointer_restoration".into(), count: 2 },
                ],
            }],
            solver_results: Vec::new(),
            proof_evidence: verify_binary_evidence_for_vcs(3),
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );

    assert_eq!(report.status, BinaryLiftStatus::Ok);
    assert_eq!(report.functions_analyzed, 1);
    assert_eq!(report.blocks, 2);
    assert_eq!(report.statements, 7);
    assert_eq!(report.vcs, 3);
    assert_eq!(report.selection, "address");
    assert_eq!(report.verification_status, "unknown");
    assert_eq!(report.trust_level, "partial");
    assert_eq!(report.solver_results.status, "unknown");
    assert_eq!(report.solver_results.total, 3);
    assert_eq!(report.solver_results.unknown, 3);
    assert_eq!(
        report.vc_counts,
        vec![
            BinaryVcKindCount { kind: "binary_memory_write_oob".into(), count: 1 },
            BinaryVcKindCount { kind: "binary_stack_pointer_restoration".into(), count: 2 },
        ]
    );
    assert!(verify_binary_should_fail(&report));

    let rendered = render_verify_binary_terminal(&report);
    assert!(rendered.contains("targo trust verify-binary report\n"));
    assert!(rendered.contains("selection: address\n"));
    assert!(rendered.contains("functions analyzed: 1\n"));
    assert!(rendered.contains("vcs generated: 3\n"));
    assert!(rendered.contains("verification status: unknown\n"));
    assert!(rendered.contains("solver results: unknown\n"));
    assert!(rendered.contains("solver counts: total=3 proved=0 failed=0 unknown=3 timeout=0\n"));
    assert!(rendered.contains("  - binary_memory_write_oob: 1\n"));
    assert!(rendered.contains("    - binary_stack_pointer_restoration: 2\n"));
}

#[test]
fn test_verify_binary_zero_generated_vcs_fails_closed() {
    let report = build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 3,
                vcs: 0,
                vc_counts: Vec::new(),
            }],
            solver_results: Vec::new(),
            proof_evidence: verify_binary_evidence_for_vcs(0),
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );

    assert_eq!(report.status, BinaryLiftStatus::Ok);
    assert_eq!(report.functions_analyzed, 1);
    assert_eq!(report.vcs, 0);
    assert_eq!(report.verification_status, "not_run");
    assert_eq!(report.solver_results.status, "not_run");
    assert!(verify_binary_should_fail(&report));
}

#[test]
fn test_verify_binary_unsupported_errors_fail_closed() {
    let report = build_verify_binary_report(
        Path::new("demo.bin"),
        None,
        false,
        true,
        verify_binary_report_input_from_result(Err(LiftError::UnsupportedSemantics {
            mode: LiftProofMode::SemanticLift,
            message: "unsupported opcode".into(),
        })),
    );

    assert_eq!(report.status, BinaryLiftStatus::Incomplete);
    assert_eq!(report.unsupported, 1);
    assert!(verify_binary_should_fail(&report));
}

#[test]
fn test_verify_binary_allow_unsupported_requires_lifted_function() {
    let report = build_verify_binary_report(
        Path::new("demo.bin"),
        None,
        false,
        false,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: Vec::new(),
            solver_results: Vec::new(),
            proof_evidence: verify_binary_evidence_for_vcs(0),
            unsupported: vec!["unsupported control flow".into()],
            failures: Vec::new(),
        },
    );

    assert_eq!(report.status, BinaryLiftStatus::Incomplete);
    assert_eq!(report.functions_analyzed, 0);
    assert!(verify_binary_should_fail(&report));
}

#[test]
fn test_verify_binary_vc_kind_counts_normalize_binary_assertions() {
    let kinds = [
        VcKind::DivisionByZero,
        VcKind::Assertion { message: "binary memory write OOB at 0x401010 (8 bytes)".into() },
        VcKind::Assertion { message: "stack pointer not restored on return in block bb0".into() },
        VcKind::Assertion { message: "stack pointer not restored on return in block bb1".into() },
    ];

    let counts = count_vc_kinds(kinds.iter());
    assert_eq!(
        counts,
        vec![
            BinaryVcKindCount { kind: "binary_memory_write_oob".into(), count: 1 },
            BinaryVcKindCount { kind: "binary_stack_pointer_restoration".into(), count: 2 },
            BinaryVcKindCount { kind: "division_by_zero".into(), count: 1 },
        ]
    );
}

#[test]
fn test_failed_binary_solver_result_with_raw_counterexample_marks_replay_not_attempted() {
    let counterexample = trust_types::Counterexample::new(vec![(
        "rax".into(),
        trust_types::CounterexampleValue::Int(0),
    )]);
    let result = trust_types::VerificationResult::Failed {
        solver: "ay-smtlib".into(),
        time_ms: 11,
        counterexample: Some(counterexample),
    };

    let item = binary_solver_result_report(
        "main",
        "binary_memory_write_oob".into(),
        Some("0x401020".into()),
        &result,
    );

    assert_eq!(item.status, "failed");
    assert_eq!(item.detail.as_deref(), Some("rax = 0"));
    assert_eq!(item.replay_status.as_deref(), Some("not_attempted"));
    let replay_detail = item.replay_detail.as_deref().expect("replay detail");
    assert!(replay_detail.contains("needs_machine_replay"));
    assert!(replay_detail.contains("no execution trace"));
    assert!(!replay_detail.contains("confirmed"));
}

#[test]
fn test_raw_counterexample_with_replay_context_is_not_marked_replayed() {
    let function = replay_test_lifted_function(vec![replay_test_annotation(0x401010)]);
    let counterexample = trust_types::Counterexample::new(vec![(
        "rax".into(),
        trust_types::CounterexampleValue::Int(0),
    )]);
    let result = trust_types::VerificationResult::Failed {
        solver: "ay-smtlib".into(),
        time_ms: 11,
        counterexample: Some(counterexample),
    };
    let context = replay_test_context([0x401010]);
    let vc = replay_test_vc();

    let item = binary_solver_result_report_with_replay(
        "main",
        "binary_memory_write_oob".into(),
        Some("0x401010".into()),
        &result,
        Some(BinaryReplayAttempt { function: &function, vc: &vc, context: Some(&context) }),
    );

    assert_eq!(item.status, "failed");
    assert_eq!(item.replay_status.as_deref(), Some("not_attempted"));
    let replay_detail = item.replay_detail.as_deref().expect("replay detail");
    assert!(replay_detail.contains("needs_machine_replay"));
    assert!(replay_detail.contains("no execution trace"));
    assert!(!replay_detail.contains("machine_replay_confirmed"));
}

#[test]
fn test_failed_binary_solver_result_without_model_marks_replay_not_attempted() {
    let result = trust_types::VerificationResult::Failed {
        solver: "ay-smtlib".into(),
        time_ms: 17,
        counterexample: None,
    };

    let item = binary_solver_result_report(
        "main",
        "binary_memory_write_oob".into(),
        Some("0x401040".into()),
        &result,
    );

    assert_eq!(item.status, "failed");
    assert_eq!(item.detail.as_deref(), Some("SAT without counterexample model"));
    assert_eq!(item.replay_status.as_deref(), Some("not_attempted"));
    assert_eq!(
        item.replay_detail.as_deref(),
        Some("needs_machine_replay: SAT without counterexample model; cannot replay")
    );
}

#[test]
fn test_failed_binary_solver_result_with_mapped_machine_trace_replays() {
    let function = replay_test_lifted_function(vec![replay_test_annotation(0x401010)]);
    let result = trust_types::VerificationResult::Failed {
        solver: "ay-smtlib".into(),
        time_ms: 19,
        counterexample: Some(replay_test_counterexample("bb0@0x401010")),
    };
    let context = replay_test_context([0x401010]);
    let vc = replay_test_vc();

    let item = binary_solver_result_report_with_replay(
        "main",
        "binary_memory_write_oob".into(),
        Some("0x401010".into()),
        &result,
        Some(BinaryReplayAttempt { function: &function, vc: &vc, context: Some(&context) }),
    );

    assert_eq!(item.status, "failed");
    assert_eq!(item.replay_status.as_deref(), Some("replayed"), "{:?}", item.replay_detail);
    assert!(
        item.replay_detail.as_deref().expect("replay detail").contains("machine_replay_confirmed")
    );
}

#[test]
fn test_failed_binary_solver_result_with_non_executable_replay_segment_fails_closed() {
    let function = replay_test_lifted_function(vec![replay_test_annotation(0x401010)]);
    let result = trust_types::VerificationResult::Failed {
        solver: "ay-smtlib".into(),
        time_ms: 19,
        counterexample: Some(replay_test_counterexample("bb0@0x401010")),
    };
    let context = replay_test_context_with_segments(
        [0x401010],
        trust_symex::BoundedMachineCodeArchitecture::Aarch64,
        vec![trust_symex::BoundedMachineCodeSegment::new(
            0x401000,
            0x1000,
            trust_symex::BoundedMachineCodeSegmentPermissions::rw(),
        )],
    );
    let vc = replay_test_vc();

    let item = binary_solver_result_report_with_replay(
        "main",
        "binary_memory_write_oob".into(),
        Some("0x401010".into()),
        &result,
        Some(BinaryReplayAttempt { function: &function, vc: &vc, context: Some(&context) }),
    );

    assert_eq!(item.status, "failed");
    assert_eq!(item.replay_status.as_deref(), Some("spurious"), "{:?}", item.replay_detail);
    let replay_detail = item.replay_detail.as_deref().expect("replay detail");
    assert!(replay_detail.contains("non-executable loaded image segments"));
    assert!(!replay_detail.contains("machine_replay_confirmed"));
}

#[test]
fn test_bounded_replay_maps_x86_64_architecture_aliases() {
    for alias in ["x86-64", "x86_64", "amd64", "X86_64"] {
        assert_eq!(
            bounded_machine_architecture(alias),
            Some(trust_symex::BoundedMachineCodeArchitecture::X86_64)
        );
    }
}

#[test]
fn test_failed_x86_64_solver_result_replays_exact_instruction_bytes() {
    let function = replay_test_lifted_function(vec![replay_test_annotation_with_bytes(
        0x401010,
        0x90,
        vec![0x90],
    )]);
    let result = trust_types::VerificationResult::Failed {
        solver: "ay-smtlib".into(),
        time_ms: 17,
        counterexample: Some(replay_test_counterexample("bb0@0x401010")),
    };
    let context = replay_test_context_with_arch(
        [0x401010],
        trust_symex::BoundedMachineCodeArchitecture::X86_64,
    );
    let vc = replay_test_vc();

    let item = binary_solver_result_report_with_replay(
        "main",
        "binary_memory_write_oob".into(),
        Some("0x401010".into()),
        &result,
        Some(BinaryReplayAttempt { function: &function, vc: &vc, context: Some(&context) }),
    );

    assert_eq!(item.status, "failed");
    assert_eq!(item.replay_status.as_deref(), Some("replayed"), "{:?}", item.replay_detail);
    assert!(
        item.replay_detail.as_deref().expect("replay detail").contains("machine_replay_confirmed")
    );
}

#[test]
fn test_exact_replay_sat_candidate_matches_checked_in_golden() {
    let exact_function = replay_test_lifted_function(vec![replay_test_annotation_with_bytes(
        0x401010,
        0x90,
        vec![0x90],
    )]);
    let missing_bytes_function =
        replay_test_lifted_function(vec![replay_test_annotation_with_bytes(
            0x401010,
            0x90,
            Vec::new(),
        )]);
    let mut missing_bytes_annotation =
        replay_test_annotation_with_bytes(0x401010, 0x90, vec![0x90]);
    missing_bytes_annotation.instruction_size = 3;
    let length_mismatch_function = replay_test_lifted_function(vec![missing_bytes_annotation]);
    let context = replay_test_context_with_arch(
        [0x401010],
        trust_symex::BoundedMachineCodeArchitecture::X86_64,
    );
    let vc = replay_test_vc();

    let exact_result = trust_types::VerificationResult::Failed {
        solver: "ay-smtlib".into(),
        time_ms: 17,
        counterexample: Some(replay_test_counterexample("bb0@0x401010")),
    };
    let exact_item = binary_solver_result_report_with_replay(
        "main",
        "binary_memory_write_oob".into(),
        Some("0x401010".into()),
        &exact_result,
        Some(BinaryReplayAttempt { function: &exact_function, vc: &vc, context: Some(&context) }),
    );

    let missing_bytes_result = trust_types::VerificationResult::Failed {
        solver: "ay-smtlib".into(),
        time_ms: 31,
        counterexample: Some(replay_test_counterexample("bb0@0x401010")),
    };
    let missing_bytes_item = binary_solver_result_report_with_replay(
        "main",
        "binary_memory_write_oob".into(),
        Some("0x401010".into()),
        &missing_bytes_result,
        Some(BinaryReplayAttempt {
            function: &missing_bytes_function,
            vc: &vc,
            context: Some(&context),
        }),
    );

    let length_mismatch_result = trust_types::VerificationResult::Failed {
        solver: "ay-smtlib".into(),
        time_ms: 37,
        counterexample: Some(replay_test_counterexample("bb0@0x401010")),
    };
    let length_mismatch_item = binary_solver_result_report_with_replay(
        "main",
        "binary_memory_write_oob".into(),
        Some("0x401010".into()),
        &length_mismatch_result,
        Some(BinaryReplayAttempt {
            function: &length_mismatch_function,
            vc: &vc,
            context: Some(&context),
        }),
    );

    let router = Router::with_backends(vec![Box::new(RawProofBackend)]);
    let provenance_vc = VerificationCondition {
        kind: VcKind::Assertion { message: "binary generated VC".into() },
        function: trust_types::Symbol::intern("binary::main"),
        location: SourceSpan::binary_address(0x401010),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };
    let (_reports, provenance_dispatch_records) = dispatch_binary_vcs_with_replay_evidence(
        &router,
        BinarySolverRoute::AYIncremental,
        Some(Path::new("fixtures/tiny.bin")),
        &exact_function,
        None,
        std::slice::from_ref(&provenance_vc),
    );
    let provenance_dispatch_json =
        serde_json::to_value(&provenance_dispatch_records[0]).expect("serialize dispatch record");
    let provenance_origin = &provenance_dispatch_json["origin"];
    assert_eq!(provenance_origin["instruction_size"], 1);
    assert_eq!(provenance_origin["instruction_bytes"], serde_json::json!([144]));

    let expected_origin = BinaryOrigin {
        binary_path: Some("fixtures/tiny.bin".into()),
        function_entry: Some(0x401000),
        instruction_address: 0x401010,
        instruction_size: Some(1),
        encoding: Some(0x90),
        instruction_bytes: vec![0x90],
        source: Some(SourceSpan::binary_address(0x401010)),
    };
    let mismatched_origin =
        BinaryOrigin { instruction_bytes: vec![0x91], ..expected_origin.clone() };
    let mismatched_report = trust_symex::BinaryReplayReport {
        status: trust_symex::BinaryReplayStatus::Spurious,
        trust_types_status: ReplayStatus::Spurious,
        normalized_witness: trust_symex::BinaryWitness::default(),
        machine_replay: trust_symex::BinaryMachineReplayReport {
            status: trust_symex::BinaryMachineReplayStatus::Spurious,
            trust_types_status: ReplayStatus::Spurious,
            backend: "constant-folder".into(),
            reason: "instruction bytes mismatch at 0x401010".into(),
            expected_artifact_digest: None,
            observed_artifact_digest: None,
            matched_artifact_digest: false,
            expected_selected_image: None,
            observed_selected_image: None,
            matched_selected_image: false,
            expected_instruction_trace: vec![expected_origin.clone()],
            observed_instruction_trace: vec![trust_symex::BinaryMachineInstructionEvidence::new(
                mismatched_origin.clone(),
            )],
            matched_instruction_trace: false,
            capability_evidence: Vec::new(),
            matched_capability_evidence: false,
            effect_evidence: Vec::new(),
            effect_diagnostics: Vec::new(),
            matched_effect_evidence: false,
            boundary_evidence: Vec::new(),
            byte_range_evidence: Vec::new(),
            byte_range_diagnostics: Vec::new(),
            attestation_slices: Vec::new(),
            replay_transcript_digest: None,
        },
        reason: "machine-code replay rejected mismatched original instruction bytes".into(),
        block_trace: vec![0],
        witness_trace: vec![0],
        terminated_normally: Some(false),
        needs_machine_replay: false,
    };
    let mismatched_fields = binary_replay_fields_from_report(&mismatched_report, false);
    assert_eq!(mismatched_fields.status, "spurious");
    assert!(mismatched_fields.detail.contains("mismatched original instruction bytes"));

    let mut mismatched_dispatch =
        sat_unreplayed_binary_dispatch("vc-sat-mismatched-original-bytes", "main");
    mismatched_dispatch.origin = Some(mismatched_origin);
    mismatched_dispatch.replay = ReplayStatus::Spurious;
    let mismatched_proof_evidence =
        VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![mismatched_dispatch]);
    let mismatched_verify_report = build_verify_binary_report(
        Path::new("fixtures/tiny.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount {
                    kind: "binary_memory_write_oob".into(),
                    count: 1,
                }],
            }],
            solver_results: vec![missing_bytes_item.clone()],
            proof_evidence: mismatched_proof_evidence,
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );
    let mismatched_verify_json: serde_json::Value =
        serde_json::from_str(&serialize_verify_binary_json(&mismatched_verify_report).unwrap())
            .expect("parse mismatched verify-binary JSON");
    assert_eq!(mismatched_verify_json["proof_grade_gate"]["accepted"], false);
    assert_eq!(mismatched_verify_json["proof_grade_gate"]["replay_semantics_satisfied"], false);
    assert_eq!(mismatched_verify_json["proof_grade_gate"]["replayed_vcs"], 0);

    let mut missing_memory_effect_dispatch =
        exact_replay_bound_sat_dispatch("vc-sat-missing-memory-effect-witness");
    missing_memory_effect_dispatch
        .diagnostics
        .retain(|diagnostic| diagnostic != EXACT_REPLAY_WITNESS_MEMORY_EFFECT_DIAGNOSTIC);
    let missing_memory_effect_proof_evidence =
        VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![missing_memory_effect_dispatch]);
    let missing_memory_effect_verify_report = build_verify_binary_report(
        Path::new("fixtures/tiny.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount {
                    kind: "binary_memory_write_oob".into(),
                    count: 1,
                }],
            }],
            solver_results: vec![exact_item.clone()],
            proof_evidence: missing_memory_effect_proof_evidence,
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );
    let missing_memory_effect_verify_json: serde_json::Value = serde_json::from_str(
        &serialize_verify_binary_json(&missing_memory_effect_verify_report).unwrap(),
    )
    .expect("parse missing memory/effect verify-binary JSON");
    assert_eq!(missing_memory_effect_verify_json["proof_grade_gate"]["accepted"], false);
    assert_eq!(
        missing_memory_effect_verify_json["proof_grade_gate"]["replay_semantics_satisfied"],
        false
    );
    assert_eq!(missing_memory_effect_verify_json["proof_grade_gate"]["replayed_vcs"], 1);
    assert_eq!(
        missing_memory_effect_verify_json["proof_grade_gate"]["exact_replay_slice_attested_vcs"],
        0
    );

    let actual = serde_json::json!({
        "failed_sat_candidate_with_exact_original_bytes": {
            "status": exact_item.status,
            "replay_status": exact_item.replay_status,
            "detail": exact_item.replay_detail,
        },
        "failed_sat_candidate_with_missing_original_bytes": {
            "status": missing_bytes_item.status,
            "replay_status": missing_bytes_item.replay_status,
            "detail": missing_bytes_item.replay_detail,
        },
        "failed_sat_candidate_with_original_byte_length_mismatch": {
            "status": length_mismatch_item.status,
            "replay_status": length_mismatch_item.replay_status,
            "detail": length_mismatch_item.replay_detail,
        },
        "failed_sat_candidate_with_mismatched_original_bytes": {
            "status": "failed",
            "replay_status": mismatched_fields.status,
            "detail": mismatched_fields.detail,
        },
        "exact_replay_provenance_json": {
            "origin": {
                "binary_path": provenance_origin["binary_path"],
                "function_entry": provenance_origin["function_entry"],
                "instruction_address": provenance_origin["instruction_address"],
                "instruction_size": provenance_origin["instruction_size"],
                "encoding": provenance_origin["encoding"],
                "instruction_bytes": provenance_origin["instruction_bytes"],
            },
        },
        "mismatched_original_bytes_proof_grade_gate": {
            "accepted": mismatched_verify_json["proof_grade_gate"]["accepted"],
            "replay_semantics_satisfied": mismatched_verify_json["proof_grade_gate"]["replay_semantics_satisfied"],
            "replayed_vcs": mismatched_verify_json["proof_grade_gate"]["replayed_vcs"],
            "missing_machine_replay": mismatched_verify_json["proof_grade_gate"]["missing_machine_replay"],
            "rejections": mismatched_verify_json["proof_grade_gate"]["rejections"],
        },
        "missing_memory_effect_witness_binding_proof_grade_gate": {
            "accepted": missing_memory_effect_verify_json["proof_grade_gate"]["accepted"],
            "replay_semantics_satisfied": missing_memory_effect_verify_json["proof_grade_gate"]["replay_semantics_satisfied"],
            "replayed_vcs": missing_memory_effect_verify_json["proof_grade_gate"]["replayed_vcs"],
            "exact_replay_slice_attested_vcs": missing_memory_effect_verify_json["proof_grade_gate"]["exact_replay_slice_attested_vcs"],
            "missing_machine_replay": missing_memory_effect_verify_json["proof_grade_gate"]["missing_machine_replay"],
            "rejections": missing_memory_effect_verify_json["proof_grade_gate"]["rejections"],
        },
    });
    let expected: serde_json::Value =
        serde_json::from_str(include_str!("fixtures/exact_replay_sat_candidate_golden.json"))
            .expect("parse exact replay golden");

    assert_eq!(actual, expected);
}

#[test]
fn test_confirmed_replay_without_exact_original_bytes_fails_closed() {
    let origin = BinaryOrigin {
        binary_path: Some("fixtures/tiny.bin".into()),
        function_entry: Some(0x401000),
        instruction_address: 0x401010,
        instruction_size: Some(1),
        encoding: Some(0x90),
        instruction_bytes: Vec::new(),
        source: Some(SourceSpan::binary_address(0x401010)),
    };
    let report = trust_symex::BinaryReplayReport {
        status: trust_symex::BinaryReplayStatus::Confirmed,
        trust_types_status: ReplayStatus::Replayed,
        normalized_witness: trust_symex::BinaryWitness::default(),
        machine_replay: trust_symex::BinaryMachineReplayReport {
            status: trust_symex::BinaryMachineReplayStatus::Replayed,
            trust_types_status: ReplayStatus::Replayed,
            backend: "constant-folder".into(),
            reason: "machine-code replay evidence matched normalized witness".into(),
            expected_artifact_digest: None,
            observed_artifact_digest: None,
            matched_artifact_digest: false,
            expected_selected_image: None,
            observed_selected_image: None,
            matched_selected_image: false,
            expected_instruction_trace: vec![origin.clone()],
            observed_instruction_trace: vec![trust_symex::BinaryMachineInstructionEvidence::new(
                origin,
            )],
            matched_instruction_trace: true,
            capability_evidence: Vec::new(),
            matched_capability_evidence: true,
            effect_evidence: Vec::new(),
            effect_diagnostics: Vec::new(),
            matched_effect_evidence: true,
            boundary_evidence: Vec::new(),
            byte_range_evidence: Vec::new(),
            byte_range_diagnostics: Vec::new(),
            attestation_slices: Vec::new(),
            replay_transcript_digest: None,
        },
        reason: "lifted replay confirmed".into(),
        block_trace: vec![0],
        witness_trace: vec![0],
        terminated_normally: Some(true),
        needs_machine_replay: false,
    };

    let fields = binary_replay_fields_from_report(&report, false);

    assert_eq!(fields.status, "not_attempted");
    assert!(fields.detail.contains("needs_machine_replay"));
    assert!(fields.detail.contains("exact original instruction bytes"));
    assert!(!fields.detail.contains("machine_replay_confirmed"));
}

#[test]
fn test_verify_binary_json_surfaces_replay_capability_evidence_without_proof_grade() {
    let capability = trust_symex::BinaryMachineReplayCapabilityEvidence::new(
        trust_symex::BinaryMachineReplayCapability::DirectBranch,
        "AArch64",
        0x401000,
        "decoded direct branch target validated against following trace step",
    )
    .with_step(Some(0))
    .with_instruction_bytes(vec![0x02, 0x00, 0x00, 0x14]);
    let replay_report = trust_symex::BinaryReplayReport {
        status: trust_symex::BinaryReplayStatus::Confirmed,
        trust_types_status: ReplayStatus::Replayed,
        normalized_witness: trust_symex::BinaryWitness::default(),
        machine_replay: trust_symex::BinaryMachineReplayReport {
            status: trust_symex::BinaryMachineReplayStatus::Replayed,
            trust_types_status: ReplayStatus::Replayed,
            backend: "bounded-machine-code".into(),
            reason: "machine-code replay evidence matched normalized witness".into(),
            expected_artifact_digest: None,
            observed_artifact_digest: None,
            matched_artifact_digest: false,
            expected_selected_image: None,
            observed_selected_image: None,
            matched_selected_image: false,
            expected_instruction_trace: Vec::new(),
            observed_instruction_trace: Vec::new(),
            matched_instruction_trace: true,
            capability_evidence: vec![capability],
            matched_capability_evidence: true,
            effect_evidence: Vec::new(),
            effect_diagnostics: Vec::new(),
            matched_effect_evidence: true,
            boundary_evidence: Vec::new(),
            byte_range_evidence: Vec::new(),
            byte_range_diagnostics: Vec::new(),
            attestation_slices: Vec::new(),
            replay_transcript_digest: None,
        },
        reason: "lifted replay confirmed direct branch target".into(),
        block_trace: vec![0],
        witness_trace: vec![0],
        terminated_normally: Some(true),
        needs_machine_replay: false,
    };
    let replay_fields = binary_replay_fields_from_report(&replay_report, true);
    assert_eq!(replay_fields.status, "replayed");
    assert_eq!(replay_fields.capability_evidence.len(), 1);
    assert_eq!(replay_fields.capability_evidence_matched, Some(true));

    let solver_item = BinarySolverResultReport {
        function: "main".into(),
        vc_kind: "binary_memory_write_oob".into(),
        location: Some("0x401000".into()),
        solver: "ay-incremental".into(),
        status: "failed".into(),
        time_ms: 9,
        detail: Some("counterexample requires replay/refutation".into()),
        replay_status: Some(replay_fields.status),
        replay_detail: Some(replay_fields.detail),
        replay_capability_evidence: replay_fields.capability_evidence,
        replay_capability_evidence_matched: replay_fields.capability_evidence_matched,
    };
    let proof_evidence = VerifyBinaryEvidence::from_solver_dispatch_records(
        1,
        vec![sat_replayed_binary_dispatch("direct-branch-sat:vc0", "main")],
    );
    let report = build_verify_binary_report(
        Path::new("fixtures/direct-branch.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("aarch64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount {
                    kind: "binary_memory_write_oob".into(),
                    count: 1,
                }],
            }],
            solver_results: vec![solver_item],
            proof_evidence,
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );

    let json = serialize_verify_binary_json(&report).expect("serialize verify-binary JSON");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse verify-binary JSON");
    let item = &value["solver_result_items"][0];
    assert_eq!(item["replay_status"], "replayed");
    assert_eq!(item["replay_capability_evidence_matched"], true);
    assert_eq!(item["replay_capability_evidence"][0]["capability"], "direct_branch");
    assert_eq!(item["replay_capability_evidence"][0]["architecture"], "AArch64");
    assert_eq!(item["replay_capability_evidence"][0]["instruction_address"], 0x401000);
    assert_eq!(
        item["replay_capability_evidence"][0]["validation"],
        "decoded direct branch target validated against following trace step"
    );
    assert_eq!(value["proof_grade_gate"]["accepted"], false);
    assert_eq!(value["proof_grade_gate"]["checked_certificates_for_all_required_vcs"], false);

    let rendered = render_verify_binary_terminal(&report);
    assert!(rendered.contains("replay_capability_evidence matched=true"));
    assert!(rendered.contains("direct_branch@0x401000"));
    assert!(rendered.contains("proof-grade gate: rejected"));
}

#[test]
fn test_failed_x86_64_replay_with_mismatched_instruction_size_fails_closed() {
    let mut annotation = replay_test_annotation_with_bytes(0x401010, 0x90, vec![0x90]);
    annotation.instruction_size = 3;
    let function = replay_test_lifted_function(vec![annotation]);
    let result = trust_types::VerificationResult::Failed {
        solver: "ay-smtlib".into(),
        time_ms: 31,
        counterexample: Some(replay_test_counterexample("bb0@0x401010")),
    };
    let context = replay_test_context_with_arch(
        [0x401010],
        trust_symex::BoundedMachineCodeArchitecture::X86_64,
    );
    let vc = replay_test_vc();

    let item = binary_solver_result_report_with_replay(
        "main",
        "binary_memory_write_oob".into(),
        Some("0x401010".into()),
        &result,
        Some(BinaryReplayAttempt { function: &function, vc: &vc, context: Some(&context) }),
    );

    assert_eq!(item.replay_status.as_deref(), Some("not_attempted"));
    let replay_detail = item.replay_detail.as_deref().expect("replay detail");
    assert!(replay_detail.contains("original instruction byte length mismatch"));
    assert!(!replay_detail.contains("machine_replay_confirmed"));
}

#[test]
fn test_failed_binary_solver_result_with_unmapped_or_non_provenance_trace_is_not_replayed() {
    let vc = replay_test_vc();

    let unmapped_function = replay_test_lifted_function(Vec::new());
    let unmapped_result = trust_types::VerificationResult::Failed {
        solver: "ay-smtlib".into(),
        time_ms: 23,
        counterexample: Some(replay_test_counterexample("bb0@0x401010")),
    };
    let context = replay_test_context([0x401010]);
    let unmapped_item = binary_solver_result_report_with_replay(
        "main",
        "binary_memory_write_oob".into(),
        Some("0x401010".into()),
        &unmapped_result,
        Some(BinaryReplayAttempt {
            function: &unmapped_function,
            vc: &vc,
            context: Some(&context),
        }),
    );
    assert_eq!(unmapped_item.replay_status.as_deref(), Some("not_attempted"));
    assert!(
        unmapped_item
            .replay_detail
            .as_deref()
            .expect("unmapped replay detail")
            .contains("no original instruction bytes mapped")
    );

    let non_provenance_function =
        replay_test_lifted_function(vec![replay_test_annotation(0x401010)]);
    let non_provenance_result = trust_types::VerificationResult::Failed {
        solver: "ay-smtlib".into(),
        time_ms: 29,
        counterexample: Some(replay_test_counterexample("bb0@0x401010")),
    };
    let non_provenance_context = replay_test_context([]);
    let non_provenance_item = binary_solver_result_report_with_replay(
        "main",
        "binary_memory_write_oob".into(),
        Some("0x401010".into()),
        &non_provenance_result,
        Some(BinaryReplayAttempt {
            function: &non_provenance_function,
            vc: &vc,
            context: Some(&non_provenance_context),
        }),
    );
    assert_eq!(non_provenance_item.replay_status.as_deref(), Some("not_attempted"));
    assert!(
        non_provenance_item
            .replay_detail
            .as_deref()
            .expect("non-provenance replay detail")
            .contains("no exact source provenance")
    );
}

fn replay_test_context(addresses: impl IntoIterator<Item = u64>) -> BinaryReplayContext {
    replay_test_context_with_arch(addresses, trust_symex::BoundedMachineCodeArchitecture::Aarch64)
}

fn replay_test_context_with_arch(
    addresses: impl IntoIterator<Item = u64>,
    architecture: trust_symex::BoundedMachineCodeArchitecture,
) -> BinaryReplayContext {
    replay_test_context_with_segments(addresses, architecture, Vec::new())
}

fn replay_test_context_with_segments(
    addresses: impl IntoIterator<Item = u64>,
    architecture: trust_symex::BoundedMachineCodeArchitecture,
    loaded_segments: Vec<trust_symex::BoundedMachineCodeSegment>,
) -> BinaryReplayContext {
    BinaryReplayContext {
        architecture,
        address_map: trust_symex::BoundedMachineCodeAddressMap::new(),
        loaded_segments,
        loaded_binary_segments: Vec::new(),
        selected_image_bytes: None,
        root_artifact_digest: None,
        selected_image_identity: None,
        invalid_instruction_bytes: BTreeMap::new(),
        exact_source_addresses: addresses.into_iter().collect::<BTreeSet<_>>(),
        exact_replay_attestations: BTreeMap::new(),
        exact_replay_slice_blockers: Vec::new(),
    }
}

fn replay_test_context_with_exact_slice_attestation(
    addresses: impl IntoIterator<Item = u64>,
    architecture: trust_symex::BoundedMachineCodeArchitecture,
) -> BinaryReplayContext {
    let mut context = replay_test_context_with_arch(addresses, architecture);
    context.exact_replay_attestations.insert(
        0x401010,
        ExactReplayInstructionAttestationSummary { accepted: true, blockers: Vec::new() },
    );
    context
}

fn replay_test_lifted_function(
    annotations: Vec<trust_lift::cfg::ProofAnnotation>,
) -> trust_lift::LiftedFunction {
    let mut cfg = trust_lift::cfg::Cfg::new();
    cfg.add_block(trust_lift::cfg::LiftedBlock {
        id: 0,
        start_addr: 0x401000,
        instructions: Vec::new(),
        successors: Vec::new(),
        is_return: true,
    });

    trust_lift::LiftedFunction {
        name: "main".into(),
        entry_point: 0x401000,
        cfg,
        trust_ir_body: trust_types::VerifiableBody {
            locals: Vec::new(),
            blocks: vec![trust_types::BasicBlock {
                id: trust_types::BlockId(0),
                stmts: Vec::new(),
                terminator: trust_types::Terminator::Return,
            }],
            arg_count: 0,
            return_ty: trust_types::Ty::unit_ty(),
        },
        ssa: None,
        annotations,
        memory_accesses: Vec::new(),
        trust_level: trust_types::TrustLevel::Partial,
        unsupported: trust_types::UnsupportedLedger::default(),
    }
}

fn replay_test_annotation(address: u64) -> trust_lift::cfg::ProofAnnotation {
    replay_test_annotation_with_bytes(address, 0xd503201f, vec![0x1f, 0x20, 0x03, 0xd5])
}

fn replay_test_annotation_with_bytes(
    address: u64,
    encoding: u32,
    instruction_bytes: Vec<u8>,
) -> trust_lift::cfg::ProofAnnotation {
    trust_lift::cfg::ProofAnnotation {
        block_id: 0,
        stmt_index: 0,
        binary_offset: address,
        encoding,
        instruction_size: instruction_bytes.len() as u8,
        instruction_bytes,
    }
}

fn replay_test_counterexample(program_point: &str) -> trust_types::Counterexample {
    let mut trace_assignments = BTreeMap::new();
    trace_assignments.insert("_local0".to_string(), "1".to_string());
    trust_types::Counterexample::with_trace(
        vec![("_local0".into(), trust_types::CounterexampleValue::Int(1))],
        trust_types::CounterexampleTrace::new(vec![trust_types::TraceStep {
            step: 0,
            assignments: trace_assignments,
            program_point: Some(program_point.into()),
        }]),
    )
}

fn replay_test_call_return_counterexample() -> trust_types::Counterexample {
    fn trace_step(step: u32, address: u64, assignments: &[(&str, &str)]) -> trust_types::TraceStep {
        trust_types::TraceStep {
            step,
            assignments: assignments
                .iter()
                .map(|(name, value)| ((*name).to_string(), (*value).to_string()))
                .collect(),
            program_point: Some(format!("bb0@0x{address:x}")),
        }
    }

    trust_types::Counterexample::with_trace(
        vec![("_local0".into(), trust_types::CounterexampleValue::Int(1))],
        trust_types::CounterexampleTrace::new(vec![
            trace_step(0, 0x401010, &[("_local0", "1"), ("RSP", "0x8000")]),
            trace_step(1, 0x401020, &[("RSP", "0x7ff8"), ("stack:sp+0:8", "0x401015")]),
            trace_step(2, 0x401015, &[("RSP", "0x8000")]),
        ]),
    )
}

fn replay_test_vc() -> trust_types::VerificationCondition {
    trust_types::VerificationCondition {
        kind: VcKind::Unreachable,
        function: trust_types::Symbol::intern("binary::main"),
        location: trust_types::SourceSpan::binary_address(0x401010),
        formula: trust_types::Formula::Bool(true),
        contract_metadata: None,
    }
}

fn replay_test_lifted_binary(
    architecture: &'static str,
    function: trust_lift::LiftedFunction,
    segments: Vec<BinarySegment>,
) -> trust_lift::LiftedBinary {
    let source_mappings = function
        .annotations
        .iter()
        .map(|annotation| trust_lift::LiftedSourceMapping {
            binary_address: annotation.binary_offset,
            source: SourceSpan::binary_address(annotation.binary_offset),
        })
        .collect::<Vec<_>>();
    trust_lift::LiftedBinary {
        format: "ELF",
        architecture,
        endianness: trust_lift::binary::BinaryEndianness::Little,
        entry_point: Some(function.entry_point),
        build_id: None,
        segments,
        memory_model: Default::default(),
        function_seeds: Vec::new(),
        source_provenance: trust_lift::LiftedSourceProvenance {
            status: trust_lift::LiftedSourceProvenanceStatus::Exact,
            exact_mapping_count: source_mappings.len(),
            ambiguous_mapping_count: 0,
            diagnostics: Vec::new(),
        },
        source_mappings,
        functions: vec![function],
        failures: Vec::new(),
    }
}

fn replay_test_segment(
    virtual_start: u64,
    file_offset: u64,
    file_size: u64,
    execute: bool,
) -> BinarySegment {
    BinarySegment {
        name: Some(".text".to_string()),
        virtual_range: BinaryAddressRange { start: virtual_start, end: virtual_start + file_size },
        file_offset: Some(file_offset),
        file_size: Some(file_size),
        permissions: BinarySegmentPermissions { read: true, write: false, execute },
    }
}

#[test]
fn test_verify_binary_timeout_solver_result_is_non_proof() {
    let result = trust_types::VerificationResult::Timeout {
        solver: "ay-incremental".into(),
        timeout_ms: 50,
    };
    let solver_item = binary_solver_result_report(
        "main",
        "binary_memory_read_invalid".into(),
        Some("0x401030".into()),
        &result,
    );

    let report = build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount {
                    kind: "binary_memory_read_invalid".into(),
                    count: 1,
                }],
            }],
            solver_results: vec![solver_item],
            proof_evidence: verify_binary_evidence_for_vcs(1),
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );

    assert_eq!(report.solver_results.status, "timeout");
    assert_eq!(report.verification_status, "timeout");
    assert!(verify_binary_should_fail(&report));
}

#[test]
fn test_verify_binary_proof_grade_gate_rejects_missing_evidence_in_terminal_and_json() {
    let report = build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 2,
                vcs: 2,
                vc_counts: vec![BinaryVcKindCount {
                    kind: "binary_memory_write_oob".into(),
                    count: 2,
                }],
            }],
            solver_results: Vec::new(),
            proof_evidence: verify_binary_evidence_for_vcs(2),
            unsupported: vec!["trust-lift @ 0x401000: unsupported opcode".into()],
            failures: Vec::new(),
        },
    );

    let gate = build_binary_cli_proof_grade_gate(&report);
    assert!(!gate.accepted);
    assert_eq!(gate.status, "rejected");
    assert!(!gate.unsupported_ledger_empty);
    assert!(!gate.all_required_vcs_proved);
    assert!(!gate.checked_certificates_for_all_required_vcs);
    assert!(!gate.full_replay_coverage);
    assert!(!gate.replay_semantics_satisfied);
    assert_eq!(gate.required_vcs, 2);
    assert_eq!(gate.proved_vcs, 0);
    assert_eq!(gate.missing_checked_certificates, 2);
    assert_eq!(gate.missing_machine_replay, 2);
    assert!(gate.rejections.iter().any(|reason| reason.contains("unsupported records present")));
    assert!(gate.rejections.iter().any(|reason| reason.contains("required binary VCs")));
    assert!(gate.rejections.iter().any(|reason| reason.contains("checked proof certificates")));
    assert!(gate.rejections.iter().any(|reason| reason.contains("replay semantics missing")));
    assert!(gate.rejections.iter().any(|reason| reason.contains("raw solver proof bytes")));

    let rendered = render_verify_binary_terminal(&report);
    assert!(rendered.contains("proof-grade gate: rejected\n"));
    assert!(rendered.contains("proof-grade gate detail: unsupported_empty=false"));
    assert!(rendered.contains("vcs_proved=false"));
    assert!(rendered.contains("checked_certs=false"));
    assert!(rendered.contains("replay_coverage=false"));
    assert!(rendered.contains("replay_semantics=false"));
    assert!(rendered.contains("raw_solver_proof_bytes_sufficient=false"));
    assert!(rendered.contains("proof-grade counts: required_vcs=2 proved=0 checked_certs=0 replayed=0 exact_replay_slice_attested=0 cert_only_replay_semantics=0 replay_semantics_satisfied=0 raw_solver_proof_bytes=0\n"));
    assert!(rendered.contains("proof-grade rejections:\n"));
    assert!(rendered.contains("unsupported records present: 1 item(s)"));
    assert!(rendered.contains("checked proof certificates missing"));
    assert!(rendered.contains("replay semantics missing"));
    assert!(rendered.contains("raw solver proof bytes are not sufficient"));

    let json = serialize_verify_binary_json(&report).expect("serialize verify-binary JSON");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse JSON");
    let proof_gate = &value["proof_grade_gate"];
    assert_eq!(proof_gate["accepted"], false);
    assert_eq!(proof_gate["status"], "rejected");
    assert_eq!(proof_gate["unsupported_ledger_empty"], false);
    assert_eq!(proof_gate["all_required_vcs_proved"], false);
    assert_eq!(proof_gate["checked_certificates_for_all_required_vcs"], false);
    assert_eq!(proof_gate["full_replay_coverage"], false);
    assert_eq!(proof_gate["replay_semantics_satisfied"], false);
    assert_eq!(proof_gate["required_vcs"], 2);
    assert_eq!(proof_gate["proved_vcs"], 0);
    assert_eq!(proof_gate["missing_checked_certificates"], 2);
    assert_eq!(proof_gate["missing_machine_replay"], 2);
    assert_eq!(proof_gate["raw_solver_proof_bytes_sufficient"], false);
    let rejections = proof_gate["rejections"].as_array().expect("rejection array");
    assert!(rejections.iter().any(|reason| reason.as_str().unwrap().contains("unsupported")));
    assert!(
        rejections
            .iter()
            .any(|reason| reason.as_str().unwrap().contains("checked proof certificates"))
    );
}

#[test]
fn test_verify_binary_proof_grade_gate_counts_checked_dispatch_evidence() {
    let report = build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("aarch64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 2,
                vcs: 2,
                vc_counts: vec![BinaryVcKindCount {
                    kind: "binary_stack_pointer_restoration".into(),
                    count: 2,
                }],
            }],
            solver_results: Vec::new(),
            proof_evidence: VerifyBinaryEvidence::from_solver_dispatch_records(
                2,
                vec![
                    checked_binary_dispatch("vc-0", "main"),
                    checked_binary_dispatch("vc-1", "main"),
                ],
            ),
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );

    let gate = build_binary_cli_proof_grade_gate(&report);
    assert!(!gate.accepted);
    assert!(gate.all_required_vcs_proved);
    assert!(gate.checked_certificates_for_all_required_vcs);
    assert!(gate.full_replay_coverage);
    assert!(gate.replay_semantics_satisfied);
    assert_eq!(gate.solver_dispatches, 2);
    assert_eq!(gate.proved_vcs, 2);
    assert_eq!(gate.checked_certificates, 2);
    assert_eq!(gate.missing_checked_certificates, 0);
    assert_eq!(gate.replayed_vcs, 2);
    assert!(gate.exact_replay_slice_attestation_for_replayed_vcs);
    assert_eq!(gate.exact_replay_slice_attested_vcs, 2);
    assert_eq!(gate.missing_exact_replay_slice_attestation, 0);
    assert_eq!(gate.replay_semantics_satisfied_vcs, 2);
    assert_eq!(gate.certificate_only_replay_semantics_vcs, 0);
    assert_eq!(gate.missing_machine_replay, 0);
    assert_eq!(gate.raw_solver_proof_bytes, 0);
    assert!(gate.rejections.iter().any(|reason| reason.contains("final trust level")));
    assert!(
        !gate.rejections.iter().any(|reason| reason.contains("checked proof certificates missing"))
    );
    assert!(
        !gate
            .rejections
            .iter()
            .any(|reason| reason.contains("raw solver proof bytes are not sufficient"))
    );

    let json = serialize_verify_binary_json(&report).expect("serialize verify-binary JSON");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse JSON");
    let proof_gate = &value["proof_grade_gate"];
    assert_eq!(proof_gate["checked_certificates"], 2);
    assert_eq!(proof_gate["missing_checked_certificates"], 0);
    assert_eq!(proof_gate["checked_certificates_for_all_required_vcs"], true);
    assert_eq!(proof_gate["full_replay_coverage"], true);
    assert_eq!(proof_gate["replay_semantics_satisfied"], true);
    assert_eq!(proof_gate["exact_replay_slice_attestation_for_replayed_vcs"], true);
}

#[test]
fn test_verify_binary_shared_summary_caps_proof_grade_until_gate_accepts() {
    let mut blocked_report = build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 1 }],
            }],
            solver_results: Vec::new(),
            proof_evidence: VerifyBinaryEvidence::from_solver_dispatch_records(
                1,
                vec![raw_solver_binary_dispatch("vc-raw", "main")],
            ),
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );
    blocked_report.trust_level = "proof_grade".into();

    let blocked_gate = build_binary_cli_proof_grade_gate(&blocked_report);
    assert!(!blocked_gate.accepted);
    assert!(!blocked_gate.checked_certificates_for_all_required_vcs);
    assert!(!blocked_gate.replay_semantics_satisfied);
    let blocked_summary = binary_verify_shared_verification_summary(&blocked_report);
    assert_eq!(blocked_summary.trust_level, trust_types::TrustLevel::Partial);
    let blocked_json =
        serialize_verify_binary_json(&blocked_report).expect("serialize blocked report");
    let blocked_value: serde_json::Value =
        serde_json::from_str(&blocked_json).expect("parse blocked report JSON");
    assert_eq!(blocked_value["proof_grade_gate"]["accepted"], false);
    assert_eq!(blocked_value["proof_evidence"]["proof_grade_gate"]["accepted"], false);
    assert_eq!(blocked_value["proof_evidence"]["proof_grade_gate"]["final_trust_level"], "Partial");

    let mut accepted_report = build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 1 }],
            }],
            solver_results: Vec::new(),
            proof_evidence: VerifyBinaryEvidence::from_solver_dispatch_records(
                1,
                vec![canonical_sha_checked_binary_dispatch("vc-checked", "main")],
            ),
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );
    accepted_report.trust_level = "proof_grade".into();

    let accepted_gate = build_binary_cli_proof_grade_gate(&accepted_report);
    assert!(!accepted_gate.accepted);
    assert!(accepted_gate.checked_certificates_for_all_required_vcs);
    assert!(accepted_gate.replay_semantics_satisfied);
    assert!(!accepted_gate.checked_certificate_readback_for_all_required_vcs);
    assert!(!accepted_gate.replay_attestation_for_all_required_vcs);
    assert!(!accepted_gate.source_backpropagation_handoff_for_all_required_vcs);
    for required_code in [
        "checked-certificate-readback-missing",
        "replay-attestation-missing",
        "checked-certificate-source-backpropagation-handoff-missing",
    ] {
        assert!(
            accepted_gate.blockers.iter().any(|blocker| blocker.code == required_code),
            "missing {required_code} in {:?}",
            accepted_gate.blockers
        );
    }
    let accepted_summary = binary_verify_shared_verification_summary(&accepted_report);
    assert_eq!(accepted_summary.trust_level, trust_types::TrustLevel::Partial);
    let accepted_json =
        serialize_verify_binary_json(&accepted_report).expect("serialize accepted report");
    let accepted_value: serde_json::Value =
        serde_json::from_str(&accepted_json).expect("parse accepted report JSON");
    assert_eq!(accepted_value["proof_grade_gate"]["accepted"], false);
    assert_eq!(
        accepted_value["proof_grade_gate"]["checked_certificate_readback_for_all_required_vcs"],
        false
    );
    assert_eq!(
        accepted_value["proof_grade_gate"]["replay_attestation_for_all_required_vcs"],
        false
    );
    assert_eq!(
        accepted_value["proof_grade_gate"]["source_backpropagation_handoff_for_all_required_vcs"],
        false
    );
    assert_eq!(accepted_value["proof_evidence"]["proof_grade_gate"]["accepted"], false);
    assert_eq!(
        accepted_value["proof_evidence"]["proof_grade_gate"]["final_trust_level"],
        "Partial"
    );
}

#[test]
fn test_verify_binary_source_backprop_gate_fails_closed() {
    let mut partial_report = build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 1 }],
            }],
            solver_results: Vec::new(),
            proof_evidence: VerifyBinaryEvidence::from_solver_dispatch_records(
                1,
                vec![canonical_sha_checked_binary_dispatch("vc-checked", "main")],
            ),
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );
    partial_report.trust_level = "partial".into();

    let partial_json =
        serialize_verify_binary_json(&partial_report).expect("serialize partial verify report");
    let partial_value: serde_json::Value =
        serde_json::from_str(&partial_json).expect("parse partial verify JSON");
    let partial_gate = &partial_value["source_backpropagation_gate"];
    assert_eq!(partial_gate["accepted"], false);
    assert_eq!(partial_gate["status"], "rejected");
    assert_eq!(partial_gate["binary_verification_evidence"], "partial");
    assert_eq!(partial_gate["checked_certificate_source_backpropagation_gate"], "missing");
    assert!(
        partial_gate["blockers"]
            .as_array()
            .expect("source backprop blockers")
            .iter()
            .any(|blocker| blocker["code"] == "proof-grade-binary-verification-missing"),
        "{partial_gate}"
    );

    partial_report.trust_level = "proof_grade".into();
    let proof_gate = build_binary_cli_proof_grade_gate(&partial_report);
    assert!(!proof_gate.accepted);
    assert!(
        proof_gate.blockers.iter().any(|blocker| {
            blocker.code == "checked-certificate-source-backpropagation-handoff-missing"
        }),
        "{:?}",
        proof_gate.blockers
    );

    let proof_json =
        serialize_verify_binary_json(&partial_report).expect("serialize proof-grade verify report");
    let proof_value: serde_json::Value =
        serde_json::from_str(&proof_json).expect("parse proof-grade verify JSON");
    let source_gate = &proof_value["source_backpropagation_gate"];
    assert_eq!(source_gate["accepted"], false);
    assert_eq!(source_gate["binary_verification_evidence"], "partial");
    assert_eq!(source_gate["reconstruction_evidence"], "missing");
    assert_eq!(source_gate["checked_certificate_source_backpropagation_gate"], "missing");
    assert!(
        source_gate["blockers"].as_array().expect("source backprop blockers").iter().any(
            |blocker| blocker["code"] == "accepted-reconstruction-target-validation-missing"
                && blocker["detail"]
                    .as_str()
                    .expect("blocker detail")
                    .contains("accepted reconstruction and target validation")
        ),
        "{source_gate}"
    );

    let rendered = render_verify_binary_terminal(&partial_report);
    assert!(rendered.contains("source backpropagation gate: rejected"));
    assert!(rendered.contains("binary_verification=partial"));
    assert!(rendered.contains("reconstruction=missing"));
    assert!(rendered.contains("checked_certificate_source_backpropagation_gate=missing"));
    assert!(rendered.contains("accepted-reconstruction-target-validation-missing"));
    assert!(rendered.contains("checked-certificate-source-backpropagation-gate-missing"));
}

#[test]
fn test_verify_binary_sat_counterexample_requires_exact_byte_replay() {
    let report = build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount {
                    kind: "binary_memory_write_oob".into(),
                    count: 1,
                }],
            }],
            solver_results: Vec::new(),
            proof_evidence: VerifyBinaryEvidence::from_solver_dispatch_records(
                1,
                vec![sat_unreplayed_binary_dispatch("vc-sat", "main")],
            ),
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );

    let gate = build_binary_cli_proof_grade_gate(&report);

    assert!(!gate.accepted);
    assert!(!gate.all_required_vcs_proved);
    assert!(!gate.replay_semantics_satisfied);
    assert!(!gate.full_replay_coverage);
    assert_eq!(gate.replayed_vcs, 0);
    assert_eq!(gate.replay_semantics_satisfied_vcs, 0);
    assert_eq!(gate.missing_machine_replay, 1);
    assert!(gate.rejections.iter().any(|reason| reason.contains("replay semantics missing")));
}

#[test]
fn test_verify_binary_unsat_checked_certificate_satisfies_replay_semantics_without_replay() {
    let report = build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 1 }],
            }],
            solver_results: Vec::new(),
            proof_evidence: VerifyBinaryEvidence::from_solver_dispatch_records(
                1,
                vec![checked_certificate_only_binary_dispatch("vc-unsat", "main")],
            ),
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );

    let gate = build_binary_cli_proof_grade_gate(&report);

    assert!(!gate.accepted);
    assert!(gate.all_required_vcs_proved);
    assert!(gate.checked_certificates_for_all_required_vcs);
    assert!(!gate.full_replay_coverage);
    assert!(gate.replay_semantics_satisfied);
    assert_eq!(gate.replayed_vcs, 0);
    assert_eq!(gate.certificate_only_replay_semantics_vcs, 1);
    assert_eq!(gate.replay_semantics_satisfied_vcs, 1);
    assert_eq!(gate.missing_machine_replay, 0);
    assert!(gate.rejections.iter().any(|reason| reason.contains("final trust level")));
    assert!(!gate.rejections.iter().any(|reason| reason.contains("replay semantics missing")));
    assert!(!gate.rejections.iter().any(|reason| reason.contains("machine replay coverage")));
}

#[test]
fn test_verify_binary_replayed_dispatch_without_exact_slice_attestation_blocks_proof_grade() {
    let mut dispatch = canonical_sha_checked_binary_dispatch("vc-replayed-unattested", "main");
    dispatch.diagnostics.clear();
    let mut report = build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 1 }],
            }],
            solver_results: Vec::new(),
            proof_evidence: VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![dispatch]),
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );
    report.trust_level = "proof_grade".into();

    let gate = build_binary_cli_proof_grade_gate(&report);

    assert!(!gate.accepted);
    assert!(gate.all_required_vcs_proved);
    assert!(gate.checked_certificates_for_all_required_vcs);
    assert!(gate.full_replay_coverage);
    assert!(!gate.replay_semantics_satisfied);
    assert!(!gate.exact_replay_slice_attestation_for_replayed_vcs);
    assert_eq!(gate.replayed_vcs, 1);
    assert_eq!(gate.exact_replay_slice_attested_vcs, 0);
    assert_eq!(gate.missing_exact_replay_slice_attestation, 1);
    assert!(gate.blockers.iter().any(|blocker| {
        blocker.code == "exact-replay-slice-attestation-missing"
            && blocker.evidence_required.contains(&"selected_image_bytes".to_string())
    }));
    assert!(
        gate.rejections.iter().any(|reason| {
            reason.contains("selected-image byte/segment attestation accepted 0/1")
        })
    );

    let json = serialize_verify_binary_json(&report).expect("serialize verify-binary JSON");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse verify-binary JSON");
    assert_eq!(value["proof_grade_gate"]["exact_replay_slice_attestation_for_replayed_vcs"], false);
    assert_eq!(value["proof_grade_gate"]["exact_replay_slice_attested_vcs"], 0);
    assert_eq!(value["proof_grade_gate"]["missing_exact_replay_slice_attestation"], 1);
    assert!(
        value["proof_grade_gate"]["blockers"]
            .as_array()
            .expect("proof-grade blockers")
            .iter()
            .any(|blocker| blocker["code"] == "exact-replay-slice-attestation-missing"),
        "{value}"
    );
}

#[test]
fn test_exact_replay_sat_candidate_missing_memory_effect_binding_is_not_replay_ready() {
    let root = temp_test_dir("exact-replay-missing-memory-effect");
    std::fs::create_dir_all(&root).expect("test dir should be writable");
    let binary_path = root.join("tiny.bin");
    let binary_bytes = vec![0x90; 64];
    std::fs::write(&binary_path, &binary_bytes).expect("test binary should be writable");

    let mut complete_dispatch = exact_replay_bound_sat_dispatch("vc-sat-complete-replay-witness");
    bind_exact_replay_dispatch_to_binary(&mut complete_dispatch, &binary_path, &binary_bytes);
    let complete_evidence =
        VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![complete_dispatch]);
    assert_eq!(complete_evidence.replayed_vcs(), 1);
    assert_eq!(complete_evidence.exact_replay_slice_attested_vcs(), 1);
    assert_eq!(complete_evidence.replay_semantics_satisfied_vcs(), 1);

    let mut missing_memory_effect =
        exact_replay_bound_sat_dispatch("vc-sat-missing-memory-effect-witness");
    bind_exact_replay_dispatch_to_binary(&mut missing_memory_effect, &binary_path, &binary_bytes);
    missing_memory_effect
        .diagnostics
        .retain(|diagnostic| diagnostic != EXACT_REPLAY_WITNESS_MEMORY_EFFECT_DIAGNOSTIC);
    let missing_evidence =
        VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![missing_memory_effect]);

    assert_eq!(missing_evidence.replayed_vcs(), 1);
    assert_eq!(missing_evidence.exact_replay_slice_attested_vcs(), 0);
    assert_eq!(missing_evidence.replay_semantics_satisfied_vcs(), 0);
    assert!(
        dispatch_exact_replay_transcript_artifact_digest(&missing_evidence.solver_dispatch[0])
            .is_none()
    );
    assert!(
        missing_evidence
            .exact_replay_slice_attestation_blockers()
            .iter()
            .any(|blocker| blocker.contains("memory/effect attestation")),
    );

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_exact_replay_producer_derives_normalized_witness_binding() {
    let root = temp_test_dir("exact-replay-producer-binding");
    std::fs::create_dir_all(&root).expect("test dir should be writable");
    let binary_path = root.join("tiny.bin");
    let binary_bytes = vec![0x90; 64];
    std::fs::write(&binary_path, &binary_bytes).expect("test binary should be writable");
    let binary_sha256 = trust_types::digest::stable_sha256_hex(&binary_bytes);

    let router = Router::with_backends(vec![Box::new(ReplaySatBackend)]);
    let function = replay_test_lifted_function(vec![replay_test_annotation_with_bytes(
        0x401010,
        0x90,
        vec![0x90],
    )]);
    let context = replay_test_context_with_exact_slice_attestation(
        [0x401010],
        trust_symex::BoundedMachineCodeArchitecture::X86_64,
    );
    let vc = replay_test_vc();

    let (_reports, dispatch_records) = dispatch_binary_vcs_with_replay_evidence(
        &router,
        BinarySolverRoute::AYIncremental,
        Some(&binary_path),
        &function,
        Some(&context),
        std::slice::from_ref(&vc),
    );
    assert_eq!(dispatch_records.len(), 1);
    assert_eq!(dispatch_records[0].replay, ReplayStatus::Replayed);
    assert!(
        dispatch_records[0]
            .diagnostics
            .contains(&EXACT_REPLAY_SLICE_ATTESTATION_ACCEPTED_DIAGNOSTIC.to_string())
    );
    assert!(
        !dispatch_records[0]
            .diagnostics
            .contains(&EXACT_REPLAY_WITNESS_BINDING_ACCEPTED_DIAGNOSTIC.to_string())
    );

    let mut evidence = VerifyBinaryEvidence::default();
    evidence.add_required_vcs(1);
    evidence.extend_solver_dispatch(dispatch_records);

    assert_eq!(evidence.replayed_vcs(), 1);
    assert_eq!(evidence.exact_replay_slice_attested_vcs(), 1);
    assert_eq!(evidence.replay_semantics_satisfied_vcs(), 1);
    let dispatch = &evidence.solver_dispatch[0];
    for diagnostic in exact_replay_witness_binding_diagnostics() {
        assert!(dispatch.diagnostics.contains(&diagnostic), "{diagnostic}");
    }
    let identity = dispatch
        .binary_artifact_digest_identity
        .as_ref()
        .expect("producer should derive binary identity");
    assert_eq!(
        identity.root_artifact_digest.as_ref().map(|digest| digest.value.as_str()),
        Some(binary_sha256.as_str())
    );
    let selected = identity.selected_image.as_ref().expect("selected image identity");
    assert_eq!(selected.file_offset, 0);
    assert_eq!(selected.file_size, 64);
    assert_eq!(selected.sha256, binary_sha256);
}

#[test]
fn test_exact_replay_selected_image_dispatch_matches_golden() {
    let binary_path = PathBuf::from("target/exact-replay-selected-image-dispatch.bin");
    std::fs::create_dir_all(binary_path.parent().expect("target parent"))
        .expect("target dir should be writable");
    let binary_bytes = vec![0x90];
    std::fs::write(&binary_path, &binary_bytes).expect("selected image fixture should be writable");
    let binary_sha256 = trust_types::digest::stable_sha256_hex(&binary_bytes);

    let function = replay_test_lifted_function(vec![replay_test_annotation_with_bytes(
        0x401010,
        0x90,
        binary_bytes.clone(),
    )]);
    let binary = replay_test_lifted_binary(
        "x86_64",
        function,
        vec![replay_test_segment(0x401010, 0, binary_bytes.len() as u64, true)],
    );
    let context = BinaryReplayContext::from_lifted_binary(&binary, Some(&binary_bytes))
        .expect("selected x86_64 image should build replay context");
    let router = Router::with_backends(vec![Box::new(ReplaySatBackend)]);
    let vc = replay_test_vc();

    let (_reports, dispatch_records) = dispatch_binary_vcs_with_replay_evidence(
        &router,
        BinarySolverRoute::AYIncremental,
        Some(&binary_path),
        &binary.functions[0],
        Some(&context),
        std::slice::from_ref(&vc),
    );
    assert_eq!(dispatch_records.len(), 1);
    assert_eq!(dispatch_records[0].replay, ReplayStatus::Replayed);
    assert!(dispatch_records[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.starts_with(EXACT_REPLAY_BYTE_RANGE_FACT_DIAGNOSTIC_PREFIX)
    }));
    assert!(dispatch_records[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.starts_with(EXACT_REPLAY_CONTROL_FLOW_FACT_DIAGNOSTIC_PREFIX)
    }));
    assert!(dispatch_records[0].diagnostics.iter().any(|diagnostic| {
        diagnostic.starts_with(EXACT_REPLAY_MEMORY_EFFECT_FACT_DIAGNOSTIC_PREFIX)
    }));

    let mut evidence = VerifyBinaryEvidence::default();
    evidence.add_required_vcs(1);
    evidence.extend_solver_dispatch(dispatch_records);
    assert_eq!(evidence.replayed_vcs(), 1);
    assert_eq!(evidence.exact_replay_slice_attested_vcs(), 1);
    assert_eq!(evidence.replay_semantics_satisfied_vcs(), 1);

    let dispatch = &evidence.solver_dispatch[0];
    let transcript_digest = dispatch_exact_replay_transcript_artifact_digest(dispatch)
        .expect("real selected-image replay should produce transcript digest");
    assert_json_canonical_sha256(
        &serde_json::Value::String(transcript_digest.clone()),
        "selected-image replay transcript digest",
    );
    let identity = dispatch
        .binary_artifact_digest_identity
        .as_ref()
        .expect("selected image replay should bind binary identity");
    assert_eq!(
        identity.root_artifact_digest.as_ref().map(|digest| digest.value.as_str()),
        Some(binary_sha256.as_str())
    );
    assert_eq!(
        identity.selected_image.as_ref().map(|selected| selected.sha256.as_str()),
        Some(binary_sha256.as_str())
    );

    let actual = serde_json::json!({
        "replay": "replayed",
        "transcript_digest": "<canonical-sha256>",
        "root_artifact_sha256": identity.root_artifact_digest.as_ref().map(|digest| digest.value.clone()),
        "selected_image": identity.selected_image.as_ref().map(|selected| serde_json::json!({
            "file_offset": selected.file_offset,
            "file_size": selected.file_size,
            "sha256": selected.sha256,
        })),
        "byte_range_facts": exact_replay_dispatch_facts(
            dispatch,
            EXACT_REPLAY_BYTE_RANGE_FACT_DIAGNOSTIC_PREFIX,
        ),
        "control_flow_facts": exact_replay_dispatch_facts(
            dispatch,
            EXACT_REPLAY_CONTROL_FLOW_FACT_DIAGNOSTIC_PREFIX,
        ),
        "memory_effect_facts": exact_replay_dispatch_facts(
            dispatch,
            EXACT_REPLAY_MEMORY_EFFECT_FACT_DIAGNOSTIC_PREFIX,
        ),
    });
    let expected: serde_json::Value = serde_json::from_str(include_str!(
        "fixtures/exact_replay_selected_image_dispatch_golden.json"
    ))
    .expect("parse selected-image exact replay golden");
    assert_eq!(actual, expected);

    let _ = std::fs::remove_file(binary_path);
}

#[test]
fn test_exact_replay_selected_image_dispatch_binds_call_return_effect_facts() {
    let binary_path = PathBuf::from("target/exact-replay-call-return-dispatch.bin");
    std::fs::create_dir_all(binary_path.parent().expect("target parent"))
        .expect("target dir should be writable");
    let call_bytes = [0xe8, 0x0b, 0x00, 0x00, 0x00];
    let ret_bytes = [0xc3];
    let nop_bytes = [0x90];
    let mut binary_bytes = vec![0x90; 0x11];
    binary_bytes[0..call_bytes.len()].copy_from_slice(&call_bytes);
    binary_bytes[0x10] = ret_bytes[0];
    std::fs::write(&binary_path, &binary_bytes)
        .expect("call-return selected image fixture should be writable");
    let binary_sha256 = trust_types::digest::stable_sha256_hex(&binary_bytes);

    let function = replay_test_lifted_function(vec![
        replay_test_annotation_with_bytes(0x401010, 0xe8, call_bytes.to_vec()),
        replay_test_annotation_with_bytes(0x401020, 0xc3, ret_bytes.to_vec()),
        replay_test_annotation_with_bytes(0x401015, 0x90, nop_bytes.to_vec()),
    ]);
    let binary = replay_test_lifted_binary(
        "x86_64",
        function,
        vec![
            replay_test_segment(0x401010, 0, binary_bytes.len() as u64, true),
            BinarySegment {
                name: Some(".stack".to_string()),
                virtual_range: BinaryAddressRange { start: 0x7000, end: 0x9000 },
                file_offset: None,
                file_size: None,
                permissions: BinarySegmentPermissions { read: true, write: true, execute: false },
            },
        ],
    );
    let context = BinaryReplayContext::from_lifted_binary(&binary, Some(&binary_bytes))
        .expect("call-return x86_64 image should build replay context");
    let router = Router::with_backends(vec![Box::new(ReplaySatCallReturnBackend)]);
    let vc = replay_test_vc();

    let (_reports, dispatch_records) = dispatch_binary_vcs_with_replay_evidence(
        &router,
        BinarySolverRoute::AYIncremental,
        Some(&binary_path),
        &binary.functions[0],
        Some(&context),
        std::slice::from_ref(&vc),
    );
    assert_eq!(dispatch_records.len(), 1);
    assert_eq!(dispatch_records[0].replay, ReplayStatus::Replayed);

    let mut evidence = VerifyBinaryEvidence::default();
    evidence.add_required_vcs(1);
    evidence.extend_solver_dispatch(dispatch_records);
    assert_eq!(evidence.replayed_vcs(), 1);
    assert_eq!(evidence.exact_replay_slice_attested_vcs(), 1);
    assert_eq!(evidence.replay_semantics_satisfied_vcs(), 1);

    let dispatch = &evidence.solver_dispatch[0];
    assert!(
        dispatch
            .diagnostics
            .contains(&EXACT_REPLAY_SLICE_ATTESTATION_ACCEPTED_DIAGNOSTIC.to_string())
    );
    let transcript_digest = dispatch_exact_replay_transcript_artifact_digest(dispatch)
        .expect("call-return replay should produce transcript digest");
    assert_json_canonical_sha256(
        &serde_json::Value::String(transcript_digest.clone()),
        "call-return replay transcript digest",
    );
    assert!(dispatch.diagnostics.iter().any(|diagnostic| diagnostic
        == &format!(
            "{EXACT_REPLAY_TRANSCRIPT_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX}{transcript_digest}"
        )));
    let identity = dispatch
        .binary_artifact_digest_identity
        .as_ref()
        .expect("call-return replay should bind binary identity");
    assert_eq!(
        identity.root_artifact_digest.as_ref().map(|digest| digest.value.as_str()),
        Some(binary_sha256.as_str())
    );
    let selected = identity.selected_image.as_ref().expect("selected image identity");
    assert_eq!(selected.file_offset, 0);
    assert_eq!(selected.file_size, binary_bytes.len() as u64);
    assert_eq!(selected.sha256, binary_sha256);

    let byte_range_facts =
        exact_replay_dispatch_facts(dispatch, EXACT_REPLAY_BYTE_RANGE_FACT_DIAGNOSTIC_PREFIX);
    for address in [0x401010, 0x401020, 0x401015] {
        assert!(
            byte_range_facts
                .iter()
                .any(|fact| fact.contains(&format!("instruction=0x{address:x};"))),
            "{byte_range_facts:?}"
        );
    }

    let control_flow_facts =
        exact_replay_dispatch_facts(dispatch, EXACT_REPLAY_CONTROL_FLOW_FACT_DIAGNOSTIC_PREFIX);
    assert!(
        control_flow_facts.iter().any(|fact| fact.contains("instruction=0x401010;")
            && fact.contains("architecture=x86_64;capability=direct_call")),
        "{control_flow_facts:?}"
    );
    assert!(
        control_flow_facts.iter().any(|fact| fact.contains("instruction=0x401020;")
            && fact.contains("architecture=x86_64;capability=return")),
        "{control_flow_facts:?}"
    );

    let effect_facts =
        exact_replay_dispatch_facts(dispatch, EXACT_REPLAY_MEMORY_EFFECT_FACT_DIAGNOSTIC_PREFIX);
    assert!(
        effect_facts.iter().any(|fact| fact.contains("instruction=0x401010;")
            && fact.contains("kind=memory_write;")
            && fact.contains("memory_address=0x7ff8;memory_width_bytes=8")),
        "{effect_facts:?}"
    );
    assert!(
        effect_facts.iter().any(|fact| fact.contains("instruction=0x401020;")
            && fact.contains("kind=memory_read;")
            && fact.contains("memory_address=0x7ff8;memory_width_bytes=8")),
        "{effect_facts:?}"
    );

    let _ = std::fs::remove_file(binary_path);
}

#[test]
fn test_exact_replay_selected_image_dispatch_rejects_missing_bytes_and_trace_mismatch() {
    let binary_path = PathBuf::from("target/exact-replay-selected-image-negative.bin");
    std::fs::create_dir_all(binary_path.parent().expect("target parent"))
        .expect("target dir should be writable");
    let binary_bytes = vec![0x90];
    std::fs::write(&binary_path, &binary_bytes).expect("selected image fixture should be writable");
    let vc = replay_test_vc();

    let missing_bytes_function =
        replay_test_lifted_function(vec![replay_test_annotation_with_bytes(
            0x401010,
            0x90,
            Vec::new(),
        )]);
    let missing_bytes_binary = replay_test_lifted_binary(
        "x86_64",
        missing_bytes_function,
        vec![replay_test_segment(0x401010, 0, binary_bytes.len() as u64, true)],
    );
    let missing_context =
        BinaryReplayContext::from_lifted_binary(&missing_bytes_binary, Some(&binary_bytes))
            .expect("missing-byte binary still has selected-image context");
    let missing_router = Router::with_backends(vec![Box::new(ReplaySatBackend)]);
    let (missing_reports, missing_dispatches) = dispatch_binary_vcs_with_replay_evidence(
        &missing_router,
        BinarySolverRoute::AYIncremental,
        Some(&binary_path),
        &missing_bytes_binary.functions[0],
        Some(&missing_context),
        std::slice::from_ref(&vc),
    );
    assert_eq!(missing_dispatches[0].replay, ReplayStatus::NotAttempted);
    assert!(
        missing_reports[0]
            .replay_detail
            .as_deref()
            .expect("missing-byte replay detail")
            .contains("original instruction bytes missing")
    );

    let exact_function = replay_test_lifted_function(vec![replay_test_annotation_with_bytes(
        0x401010,
        0x90,
        binary_bytes.clone(),
    )]);
    let exact_binary = replay_test_lifted_binary(
        "x86_64",
        exact_function,
        vec![replay_test_segment(0x401010, 0, binary_bytes.len() as u64, true)],
    );
    let exact_context = BinaryReplayContext::from_lifted_binary(&exact_binary, Some(&binary_bytes))
        .expect("exact binary should build selected-image context");
    let mismatch_router =
        Router::with_backends(vec![Box::new(ReplaySatProgramPointBackend("bb0@0x401011"))]);
    let (mismatch_reports, mismatch_dispatches) = dispatch_binary_vcs_with_replay_evidence(
        &mismatch_router,
        BinarySolverRoute::AYIncremental,
        Some(&binary_path),
        &exact_binary.functions[0],
        Some(&exact_context),
        std::slice::from_ref(&vc),
    );
    assert_eq!(mismatch_dispatches[0].replay, ReplayStatus::NotAttempted);
    assert!(
        mismatch_reports[0]
            .replay_detail
            .as_deref()
            .expect("trace-mismatch replay detail")
            .contains("no exact source provenance for trace address 0x401011")
    );

    let _ = std::fs::remove_file(binary_path);
}

#[test]
fn test_exact_replay_selected_image_dispatch_rejects_unsupported_and_bad_ranges() {
    let binary_path = PathBuf::from("target/exact-replay-selected-image-ranges.bin");
    std::fs::create_dir_all(binary_path.parent().expect("target parent"))
        .expect("target dir should be writable");
    let vc = replay_test_vc();

    let push_bytes = vec![0x50];
    std::fs::write(&binary_path, &push_bytes).expect("selected image fixture should be writable");
    let push_function = replay_test_lifted_function(vec![replay_test_annotation_with_bytes(
        0x401010,
        0x50,
        push_bytes.clone(),
    )]);
    let push_binary = replay_test_lifted_binary(
        "x86_64",
        push_function,
        vec![replay_test_segment(0x401010, 0, push_bytes.len() as u64, true)],
    );
    let push_context = BinaryReplayContext::from_lifted_binary(&push_binary, Some(&push_bytes))
        .expect("push binary should build selected-image context");
    let router = Router::with_backends(vec![Box::new(ReplaySatBackend)]);
    let (push_reports, push_dispatches) = dispatch_binary_vcs_with_replay_evidence(
        &router,
        BinarySolverRoute::AYIncremental,
        Some(&binary_path),
        &push_binary.functions[0],
        Some(&push_context),
        std::slice::from_ref(&vc),
    );
    assert_eq!(push_dispatches[0].replay, ReplayStatus::NotAttempted);
    let push_detail = push_reports[0].replay_detail.as_deref().expect("push replay detail");
    assert!(push_detail.contains("unsupported bounded machine replay"), "{push_detail}");
    assert!(push_detail.contains("memory write"), "{push_detail}");

    let nonexec_function = replay_test_lifted_function(vec![replay_test_annotation_with_bytes(
        0x401010,
        0x90,
        vec![0x90],
    )]);
    let nonexec_binary = replay_test_lifted_binary(
        "x86_64",
        nonexec_function,
        vec![replay_test_segment(0x401010, 0, 1, false)],
    );
    let nonexec_context = BinaryReplayContext::from_lifted_binary(&nonexec_binary, Some(&[0x90]))
        .expect("non-executable binary should still build selected-image context");
    let nonexec_router = Router::with_backends(vec![Box::new(ReplaySatBackend)]);
    let (nonexec_reports, nonexec_dispatches) = dispatch_binary_vcs_with_replay_evidence(
        &nonexec_router,
        BinarySolverRoute::AYIncremental,
        Some(&binary_path),
        &nonexec_binary.functions[0],
        Some(&nonexec_context),
        std::slice::from_ref(&vc),
    );
    assert_eq!(nonexec_dispatches[0].replay, ReplayStatus::NotAttempted);
    assert!(
        nonexec_reports[0]
            .replay_detail
            .as_deref()
            .expect("non-executable replay detail")
            .contains("no file-backed executable byte range")
    );

    let out_of_image_function =
        replay_test_lifted_function(vec![replay_test_annotation_with_bytes(
            0x401010,
            0x90,
            vec![0x90],
        )]);
    let out_of_image_binary = replay_test_lifted_binary(
        "x86_64",
        out_of_image_function,
        vec![replay_test_segment(0x401010, 8, 1, true)],
    );
    let out_of_image_context =
        BinaryReplayContext::from_lifted_binary(&out_of_image_binary, Some(&[0x90]))
            .expect("out-of-image binary should still build selected-image context");
    let out_router = Router::with_backends(vec![Box::new(ReplaySatBackend)]);
    let (out_reports, out_dispatches) = dispatch_binary_vcs_with_replay_evidence(
        &out_router,
        BinarySolverRoute::AYIncremental,
        Some(&binary_path),
        &out_of_image_binary.functions[0],
        Some(&out_of_image_context),
        std::slice::from_ref(&vc),
    );
    assert_eq!(out_dispatches[0].replay, ReplayStatus::NotAttempted);
    assert!(
        out_reports[0]
            .replay_detail
            .as_deref()
            .expect("out-of-image replay detail")
            .contains("outside selected loaded image")
    );

    let _ = std::fs::remove_file(binary_path);
}

#[test]
fn test_exact_replay_selected_image_dispatch_rejects_architecture_mismatch() {
    let binary_path = PathBuf::from("target/exact-replay-selected-image-arch-mismatch.bin");
    std::fs::create_dir_all(binary_path.parent().expect("target parent"))
        .expect("target dir should be writable");
    let aarch64_nop = vec![0x1f, 0x20, 0x03, 0xd5];
    std::fs::write(&binary_path, &aarch64_nop).expect("selected image fixture should be writable");
    let function = replay_test_lifted_function(vec![replay_test_annotation_with_bytes(
        0x401010,
        0xd503201f,
        aarch64_nop.clone(),
    )]);
    let binary = replay_test_lifted_binary(
        "x86_64",
        function,
        vec![replay_test_segment(0x401010, 0, aarch64_nop.len() as u64, true)],
    );
    let context = BinaryReplayContext::from_lifted_binary(&binary, Some(&aarch64_nop))
        .expect("architecture mismatch binary should build selected-image context");
    let router = Router::with_backends(vec![Box::new(ReplaySatBackend)]);
    let vc = replay_test_vc();

    let (reports, dispatches) = dispatch_binary_vcs_with_replay_evidence(
        &router,
        BinarySolverRoute::AYIncremental,
        Some(&binary_path),
        &binary.functions[0],
        Some(&context),
        std::slice::from_ref(&vc),
    );

    assert_eq!(dispatches[0].replay, ReplayStatus::NotAttempted);
    let replay_detail = reports[0].replay_detail.as_deref().expect("arch replay detail");
    assert!(replay_detail.contains("architecture mismatch"), "{replay_detail}");
    assert!(replay_detail.contains("x86_64"), "{replay_detail}");
    assert!(replay_detail.contains("AArch64"), "{replay_detail}");

    let _ = std::fs::remove_file(binary_path);
}

#[test]
fn test_replay_transcript_digest_derives_from_exact_replay_witness_binding() {
    let root = temp_test_dir("exact-replay-transcript-digest");
    std::fs::create_dir_all(&root).expect("test dir should be writable");
    let binary_path = root.join("tiny.bin");
    let binary_bytes = vec![0x90; 64];
    std::fs::write(&binary_path, &binary_bytes).expect("test binary should be writable");

    let mut dispatch = exact_replay_bound_sat_dispatch("vc-sat-replay-transcript");
    bind_exact_replay_dispatch_to_binary(&mut dispatch, &binary_path, &binary_bytes);
    dispatch.diagnostics.retain(|diagnostic| {
        !diagnostic.starts_with(EXACT_REPLAY_TRANSCRIPT_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX)
    });
    let mut evidence = VerifyBinaryEvidence::default();
    evidence.add_required_vcs(1);
    evidence.extend_solver_dispatch([dispatch]);

    assert_eq!(evidence.exact_replay_slice_attested_vcs(), 1);
    let dispatch = &evidence.solver_dispatch[0];
    let digest = dispatch_exact_replay_transcript_artifact_digest(dispatch)
        .expect("replay-ready witness should produce transcript digest");
    assert_json_canonical_sha256(
        &serde_json::Value::String(digest.clone()),
        "exact replay transcript digest",
    );
    assert!(
        dispatch.diagnostics.iter().any(|diagnostic| diagnostic
            == &format!("{EXACT_REPLAY_TRANSCRIPT_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX}{digest}")),
        "{:?}",
        dispatch.diagnostics
    );

    let mut changed_instruction =
        exact_replay_bound_sat_dispatch("vc-sat-replay-transcript-changed-instruction");
    bind_exact_replay_dispatch_to_binary(&mut changed_instruction, &binary_path, &binary_bytes);
    changed_instruction
        .origin
        .as_mut()
        .expect("exact replay fixture has origin")
        .instruction_bytes = vec![0x91];
    let mut changed_evidence = VerifyBinaryEvidence::default();
    changed_evidence.add_required_vcs(1);
    changed_evidence.extend_solver_dispatch([changed_instruction]);
    let changed_digest =
        dispatch_exact_replay_transcript_artifact_digest(&changed_evidence.solver_dispatch[0])
            .expect("changed instruction binding should still produce a digest");
    assert_ne!(digest, changed_digest, "transcript digest must bind normalized instruction bytes");

    let mut changed_fact = exact_replay_bound_sat_dispatch("vc-sat-replay-transcript-changed-fact");
    bind_exact_replay_dispatch_to_binary(&mut changed_fact, &binary_path, &binary_bytes);
    changed_fact.diagnostics.push(format!(
        "{EXACT_REPLAY_MEMORY_EFFECT_FACT_DIAGNOSTIC_PREFIX}instruction=0x401010;step=0;witness_step=0;architecture=x86_64;kind=no_state_change;subject=changed;memory_address=none;memory_width_bytes=none;validation_sha256={}",
        trust_types::digest::stable_sha256_hex(b"changed memory effect fact")
    ));
    let mut changed_fact_evidence = VerifyBinaryEvidence::default();
    changed_fact_evidence.add_required_vcs(1);
    changed_fact_evidence.extend_solver_dispatch([changed_fact]);
    let changed_fact_digest =
        dispatch_exact_replay_transcript_artifact_digest(&changed_fact_evidence.solver_dispatch[0])
            .expect("changed fact binding should still produce a digest");
    assert_ne!(digest, changed_fact_digest, "transcript digest must bind replay fact diagnostics");

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_replay_transcript_digest_rejects_stale_selected_image_binding() {
    let root = temp_test_dir("exact-replay-transcript-stale-selected-image");
    std::fs::create_dir_all(&root).expect("test dir should be writable");
    let binary_path = root.join("tiny.bin");
    let binary_bytes = vec![0x90; 64];
    std::fs::write(&binary_path, &binary_bytes).expect("test binary should be writable");

    let mut dispatch = exact_replay_bound_sat_dispatch("vc-sat-stale-selected-image");
    bind_exact_replay_dispatch_to_binary(&mut dispatch, &binary_path, &binary_bytes);
    dispatch
        .binary_artifact_digest_identity
        .as_mut()
        .and_then(|identity| identity.selected_image.as_mut())
        .expect("selected image identity")
        .sha256 = trust_types::digest::stable_sha256_hex(b"stale selected image binding");
    let mut evidence = VerifyBinaryEvidence::default();
    evidence.add_required_vcs(1);
    evidence.extend_solver_dispatch([dispatch]);

    assert_eq!(evidence.replayed_vcs(), 1);
    assert_eq!(evidence.exact_replay_slice_attested_vcs(), 0);
    assert!(
        dispatch_exact_replay_transcript_artifact_digest(&evidence.solver_dispatch[0]).is_none()
    );
    assert!(
        evidence
            .exact_replay_slice_attestation_blockers()
            .iter()
            .any(|blocker| blocker.contains("selected image digest does not match")),
        "{:?}",
        evidence.exact_replay_slice_attestation_blockers()
    );

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_replay_transcript_digest_rejects_unsupported_memory_effect_binding() {
    let root = temp_test_dir("exact-replay-transcript-unsupported-effect");
    std::fs::create_dir_all(&root).expect("test dir should be writable");
    let binary_path = root.join("tiny.bin");
    let binary_bytes = vec![0x90; 64];
    std::fs::write(&binary_path, &binary_bytes).expect("test binary should be writable");

    let mut dispatch = exact_replay_bound_sat_dispatch("vc-sat-unsupported-effect");
    bind_exact_replay_dispatch_to_binary(&mut dispatch, &binary_path, &binary_bytes);
    dispatch
        .diagnostics
        .retain(|diagnostic| diagnostic != EXACT_REPLAY_WITNESS_MEMORY_EFFECT_DIAGNOSTIC);
    dispatch.diagnostics.push("unsupported machine memory/effect witness class".to_string());
    let mut evidence = VerifyBinaryEvidence::default();
    evidence.add_required_vcs(1);
    evidence.extend_solver_dispatch([dispatch]);

    assert_eq!(evidence.replayed_vcs(), 1);
    assert_eq!(evidence.exact_replay_slice_attested_vcs(), 0);
    assert!(
        dispatch_exact_replay_transcript_artifact_digest(&evidence.solver_dispatch[0]).is_none()
    );
    assert!(
        evidence
            .exact_replay_slice_attestation_blockers()
            .iter()
            .any(|blocker| blocker.contains("memory/effect attestation")),
        "{:?}",
        evidence.exact_replay_slice_attestation_blockers()
    );

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_exact_replay_sat_candidate_mismatched_instruction_size_binding_is_not_replay_ready() {
    let mut dispatch = exact_replay_bound_sat_dispatch("vc-sat-mismatched-instruction-size");
    dispatch.origin.as_mut().expect("origin").instruction_size = Some(2);
    let evidence = VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![dispatch]);

    assert_eq!(evidence.replayed_vcs(), 1);
    assert_eq!(evidence.exact_replay_slice_attested_vcs(), 0);
    assert_eq!(evidence.replay_semantics_satisfied_vcs(), 0);
    assert!(
        evidence
            .exact_replay_slice_attestation_blockers()
            .iter()
            .any(|blocker| blocker.contains("instruction byte length mismatch")),
    );
}

#[test]
fn test_verify_binary_checked_certificate_requires_canonical_vc_and_origin_binding() {
    let evidence = VerifyBinaryEvidence::from_solver_dispatch_records(
        1,
        vec![checked_binary_dispatch_without_canonical_binding("vc-unbound", "main")],
    );
    assert_eq!(evidence.proved_vcs(), 1);
    assert_eq!(evidence.checked_certificates(), 0);
    assert_eq!(evidence.certificate_only_replay_semantics_vcs(), 0);
    assert_eq!(evidence.replay_semantics_satisfied_vcs(), 0);

    let report = build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 1 }],
            }],
            solver_results: Vec::new(),
            proof_evidence: evidence,
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );

    let gate = build_binary_cli_proof_grade_gate(&report);
    assert!(!gate.accepted);
    assert!(gate.all_required_vcs_proved);
    assert!(!gate.checked_certificates_for_all_required_vcs);
    assert!(!gate.replay_semantics_satisfied);
    assert_eq!(gate.checked_certificates, 0);
    assert_eq!(gate.missing_checked_certificates, 1);
    assert_eq!(gate.certificate_only_replay_semantics_vcs, 0);
    assert_eq!(gate.replay_semantics_satisfied_vcs, 0);
    assert!(
        gate.rejections.iter().any(|reason| reason.contains("checked proof certificates missing"))
    );
    assert!(gate.rejections.iter().any(|reason| reason.contains("replay semantics missing")));
}

#[test]
fn test_verify_binary_unknown_and_unsupported_states_do_not_satisfy_replay_semantics() {
    let mut unknown = unsupported_binary_dispatch("vc-unknown", "main");
    unknown.status = SolverDispatchStatus::Unknown;
    let evidence = VerifyBinaryEvidence::from_solver_dispatch_records(
        2,
        vec![unknown, unsupported_binary_dispatch("vc-unsupported", "main")],
    );
    let report = build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 2,
                vcs: 2,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 2 }],
            }],
            solver_results: Vec::new(),
            proof_evidence: evidence,
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );

    let gate = build_binary_cli_proof_grade_gate(&report);

    assert!(!gate.accepted);
    assert!(!gate.all_required_vcs_proved);
    assert!(!gate.replay_semantics_satisfied);
    assert_eq!(gate.replay_semantics_satisfied_vcs, 0);
    assert_eq!(gate.missing_machine_replay, 2);
    assert!(gate.rejections.iter().any(|reason| reason.contains("required binary VCs")));
    assert!(gate.rejections.iter().any(|reason| reason.contains("replay semantics missing")));
}

#[test]
fn test_verify_binary_raw_solver_proof_bytes_do_not_satisfy_proof_grade_gate() {
    let solver_item = binary_solver_result_report(
        "main",
        "division_by_zero".into(),
        Some("0x401010".into()),
        &trust_types::VerificationResult::Proved {
            solver: "ay-incremental".into(),
            time_ms: 4,
            strength: trust_types::ProofStrength::smt_unsat(),
            proof_certificate: Some(vec![1, 2, 3, 4]),
            solver_warnings: None,
            native_proof_envelope: None,
        },
    );
    assert_eq!(solver_item.status, "proved");
    assert!(solver_item.detail.as_deref().unwrap().contains("raw solver proof bytes present"));

    let report = build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 1 }],
            }],
            solver_results: vec![solver_item],
            proof_evidence: VerifyBinaryEvidence::from_solver_dispatch_records(
                1,
                vec![raw_solver_binary_dispatch("vc-0", "main")],
            ),
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );

    assert_eq!(report.solver_results.status, "proved");
    let gate = build_binary_cli_proof_grade_gate(&report);
    assert!(!gate.accepted);
    assert!(gate.all_required_vcs_proved);
    assert_eq!(gate.raw_solver_proof_bytes, 1);
    assert!(!gate.raw_solver_proof_bytes_sufficient);
    assert!(gate.rejections.iter().any(|reason| {
        reason.contains("raw solver proof bytes present")
            && reason.contains("not checked proof certificates")
    }));
    assert!(gate.rejections.iter().any(|reason| reason.contains("checked proof certificates")));
    assert!(gate.rejections.iter().any(|reason| reason.contains("replay semantics missing")));

    let rendered = render_verify_binary_terminal(&report);
    assert!(rendered.contains("proof-grade gate: rejected\n"));
    assert!(rendered.contains("vcs_proved=true"));
    assert!(rendered.contains("checked_certs=false"));
    assert!(rendered.contains("replay_coverage=false"));
    assert!(rendered.contains("replay_semantics=false"));
    assert!(rendered.contains("raw_solver_proof_bytes=1"));
    assert!(rendered.contains("proof evidence: total_vcs=1 solver_dispatches=1"));
    assert!(rendered.contains("replay=NotAttempted"));
    assert!(rendered.contains("raw_solver_proof_byte_count=4"));
    assert!(rendered.contains("shared_proof_grade_gate=rejected"));
    assert!(rendered.contains("proof evidence solver dispatch counts: Unsat=1"));
    assert!(rendered.contains("proof evidence replay counts: NotAttempted=1"));
    assert!(rendered.contains("raw_solver_bytes_sufficient=false"));
    assert!(rendered.contains("raw solver proof bytes present for 1 VC(s)"));
    assert!(!rendered.contains("proof-grade gate: accepted"));

    let json = serialize_verify_binary_json(&report).expect("serialize verify-binary JSON");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse JSON");
    assert_eq!(value["proof_grade_gate"]["accepted"], false);
    assert_eq!(value["proof_grade_gate"]["all_required_vcs_proved"], true);
    assert_eq!(value["proof_grade_gate"]["raw_solver_proof_bytes"], 1);
    assert_eq!(value["proof_grade_gate"]["raw_solver_proof_bytes_sufficient"], false);
    assert_eq!(value["checked_certificate_evidence"]["status"], "blocked");
    assert_eq!(value["checked_certificate_evidence"]["checked_certificates"], 0);
    assert_eq!(value["checked_certificate_evidence"]["missing_checked_certificates"], 1);
    assert_eq!(value["checked_certificate_evidence"]["raw_solver_proof_bytes"], 1);
    assert_eq!(value["checked_certificate_evidence"]["raw_solver_proof_byte_count"], 4);
    assert_eq!(value["checked_certificate_evidence"]["raw_solver_proof_bytes_sufficient"], false);
    assert!(
        value["checked_certificate_evidence"]["blockers"]
            .as_array()
            .expect("checked certificate blockers")
            .iter()
            .any(|blocker| blocker["code"] == "raw-solver-proof-bytes-audit-only")
    );
    let proof_evidence = &value["proof_evidence"];
    assert_eq!(proof_evidence["total_vcs"], 1);
    assert_eq!(proof_evidence["solver_dispatches"], 1);
    assert_eq!(proof_evidence["solver_dispatch_status_counts"]["Unsat"], 1);
    assert_eq!(proof_evidence["replay"], "NotAttempted");
    assert_eq!(proof_evidence["replay_status_counts"]["NotAttempted"], 1);
    assert_eq!(proof_evidence["checked_certificate_coverage"]["required_vcs"], 1);
    assert_eq!(proof_evidence["checked_certificate_coverage"]["checked_certificates"], 0);
    assert_eq!(proof_evidence["checked_certificate_coverage"]["missing_checked_certificates"], 1);
    assert_eq!(proof_evidence["checked_certificate_coverage"]["raw_solver_proof_bytes"], 1);
    assert_eq!(proof_evidence["checked_certificate_coverage"]["raw_solver_proof_byte_count"], 4);
    assert_eq!(
        proof_evidence["checked_certificate_coverage"]["raw_solver_proof_bytes_satisfy_coverage"],
        false
    );
    assert_eq!(proof_evidence["proof_grade_gate"]["accepted"], false);
    assert_eq!(proof_evidence["proof_grade_gate"]["raw_solver_proof_bytes"], 1);
    assert_eq!(proof_evidence["proof_grade_gate"]["raw_solver_proof_byte_count"], 4);
    assert!(json.contains("raw solver proof bytes present"));
}

#[test]
fn test_verify_binary_json_never_promotes_blocked_certificate_evidence_to_checked_proof_grade() {
    let proof_evidence = VerifyBinaryEvidence::from_solver_dispatch_records(
        2,
        vec![
            raw_solver_binary_dispatch("vc-raw", "main"),
            missing_checker_identity_binary_dispatch("vc-missing-checker", "main"),
        ],
    );
    let production_report = proof_evidence
        .checked_certificate_production_blocker_report(Path::new("target/checked-certs"));
    let mut report = build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 2,
                vcs: 2,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 2 }],
            }],
            solver_results: Vec::new(),
            proof_evidence,
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );
    report.checked_certificate_production = Some(production_report);

    let gate = build_binary_cli_proof_grade_gate(&report);
    assert!(!gate.accepted);
    assert!(gate.all_required_vcs_proved);
    assert_eq!(gate.checked_certificates, 0);
    assert_eq!(gate.missing_checked_certificates, 2);
    assert_eq!(gate.raw_solver_proof_bytes, 1);
    assert!(!gate.raw_solver_proof_bytes_sufficient);
    assert!(!gate.replay_semantics_satisfied);
    assert!(gate.blockers.iter().any(|blocker| blocker.code == "checker-selection-missing"));

    let json = serialize_verify_binary_json(&report).expect("serialize verify-binary JSON");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse verify-binary JSON");
    assert_eq!(value["proof_grade_gate"]["accepted"], false);
    assert_eq!(value["proof_grade_gate"]["checked_certificates"], 0);
    assert_eq!(value["proof_grade_gate"]["checked_certificates_for_all_required_vcs"], false);
    assert_eq!(value["proof_grade_gate"]["missing_checked_certificates"], 2);
    assert_eq!(value["proof_grade_gate"]["raw_solver_proof_bytes"], 1);
    assert_eq!(value["proof_grade_gate"]["raw_solver_proof_bytes_sufficient"], false);
    assert_eq!(value["proof_evidence"]["checked_certificate_coverage"]["checked_certificates"], 0);
    assert_eq!(
        value["proof_evidence"]["checked_certificate_coverage"]["raw_solver_proof_bytes_satisfy_coverage"],
        false
    );
    assert_eq!(value["checked_certificate_production"]["already_checked_certificates"], 0);
    assert_eq!(value["checked_certificate_production"]["checker_selection"], "absent");
    assert_eq!(value["checked_certificate_production"]["proof_export_candidates"], 0);
    assert_eq!(value["checked_certificate_production"]["raw_solver_proof_byte_dispatches"], 1);
    assert_eq!(value["checked_certificate_production"]["status"], "blocked");
    assert_eq!(
        value["checked_certificate_production"]["proof_export_records"][0]["status"],
        "blocked_raw_solver_bytes"
    );
    assert_eq!(
        value["checked_certificate_production"]["certificate_check_records"][0]["status"],
        "rejected"
    );
    assert_eq!(
        value["checked_certificate_production"]["certificate_check_records"][0]["error_kind"],
        "raw_solver_bytes_audit_only"
    );
    assert!(
        value["checked_certificate_production"]["blockers"]
            .as_array()
            .expect("production blockers")
            .iter()
            .any(|blocker| blocker
                .as_str()
                .unwrap()
                .contains("raw solver proof bytes cannot be promoted"))
    );
    assert!(
        value["checked_certificate_production"]["blockers"]
            .as_array()
            .expect("production blockers")
            .iter()
            .any(|blocker| blocker
                .as_str()
                .unwrap()
                .contains("no production checker/exportable proof artifact exists"))
    );
}

#[test]
fn test_verify_binary_dispatch_records_preserve_raw_proof_as_unchecked_certificate() {
    let router = Router::with_backends(vec![Box::new(RawProofBackend)]);
    let vc = binary_vc(VcKind::DivisionByZero);

    let (reports, dispatch_records) = dispatch_binary_vcs_with_evidence(
        &router,
        BinarySolverRoute::AYIncremental,
        "main",
        0x401000,
        &[vc],
    );

    assert_eq!(reports.len(), 1);
    assert_eq!(dispatch_records.len(), 1);
    assert_eq!(reports[0].status, "proved");
    assert!(reports[0].detail.as_deref().unwrap().contains("raw solver proof bytes present"));

    let record = &dispatch_records[0];
    assert_eq!(record.status, SolverDispatchStatus::Unsat);
    assert_eq!(record.replay, ReplayStatus::NotAttempted);
    assert!(!record.certificate.is_checked());
    assert!(matches!(
        record.certificate,
        ProofCertificateStatus::Present { ref format, .. } if format == "solver-native"
    ));

    let evidence = VerifyBinaryEvidence::from_solver_dispatch_records(1, dispatch_records);
    assert_eq!(evidence.proved_vcs(), 1);
    assert_eq!(evidence.raw_solver_proof_bytes(), 1);
    assert_eq!(evidence.checked_certificates(), 0);
    assert_eq!(evidence.replayed_vcs(), 0);
    assert_eq!(evidence.certificate_only_replay_semantics_vcs(), 0);
    assert_eq!(evidence.replay_semantics_satisfied_vcs(), 0);
}

#[test]
fn test_verify_binary_dispatch_records_include_vc_origin_and_stable_canonical_bytes() {
    let router = Router::with_backends(vec![Box::new(RawProofBackend)]);
    let function = replay_test_lifted_function(vec![replay_test_annotation_with_bytes(
        0x401010,
        0x90,
        vec![0x90],
    )]);
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "binary generated VC".into() },
        function: trust_types::Symbol::intern("binary::main"),
        location: SourceSpan::binary_address(0x401010),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let (reports, dispatch_records) = dispatch_binary_vcs_with_replay_evidence(
        &router,
        BinarySolverRoute::AYIncremental,
        Some(Path::new("fixtures/tiny.bin")),
        &function,
        None,
        std::slice::from_ref(&vc),
    );

    assert_eq!(reports.len(), 1);
    assert_eq!(dispatch_records.len(), 1);
    let record = &dispatch_records[0];
    assert_eq!(record.id, "main:0x401000:0");
    assert_eq!(
        format!("{:?}", record.vc_kind.as_ref().expect("record VC kind")),
        format!("{:?}", &vc.kind)
    );

    let record_vc = record.vc.as_ref().expect("serialized VC");
    assert_eq!(format!("{:?}", &record_vc.kind), format!("{:?}", &vc.kind));
    assert_eq!(record_vc.function, vc.function);
    assert_eq!(record_vc.location, vc.location);
    assert_eq!(record_vc.formula, vc.formula);

    let origin = record.origin.as_ref().expect("binary origin");
    assert_eq!(origin.binary_path.as_deref(), Some("fixtures/tiny.bin"));
    assert_eq!(origin.function_entry, Some(0x401000));
    assert_eq!(origin.instruction_address, 0x401010);
    assert_eq!(origin.instruction_size, Some(1));
    assert_eq!(origin.encoding, Some(0x90));
    assert_eq!(origin.instruction_bytes, vec![0x90]);
    assert_eq!(origin.source.as_ref(), Some(&SourceSpan::binary_address(0x401010)));

    let canonical_bytes = serde_json::to_vec(record_vc).expect("serialize record VC");
    let regenerated_bytes =
        serde_json::to_vec(&SerializableVc::from_vc(&vc)).expect("serialize regenerated VC");
    assert_eq!(canonical_bytes, regenerated_bytes);
    assert_eq!(canonical_bytes, serde_json::to_vec(record_vc).expect("serialize VC again"));
}

#[test]
fn test_verify_binary_dispatch_context_binds_selected_image_identity_and_assumptions() {
    let router = Router::with_backends(vec![Box::new(RawProofBackend)]);
    let function = replay_test_lifted_function(vec![replay_test_annotation_with_bytes(
        0x401010,
        0x90,
        vec![0x90],
    )]);
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "binary generated VC".into() },
        function: trust_types::Symbol::intern("binary::main"),
        location: SourceSpan::binary_address(0x401010),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };
    let (_reports, mut dispatch_records) = dispatch_binary_vcs_with_replay_evidence(
        &router,
        BinarySolverRoute::AYIncremental,
        Some(Path::new("fixtures/tiny.bin")),
        &function,
        None,
        std::slice::from_ref(&vc),
    );
    let identity = BinaryArtifactDigestIdentity {
        root_artifact_digest: Some(BinaryArtifactDigest::sha256(trust_types::digest::stable_sha256_hex(b"root artifact"))),
        selected_image: Some(BinarySelectedImageIdentity {
            file_offset: 8,
            file_size: 64,
            sha256: trust_types::digest::stable_sha256_hex(b"selected image"),
        }),
    };
    let assumptions = vec![trust_types::ModelAssumption {
        stage: "trust-lift::binary-memory".to_string(),
        description: "loader segment metadata assumed exact for dispatch binding".to_string(),
    }];

    super::bind_binary_dispatch_context(&mut dispatch_records, Some(&identity), &assumptions);

    assert_eq!(dispatch_records[0].binary_artifact_digest_identity, Some(identity));
    assert_eq!(dispatch_records[0].assumptions, assumptions);
}

#[test]
fn test_verify_binary_dispatch_origin_omits_noncanonical_instruction_bytes() {
    let router = Router::with_backends(vec![Box::new(RawProofBackend)]);
    let mut annotation = replay_test_annotation_with_bytes(0x401010, 0x90, vec![0x90]);
    annotation.instruction_size = 3;
    let function = replay_test_lifted_function(vec![annotation]);
    let vc = VerificationCondition {
        kind: VcKind::Unreachable,
        function: trust_types::Symbol::intern("binary::main"),
        location: SourceSpan::binary_address(0x401010),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let (_reports, dispatch_records) = dispatch_binary_vcs_with_replay_evidence(
        &router,
        BinarySolverRoute::AYIncremental,
        Some(Path::new("fixtures/tiny.bin")),
        &function,
        None,
        std::slice::from_ref(&vc),
    );

    let origin = dispatch_records[0].origin.as_ref().expect("binary origin");
    assert_eq!(origin.instruction_size, Some(3));
    assert_eq!(origin.encoding, Some(0x90));
    assert!(origin.instruction_bytes.is_empty());
}

#[test]
fn test_verify_binary_dispatch_origin_strips_noncanonical_memory_origin_bytes() {
    let router = Router::with_backends(vec![Box::new(RawProofBackend)]);
    let annotation = replay_test_annotation_with_bytes(0x401010, 0x90, vec![0x90]);
    let mut function = replay_test_lifted_function(vec![annotation]);
    function.memory_accesses.push(MemoryAccessFact {
        origin: BinaryOrigin {
            binary_path: None,
            function_entry: None,
            instruction_address: 0x401010,
            instruction_size: Some(3),
            encoding: Some(0x90),
            instruction_bytes: vec![0x90],
            source: None,
        },
        kind: MemoryAccessKind::Read,
        address: Formula::Int(0x1000),
        width_bytes: 8,
        endianness: Endianness::Little,
        region: MemoryRegionKind::Stack,
        base_object: None,
        offset: None,
        extent: None,
        provenance: None,
        taint: Vec::new(),
    });
    let vc = VerificationCondition {
        kind: VcKind::Unreachable,
        function: trust_types::Symbol::intern("binary::main"),
        location: SourceSpan::binary_address(0x401010),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let (_reports, dispatch_records) = dispatch_binary_vcs_with_replay_evidence(
        &router,
        BinarySolverRoute::AYIncremental,
        Some(Path::new("fixtures/tiny.bin")),
        &function,
        None,
        std::slice::from_ref(&vc),
    );

    let origin = dispatch_records[0].origin.as_ref().expect("binary origin");
    assert_eq!(origin.binary_path.as_deref(), Some("fixtures/tiny.bin"));
    assert_eq!(origin.function_entry, Some(0x401000));
    assert_eq!(origin.instruction_size, Some(1));
    assert_eq!(origin.encoding, Some(0x90));
    assert_eq!(origin.instruction_bytes, vec![0x90]);
    assert_eq!(origin.source.as_ref(), Some(&SourceSpan::binary_address(0x401010)));
}

#[test]
fn test_verify_binary_evidence_counts_replay_and_checked_certificates_but_not_raw_bytes() {
    let evidence = VerifyBinaryEvidence::from_solver_dispatch_records(
        2,
        vec![
            raw_solver_binary_dispatch("raw-vc", "main"),
            checked_binary_dispatch("checked-vc", "main"),
        ],
    );

    assert_eq!(evidence.proved_vcs(), 2);
    assert_eq!(evidence.raw_solver_proof_bytes(), 1);
    assert_eq!(evidence.checked_certificates(), 1);
    assert_eq!(evidence.replayed_vcs(), 1);
    assert_eq!(evidence.certificate_only_replay_semantics_vcs(), 0);
    assert_eq!(evidence.replay_semantics_satisfied_vcs(), 1);
}

#[test]
fn test_verify_binary_evidence_loads_checked_artifact_by_canonical_vc_and_origin_digest() {
    let (previous_dispatch, canonical_vc_bytes) = importable_binary_dispatch("previous-run:vc0");
    let artifact = checked_binary_artifact_for_dispatch(&previous_dispatch, &canonical_vc_bytes);
    let root = temp_test_dir("checked-cert-import");
    let path = persist_checked_certificate_artifact(&root, &artifact)
        .expect("checked artifact should persist");

    let (current_dispatch, _) = importable_binary_dispatch("current-run:vc0");
    let mut evidence =
        VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![current_dispatch]);

    let import_report = evidence
        .load_and_import_checked_certificate_artifacts([path.as_path()])
        .expect("persisted checked artifact should load");

    assert_eq!(import_report.loaded_artifacts, 1);
    assert_eq!(import_report.loader_status, "loaded");
    assert_eq!(import_report.requested_artifacts, 1);
    assert_eq!(import_report.requested_manifests, 0);
    assert_eq!(import_report.imported, 1);
    assert_eq!(import_report.unmatched_artifacts, 0);
    assert_eq!(import_report.rejected_artifacts, 0);
    assert_eq!(evidence.checked_certificates(), 1);
    assert_eq!(evidence.raw_solver_proof_bytes(), 0);
    assert_eq!(evidence.certificate_only_replay_semantics_vcs(), 1);
    assert_eq!(evidence.replay_semantics_satisfied_vcs(), 1);
    assert_ne!(evidence.solver_dispatch[0].id, artifact.dispatch_id);
    assert!(matches!(
        &evidence.solver_dispatch[0].certificate,
        ProofCertificateStatus::Checked { sha256: Some(sha256), .. }
            if sha256 == &artifact.certificate_sha256
    ));

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_verify_binary_checked_certificate_import_wrong_origin_stays_unmatched() {
    let (previous_dispatch, canonical_vc_bytes) = importable_binary_dispatch("previous-run:vc0");
    let artifact = checked_binary_artifact_for_dispatch(&previous_dispatch, &canonical_vc_bytes);

    let (mut current_dispatch, _) = importable_binary_dispatch("current-run:wrong-origin");
    current_dispatch
        .origin
        .as_mut()
        .expect("fixture dispatch has binary origin")
        .instruction_address = 0x401011;

    let mut evidence =
        VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![current_dispatch]);
    let import_report = evidence.import_checked_certificate_artifacts(&[artifact]);

    assert_eq!(import_report.loaded_artifacts, 1);
    assert_eq!(import_report.imported, 0);
    assert_eq!(import_report.rejected_artifacts, 0);
    assert_eq!(import_report.unmatched_artifacts, 1);
    assert_eq!(evidence.checked_certificates(), 0);
    assert_eq!(evidence.replay_semantics_satisfied_vcs(), 0);
}

#[test]
fn test_verify_binary_evidence_loads_checked_artifact_from_manifest() {
    let (previous_dispatch, canonical_vc_bytes) = importable_binary_dispatch("previous-run:vc0");
    let artifact = checked_binary_artifact_for_dispatch(&previous_dispatch, &canonical_vc_bytes);
    let root = temp_test_dir("checked-cert-manifest-import");
    let path = persist_checked_certificate_artifact(&root, &artifact)
        .expect("checked artifact should persist");
    let relative_path =
        path.strip_prefix(&root).expect("artifact should be below manifest root").to_path_buf();
    let mut manifest = CheckedBinaryCertificateManifest::new();
    manifest.add_certificate(CheckedBinaryCertificateManifestEntry::from_artifact(
        &artifact,
        relative_path,
    ));
    let manifest_path = root.join("checked-binary-certificate-manifest.json");
    std::fs::write(&manifest_path, manifest.to_json().expect("manifest JSON should serialize"))
        .expect("manifest should persist");

    let (current_dispatch, _) = importable_binary_dispatch("current-run:vc0");
    let mut evidence =
        VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![current_dispatch]);

    let import_report = evidence
        .load_and_import_checked_certificate_artifacts_and_manifests(
            std::iter::empty::<&Path>(),
            [manifest_path.as_path()],
        )
        .expect("manifest-listed checked artifact should load");

    assert_eq!(import_report.loaded_artifacts, 1);
    assert_eq!(import_report.loader_status, "loaded");
    assert_eq!(import_report.requested_artifacts, 0);
    assert_eq!(import_report.requested_manifests, 1);
    assert_eq!(import_report.imported, 1);
    assert_eq!(import_report.unmatched_artifacts, 0);
    assert_eq!(import_report.rejected_artifacts, 0);
    assert_eq!(import_report.artifacts[0].artifact_path, Some(path.display().to_string()));
    assert_eq!(evidence.checked_certificates(), 1);
    assert_eq!(evidence.certificate_only_replay_semantics_vcs(), 1);
    assert_eq!(evidence.replay_semantics_satisfied_vcs(), 1);

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn test_verify_binary_production_manifest_readback_requires_aligned_row_identity() {
    let root = temp_test_dir("verify-binary-production-manifest-readback");
    let proof_dir = root.join("proofs");
    std::fs::create_dir_all(&proof_dir).expect("proof dir should be created");
    let proof_bytes = b"normalized verify-binary readback proof payload";
    let proof_path = proof_dir.join("vc0.lrat");
    std::fs::write(&proof_path, proof_bytes).expect("proof export should be written");
    let replay_transcript_digest = trust_types::digest::stable_sha256_hex(b"deterministic replay transcript for vc0");

    let (mut dispatch, canonical_vc_bytes) = importable_binary_dispatch("manifest-readback:vc0");
    dispatch.replay = ReplayStatus::Replayed;
    dispatch.certificate = ProofCertificateStatus::Present {
        format: "lrat".to_string(),
        sha256: Some(trust_types::digest::stable_sha256_hex(proof_bytes)),
        artifact_path: Some(proof_path.display().to_string()),
    };
    let export = SolverProofExport::new(
        &dispatch,
        &canonical_vc_bytes,
        "lrat",
        proof_bytes.to_vec(),
        None,
        1_777_070_405_000,
    );
    let checker = StructuralBinaryCertificateChecker::new(
        "verify-readback-checker",
        "0.1.0",
        vec!["lrat".to_string()],
        1_777_070_405_000,
    );
    let mut request =
        BinaryCertificateCheckRequest::from_export(&dispatch, &canonical_vc_bytes, &export);
    request.replay_transcript_digest = Some(replay_transcript_digest.as_str());
    let check = check_binary_certificate(&checker, request);
    assert!(check.accepted, "{:?}", check.error);
    let artifact = check.certificate.expect("accepted check should carry artifact");

    let export_dir = root.join("checked-certs");
    let artifact_path = persist_checked_certificate_artifact(&export_dir, &artifact)
        .expect("checked artifact should persist");
    let relative_path = artifact_path
        .strip_prefix(&export_dir)
        .expect("artifact should be below export root")
        .to_path_buf();
    let entry = CheckedBinaryCertificateManifestEntry::from_artifact(&artifact, relative_path);
    let checker_script = write_checker_fixture_script(
        &root,
        "verify-readback-external-checker.sh",
        "#!/bin/sh\nprintf 'verify readback checker ok'\n",
    );
    let runner = CheckedBinaryCertificateExternalCheckerRunner::from_command_path(
        checker_script.as_path(),
        std::iter::empty::<String>(),
        1_777_070_405_000,
    )
    .expect("external checker runner should initialize");
    let production_evidence =
        runner.run_for_manifest_entry(&entry).expect("external checker evidence should run");
    let acceptance_request =
        CheckedBinaryCertificateManifestAcceptanceRequest::from_manifest_entry_and_solver_proof_export_metadata(
            &entry,
            export.normalized_metadata(),
        )
        .and_then(|request| request.with_production_checker_evidence(production_evidence))
        .and_then(|request| {
            request.with_source_backpropagation_gate(
                CheckedBinaryCertificateSourceBackpropagationGate::default(),
            )
        })
        .expect("acceptance request should bind production row evidence");
    let mut accepted_dispatch = dispatch.clone();
    let acceptance_record = import_checked_certificate_manifest_entry_for_dispatch(
        &mut accepted_dispatch,
        &canonical_vc_bytes,
        &export_dir,
        &entry,
        &acceptance_request,
    )
    .expect("accepted manifest row should import before audit export");
    let audit_export = CheckedBinaryCertificateAuditExport::from_manifest_entry_and_record(
        entry.clone(),
        acceptance_record,
    )
    .expect("audit export should bind accepted manifest row");
    let mut manifest = CheckedBinaryCertificateManifest::new();
    manifest.add_certificate(entry);
    persist_checked_certificate_audit_export_bundle(&export_dir, &manifest, &[audit_export])
        .expect("audit export bundle should persist");
    let manifest_path = trust_proof_cert::checked_certificate_manifest_path(&export_dir);

    let (mut current_dispatch, _) = importable_binary_dispatch("manifest-readback-current:vc0");
    current_dispatch.replay = ReplayStatus::Replayed;
    let mut proof_evidence =
        VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![current_dispatch]);
    let import_report = proof_evidence
        .load_and_import_checked_certificate_artifacts_and_manifests(
            std::iter::empty::<&Path>(),
            [manifest_path.as_path()],
        )
        .expect("aligned production manifest row should load");
    assert_eq!(import_report.imported, 1);
    assert_eq!(import_report.artifacts[0].production_checker_evidence_status, "present");
    assert!(import_report.artifacts[0].production_checker_evidence_sha256.is_some());
    assert!(import_report.artifacts[0].manifest_identity_sha256.is_some());
    assert!(import_report.artifacts[0].source_backpropagation_gate_sha256.is_some());
    assert_eq!(import_report.artifacts[0].replay_digest_identity.status, "accepted");

    let mut report = build_verify_binary_report(
        Path::new("fixtures/tiny.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 1 }],
            }],
            solver_results: Vec::new(),
            proof_evidence,
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );
    report.checked_certificate_import = Some(import_report.clone());
    let value: serde_json::Value = serde_json::from_str(
        &serialize_verify_binary_json(&report).expect("serialize aligned readback JSON"),
    )
    .expect("parse aligned readback JSON");
    let evidence = &value["checked_certificate_evidence"];
    assert_eq!(evidence["status"], "blocked");
    assert_eq!(evidence["accepted_certificate_rows"], 1);
    assert!(
        evidence["blockers"]
            .as_array()
            .expect("blockers should be an array")
            .iter()
            .any(|blocker| blocker["code"] == "proof-grade-release-transcript-row-incomplete")
    );
    assert_eq!(
        evidence["accepted_certificates"][0]["production_checker_evidence_status"],
        "present"
    );
    let accepted = &evidence["accepted_certificates"][0];
    assert_eq!(
        accepted["manifest_identity_sha256"].as_str(),
        import_report.artifacts[0].manifest_identity_sha256.as_deref()
    );
    assert_eq!(
        accepted["replay_transcript_digest"].as_str(),
        Some(replay_transcript_digest.as_str())
    );
    let binding = &accepted["release_transcript_binding"];
    assert_eq!(binding["schema_version"], "targo-trust-release-transcript-binding.v1");
    assert_eq!(binding["status"], "accepted", "{binding}");
    assert_eq!(
        binding["replay_transcript_sha256"].as_str(),
        Some(replay_transcript_digest.as_str())
    );
    assert_eq!(
        binding["selected_image_sha256"].as_str(),
        Some(
            artifact
                .binary_artifact_digest_identity
                .selected_image
                .as_ref()
                .expect("artifact selected image")
                .sha256
                .as_str()
        )
    );
    assert_json_canonical_sha256(
        &evidence["accepted_certificates"][0]["proof_export_sha256"],
        "accepted proof metadata digest",
    );

    let bundle_path = checked_certificate_audit_export_bundle_path(&export_dir);
    let mut bundle_value: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(&bundle_path).expect("bundle should be readable"),
    )
    .expect("bundle JSON should parse");
    let audit_export_path = export_dir.join(
        bundle_value["audit_exports"][0]["audit_export_path"]
            .as_str()
            .expect("bundle row should include audit export path"),
    );
    let mut audit_value: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(&audit_export_path).expect("audit export should be readable"),
    )
    .expect("audit export JSON should parse");
    audit_value["acceptance_record"]["solver_proof_export"]["metadata_sha256"] =
        serde_json::Value::String(trust_types::digest::stable_sha256_hex(b"tampered proof metadata digest"));
    let audit_json =
        serde_json::to_string_pretty(&audit_value).expect("tampered audit export should serialize");
    std::fs::write(&audit_export_path, audit_json.as_bytes())
        .expect("tampered audit export should persist");
    bundle_value["audit_exports"][0]["audit_export_sha256"] =
        serde_json::Value::String(trust_types::digest::stable_sha256_hex(audit_json.as_bytes()));
    let bundle_json =
        serde_json::to_string_pretty(&bundle_value).expect("tampered bundle should serialize");
    std::fs::write(&bundle_path, bundle_json.as_bytes()).expect("tampered bundle should persist");

    let (mut tampered_dispatch, _) = importable_binary_dispatch("manifest-readback-tampered:vc0");
    tampered_dispatch.replay = ReplayStatus::Replayed;
    let mut tampered_evidence =
        VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![tampered_dispatch]);
    let error = tampered_evidence
        .load_and_import_checked_certificate_artifacts_and_manifests(
            std::iter::empty::<&Path>(),
            [manifest_path.as_path()],
        )
        .expect_err("tampered production manifest row must fail closed before import");
    let error = error.to_string();
    assert!(error.contains("checked certificate audit export bundle row rejected"), "{error}");
    assert!(error.contains("proof_export_sha256") || error.contains("metadata_sha256"), "{error}");

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_verify_binary_report_surfaces_checked_certificate_import_json_and_terminal() {
    let (previous_dispatch, canonical_vc_bytes) = importable_binary_dispatch("previous-run:vc0");
    let artifact = checked_binary_artifact_for_dispatch(&previous_dispatch, &canonical_vc_bytes);
    let root = temp_test_dir("checked-cert-import-report");
    let path = persist_checked_certificate_artifact(&root, &artifact)
        .expect("checked artifact should persist");

    let (current_dispatch, _) = importable_binary_dispatch("current-run:vc0");
    let mut proof_evidence =
        VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![current_dispatch]);
    let import_report = proof_evidence
        .load_and_import_checked_certificate_artifacts([path.as_path()])
        .expect("persisted checked artifact should load");
    let mut report = build_verify_binary_report(
        Path::new("fixtures/tiny.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 1 }],
            }],
            solver_results: Vec::new(),
            proof_evidence,
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );
    report.checked_certificate_import = Some(import_report);

    let rendered = render_verify_binary_terminal(&report);
    assert!(rendered.contains("checked certificate import: loaded=1 imported=1 unmatched=0 rejected=0 dispatches_missing_canonical_binding=0\n"));
    assert!(rendered.contains("proof evidence certificate coverage: candidates=1 checked=1"));

    let json = serialize_verify_binary_json(&report).expect("serialize verify-binary JSON");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse JSON");
    assert_eq!(value["checked_certificate_import"]["loaded_artifacts"], 1);
    assert_eq!(value["checked_certificate_import"]["imported"], 1);
    assert_eq!(value["checked_certificate_import"]["unmatched_artifacts"], 0);
    assert_eq!(value["checked_certificate_import"]["rejected_artifacts"], 0);
    assert_eq!(value["checked_certificate_evidence"]["status"], "accepted");
    assert_eq!(value["checked_certificate_evidence"]["loader"]["status"], "loaded");
    assert_eq!(value["checked_certificate_evidence"]["checked_artifact_rows"], 1);
    assert_eq!(value["checked_certificate_evidence"]["imported_artifact_rows"], 1);
    assert_eq!(value["checked_certificate_evidence"]["checker_successes"], 1);
    assert_eq!(value["checked_certificate_evidence"]["checked_certificates"], 1);
    assert_eq!(value["checked_certificate_evidence"]["accepted_certificate_rows"], 1);
    assert_eq!(value["checked_certificate_evidence"]["missing_checked_certificates"], 0);
    assert_eq!(value["checked_certificate_evidence"]["raw_solver_proof_bytes_sufficient"], false);
    assert_eq!(value["checked_certificate_evidence"]["artifacts"][0]["status"], "imported");
    assert_eq!(
        value["checked_certificate_evidence"]["artifacts"][0]["source_backpropagation_gate"]["source_backpropagation_allowed"],
        false
    );
    assert!(
        value["checked_certificate_evidence"]["artifacts"][0]["source_backpropagation_gate"]
            ["blockers"]
            .as_array()
            .expect("artifact source-backprop blockers")
            .iter()
            .any(|blocker| blocker == "source_backpropagation_gate_not_evaluated")
    );
    let accepted = &value["checked_certificate_evidence"]["accepted_certificates"][0];
    assert_eq!(accepted["source"], "checked_certificate_import");
    assert_eq!(accepted["status"], "accepted");
    assert_eq!(accepted["artifact_path"], path.display().to_string());
    assert_eq!(accepted["certificate_sha256"], artifact.certificate_sha256);
    assert_eq!(accepted["checker"], artifact.checker);
    assert_eq!(accepted["checker_version"], artifact.checker_version);
    assert_eq!(accepted["format"], artifact.format);
    assert_eq!(accepted["vc_sha256"], artifact.vc_sha256);
    assert_eq!(accepted["origin_sha256"], artifact.origin_sha256);
    assert_eq!(accepted["dispatch_id"], "current-run:vc0");
    let binding = &accepted["release_transcript_binding"];
    assert_eq!(binding["schema_version"], "targo-trust-release-transcript-binding.v1");
    assert_json_canonical_sha256(&binding["commit_sha256"], "verify release transcript commit");
    assert_eq!(
        binding["binary_sha256"],
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
    );
    assert_eq!(
        binding["selected_image_sha256"],
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
    );
    assert_eq!(binding["vc_sha256"], artifact.vc_sha256);
    assert_eq!(binding["checked_certificate_sha256"], artifact.certificate_sha256);
    assert_eq!(binding["provenance_sha256"], artifact.origin_sha256);
    assert_eq!(binding["target_consumer_evidence_sha256"], serde_json::Value::Null);
    assert_eq!(binding["status"], "rejected");
    assert!(
        binding["blockers"]
            .as_array()
            .expect("binding blockers")
            .iter()
            .any(|blocker| { blocker.as_str() == Some("replay transcript digest is missing") }),
        "{binding}"
    );
    assert_eq!(accepted["source_backpropagation_gate"]["source_backpropagation_allowed"], false);
    assert_eq!(
        value["source_backpropagation_gate"]["accepted"], false,
        "checked certificate coverage must not independently authorize source rewrites"
    );
    assert_eq!(value["proof_evidence"]["checked_certificate_coverage"]["checked_certificates"], 1);
    assert_eq!(value["proof_grade_gate"]["certificate_only_replay_semantics_vcs"], 1);

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_verify_binary_production_row_missing_selected_image_blocks_release_transcript_binding() {
    let (previous_dispatch, canonical_vc_bytes) =
        importable_binary_dispatch("release-binding-previous:vc0");
    let artifact = checked_binary_artifact_for_dispatch(&previous_dispatch, &canonical_vc_bytes);
    let root = temp_test_dir("verify-release-transcript-binding");
    let path = persist_checked_certificate_artifact(&root, &artifact)
        .expect("checked artifact should persist");

    let (current_dispatch, _) = importable_binary_dispatch("release-binding-current:vc0");
    let mut proof_evidence =
        VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![current_dispatch]);
    let mut import_report = proof_evidence
        .load_and_import_checked_certificate_artifacts([path.as_path()])
        .expect("persisted checked artifact should load");
    let transcript_sha256 = trust_types::digest::stable_sha256_hex(b"production replay transcript");
    {
        let row = import_report.artifacts.get_mut(0).expect("imported row");
        row.manifest_identity_sha256 = Some(trust_types::digest::stable_sha256_hex(b"manifest identity"));
        row.source_backpropagation_gate_sha256 = Some(trust_types::digest::stable_sha256_hex(b"source gate"));
        row.production_checker_evidence_sha256 = Some(trust_types::digest::stable_sha256_hex(b"production checker"));
        row.production_checker_evidence_status = "present".to_string();
        row.replay_transcript_digest = Some(transcript_sha256.clone());
        row.replay_digest_identity = checked_certificate_replay_digest_identity_record(
            ReplayStatus::Replayed,
            Some(transcript_sha256),
            Some(row.binary_artifact_digest_identity.clone()),
        );
        row.binary_artifact_digest_identity.selected_image = None;
    }

    let mut report = build_verify_binary_report(
        Path::new("fixtures/tiny.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 1 }],
            }],
            solver_results: Vec::new(),
            proof_evidence,
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );
    report.checked_certificate_import = Some(import_report);

    let value: serde_json::Value = serde_json::from_str(
        &serialize_verify_binary_json(&report).expect("serialize verify-binary JSON"),
    )
    .expect("parse verify-binary JSON");
    let evidence = &value["checked_certificate_evidence"];
    assert_eq!(evidence["status"], "blocked");
    assert_eq!(evidence["accepted_certificate_rows"], 0);
    assert_eq!(evidence["accepted_certificates"].as_array().expect("accepted rows").len(), 0);
    assert!(
        evidence["blockers"].as_array().expect("blockers").iter().any(|blocker| {
            blocker["code"] == "release-transcript-binding-missing"
                && blocker["evidence_required"]
                    .as_array()
                    .expect("evidence required")
                    .iter()
                    .any(|item| item.as_str() == Some("selected_image_digest_identity"))
        }),
        "{evidence}"
    );

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_verify_binary_json_surfaces_checked_certificate_loader_failure() {
    let mut report = build_verify_binary_report(
        Path::new("fixtures/tiny.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 1 }],
            }],
            solver_results: Vec::new(),
            proof_evidence: VerifyBinaryEvidence::from_solver_dispatch_records(
                1,
                vec![importable_binary_dispatch("current-run:vc0").0],
            ),
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );
    report.checked_certificate_import = Some(CheckedCertificateImportReport::loader_failure(
        "verify-binary",
        1,
        1,
        "manifest entry target/checked-cert.json was not readable",
    ));

    assert!(verify_binary_should_fail(&report));
    let gate = build_binary_cli_proof_grade_gate(&report);
    assert!(gate.rejections.iter().any(|rejection| {
        rejection.contains("checked certificate loader blocked")
            && rejection.contains("manifest entry")
    }));

    let json = serialize_verify_binary_json(&report).expect("serialize verify-binary JSON");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse JSON");
    assert_eq!(value["checked_certificate_import"]["loader_status"], "load_failed");
    assert_eq!(value["checked_certificate_import"]["requested_artifacts"], 1);
    assert_eq!(value["checked_certificate_import"]["requested_manifests"], 1);
    assert_eq!(
        value["checked_certificate_import"]["loader_blocker"]["code"],
        "checked-certificate-load-failed"
    );
    let evidence = &value["checked_certificate_evidence"];
    assert_eq!(evidence["status"], "blocked");
    assert_eq!(evidence["loader"]["status"], "load_failed");
    assert_eq!(evidence["loader"]["requested_artifacts"], 1);
    assert_eq!(evidence["loader"]["requested_manifests"], 1);
    assert_eq!(evidence["loader"]["blocker"]["code"], "checked-certificate-load-failed");
    assert_eq!(evidence["accepted_certificate_rows"], 0);
    assert_eq!(evidence["accepted_certificates"].as_array().unwrap().len(), 0);
    assert!(
        evidence["blockers"]
            .as_array()
            .expect("checked certificate blockers")
            .iter()
            .any(|blocker| blocker["code"] == "checked-certificate-load-failed")
    );
}

#[test]
fn test_verify_binary_checked_certificate_export_request_blocks_without_production_checker_golden()
{
    let (dispatch, _) = importable_binary_dispatch("export-run:vc0");
    let proof_evidence = VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![dispatch]);
    let production_report = proof_evidence
        .checked_certificate_production_blocker_report(Path::new("target/checked-certs"));
    let solver_item = binary_solver_result_report(
        "main",
        "division_by_zero".into(),
        Some("0x401010".into()),
        &trust_types::VerificationResult::Proved {
            solver: "ay-incremental".into(),
            time_ms: 4,
            strength: trust_types::ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        },
    );
    let mut report = build_verify_binary_report(
        Path::new("fixtures/tiny.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 1 }],
            }],
            solver_results: vec![solver_item],
            proof_evidence,
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );
    report.checked_certificate_production = Some(production_report);

    let rendered = render_verify_binary_terminal(&report);
    assert!(rendered.contains("checked certificate production: status=blocked export_dir=target/checked-certs checker_selection=absent"));
    assert!(rendered.contains("solver dispatch evidence contains no normalized proof exports"));
    assert!(rendered.contains("checked certificate production proof exports:"));
    assert!(rendered.contains("dispatch=export-run:vc0 status=missing"));

    let gate = build_binary_cli_proof_grade_gate(&report);
    let json = serialize_verify_binary_json(&report).expect("serialize verify-binary JSON");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse verify-binary JSON");
    assert_eq!(
        value["checked_certificate_production"]["proof_export_records"][0]["status"],
        "missing"
    );
    assert_eq!(
        value["checked_certificate_production"]["certificate_check_records"][0]["status"],
        "not_run"
    );
    let actual = serde_json::json!({
        "checked_certificate_production": value["checked_certificate_production"],
        "proof_grade_gate": {
            "accepted": gate.accepted,
            "checked_certificate_blocked": gate
                .blockers
                .iter()
                .any(|blocker| blocker.code == "checker-selection-missing"),
            "status": gate.status,
        },
        "verify_binary_should_fail": verify_binary_should_fail(&report),
    });
    let expected: serde_json::Value = serde_json::from_str(include_str!(
        "fixtures/checked_certificate_export_blocker_golden.json"
    ))
    .expect("parse checked certificate export blocker golden");
    assert_eq!(actual, expected);
}

#[test]
fn test_verify_binary_checked_certificate_export_reports_normalized_proof_export_status() {
    let root = temp_test_dir("normalized-export-status");
    let (mut dispatch, canonical_vc_bytes) =
        importable_binary_dispatch("normalized-export-run:vc0");
    attach_normalized_proof_export_artifact(
        &root,
        &mut dispatch,
        &canonical_vc_bytes,
        b"normalized verify-binary proof payload",
        None,
        &CheckedBinaryCertificateSourceBackpropagationGate::default(),
    );
    let proof_evidence = VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![dispatch]);
    let production_report = proof_evidence
        .checked_certificate_production_blocker_report(Path::new("target/checked-certs"));

    assert!(production_report.is_blocked());
    assert_eq!(production_report.candidate_dispatches, 1);
    assert_eq!(production_report.canonical_binding_candidates, 1);
    assert_eq!(production_report.proof_export_candidates, 1);
    assert_eq!(production_report.raw_solver_proof_byte_dispatches, 0);
    assert_eq!(production_report.proof_export_records[0].status, "available");
    assert_eq!(production_report.proof_export_records[0].format.as_deref(), Some("lrat"));
    assert_eq!(
        production_report.certificate_check_records[0].status,
        "blocked_checker_selection_missing"
    );
    assert!(production_report.blocker_records.iter().any(|record| {
        record.code == "checked-certificate-missing"
            && record.dispatch_id.as_deref() == Some("normalized-export-run:vc0")
    }));

    let value = serde_json::to_value(&production_report).expect("production report JSON");
    assert_eq!(value["proof_export_candidates"], 1);
    assert_eq!(value["proof_export_records"][0]["status"], "available");
    assert_eq!(
        value["certificate_check_records"][0]["status"],
        "blocked_checker_selection_missing"
    );
    assert_eq!(value["proof_export_records"][0]["raw_solver_proof_bytes"], serde_json::Value::Null);

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn test_verify_binary_checked_certificate_export_rejects_raw_proof_file_as_normalized_export() {
    let root = temp_test_dir("verify-binary-raw-proof-file-export");
    let proof_path = root.join("raw-vc0.lrat");
    let proof_bytes = b"raw lrat bytes without targo-trust normalized envelope";
    std::fs::create_dir_all(&root).expect("temp root should exist");
    std::fs::write(&proof_path, proof_bytes).expect("raw proof fixture should be written");

    let (mut dispatch, _) = importable_binary_dispatch("raw-proof-file-export:vc0");
    dispatch.certificate = ProofCertificateStatus::Present {
        format: "lrat".to_string(),
        sha256: Some(trust_types::digest::stable_sha256_hex(proof_bytes)),
        artifact_path: Some(proof_path.display().to_string()),
    };
    let mut proof_evidence = VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![dispatch]);
    let checker = write_checker_fixture_script(
        &root,
        "raw-proof-file-checker.sh",
        "#!/bin/sh\nprintf 'raw proof file checker should not run'\n",
    );

    let production_report = proof_evidence.produce_checked_certificate_artifacts(
        &root.join("checked-certs"),
        Some(checker.as_path()),
        1_777_070_404_000,
    );

    assert_eq!(production_report.status, "blocked");
    assert_eq!(production_report.exported_artifacts, 0);
    assert_eq!(
        production_report.proof_export_records[0].status,
        "blocked_invalid_normalized_export"
    );
    assert_eq!(
        production_report.certificate_check_records[0].error_kind.as_deref(),
        Some("normalized-proof-export-not-normalized")
    );
    assert!(production_report.blocker_records.iter().any(|record| {
        record.code == "normalized-proof-export-not-normalized"
            && record.detail.contains("raw solver proof bytes are not accepted")
    }));
    assert_eq!(proof_evidence.checked_certificates(), 0);

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn test_verify_binary_checked_certificate_export_requires_content_addressed_proof_export() {
    let root = temp_test_dir("verify-binary-proof-export-content-address");
    let (mut dispatch, canonical_vc_bytes) =
        importable_binary_dispatch("proof-export-content-address:vc0");
    let source_backpropagation_gate = CheckedBinaryCertificateSourceBackpropagationGate::default();
    let artifact =
        build_normalized_solver_proof_export_artifact(NormalizedSolverProofExportArtifactInput {
            dispatch: &dispatch,
            canonical_vc_bytes: &canonical_vc_bytes,
            format: "lrat",
            proof_bytes: b"normalized proof payload at stale path".to_vec(),
            solver_version: None,
            exported_at_unix_ms: 1_777_070_404_000,
            replay_transcript_digest: None,
            source_backpropagation_gate: &source_backpropagation_gate,
        })
        .expect("normalized artifact should build");
    let stale_path = root.join("stale-name.targo-trust-normalized-solver-proof-export.json");
    std::fs::create_dir_all(&root).expect("temp root should exist");
    std::fs::write(
        &stale_path,
        serde_json::to_vec(&artifact).expect("normalized artifact should serialize"),
    )
    .expect("stale proof export artifact should be written");
    dispatch.certificate = ProofCertificateStatus::Present {
        format: "lrat".to_string(),
        sha256: Some(artifact.proof_sha256.clone()),
        artifact_path: Some(stale_path.display().to_string()),
    };
    let mut proof_evidence = VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![dispatch]);
    let checker = write_checker_fixture_script(
        &root,
        "content-address-checker.sh",
        "#!/bin/sh\nprintf 'content address checker should not run'\n",
    );

    let production_report = proof_evidence.produce_checked_certificate_artifacts(
        &root.join("checked-certs"),
        Some(checker.as_path()),
        1_777_070_404_000,
    );

    assert_eq!(production_report.status, "blocked");
    assert_eq!(production_report.exported_artifacts, 0);
    assert_eq!(
        production_report.certificate_check_records[0].error_kind.as_deref(),
        Some("normalized-proof-export-content-address-missing")
    );
    assert!(production_report.blocker_records.iter().any(|record| {
        record.code == "normalized-proof-export-content-address-missing"
            && record.detail.contains("not content-addressed")
    }));

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn test_verify_binary_checked_certificate_export_produces_artifact_with_production_evidence() {
    let root = temp_test_dir("verify-binary-production-export");
    let proof_bytes = b"normalized verify-binary proof payload";

    let (mut dispatch, canonical_vc_bytes) =
        importable_binary_dispatch("verify-production-export:vc0");
    let origin_sha256 =
        digest_binary_origin(dispatch.origin.as_ref().expect("fixture dispatch has origin"))
            .expect("fixture origin should digest");
    let assumption_digest = digest_model_assumptions(&dispatch.assumptions);
    let selected_image_identity = dispatch
        .binary_artifact_digest_identity
        .as_ref()
        .and_then(|identity| identity.selected_image.clone())
        .expect("fixture dispatch has selected image identity");
    let proof_export_path = attach_normalized_proof_export_artifact(
        &root,
        &mut dispatch,
        &canonical_vc_bytes,
        proof_bytes,
        None,
        &CheckedBinaryCertificateSourceBackpropagationGate::default(),
    );
    let mut proof_evidence = VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![dispatch]);
    let checker = write_checker_fixture_script(
        &root,
        "verify-production-checker.sh",
        "#!/bin/sh\nset -eu\ncert=\nmetadata=\npayload=\nwhile [ $# -gt 0 ]; do\n  case \"$1\" in\n    --checked-certificate) cert=\"$2\"; shift 2 ;;\n    --solver-proof-export-metadata) metadata=\"$2\"; shift 2 ;;\n    --solver-proof-payload) payload=\"$2\"; shift 2 ;;\n    --vc-sha256|--origin-sha256|--assumption-digest|--certificate-sha256|--proof-export-sha256|--proof-sha256) shift 2 ;;\n    *) shift ;;\n  esac\ndone\ntest -s \"$cert\"\ntest -s \"$metadata\"\ntest -s \"$payload\"\nprintf 'verify production ok'\n",
    );
    let export_dir = root.join("checked-certs");

    let production_report = proof_evidence.produce_checked_certificate_artifacts(
        &export_dir,
        Some(checker.as_path()),
        1_777_070_404_000,
    );

    assert_eq!(production_report.status, "exported", "{production_report:#?}");
    assert_eq!(production_report.exported_artifacts, 1);
    assert_eq!(production_report.rejected_dispatches, 0);
    assert!(production_report.blockers.is_empty(), "{:?}", production_report.blockers);
    assert_eq!(production_report.proof_export_records[0].status, "exported");
    let proof_export_record = &production_report.proof_export_records[0];
    let proof_export_metadata_path = proof_export_record
        .proof_export_metadata_path
        .as_deref()
        .expect("production export should persist normalized proof metadata");
    let proof_export_payload_path = proof_export_record
        .proof_export_payload_path
        .as_deref()
        .expect("production export should persist normalized proof payload");
    assert!(Path::new(proof_export_metadata_path).exists());
    assert!(Path::new(proof_export_payload_path).exists());
    assert_eq!(
        std::fs::read(proof_export_payload_path).expect("proof payload should read back"),
        &proof_bytes[..]
    );
    let proof_export_metadata: serde_json::Value = serde_json::from_slice(
        &std::fs::read(proof_export_metadata_path).expect("proof metadata should read back"),
    )
    .expect("proof metadata JSON should parse");
    assert_eq!(proof_export_metadata["dispatch_id"], "verify-production-export:vc0");
    assert_eq!(proof_export_metadata["format"], "lrat");
    assert_eq!(proof_export_metadata["proof_sha256"], trust_types::digest::stable_sha256_hex(proof_bytes));
    assert_json_canonical_sha256(
        &proof_export_metadata["assumption_digest"],
        "normalized proof assumption digest",
    );
    assert_eq!(production_report.certificate_check_records[0].status, "checked");
    assert!(
        production_report.certificate_check_records[0].production_checker_evidence_sha256.is_some()
    );
    assert_eq!(production_report.export_row_records.len(), 1);
    let export_row = production_report.export_row_records[0].clone();
    assert_eq!(export_row.dispatch_id, "verify-production-export:vc0");
    assert_eq!(export_row.vc_sha256, trust_types::digest::stable_sha256_hex(&canonical_vc_bytes));
    assert_eq!(export_row.origin_sha256, origin_sha256);
    assert_eq!(export_row.assumption_digest, assumption_digest);
    assert_eq!(export_row.query_semantics, SolverQuerySemantics::SatIsCounterexample);
    assert_eq!(export_row.replay, ReplayStatus::NotAttempted);
    assert_eq!(export_row.selected_image_identity, selected_image_identity);
    assert!(!export_row.source_backpropagation_gate.source_backpropagation_allowed);
    assert_json_canonical_sha256(
        &serde_json::Value::String(export_row.manifest_identity_sha256.clone()),
        "export row manifest identity",
    );
    assert_json_canonical_sha256(
        &serde_json::Value::String(export_row.source_backpropagation_gate_sha256.clone()),
        "export row source-backpropagation gate identity",
    );
    assert_json_canonical_sha256(
        &serde_json::Value::String(export_row.production_checker_evidence_sha256.clone()),
        "export row production checker evidence identity",
    );
    assert!(Path::new(&export_row.proof_export_artifact_path).starts_with(&export_dir));
    assert!(Path::new(&export_row.proof_export_artifact_path).exists());
    assert_ne!(export_row.proof_export_artifact_path, proof_export_path.display().to_string());
    assert_json_canonical_sha256(
        &serde_json::Value::String(export_row.proof_export_artifact_sha256.clone()),
        "export row normalized proof export artifact identity",
    );
    assert!(Path::new(&production_report.artifact_paths[0]).exists());
    assert!(production_report.manifest_path.as_ref().is_some_and(|path| Path::new(path).exists()));
    assert!(checked_certificate_audit_export_bundle_path(&export_dir).exists());
    let bundle_validation = load_checked_certificate_audit_export_bundle_rows(&export_dir)
        .expect("produced audit export bundle should validate");
    assert_eq!(bundle_validation.rows.len(), 1);
    let accepted_row = match &bundle_validation.rows[0] {
        trust_proof_cert::CheckedBinaryCertificateAuditExportBundleValidationRow::Accepted(row) => {
            row
        }
        trust_proof_cert::CheckedBinaryCertificateAuditExportBundleValidationRow::Rejected(row) => {
            panic!("produced audit export row should be accepted: {row:?}")
        }
    };
    assert_eq!(accepted_row.bundle_entry.vc_sha256, export_row.vc_sha256);
    assert_eq!(accepted_row.bundle_entry.origin_sha256, export_row.origin_sha256);
    assert_eq!(accepted_row.bundle_entry.assumption_digest, export_row.assumption_digest);
    assert_eq!(accepted_row.bundle_entry.replay, export_row.replay);
    assert_eq!(
        accepted_row.bundle_entry.source_backpropagation_gate,
        export_row.source_backpropagation_gate
    );
    assert_eq!(
        accepted_row.acceptance_record.solver_proof_export.metadata.query_semantics,
        export_row.query_semantics
    );
    assert_eq!(
        accepted_row
            .acceptance_record
            .artifact_identity
            .binary_artifact_digest_identity
            .selected_image
            .as_ref(),
        Some(&export_row.selected_image_identity)
    );
    let production_check = &production_report.certificate_check_records[0];
    assert!(production_check.manifest_identity_sha256.as_deref().is_some_and(|sha| {
        sha.len() == 64
            && sha.bytes().all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
    }));
    assert!(
        production_check
            .source_backpropagation_gate_sha256
            .as_deref()
            .is_some_and(|sha| sha.len() == 64)
    );
    assert_eq!(production_check.replay_digest_identity.status, "rejected");
    assert!(
        production_check
            .replay_digest_identity
            .blockers
            .iter()
            .any(|blocker| blocker.contains("replay transcript digest is missing"))
    );
    assert_eq!(proof_evidence.checked_certificates(), 1);
    assert_eq!(proof_evidence.replay_semantics_satisfied_vcs(), 1);
    assert!(matches!(
        &proof_evidence.solver_dispatch[0].certificate,
        ProofCertificateStatus::Checked { checker, format, sha256: Some(_) }
            if checker.contains("production_checker_evidence_sha256=") && format == "lrat"
    ));

    let solver_item = binary_solver_result_report(
        "main",
        "division_by_zero".into(),
        Some("0x401010".into()),
        proof_evidence.solver_dispatch[0]
            .result
            .as_ref()
            .expect("fixture dispatch has solver result"),
    );
    let mut report = build_verify_binary_report(
        Path::new("fixtures/tiny.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 1 }],
            }],
            solver_results: vec![solver_item],
            proof_evidence,
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );
    report.checked_certificate_production = Some(production_report);
    assert!(!verify_binary_should_fail(&report));

    let json = serialize_verify_binary_json(&report).expect("serialize verify-binary JSON");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse verify-binary JSON");
    assert_eq!(value["checked_certificate_production"]["status"], "exported");
    assert_eq!(value["checked_certificate_evidence"]["status"], "accepted");
    assert_eq!(value["checked_certificate_evidence"]["loader"]["status"], "exported");
    assert_eq!(value["checked_certificate_evidence"]["normalized_solver_proof_exports"], 1);
    assert_eq!(value["checked_certificate_evidence"]["checker_successes"], 1);
    assert_eq!(value["checked_certificate_evidence"]["checked_certificates"], 1);
    assert_eq!(value["checked_certificate_evidence"]["missing_checked_certificates"], 0);
    let production_check_json =
        &value["checked_certificate_production"]["certificate_check_records"][0];
    assert_json_canonical_sha256(
        &production_check_json["manifest_identity_sha256"],
        "production manifest identity",
    );
    assert_json_canonical_sha256(
        &production_check_json["source_backpropagation_gate_sha256"],
        "production source-backpropagation gate identity",
    );
    assert_json_canonical_sha256(
        &production_check_json["production_checker_evidence_sha256"],
        "production checker evidence identity",
    );
    assert!(value["checked_certificate_production"]["proof_export_records"][0]
        ["proof_export_metadata_path"]
        .as_str()
        .is_some_and(|path| Path::new(path).exists()));
    assert!(value["checked_certificate_production"]["proof_export_records"][0]
        ["proof_export_payload_path"]
        .as_str()
        .is_some_and(|path| Path::new(path).exists()));
    assert_eq!(production_check_json["replay_digest_identity"]["status"], "rejected");
    let export_row_json = &value["checked_certificate_production"]["export_row_records"][0];
    assert_eq!(export_row_json["vc_sha256"], export_row.vc_sha256);
    assert_eq!(export_row_json["origin_sha256"], export_row.origin_sha256);
    assert_eq!(export_row_json["assumption_digest"], export_row.assumption_digest);
    assert_eq!(export_row_json["query_semantics"], "SatIsCounterexample");
    assert_eq!(export_row_json["replay"], "NotAttempted");
    assert_eq!(
        export_row_json["selected_image_identity"]["sha256"],
        export_row.selected_image_identity.sha256
    );
    assert_eq!(
        export_row_json["source_backpropagation_gate"]["source_backpropagation_allowed"],
        false
    );
    assert_eq!(
        export_row_json["proof_export_artifact_sha256"],
        export_row.proof_export_artifact_sha256
    );

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn test_verify_binary_checked_certificate_export_covers_all_required_vc_proof_exports() {
    let root = temp_test_dir("verify-binary-production-export-all-vcs");

    let (mut first_dispatch, first_canonical_vc_bytes) =
        importable_binary_dispatch("verify-production-all-vcs:vc0");
    let (mut second_dispatch, second_canonical_vc_bytes) = importable_binary_dispatch_with_kind(
        "verify-production-all-vcs:vc1",
        VcKind::RemainderByZero,
        0x401011,
        0x91,
    );
    attach_normalized_proof_export_artifact(
        &root,
        &mut first_dispatch,
        &first_canonical_vc_bytes,
        b"normalized verify-binary all-vc proof payload 0",
        None,
        &CheckedBinaryCertificateSourceBackpropagationGate::default(),
    );
    attach_normalized_proof_export_artifact(
        &root,
        &mut second_dispatch,
        &second_canonical_vc_bytes,
        b"normalized verify-binary all-vc proof payload 1",
        None,
        &CheckedBinaryCertificateSourceBackpropagationGate::default(),
    );
    let expected_vc_digests =
        [trust_types::digest::stable_sha256_hex(&first_canonical_vc_bytes), trust_types::digest::stable_sha256_hex(&second_canonical_vc_bytes)]
            .into_iter()
            .collect::<BTreeSet<_>>();
    let mut proof_evidence = VerifyBinaryEvidence::from_solver_dispatch_records(
        2,
        vec![first_dispatch, second_dispatch],
    );
    let checker = write_checker_fixture_script(
        &root,
        "verify-production-all-vcs-checker.sh",
        "#!/bin/sh\nprintf 'verify production all-vcs ok'\n",
    );
    let export_dir = root.join("checked-certs");

    let production_report = proof_evidence.produce_checked_certificate_artifacts(
        &export_dir,
        Some(checker.as_path()),
        1_777_070_404_000,
    );

    assert_eq!(production_report.status, "exported", "{production_report:#?}");
    assert_eq!(production_report.candidate_dispatches, 2);
    assert_eq!(production_report.canonical_binding_candidates, 2);
    assert_eq!(production_report.proof_export_candidates, 2);
    assert_eq!(production_report.exported_artifacts, 2);
    assert_eq!(production_report.rejected_dispatches, 0);
    assert!(production_report.blockers.is_empty(), "{:?}", production_report.blockers);
    assert_eq!(
        production_report
            .proof_export_records
            .iter()
            .map(|record| record.status.as_str())
            .collect::<Vec<_>>(),
        vec!["exported", "exported"]
    );
    assert!(
        production_report.certificate_check_records.iter().all(|record| record.status == "checked")
    );
    assert_eq!(production_report.export_row_records.len(), 2);
    let row_vc_digests = production_report
        .export_row_records
        .iter()
        .map(|row| row.vc_sha256.clone())
        .collect::<BTreeSet<_>>();
    assert_eq!(row_vc_digests, expected_vc_digests);
    assert_eq!(
        production_report
            .export_row_records
            .iter()
            .map(|row| row.proof_export_artifact_sha256.clone())
            .collect::<BTreeSet<_>>()
            .len(),
        2
    );
    assert_eq!(
        production_report
            .export_row_records
            .iter()
            .map(|row| row.certificate_sha256.clone())
            .collect::<BTreeSet<_>>()
            .len(),
        2
    );

    let bundle_validation = load_checked_certificate_audit_export_bundle_rows(&export_dir)
        .expect("produced all-VC audit export bundle should validate");
    assert_eq!(bundle_validation.rows.len(), 2);
    assert!(
        bundle_validation.rows.iter().all(|row| matches!(
            row,
            trust_proof_cert::CheckedBinaryCertificateAuditExportBundleValidationRow::Accepted(_)
        )),
        "{bundle_validation:#?}"
    );

    let manifest_path = production_report
        .manifest_path
        .as_ref()
        .expect("all-VC production export should write a manifest");
    let (first_readback, _) = importable_binary_dispatch("verify-production-all-vcs-readback:vc0");
    let (second_readback, _) = importable_binary_dispatch_with_kind(
        "verify-production-all-vcs-readback:vc1",
        VcKind::RemainderByZero,
        0x401011,
        0x91,
    );
    let mut readback_evidence = VerifyBinaryEvidence::from_solver_dispatch_records(
        2,
        vec![first_readback, second_readback],
    );
    let import_report = readback_evidence
        .load_and_import_checked_certificate_artifacts_and_manifests(
            std::iter::empty::<&Path>(),
            [Path::new(manifest_path)],
        )
        .expect("produced all-VC manifest should load");

    assert_eq!(import_report.imported, 2, "{import_report:#?}");
    assert_eq!(import_report.unmatched_artifacts, 0);
    assert_eq!(readback_evidence.checked_certificates(), 2);
    assert_eq!(proof_evidence.checked_certificates(), 2);

    let value = serde_json::to_value(&production_report).expect("production report JSON");
    assert_eq!(value["proof_export_candidates"], 2);
    assert_eq!(value["exported_artifacts"], 2);
    assert_eq!(value["export_row_records"].as_array().expect("export rows").len(), 2);

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn test_verify_binary_checked_certificate_export_blocks_missing_per_vc_proof_export() {
    let root = temp_test_dir("verify-binary-production-missing-per-vc-proof-export");

    let (mut first_dispatch, first_canonical_vc_bytes) =
        importable_binary_dispatch("verify-production-missing-export:vc0");
    attach_normalized_proof_export_artifact(
        &root,
        &mut first_dispatch,
        &first_canonical_vc_bytes,
        b"normalized verify-binary partial proof payload 0",
        None,
        &CheckedBinaryCertificateSourceBackpropagationGate::default(),
    );
    let (second_dispatch, _) = importable_binary_dispatch_with_kind(
        "verify-production-missing-export:vc1",
        VcKind::RemainderByZero,
        0x401011,
        0x91,
    );
    let mut proof_evidence = VerifyBinaryEvidence::from_solver_dispatch_records(
        2,
        vec![first_dispatch, second_dispatch],
    );
    let checker = write_checker_fixture_script(
        &root,
        "verify-production-missing-export-checker.sh",
        "#!/bin/sh\nprintf 'verify production partial ok'\n",
    );

    let production_report = proof_evidence.produce_checked_certificate_artifacts(
        &root.join("checked-certs"),
        Some(checker.as_path()),
        1_777_070_404_000,
    );

    assert_eq!(production_report.status, "blocked");
    assert_eq!(production_report.candidate_dispatches, 2);
    assert_eq!(production_report.proof_export_candidates, 1);
    assert_eq!(production_report.exported_artifacts, 1);
    assert_eq!(production_report.rejected_dispatches, 1);
    assert_eq!(proof_evidence.checked_certificates(), 1);
    assert!(production_report.blocker_records.iter().any(|record| {
        record.code == "normalized-proof-export-missing"
            && record.dispatch_id.as_deref() == Some("verify-production-missing-export:vc1")
    }));
    assert!(production_report.blocker_records.iter().any(|record| {
        record.code == "normalized-proof-export-coverage-incomplete"
            && record.detail.contains("cover 1 required VC dispatch")
    }));
    assert!(production_report.blocker_records.iter().any(|record| {
        record.code == "checked-certificate-export-coverage-incomplete"
            && record.detail.contains("cover 1 required VC dispatch")
    }));
    assert!(
        production_report
            .blocker_records
            .iter()
            .any(|record| { record.code == "checked-certificate-production-coverage-incomplete" })
    );
    let missing_record = production_report
        .proof_export_records
        .iter()
        .find(|record| record.dispatch_id == "verify-production-missing-export:vc1")
        .expect("missing dispatch should have a proof export record");
    assert_eq!(missing_record.status, "missing");

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn test_verify_binary_checked_certificate_export_blocks_duplicate_per_vc_proof_export() {
    let root = temp_test_dir("verify-binary-production-duplicate-per-vc-proof-export");

    let (mut first_dispatch, first_canonical_vc_bytes) =
        importable_binary_dispatch("verify-production-duplicate-export:vc0");
    attach_normalized_proof_export_artifact(
        &root,
        &mut first_dispatch,
        &first_canonical_vc_bytes,
        b"normalized verify-binary duplicate proof payload 0",
        None,
        &CheckedBinaryCertificateSourceBackpropagationGate::default(),
    );
    let duplicate_certificate = first_dispatch.certificate.clone();
    let (mut second_dispatch, _) = importable_binary_dispatch_with_kind(
        "verify-production-duplicate-export:vc1",
        VcKind::RemainderByZero,
        0x401011,
        0x91,
    );
    second_dispatch.certificate = duplicate_certificate;
    let mut proof_evidence = VerifyBinaryEvidence::from_solver_dispatch_records(
        2,
        vec![first_dispatch, second_dispatch],
    );
    let checker = write_checker_fixture_script(
        &root,
        "verify-production-duplicate-export-checker.sh",
        "#!/bin/sh\nprintf 'verify production duplicate ok'\n",
    );

    let production_report = proof_evidence.produce_checked_certificate_artifacts(
        &root.join("checked-certs"),
        Some(checker.as_path()),
        1_777_070_404_000,
    );

    assert_eq!(production_report.status, "blocked");
    assert_eq!(production_report.proof_export_candidates, 1);
    assert_eq!(production_report.exported_artifacts, 1);
    assert_eq!(proof_evidence.checked_certificates(), 1);
    assert!(production_report.blocker_records.iter().any(|record| {
        record.code == "normalized-proof-export-binding-mismatch"
            && record.dispatch_id.as_deref() == Some("verify-production-duplicate-export:vc1")
    }));
    assert!(production_report.blocker_records.iter().any(|record| {
        record.code == "duplicate-normalized-proof-export-path"
            && record.detail.contains("verify-production-duplicate-export:vc0")
            && record.detail.contains("verify-production-duplicate-export:vc1")
    }));
    let duplicate_record = production_report
        .proof_export_records
        .iter()
        .find(|record| record.dispatch_id == "verify-production-duplicate-export:vc1")
        .expect("duplicate dispatch should have a proof export record");
    assert_eq!(duplicate_record.status, "blocked_invalid_normalized_export");
    let duplicate_check = production_report
        .certificate_check_records
        .iter()
        .find(|record| record.dispatch_id == "verify-production-duplicate-export:vc1")
        .expect("duplicate dispatch should have a certificate check record");
    assert_eq!(
        duplicate_check.error_kind.as_deref(),
        Some("normalized-proof-export-binding-mismatch")
    );

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn test_verify_binary_checked_certificate_export_blocks_mismatched_per_vc_proof_export() {
    let root = temp_test_dir("verify-binary-production-mismatched-per-vc-proof-export");

    let (mut first_dispatch, first_canonical_vc_bytes) =
        importable_binary_dispatch("verify-production-mismatched-export:vc0");
    attach_normalized_proof_export_artifact(
        &root,
        &mut first_dispatch,
        &first_canonical_vc_bytes,
        b"normalized verify-binary mismatched proof payload 0",
        None,
        &CheckedBinaryCertificateSourceBackpropagationGate::default(),
    );
    let (mut second_dispatch, second_canonical_vc_bytes) = importable_binary_dispatch_with_kind(
        "verify-production-mismatched-export:vc1",
        VcKind::RemainderByZero,
        0x401011,
        0x91,
    );
    attach_normalized_proof_export_artifact(
        &root,
        &mut second_dispatch,
        &second_canonical_vc_bytes,
        b"normalized verify-binary mismatched proof payload 1",
        None,
        &CheckedBinaryCertificateSourceBackpropagationGate::default(),
    );
    if let ProofCertificateStatus::Present { sha256, .. } = &mut second_dispatch.certificate {
        *sha256 = Some(trust_types::digest::stable_sha256_hex(b"wrong per-vc proof export digest"));
    } else {
        panic!("fixture should attach a normalized proof export certificate");
    }
    let mut proof_evidence = VerifyBinaryEvidence::from_solver_dispatch_records(
        2,
        vec![first_dispatch, second_dispatch],
    );
    let checker = write_checker_fixture_script(
        &root,
        "verify-production-mismatched-export-checker.sh",
        "#!/bin/sh\nprintf 'verify production mismatched ok'\n",
    );

    let production_report = proof_evidence.produce_checked_certificate_artifacts(
        &root.join("checked-certs"),
        Some(checker.as_path()),
        1_777_070_404_000,
    );

    assert_eq!(production_report.status, "blocked");
    assert_eq!(production_report.proof_export_candidates, 1);
    assert_eq!(production_report.exported_artifacts, 1);
    assert_eq!(proof_evidence.checked_certificates(), 1);
    assert!(production_report.blocker_records.iter().any(|record| {
        record.code == "normalized-proof-export-binding-mismatch"
            && record.dispatch_id.as_deref() == Some("verify-production-mismatched-export:vc1")
    }));
    assert!(production_report.blocker_records.iter().any(|record| {
        record.code == "normalized-proof-export-coverage-incomplete"
            && record.detail.contains("cover 1 required VC dispatch")
    }));
    let mismatched_check = production_report
        .certificate_check_records
        .iter()
        .find(|record| record.dispatch_id == "verify-production-mismatched-export:vc1")
        .expect("mismatched dispatch should have a certificate check record");
    assert_eq!(
        mismatched_check.error_kind.as_deref(),
        Some("normalized-proof-export-binding-mismatch")
    );

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn test_verify_binary_checked_certificate_export_binds_replay_transcript_digest() {
    let root = temp_test_dir("verify-binary-production-export-replay-digest");
    let proof_bytes = b"normalized verify-binary replay-bound proof payload";
    let replay_transcript_digest = trust_types::digest::stable_sha256_hex(b"verify-binary replay transcript digest");

    let (mut dispatch, canonical_vc_bytes) =
        importable_binary_dispatch("verify-production-replay:vc0");
    dispatch.replay = ReplayStatus::Replayed;
    dispatch.diagnostics.push(format!(
        "{EXACT_REPLAY_TRANSCRIPT_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX}{replay_transcript_digest}"
    ));
    attach_normalized_proof_export_artifact(
        &root,
        &mut dispatch,
        &canonical_vc_bytes,
        proof_bytes,
        Some(replay_transcript_digest.as_str()),
        &CheckedBinaryCertificateSourceBackpropagationGate::default(),
    );
    let mut proof_evidence = VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![dispatch]);
    let checker = write_checker_fixture_script(
        &root,
        "verify-production-replay-checker.sh",
        "#!/bin/sh\nprintf 'verify replay production ok'\n",
    );
    let export_dir = root.join("checked-certs");

    let production_report = proof_evidence.produce_checked_certificate_artifacts(
        &export_dir,
        Some(checker.as_path()),
        1_777_070_404_000,
    );

    assert_eq!(production_report.status, "exported", "{production_report:#?}");
    assert_eq!(production_report.exported_artifacts, 1);
    assert!(production_report.blockers.is_empty(), "{:?}", production_report.blockers);
    assert_eq!(
        production_report.export_row_records[0].replay_transcript_digest.as_deref(),
        Some(replay_transcript_digest.as_str())
    );
    assert_eq!(
        production_report.certificate_check_records[0].replay_transcript_digest.as_deref(),
        Some(replay_transcript_digest.as_str())
    );
    assert_eq!(
        production_report.certificate_check_records[0].replay_digest_identity.status,
        "accepted"
    );

    let manifest_path = production_report
        .manifest_path
        .as_ref()
        .expect("production export should write a manifest");
    let (mut current_dispatch, _) = importable_binary_dispatch("verify-production-readback:vc0");
    current_dispatch.replay = ReplayStatus::Replayed;
    let mut readback_evidence =
        VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![current_dispatch]);
    let import_report = readback_evidence
        .load_and_import_checked_certificate_artifacts_and_manifests(
            std::iter::empty::<&Path>(),
            [Path::new(manifest_path)],
        )
        .expect("produced replay-bound manifest should load");

    assert_eq!(import_report.imported, 1, "{import_report:#?}");
    assert_eq!(
        import_report.artifacts[0].replay_transcript_digest.as_deref(),
        Some(replay_transcript_digest.as_str())
    );
    assert_eq!(import_report.artifacts[0].replay_digest_identity.status, "accepted");
    assert_eq!(readback_evidence.checked_certificates(), 1);

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn test_verify_binary_checked_certificate_export_rejects_replayed_vc_without_transcript_digest() {
    let root = temp_test_dir("verify-binary-production-export-missing-replay-digest");
    let proof_dir = root.join("proofs");
    std::fs::create_dir_all(&proof_dir).expect("proof dir should be created");
    let proof_bytes = b"normalized verify-binary replay proof without digest";
    let proof_path = proof_dir.join("vc0.lrat");
    std::fs::write(&proof_path, proof_bytes).expect("proof export should be written");

    let (mut dispatch, _) = importable_binary_dispatch("verify-production-replay-missing:vc0");
    dispatch.replay = ReplayStatus::Replayed;
    dispatch.certificate = ProofCertificateStatus::Present {
        format: "lrat".to_string(),
        sha256: Some(trust_types::digest::stable_sha256_hex(proof_bytes)),
        artifact_path: Some(proof_path.display().to_string()),
    };
    let mut proof_evidence = VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![dispatch]);
    let checker = write_checker_fixture_script(
        &root,
        "verify-production-replay-missing-checker.sh",
        "#!/bin/sh\nprintf 'verify replay production ok'\n",
    );

    let production_report = proof_evidence.produce_checked_certificate_artifacts(
        &root.join("checked-certs"),
        Some(checker.as_path()),
        1_777_070_404_000,
    );

    assert_eq!(production_report.status, "blocked");
    assert_eq!(production_report.exported_artifacts, 0);
    assert_eq!(production_report.certificate_check_records[0].status, "rejected");
    assert_eq!(
        production_report.certificate_check_records[0].error_kind.as_deref(),
        Some("replay-transcript-digest-missing")
    );
    assert!(production_report.blocker_records.iter().any(|record| {
        record.code == "replay-transcript-digest-missing"
            && record.dispatch_id.as_deref() == Some("verify-production-replay-missing:vc0")
    }));
    assert_eq!(proof_evidence.checked_certificates(), 0);
    assert!(matches!(
        proof_evidence.solver_dispatch[0].certificate,
        ProofCertificateStatus::Present { .. }
    ));

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn test_verify_binary_checked_certificate_export_fails_closed_when_checker_fails() {
    let root = temp_test_dir("verify-binary-production-export-fails");
    let proof_bytes = b"normalized verify-binary proof payload";

    let (mut dispatch, canonical_vc_bytes) =
        importable_binary_dispatch("verify-production-fails:vc0");
    attach_normalized_proof_export_artifact(
        &root,
        &mut dispatch,
        &canonical_vc_bytes,
        proof_bytes,
        None,
        &CheckedBinaryCertificateSourceBackpropagationGate::default(),
    );
    let mut proof_evidence = VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![dispatch]);
    let checker = write_checker_fixture_script(
        &root,
        "verify-production-checker-fails.sh",
        "#!/bin/sh\nprintf 'reject'; exit 7\n",
    );

    let production_report = proof_evidence.produce_checked_certificate_artifacts(
        &root.join("checked-certs"),
        Some(checker.as_path()),
        1_777_070_404_000,
    );

    assert_eq!(production_report.status, "blocked");
    assert_eq!(production_report.exported_artifacts, 0);
    assert_eq!(production_report.certificate_check_records[0].status, "rejected");
    assert_eq!(
        production_report.certificate_check_records[0].error_kind.as_deref(),
        Some("production-checker-evidence-failed")
    );
    assert!(
        production_report
            .blockers
            .iter()
            .any(|blocker| { blocker.contains("production checked-certificate checker failed") })
    );
    assert_eq!(proof_evidence.checked_certificates(), 0);
    assert!(matches!(
        proof_evidence.solver_dispatch[0].certificate,
        ProofCertificateStatus::Present { .. }
    ));

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn test_verify_binary_checked_certificate_export_rejects_noncanonical_proof_export_digest() {
    let root = temp_test_dir("verify-binary-production-export-noncanonical");
    let proof_dir = root.join("proofs");
    std::fs::create_dir_all(&proof_dir).expect("proof dir should be created");
    let proof_bytes = b"normalized verify-binary proof payload";
    let proof_path = proof_dir.join("vc0.lrat");
    std::fs::write(&proof_path, proof_bytes).expect("proof export should be written");

    let (mut dispatch, _) = importable_binary_dispatch("verify-production-noncanonical:vc0");
    dispatch.certificate = ProofCertificateStatus::Present {
        format: "lrat".to_string(),
        sha256: Some(trust_types::digest::stable_sha256_hex(proof_bytes).to_ascii_uppercase()),
        artifact_path: Some(proof_path.display().to_string()),
    };
    let mut proof_evidence = VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![dispatch]);
    let checker = write_checker_fixture_script(
        &root,
        "verify-production-checker.sh",
        "#!/bin/sh\nprintf 'should not be reached'\n",
    );

    let production_report = proof_evidence.produce_checked_certificate_artifacts(
        &root.join("checked-certs"),
        Some(checker.as_path()),
        1_777_070_404_000,
    );

    assert_eq!(production_report.status, "blocked");
    assert_eq!(production_report.exported_artifacts, 0);
    assert_eq!(production_report.certificate_check_records[0].status, "rejected");
    assert_eq!(
        production_report.certificate_check_records[0].error_kind.as_deref(),
        Some("normalized-proof-export-digest-noncanonical")
    );
    assert!(production_report.artifact_paths.is_empty());
    assert_eq!(proof_evidence.checked_certificates(), 0);

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_verify_binary_checked_certificate_export_request_raw_bytes_stays_fail_closed_golden() {
    let proof_evidence = VerifyBinaryEvidence::from_solver_dispatch_records(
        1,
        vec![raw_solver_binary_dispatch("raw-export-run:vc0", "main")],
    );
    let production_report = proof_evidence
        .checked_certificate_production_blocker_report(Path::new("target/raw-checked-certs"));
    let mut report = build_verify_binary_report(
        Path::new("fixtures/tiny.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 1 }],
            }],
            solver_results: Vec::new(),
            proof_evidence,
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );
    report.checked_certificate_production = Some(production_report);

    let gate = build_binary_cli_proof_grade_gate(&report);
    assert!(!gate.accepted);
    assert_eq!(gate.checked_certificates, 0);
    assert_eq!(gate.missing_checked_certificates, 1);
    assert_eq!(gate.raw_solver_proof_bytes, 1);
    assert!(!gate.raw_solver_proof_bytes_sufficient);
    assert!(gate.rejections.iter().any(|reason| {
        reason.contains("raw solver proof bytes present") && reason.contains("cannot upgrade trust")
    }));
    assert!(
        gate.blockers.iter().any(|blocker| blocker.code == "raw-solver-proof-bytes-audit-only")
    );

    let rendered = render_verify_binary_terminal(&report);
    assert!(rendered.contains(
        "proof_exports=0 raw_solver_proof_bytes=1 already_checked=0 exported=0 rejected=1"
    ));

    let json = serialize_verify_binary_json(&report).expect("serialize verify-binary JSON");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse verify-binary JSON");
    let actual = serde_json::json!({
        "checked_certificate_production": value["checked_certificate_production"],
        "proof_evidence": {
            "checked_certificates": value["proof_evidence"]["checked_certificate_coverage"]["checked_certificates"],
            "missing_checked_certificates": value["proof_evidence"]["checked_certificate_coverage"]["missing_checked_certificates"],
            "raw_solver_proof_bytes": value["proof_evidence"]["checked_certificate_coverage"]["raw_solver_proof_bytes"],
            "raw_solver_proof_bytes_satisfy_coverage": value["proof_evidence"]["checked_certificate_coverage"]["raw_solver_proof_bytes_satisfy_coverage"],
        },
        "proof_grade_gate": {
            "accepted": value["proof_grade_gate"]["accepted"],
            "checked_certificates": value["proof_grade_gate"]["checked_certificates"],
            "raw_solver_proof_bytes": value["proof_grade_gate"]["raw_solver_proof_bytes"],
            "raw_solver_proof_bytes_sufficient": value["proof_grade_gate"]["raw_solver_proof_bytes_sufficient"],
            "status": value["proof_grade_gate"]["status"],
        },
        "verify_binary_should_fail": verify_binary_should_fail(&report),
    });
    let expected: serde_json::Value = serde_json::from_str(include_str!(
        "fixtures/checked_certificate_export_raw_bytes_fail_closed_golden.json"
    ))
    .expect("parse checked certificate raw export golden");
    assert_eq!(actual, expected);
}

#[test]
fn test_verify_binary_imports_produced_checked_certificate_and_matches_refutation_golden() {
    let (producer_dispatch, canonical_vc_bytes) = importable_binary_dispatch("producer-run:vc0");
    let export = SolverProofExport::new(
        &producer_dispatch,
        &canonical_vc_bytes,
        "lrat",
        b"normalized checked proof payload".to_vec(),
        Some("4.13.0".to_string()),
        1_777_070_400_000,
    );
    let checker = StructuralBinaryCertificateChecker::new(
        "ay-lrat-binary-check",
        "0.1.0",
        vec!["lrat".to_string()],
        1_777_070_401_000,
    );
    let root = temp_test_dir("checked-cert-positive-refutation");
    let artifact_ref = produce_checked_certificate_artifact(
        &checker,
        BinaryCertificateCheckRequest::from_export(
            &producer_dispatch,
            &canonical_vc_bytes,
            &export,
        ),
        &root,
    )
    .expect("production helper should persist checked artifact");
    assert!(artifact_ref.path.exists());

    let cli_args = vec![
        "fixtures/tiny.bin".to_string(),
        "--json".to_string(),
        "--solver=ay".to_string(),
        "--checked-cert-artifact".to_string(),
        artifact_ref.path.display().to_string(),
    ];
    let parsed_cli =
        parse_subcommand_args(&cli_args).expect("positive checked-certificate CLI should parse");
    assert_eq!(parsed_cli.format, OutputFormat::Json);
    assert_eq!(parsed_cli.solver.as_deref(), Some("ay"));
    assert_eq!(parsed_cli.passthrough, vec!["fixtures/tiny.bin"]);
    assert_eq!(
        parsed_cli.checked_certificate_artifacts,
        vec![artifact_ref.path.display().to_string()]
    );

    let (current_dispatch, _) = importable_binary_dispatch("verify-run:vc0");
    let mut proof_evidence =
        VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![current_dispatch]);
    let import_report = proof_evidence
        .load_and_import_checked_certificate_artifacts([artifact_ref.path.as_path()])
        .expect("produced checked artifact should import through verify-binary path");
    let solver_item = binary_solver_result_report(
        "main",
        "division_by_zero".into(),
        Some("0x401010".into()),
        &trust_types::VerificationResult::Proved {
            solver: "ay-incremental".into(),
            time_ms: 4,
            strength: trust_types::ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        },
    );
    let mut verify_report = build_verify_binary_report(
        Path::new("fixtures/tiny.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 1 }],
            }],
            solver_results: vec![solver_item],
            proof_evidence,
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );
    verify_report.checked_certificate_import = Some(import_report);

    let rendered = render_verify_binary_terminal(&verify_report);
    assert!(rendered.contains("checked certificate import artifacts:\n"));
    assert!(rendered.contains("status=imported"));
    assert!(rendered.contains(
        "checker=ay-lrat-binary-check checker_version=0.1.0 format=lrat checked_at_unix_ms=1777070401000"
    ));
    assert!(rendered.contains(&format!("certificate_sha256={}", artifact_ref.content_sha256)));
    assert!(rendered.contains(&format!("path={}", artifact_ref.path.display())));

    let exploit_report =
        build_exploit_find_report(ExploitFindTarget::Verifier, verify_report.clone());
    let verify_json = serialize_verify_binary_json(&verify_report)
        .expect("serialize verify-binary checked import JSON");
    let verify_value: serde_json::Value =
        serde_json::from_str(&verify_json).expect("parse verify-binary JSON");
    let artifact = &verify_value["checked_certificate_import"]["artifacts"][0];
    assert_eq!(artifact["artifact_path"], artifact_ref.path.display().to_string());
    assert_eq!(artifact["certificate_sha256"], artifact_ref.content_sha256);
    assert_eq!(artifact["checker"], "ay-lrat-binary-check");
    assert_eq!(artifact["checker_version"], "0.1.0");
    assert_eq!(artifact["format"], "lrat");
    assert_eq!(artifact["checked_at_unix_ms"], 1_777_070_401_000u64);
    assert_eq!(artifact["status"], "imported");
    assert_eq!(artifact["dispatch_id"], "verify-run:vc0");
    assert_eq!(artifact["source_backpropagation_gate"]["source_backpropagation_allowed"], false);
    assert_eq!(
        artifact["binary_artifact_digest_identity"]["root_artifact_digest"]["value"],
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
    );
    assert_eq!(artifact["binary_artifact_digest_identity"]["selected_image"]["file_size"], 64);
    let exploit_json = serialize_exploit_find_json(&exploit_report)
        .expect("serialize exploit-find refutation JSON");
    let exploit_value: serde_json::Value =
        serde_json::from_str(&exploit_json).expect("parse exploit-find JSON");
    let refutation_accounting = &exploit_value["checked_certificate_refutation_accounting"];
    assert_eq!(refutation_accounting["required_vcs"], 1);
    assert_eq!(refutation_accounting["solver_dispatches"], 1);
    assert_eq!(refutation_accounting["proved_vcs"], 1);
    assert_eq!(refutation_accounting["checked_unsat_refutations"], 1);
    assert_eq!(refutation_accounting["missing_checked_unsat_refutations"], 0);
    assert_eq!(refutation_accounting["all_required_vcs_checked_unsat"], true);
    assert_eq!(refutation_accounting["raw_solver_candidates"], 0);
    assert_eq!(refutation_accounting["exact_replayed_candidates"], 0);
    assert_eq!(refutation_accounting["independent_refutation_status"], "not_run");
    assert_eq!(refutation_accounting["independent_refutation_satisfied"], false);
    assert!(
        refutation_accounting["diagnostic"]
            .as_str()
            .expect("refutation accounting diagnostic")
            .contains("no exploit claim was captured")
    );

    let actual = serde_json::json!({
        "verify_binary": {
            "checked_certificate_import": {
                "diagnostics": verify_value["checked_certificate_import"]["diagnostics"],
                "dispatches_missing_canonical_binding": verify_value["checked_certificate_import"]["dispatches_missing_canonical_binding"],
                "imported": verify_value["checked_certificate_import"]["imported"],
                "loaded_artifacts": verify_value["checked_certificate_import"]["loaded_artifacts"],
                "rejected_artifacts": verify_value["checked_certificate_import"]["rejected_artifacts"],
                "unmatched_artifacts": verify_value["checked_certificate_import"]["unmatched_artifacts"],
            },
            "checked_certificate_coverage": {
                "checked_certificates": verify_value["proof_evidence"]["checked_certificate_coverage"]["checked_certificates"],
                "missing_checked_certificates": verify_value["proof_evidence"]["checked_certificate_coverage"]["missing_checked_certificates"],
                "checked_certificates_satisfy_coverage": verify_value["proof_evidence"]["checked_certificate_coverage"]["checked_certificates_satisfy_coverage"],
            },
            "proof_grade_gate": {
                "checked_certificates": verify_value["proof_grade_gate"]["checked_certificates"],
                "certificate_only_replay_semantics_vcs": verify_value["proof_grade_gate"]["certificate_only_replay_semantics_vcs"],
                "replay_semantics_satisfied": verify_value["proof_grade_gate"]["replay_semantics_satisfied"],
            },
        },
        "exploit_find": {
            "independent_refutation_status": exploit_value["independent_refutation_status"],
            "independent_refutation_note": exploit_value["independent_refutation_note"],
            "evidence_gate": {
                "accepted": exploit_value["evidence_gate"]["accepted"],
                "independent_refutation": exploit_value["evidence_gate"]["independent_refutation"],
                "proof_grade_complete": exploit_value["evidence_gate"]["proof_grade_complete"],
                "unsupported_evidence_blocks_completion": exploit_value["evidence_gate"]["unsupported_evidence_blocks_completion"],
            },
            "typed_scaffold_refutation": {
                "status": exploit_value["typed_scaffold"]["refutation"]["status"],
                "independently_refuted": exploit_value["typed_scaffold"]["refutation"]["independently_refuted"],
            },
        },
    });
    let expected: serde_json::Value = serde_json::from_str(include_str!(
        "fixtures/checked_certificate_positive_refutation_golden.json"
    ))
    .expect("parse checked certificate positive golden");
    assert_eq!(actual, expected);

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_verify_binary_evidence_rejects_import_when_raw_proof_bytes_are_present() {
    let (previous_dispatch, canonical_vc_bytes) = importable_binary_dispatch("previous-run:vc0");
    let artifact = checked_binary_artifact_for_dispatch(&previous_dispatch, &canonical_vc_bytes);

    let (mut current_dispatch, _) = importable_binary_dispatch("current-run:vc0");
    current_dispatch.result = Some(trust_types::VerificationResult::Proved {
        solver: "ay-incremental".into(),
        time_ms: 4,
        strength: trust_types::ProofStrength::smt_unsat(),
        proof_certificate: Some(b"raw solver proof bytes".to_vec()),
        solver_warnings: None,
        native_proof_envelope: None,
    });

    let mut evidence =
        VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![current_dispatch]);
    let import_report = evidence.import_checked_certificate_artifacts(&[artifact]);

    assert_eq!(import_report.loaded_artifacts, 1);
    assert_eq!(import_report.imported, 0);
    assert_eq!(import_report.rejected_artifacts, 1);
    assert_eq!(import_report.unmatched_artifacts, 0);
    assert!(import_report.diagnostics[0].contains("cannot be upgraded to Checked"));
    assert_eq!(evidence.checked_certificates(), 0);
    assert_eq!(evidence.raw_solver_proof_bytes(), 1);
    assert!(!evidence.solver_dispatch[0].certificate.is_checked());
}

#[test]
fn test_verify_binary_checked_certificate_import_rejection_stays_fail_closed_in_report() {
    let (previous_dispatch, canonical_vc_bytes) = importable_binary_dispatch("previous-run:vc0");
    let artifact = checked_binary_artifact_for_dispatch(&previous_dispatch, &canonical_vc_bytes);

    let (mut current_dispatch, _) = importable_binary_dispatch("current-run:vc0");
    current_dispatch.result = Some(trust_types::VerificationResult::Proved {
        solver: "ay-incremental".into(),
        time_ms: 4,
        strength: trust_types::ProofStrength::smt_unsat(),
        proof_certificate: Some(b"raw solver proof bytes".to_vec()),
        solver_warnings: None,
        native_proof_envelope: None,
    });

    let mut proof_evidence =
        VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![current_dispatch]);
    let import_report = proof_evidence.import_checked_certificate_artifacts(&[artifact]);
    let mut report = build_verify_binary_report(
        Path::new("fixtures/tiny.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 1 }],
            }],
            solver_results: Vec::new(),
            proof_evidence,
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );
    report.checked_certificate_import = Some(import_report);

    let gate = build_binary_cli_proof_grade_gate(&report);
    assert!(!gate.accepted);
    assert_eq!(gate.checked_certificates, 0);
    assert_eq!(gate.raw_solver_proof_bytes, 1);
    assert!(gate.rejections.iter().any(|reason| reason.contains("raw solver proof bytes present")));

    let rendered = render_verify_binary_terminal(&report);
    assert!(rendered.contains("checked certificate import: loaded=1 imported=0 unmatched=0 rejected=1 dispatches_missing_canonical_binding=0\n"));
    assert!(rendered.contains("cannot be upgraded to Checked"));
    let json = serialize_verify_binary_json(&report).expect("serialize verify-binary JSON");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse JSON");
    assert_eq!(value["checked_certificate_import"]["rejected_artifacts"], 1);
    assert_eq!(value["proof_evidence"]["checked_certificate_coverage"]["checked_certificates"], 0);
    assert_eq!(value["proof_grade_gate"]["raw_solver_proof_bytes"], 1);
}

#[test]
fn test_verify_binary_report_renders_counterexample_replay_status() {
    let counterexample = trust_types::Counterexample::new(vec![(
        "ptr".into(),
        trust_types::CounterexampleValue::Uint(0xdead_beef),
    )]);
    let result = trust_types::VerificationResult::Failed {
        solver: "ay-smtlib".into(),
        time_ms: 13,
        counterexample: Some(counterexample),
    };
    let solver_item = binary_solver_result_report(
        "main",
        "binary_memory_read_invalid".into(),
        Some("0x401030".into()),
        &result,
    );

    let report = build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount {
                    kind: "binary_memory_read_invalid".into(),
                    count: 1,
                }],
            }],
            solver_results: vec![solver_item],
            proof_evidence: verify_binary_evidence_for_vcs(1),
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );

    let item = &report.solver_result_items[0];
    assert_eq!(item.replay_status.as_deref(), Some("not_attempted"));
    assert!(item.replay_detail.as_deref().unwrap().contains("needs_machine_replay"));

    let rendered = render_verify_binary_terminal(&report);
    assert!(rendered.contains("replay=not_attempted: needs_machine_replay"));
    assert!(!rendered.contains("confirmed"));

    let json = serde_json::to_string(&report).expect("serialize verify-binary report");
    assert!(json.contains("\"replay_status\":\"not_attempted\""));
    assert!(json.contains("needs_machine_replay"));
    assert!(!json.contains("confirmed"));
}

#[test]
fn test_parse_args_decompile_target_uses_to_option() {
    let args: Vec<String> = vec![
        "demo.bin".into(),
        "--to".into(),
        "rust".into(),
        "--json".into(),
        "--allow-unsupported".into(),
    ];
    let result = parse_subcommand_args(&args).expect("should parse decompile args");
    assert_eq!(result.passthrough, vec!["demo.bin"]);
    assert_eq!(result.to_ref.as_deref(), Some("rust"));
    assert_eq!(parse_decompile_target(result.to_ref.as_deref()).unwrap(), DecompileTarget::Rust);
    assert_eq!(result.format, OutputFormat::Json);
    assert!(!result.strict);
}

#[test]
fn test_parse_decompile_target_accepts_derived_text_targets() {
    assert_eq!(parse_decompile_target(Some("trust_ir")).unwrap(), DecompileTarget::TrustIr);
    assert_eq!(parse_decompile_target(Some("rust")).unwrap(), DecompileTarget::Rust);
    assert_eq!(parse_decompile_target(Some("trust-cg")).unwrap(), DecompileTarget::TrustCg);
    assert_eq!(parse_decompile_target(Some("wasm")).unwrap(), DecompileTarget::Wasm);
    assert!(parse_decompile_target(None).is_err());
    assert!(parse_decompile_target(Some("html")).is_err());
}

#[test]
fn test_decompile_output_kind_routes_derived_targets_to_text_outputs() {
    assert_eq!(
        decompile_output_kind(DecompileTarget::TrustCg, OutputFormat::Terminal),
        DecompileOutputKind::TrustCgText
    );
    assert_eq!(
        decompile_output_kind(DecompileTarget::Wasm, OutputFormat::Json),
        DecompileOutputKind::WasmText
    );
}

#[test]
fn test_decompile_rejects_html_format() {
    let args: Vec<String> = vec!["--to=trust_ir".into(), "--format=html".into()];
    assert_eq!(run_decompile_subcommand(&args), ExitCode::from(2));
}

#[test]
fn test_parse_convert_target_accepts_binary_conversion_targets() {
    let args: Vec<String> = vec![
        "demo.bin".into(),
        "--to".into(),
        "wasm".into(),
        "--entry=0x401000".into(),
        "--json".into(),
    ];
    let result = parse_subcommand_args(&args).expect("should parse convert args");
    assert_eq!(result.passthrough, vec!["demo.bin"]);
    assert_eq!(result.to_ref.as_deref(), Some("wasm"));
    assert_eq!(parse_convert_target(result.to_ref.as_deref()).unwrap(), DecompileTarget::Wasm);
    assert_eq!(parse_convert_target(Some("trust_ir")).unwrap(), DecompileTarget::TrustIr);
    assert_eq!(parse_convert_target(Some("rust")).unwrap(), DecompileTarget::Rust);
    assert_eq!(parse_convert_target(Some("trust-cg")).unwrap(), DecompileTarget::TrustCg);
    assert!(parse_convert_target(None).is_err());
    assert!(parse_convert_target(Some("html")).is_err());
}

#[test]
fn test_convert_rejects_html_format() {
    let args: Vec<String> = vec!["--to=trust_ir".into(), "--format=html".into()];
    assert_eq!(run_convert_subcommand(&args), ExitCode::from(2));
}

#[test]
fn test_convert_rejects_entry_and_all_conflict() {
    let args: Vec<String> =
        vec!["demo.bin".into(), "--to=trust_ir".into(), "--entry=0x401000".into(), "--all".into()];
    assert_eq!(run_convert_subcommand(&args), ExitCode::from(2));
}

fn trust_cg_refinement_blocker() -> TargetValidationBlocker {
    TargetValidationBlocker {
        target: trust_types::DecompileTarget::TrustCg,
        code: "missing-refinement-metadata".to_string(),
        feature: "missing-refinement-metadata".to_string(),
        reason: "trust-cg LIR has no bidirectional refinement metadata tying it to lifted TrustIr"
            .to_string(),
        ..Default::default()
    }
}

fn trust_cg_symbolic_formula_blocker() -> TargetValidationBlocker {
    TargetValidationBlocker {
        target: trust_types::DecompileTarget::TrustCg,
        function: Some("symbolic_blocked".to_string()),
        code: "symbolic-formula-proof-semantics".to_string(),
        stage: "trust-cg-bridge::target-validation".to_string(),
        feature: "symbolic-formula-proof-semantics".to_string(),
        reason:
            "symbolic formula is preserved for inspection, but target proof semantics are not discharged"
                .to_string(),
        diagnostics: vec!["blocker-code=symbolic-formula-proof-semantics".to_string()],
        ..Default::default()
    }
}

#[test]
fn test_decompile_target_validation_blocker_code_prefers_typed_machine_identity() {
    let blocker = TargetValidationBlocker {
        code: "trust-cg-backend-unavailable".to_string(),
        stage: "symbolic-proof-replay".to_string(),
        feature: "missing-refinement-metadata".to_string(),
        reason: "symbolic formula proof and source replay are unavailable".to_string(),
        diagnostics: vec!["blocker-code=legacy-wrong-code".to_string()],
        ..Default::default()
    };

    assert_eq!(decompile_target_validation_blocker_code(&blocker), "trust-cg-backend-unavailable");
}

#[test]
fn test_decompile_target_validation_blocker_code_preserves_legacy_fallback_order() {
    let diagnostic_blocker = TargetValidationBlocker {
        feature: "stable-feature-code".to_string(),
        reason: "symbolic formula would trigger the prose heuristic".to_string(),
        diagnostics: vec!["blocker-code=legacy-diagnostic-code".to_string()],
        ..Default::default()
    };
    assert_eq!(
        decompile_target_validation_blocker_code(&diagnostic_blocker),
        "legacy-diagnostic-code"
    );

    let feature_blocker = TargetValidationBlocker {
        feature: "stable-feature-code".to_string(),
        reason: "symbolic formula would trigger the prose heuristic".to_string(),
        ..Default::default()
    };
    assert_eq!(decompile_target_validation_blocker_code(&feature_blocker), "stable-feature-code");

    let prose_only_blocker = TargetValidationBlocker {
        // Old artifacts can have an empty/non-machine-readable feature and no
        // legacy diagnostic; retain their final compatibility path.
        feature: "Wasm validation blocker".to_string(),
        reason: "symbolic formula is preserved but not consumed".to_string(),
        ..Default::default()
    };
    assert_eq!(
        decompile_target_validation_blocker_code(&prose_only_blocker),
        "symbolic-formula-preservation-not-consumed"
    );
}

#[test]
fn test_checked_certificate_blocker_classification_prefers_machine_identity() {
    let unrelated = TargetValidationBlocker {
        code: "trust-cg-backend-unavailable".to_string(),
        reason: "proof certificate checks cannot run without the backend".to_string(),
        ..Default::default()
    };
    assert!(!target_blocker_mentions_checked_certificate(&unrelated));

    let typed = TargetValidationBlocker {
        code: "missing-checked-proof-certificate".to_string(),
        reason: "generic target validation failure".to_string(),
        ..Default::default()
    };
    assert!(target_blocker_mentions_checked_certificate(&typed));
    assert_eq!(
        convert_checked_certificate_blocker_code(&typed),
        "missing-checked-proof-certificate"
    );

    let legacy_diagnostic = TargetValidationBlocker {
        feature: "legacy proof feature".to_string(),
        diagnostics: vec!["blocker-code=raw-solver-proof-bytes-audit-only".to_string()],
        ..Default::default()
    };
    assert!(target_blocker_mentions_checked_certificate(&legacy_diagnostic));
    assert_eq!(
        convert_checked_certificate_blocker_code(&legacy_diagnostic),
        "raw-solver-proof-bytes-audit-only"
    );

    let prose_only = TargetValidationBlocker {
        feature: "missing checked-certificate evidence".to_string(),
        ..Default::default()
    };
    assert!(target_blocker_mentions_checked_certificate(&prose_only));
    assert_eq!(
        convert_checked_certificate_blocker_code(&prose_only),
        "checked-certificate-missing"
    );
}

fn trust_cg_preserved_symbolic_formula() -> PreservedSymbolicFormula {
    PreservedSymbolicFormula {
        target: trust_types::DecompileTarget::TrustCg,
        function: Some("symbolic_blocked".to_string()),
        block: Some(0),
        statement_index: Some(0),
        location: "statement.assign".to_string(),
        formula: Formula::Var("lifted_rax".to_string(), Sort::Int),
    }
}

#[test]
fn test_decompile_error_report_is_rejected_and_has_no_output() {
    let report = build_decompile_report(
        Path::new("demo.bin"),
        None,
        false,
        true,
        DecompileTarget::Rust,
        Err(trust_decompile::DecompileError::Lift(LiftError::UnsupportedBinaryFormat {
            format: "PE/COFF",
            reason: "test unsupported format",
        })),
    );

    assert_eq!(report.format.as_deref(), Some("PE/COFF"));
    assert!(report.architecture.is_none());
    assert_eq!(report.functions_decompiled, 0);
    assert!(report.output_kind.is_none());
    assert!(report.output_content.is_none());
    assert_eq!(report.output_trust_level, "rejected");
    assert_eq!(report.output_validation, "artifact_not_produced");
    assert!(decompile_should_fail(&report));

    let rendered = render_decompile_terminal(&report);
    assert!(rendered.contains("output trust: rejected\n"));
    assert!(!rendered.contains("output trust: partial\n"));
    assert!(!rendered.contains("output trust: exploratory\n"));
}

#[test]
fn test_decompile_macho_x86_64_unsupported_error_reports_metadata() {
    let root = temp_test_dir("decompile-macho-x86-64-unsupported");
    std::fs::create_dir_all(&root).expect("should create temp dir");
    let binary = root.join("demo-macho-x86-64");
    std::fs::write(&binary, minimal_macho_x86_64_header()).expect("should write Mach-O fixture");

    let report = build_decompile_report(
        &binary,
        None,
        false,
        true,
        DecompileTarget::TrustIr,
        Err(trust_decompile::DecompileError::Lift(LiftError::UnsupportedBinaryFormat {
            format: "Mach-O",
            reason: "only AArch64 Mach-O lifting is supported",
        })),
    );

    assert_eq!(report.status, BinaryLiftStatus::Incomplete);
    assert_eq!(report.format.as_deref(), Some("Mach-O"));
    assert_eq!(report.architecture.as_deref(), Some("x86-64"));
    assert!(report.binary_entry.is_none());
    assert_eq!(report.functions_decompiled, 0);
    assert_eq!(report.output_trust_level, "rejected");
    assert_eq!(report.unsupported, 1);
    assert_eq!(report.failures, 0);
    assert!(report.unsupported_items[0].contains("only AArch64 Mach-O lifting is supported"));
    assert!(decompile_should_fail(&report));

    let rendered = render_decompile_terminal(&report);
    assert!(rendered.contains("format: Mach-O\n"));
    assert!(rendered.contains("architecture: x86-64\n"));

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_decompile_pe_i386_json_report_stays_fail_closed() {
    let root = temp_test_dir("decompile-pe-i386-fail-closed");
    std::fs::create_dir_all(&root).expect("should create temp dir");
    let binary = root.join("minimal-pe-i386.exe");
    let bytes = minimal_pe_i386_header();
    std::fs::write(&binary, &bytes).expect("should write PE fixture");

    let report = build_decompile_report(
        &binary,
        None,
        false,
        true,
        DecompileTarget::TrustIr,
        trust_decompile::decompile_binary(&bytes, trust_decompile::DecompileOptions::default()),
    );

    assert_eq!(report.status, BinaryLiftStatus::Incomplete);
    assert_eq!(report.format.as_deref(), Some("PE/COFF"));
    assert_eq!(report.architecture.as_deref(), Some("x86"));
    assert_eq!(report.functions_decompiled, 0);
    assert_eq!(report.output_trust_level, "rejected");
    assert_eq!(report.output_validation, "artifact_not_produced");
    assert_eq!(report.unsupported, 1);
    assert_eq!(report.failures, 0);
    assert!(report.output_kind.is_none());
    assert!(report.output_content.is_none());
    assert!(
        report
            .unsupported_items
            .iter()
            .any(|item| { item.contains("PE/COFF") && item.contains("not implemented") })
    );
    assert!(decompile_should_fail(&report));

    let json = serde_json::to_value(&report).expect("decompile report should serialize");
    assert_eq!(json["status"], "incomplete");
    assert_eq!(json["format"], "PE/COFF");
    assert_eq!(json["architecture"], "x86");
    assert_eq!(json["output_trust_level"], "rejected");
    assert_eq!(json["functions_decompiled"], 0);
    assert_eq!(json["output_kind"], serde_json::Value::Null);
    assert_eq!(json["output_content"], serde_json::Value::Null);

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_decompile_elf_i386_json_report_stays_fail_closed() {
    let root = temp_test_dir("decompile-elf-i386-fail-closed");
    std::fs::create_dir_all(&root).expect("should create temp dir");
    let binary = root.join("minimal-i386.o");
    let bytes = minimal_elf32_i386_header();
    std::fs::write(&binary, &bytes).expect("should write ELF fixture");

    let report = build_decompile_report(
        &binary,
        None,
        false,
        true,
        DecompileTarget::TrustIr,
        trust_decompile::decompile_binary(&bytes, trust_decompile::DecompileOptions::default()),
    );

    assert_eq!(report.status, BinaryLiftStatus::Incomplete);
    assert_eq!(report.format.as_deref(), Some("ELF"));
    assert_eq!(report.architecture.as_deref(), Some("x86"));
    assert_eq!(report.functions_decompiled, 0);
    assert_eq!(report.output_trust_level, "rejected");
    assert_eq!(report.output_validation, "artifact_not_produced");
    assert_eq!(report.unsupported, 1);
    assert_eq!(report.failures, 0);
    assert!(report.output_kind.is_none());
    assert!(report.output_content.is_none());
    assert!(
        report
            .unsupported_items
            .iter()
            .any(|item| { item.contains("32-bit x86/i386 lifting is not implemented yet") })
    );
    assert!(decompile_should_fail(&report));

    let json = serde_json::to_value(&report).expect("decompile report should serialize");
    assert_eq!(json["status"], "incomplete");
    assert_eq!(json["format"], "ELF");
    assert_eq!(json["architecture"], "x86");
    assert_eq!(json["output_trust_level"], "rejected");
    assert_eq!(json["functions_decompiled"], 0);
    assert_eq!(json["output_kind"], serde_json::Value::Null);
    assert_eq!(json["output_content"], serde_json::Value::Null);

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_decompile_report_surfaces_x86_64_empty_ledger_binary_evidence() {
    let bytes = decode_hex_fixture(include_str!(
        "../../tests/fixtures/binary_decomp/x86_64-empty-ledger-nop-elf.hex"
    ));
    let root = temp_test_dir("decompile-x86-empty-ledger");
    std::fs::create_dir_all(&root).expect("should create temp dir");
    let binary = root.join("x86_64-empty-ledger-nop.elf");
    std::fs::write(&binary, &bytes).expect("should write checked-in ELF fixture");

    let artifact = trust_decompile::decompile_binary(
        &bytes,
        trust_decompile::DecompileOptions::with_lift(
            trust_lift::BinaryLiftOptions::functions_by_address([0x400000]),
        )
        .with_outputs([DecompileOutputKind::TrustIrJson]),
    );
    let report = build_decompile_report(
        &binary,
        Some(0x400000),
        false,
        true,
        DecompileTarget::TrustIr,
        artifact,
    );

    assert_eq!(report.status, BinaryLiftStatus::Ok);
    assert_eq!(report.unsupported, 0);
    assert!(report.unsupported_items.is_empty());
    assert_eq!(report.output_trust_level, "partial");
    assert!(report.production_proof_grade_evidence.is_none());
    assert!(report.binary_evidence.unsupported_ledger.empty);
    assert_eq!(report.binary_evidence.unsupported_ledger.total_records, 0);
    assert!(report.binary_evidence.verification_unsupported_ledger.empty);
    assert_eq!(report.binary_evidence.release_gate.status, "rejected");
    assert!(
        report
            .binary_evidence
            .release_gate
            .blockers
            .iter()
            .any(|blocker| blocker.code == "binary-verification-missing")
    );

    let identity = report
        .binary_evidence
        .binary_artifact_digest_identity
        .as_ref()
        .expect("decompile binary evidence should surface artifact digest identity");
    assert!(identity.digest_identity_allows_replay());
    assert_eq!(identity.selected_image.as_ref().map(|image| image.file_offset), Some(0));
    assert_eq!(
        identity.selected_image.as_ref().map(|image| image.file_size),
        Some(bytes.len() as u64)
    );

    let json = serde_json::to_value(&report).expect("decompile report should serialize");
    assert_eq!(json["binary_evidence"]["unsupported_ledger"]["empty"], true);
    assert_eq!(
        json["binary_evidence"]["binary_artifact_digest_identity"]["selected_image"]["file_size"],
        bytes.len() as u64
    );
    let output: serde_json::Value =
        serde_json::from_str(report.output_content.as_deref().expect("TrustIr JSON output"))
            .expect("TrustIr output should be JSON");
    assert_eq!(output["unsupported"]["records"].as_array().unwrap().len(), 0);
    assert!(output["metadata"]["root_artifact_digest"]["value"].as_str().is_some());

    let _ = std::fs::remove_dir_all(root);
}

fn x86_64_empty_ledger_decompile_report() -> DecompileReport {
    let bytes = decode_hex_fixture(include_str!(
        "../../tests/fixtures/binary_decomp/x86_64-empty-ledger-nop-elf.hex"
    ));
    let artifact = trust_decompile::decompile_binary(
        &bytes,
        trust_decompile::DecompileOptions::with_lift(
            trust_lift::BinaryLiftOptions::functions_by_address([0x400000]),
        )
        .with_outputs([DecompileOutputKind::TrustIrJson]),
    );
    build_decompile_report(
        Path::new("tests/fixtures/binary_decomp/x86_64-empty-ledger-nop.elf"),
        Some(0x400000),
        false,
        true,
        DecompileTarget::TrustIr,
        artifact,
    )
}

fn blocked_x86_64_empty_ledger_release_transcript_row(
    report: &DecompileReport,
) -> ProofGradeReleaseTranscriptRowReport {
    let target_consumer =
        TargetConsumerDigestBinding { required: true, evidence_sha256: None, binding_sha256: None };
    let identity = report
        .binary_evidence
        .binary_artifact_digest_identity
        .as_ref()
        .expect("x86_64 empty-ledger report should carry binary artifact identity");
    proof_grade_release_transcript_row_report(ProofGradeReleaseTranscriptRowInput {
        evidence_origin: "targo_trust_release_export",
        candidate_commit: None,
        binary_artifact_digest_identity: identity,
        vc_sha256s: Vec::new(),
        checked_certificate_sha256s: Vec::new(),
        replay_transcript_sha256s: Vec::new(),
        provenance_sha256s: Vec::new(),
        unsupported_ledgers_empty: true,
        target_consumer: &target_consumer,
        exact_source_ownership_sha256: None,
        type_ownership_sha256: None,
        aarch64_ordering_monitor_evidence: Vec::new(),
    })
}

fn x86_64_empty_ledger_release_evidence_json(
    report: &DecompileReport,
    release_row: &ProofGradeReleaseTranscriptRowReport,
) -> serde_json::Value {
    let report_json = serde_json::to_value(report).expect("decompile report should serialize");
    let trust_ir_json: serde_json::Value =
        serde_json::from_str(report.output_content.as_deref().expect("TrustIr JSON output"))
            .expect("TrustIr output should parse");
    let release_gate = &report.binary_evidence.release_gate;
    let blocker_codes =
        release_gate.blockers.iter().map(|blocker| blocker.code.clone()).collect::<Vec<_>>();
    serde_json::json!({
        "schema_version": "targo-trust-x86_64-empty-ledger-release-evidence.v1",
        "fixture": "tests/fixtures/binary_decomp/x86_64-empty-ledger-nop-elf.hex",
        "selection": {
            "mode": "selected-address",
            "entry": "0x400000",
            "symbol": "trust_fixture_x86_empty_ledger",
        },
        "decompile_report": {
            "status": report_json["status"].clone(),
            "target": report_json["target"].clone(),
            "output_kind": report.output_kind.clone(),
            "output_trust_level": report.output_trust_level.clone(),
            "functions_decompiled": report.functions_decompiled,
            "unsupported": report.unsupported,
            "unsupported_items": report.unsupported_items.clone(),
            "production_proof_grade_evidence": report.production_proof_grade_evidence.clone(),
        },
        "empty_unsupported_ledgers": {
            "decompile_ledger": report.unsupported == 0 && report.unsupported_items.is_empty(),
            "binary_evidence_ledger": report.binary_evidence.unsupported_ledger.empty,
            "verification_ledger": report.binary_evidence.verification_unsupported_ledger.empty,
            "trust_ir_output_ledger_records": trust_ir_json["unsupported"]["records"].as_array().map_or(0, Vec::len),
        },
        "binary_artifact_digest_identity": report.binary_evidence.binary_artifact_digest_identity.clone(),
        "trust_ir_output_identity": {
            "root_artifact_digest": trust_ir_json["metadata"]["root_artifact_digest"].clone(),
            "selected_image": trust_ir_json["metadata"]["selected_image"].clone(),
        },
        "artifact_release_gate": {
            "accepted": release_gate.accepted,
            "status": release_gate.status.clone(),
            "blocker_codes": blocker_codes,
        },
        "proof_grade_release_transcript_candidate": release_row.clone(),
    })
}

#[test]
fn test_x86_64_empty_ledger_release_evidence_matches_golden_and_blocks_release() {
    let report = x86_64_empty_ledger_decompile_report();
    assert_eq!(report.status, BinaryLiftStatus::Ok);
    assert_eq!(report.unsupported, 0);
    assert!(report.unsupported_items.is_empty());
    assert!(report.binary_evidence.unsupported_ledger.empty);
    assert!(report.binary_evidence.verification_unsupported_ledger.empty);

    let identity = report
        .binary_evidence
        .binary_artifact_digest_identity
        .as_ref()
        .expect("binary evidence should include artifact identity");
    assert!(identity.digest_identity_allows_replay());
    assert_eq!(
        identity.root_artifact_digest.as_ref().map(|digest| digest.value.as_str()),
        Some("56563acaca5b9f8590ad7513c7225c9fa85fffe192a0c9e2ed946e9bc6fb9eb0")
    );
    assert_eq!(identity.selected_image.as_ref().map(|image| image.file_offset), Some(0));
    assert_eq!(identity.selected_image.as_ref().map(|image| image.file_size), Some(816));
    assert_eq!(
        identity.selected_image.as_ref().map(|image| image.sha256.as_str()),
        Some("56563acaca5b9f8590ad7513c7225c9fa85fffe192a0c9e2ed946e9bc6fb9eb0")
    );

    assert!(!report.binary_evidence.release_gate.accepted);
    assert_eq!(report.binary_evidence.release_gate.status, "rejected");
    assert!(
        report
            .binary_evidence
            .release_gate
            .blockers
            .iter()
            .any(|blocker| blocker.code == "binary-verification-missing")
    );
    assert!(
        report
            .binary_evidence
            .release_gate
            .blockers
            .iter()
            .any(|blocker| blocker.code == "exact-source-provenance-missing")
    );

    let release_row = blocked_x86_64_empty_ledger_release_transcript_row(&report);
    assert!(!release_row.accepted);
    assert_eq!(release_row.status, "blocked");
    assert!(release_row.release_transcript_binding_digest.is_none());
    let blockers = release_row.blockers.join("\n");
    for expected in [
        "checked_certificate_digests must be a non-empty typed digest inventory",
        "replay_transcript_digests must be a non-empty list",
        "provenance_artifact_digests must be a non-empty list",
        "target proof-consumer evidence digest is missing",
        "target proof-consumer binding digest is missing",
        "exact_source_ownership_evidence.digest is missing",
        "type_ownership_evidence.digest is missing",
    ] {
        assert!(blockers.contains(expected), "missing `{expected}` in {blockers}");
    }

    let transcript = proof_grade_release_transcript_report(std::slice::from_ref(&release_row));
    assert!(transcript.accepted_proof_grade_rows.is_empty());
    assert_eq!(transcript.blocked_proof_grade_rows, vec![release_row.clone()]);

    let actual = x86_64_empty_ledger_release_evidence_json(&report, &release_row);
    let actual_pretty =
        serde_json::to_string_pretty(&actual).expect("serialize x86 empty-ledger evidence") + "\n";
    let expected: serde_json::Value = serde_json::from_str(include_str!(
        "fixtures/x86_64_empty_ledger_release_evidence_golden.json"
    ))
    .expect("parse x86 empty-ledger release evidence golden");
    assert_eq!(actual, expected, "generated x86 empty-ledger evidence:\n{actual_pretty}");
}

#[test]
fn test_decompile_big_endian_elf_aarch64_json_report_stays_fail_closed() {
    let root = temp_test_dir("decompile-elf-be-aarch64-fail-closed");
    std::fs::create_dir_all(&root).expect("should create temp dir");
    let binary = root.join("minimal-be-aarch64.elf");
    let bytes = minimal_elf64_be_aarch64_header();
    std::fs::write(&binary, &bytes).expect("should write ELF fixture");

    let report = build_decompile_report(
        &binary,
        None,
        false,
        true,
        DecompileTarget::TrustIr,
        trust_decompile::decompile_binary(&bytes, trust_decompile::DecompileOptions::default()),
    );

    assert_eq!(report.status, BinaryLiftStatus::Incomplete);
    assert_eq!(report.format.as_deref(), Some("ELF"));
    assert_eq!(report.architecture.as_deref(), Some("AArch64"));
    assert_eq!(report.binary_entry.as_deref(), Some("0x0"));
    assert_eq!(report.functions_decompiled, 0);
    assert_eq!(report.output_trust_level, "rejected");
    assert_eq!(report.output_validation, "artifact_not_produced");
    assert_eq!(report.unsupported, 1);
    assert_eq!(report.failures, 0);
    assert!(report.output_kind.is_none());
    assert!(report.output_content.is_none());
    assert!(report.unsupported_items.iter().any(|item| {
        item.contains("ELF") && item.contains("only little-endian AArch64 and x86-64")
    }));
    assert!(decompile_should_fail(&report));

    let json = serde_json::to_value(&report).expect("decompile report should serialize");
    assert_eq!(json["status"], "incomplete");
    assert_eq!(json["format"], "ELF");
    assert_eq!(json["architecture"], "AArch64");
    assert_eq!(json["binary_entry"], "0x0");
    assert_eq!(json["output_trust_level"], "rejected");
    assert_eq!(json["functions_decompiled"], 0);
    assert_eq!(json["unsupported"], 1);
    assert_eq!(json["failures"], 0);
    assert_eq!(json["output_kind"], serde_json::Value::Null);
    assert_eq!(json["output_content"], serde_json::Value::Null);

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_decompile_json_report_preserves_instruction_provenance() {
    let movabs_bytes = vec![0x48, 0xB8, 0x78, 0x56, 0x34, 0x12, 0, 0, 0, 0];
    let movabs_origin = BinaryOrigin {
        binary_path: Some("demo.bin".to_string()),
        function_entry: Some(0x401000),
        instruction_address: 0x401000,
        instruction_size: Some(10),
        encoding: Some(0xB8),
        instruction_bytes: movabs_bytes.clone(),
        source: Some(SourceSpan::binary_address(0x401000)),
    };
    let artifact = trust_types::DecompilationArtifact {
        binary: trust_types::BinaryArtifactMetadata {
            path: Some("demo.bin".to_string()),
            format: trust_types::BinaryArtifactFormat::Elf,
            architecture: "x86-64".to_string(),
            entry_point: Some(0x401000),
            ..Default::default()
        },
        functions: vec![trust_types::DecompiledFunction {
            name: "return_imm".to_string(),
            entry: 0x401000,
            origin: Some(movabs_origin.clone()),
            instruction_provenance: vec![movabs_origin.clone()],
            ..Default::default()
        }],
        ..Default::default()
    };

    let report = build_decompile_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        DecompileTarget::TrustIr,
        Ok(artifact),
    );

    assert_eq!(report.functions.len(), 1);
    assert_eq!(report.functions[0].instruction_provenance, vec![movabs_origin]);
    let json = serde_json::to_value(&report).expect("decompile report should serialize");
    assert_eq!(
        json["functions"][0]["instruction_provenance"][0]["instruction_bytes"],
        serde_json::json!(movabs_bytes)
    );
    assert_eq!(json["functions"][0]["instruction_provenance"][0]["instruction_size"], 10);
}

fn minimal_macho_x86_64_header() -> Vec<u8> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&0xfeed_facfu32.to_le_bytes());
    bytes.extend_from_slice(&0x0100_0007i32.to_le_bytes());
    bytes.extend_from_slice(&3i32.to_le_bytes());
    bytes.extend_from_slice(&2u32.to_le_bytes());
    bytes.extend_from_slice(&0u32.to_le_bytes());
    bytes.extend_from_slice(&0u32.to_le_bytes());
    bytes.extend_from_slice(&0u32.to_le_bytes());
    bytes.extend_from_slice(&0u32.to_le_bytes());
    bytes
}

fn minimal_pe_i386_header() -> Vec<u8> {
    let mut bytes = vec![0u8; 0x80];
    bytes[0..2].copy_from_slice(b"MZ");
    bytes[0x3c..0x40].copy_from_slice(&0x40u32.to_le_bytes());
    bytes[0x40..0x44].copy_from_slice(b"PE\0\0");
    bytes[0x44..0x46].copy_from_slice(&0x014cu16.to_le_bytes());
    bytes
}

fn decode_hex_fixture(text: &str) -> Vec<u8> {
    let compact: Vec<_> = text.bytes().filter(|byte| !byte.is_ascii_whitespace()).collect();
    assert_eq!(compact.len() % 2, 0, "hex fixture should contain whole bytes");
    compact.chunks(2).map(|pair| (hex_nibble(pair[0]) << 4) | hex_nibble(pair[1])).collect()
}

fn hex_nibble(byte: u8) -> u8 {
    match byte {
        b'0'..=b'9' => byte - b'0',
        b'a'..=b'f' => byte - b'a' + 10,
        b'A'..=b'F' => byte - b'A' + 10,
        _ => panic!("non-hex byte in fixture: {byte}"),
    }
}

fn minimal_elf64_be_aarch64_header() -> Vec<u8> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(b"\x7fELF");
    bytes.push(2); // ELFCLASS64
    bytes.push(2); // ELFDATA2MSB
    bytes.push(1); // EV_CURRENT
    bytes.push(0); // OS/ABI
    bytes.extend_from_slice(&[0u8; 8]);
    bytes.extend_from_slice(&2u16.to_be_bytes()); // ET_EXEC
    bytes.extend_from_slice(&0xB7u16.to_be_bytes()); // EM_AARCH64
    bytes.extend_from_slice(&1u32.to_be_bytes()); // e_version
    bytes.extend_from_slice(&0u64.to_be_bytes()); // e_entry
    bytes.extend_from_slice(&0u64.to_be_bytes()); // e_phoff
    bytes.extend_from_slice(&0u64.to_be_bytes()); // e_shoff
    bytes.extend_from_slice(&0u32.to_be_bytes()); // e_flags
    bytes.extend_from_slice(&64u16.to_be_bytes()); // e_ehsize
    bytes.extend_from_slice(&56u16.to_be_bytes()); // e_phentsize
    bytes.extend_from_slice(&0u16.to_be_bytes()); // e_phnum
    bytes.extend_from_slice(&64u16.to_be_bytes()); // e_shentsize
    bytes.extend_from_slice(&0u16.to_be_bytes()); // e_shnum
    bytes.extend_from_slice(&0u16.to_be_bytes()); // e_shstrndx
    bytes
}

fn minimal_elf32_i386_header() -> Vec<u8> {
    let mut bytes = vec![0u8; 52];
    bytes[0..4].copy_from_slice(b"\x7fELF");
    bytes[4] = 1;
    bytes[5] = 1;
    bytes[6] = 1;
    bytes[16..18].copy_from_slice(&1u16.to_le_bytes());
    bytes[18..20].copy_from_slice(&3u16.to_le_bytes());
    bytes[20..24].copy_from_slice(&1u32.to_le_bytes());
    bytes[40..42].copy_from_slice(&52u16.to_le_bytes());
    bytes
}

fn exact_binary_source_provenance_summary() -> BinarySourceProvenanceSummary {
    BinarySourceProvenanceSummary {
        status: "exact".into(),
        exact_mapping_count: 1,
        ambiguous_mapping_count: 0,
        diagnostics: Vec::new(),
        source_backpropagation_allowed: true,
    }
}

fn accepted_checked_source_gate() -> CheckedBinaryCertificateSourceBackpropagationGate {
    CheckedBinaryCertificateSourceBackpropagationGate {
        replay_grade_artifact_identity: true,
        checked_certificate_identity: true,
        exact_replay_identity: true,
        accepted_reconstruction_validation: true,
        accepted_target_validation: true,
        exact_source_provenance: true,
        source_provenance: exact_binary_source_provenance_summary(),
        source_backpropagation_allowed: true,
        blockers: Vec::new(),
        ..Default::default()
    }
}

fn unconsumed_symbolic_checked_source_gate() -> CheckedBinaryCertificateSourceBackpropagationGate {
    accepted_checked_source_gate().with_symbolic_formula_consumer_evidence(1, false)
}

fn consumed_symbolic_checked_source_gate() -> CheckedBinaryCertificateSourceBackpropagationGate {
    accepted_checked_source_gate().with_symbolic_formula_consumer_evidence(1, true)
}

fn proof_grade_convert_report_with_source_provenance(
    source_provenance: BinarySourceProvenanceSummary,
) -> DecompileReport {
    DecompileReport {
        binary: "demo.bin".into(),
        format: Some("ELF".into()),
        architecture: Some("x86_64".into()),
        selection: "address".into(),
        entry: Some("0x401000".into()),
        binary_entry: Some("0x401000".into()),
        source_provenance,
        strict: true,
        target: DecompileTarget::TrustCg,
        status: BinaryLiftStatus::Ok,
        output_kind: Some("trust_cg_text".into()),
        output_trust_level: "proof_grade".into(),
        output_validation: "translation_validated".into(),
        validation_note: "synthetic target validation accepted".into(),
        output_content: Some("{\"functions\":[]}".into()),
        production_proof_grade_evidence: None,
        binary_evidence: DecompileBinaryEvidenceReport::default(),
        target_validation_blockers: Vec::new(),
        preserved_symbolic_formulas: Vec::new(),
        functions_decompiled: 1,
        blocks: 1,
        instructions: 1,
        statements: 1,
        memory_facts: 0,
        unsupported: 0,
        failures: 0,
        functions: Vec::new(),
        unsupported_items: Vec::new(),
        failure_items: Vec::new(),
    }
}

#[test]
fn test_decompile_and_convert_json_surface_source_provenance_summary() {
    let report = proof_grade_convert_report_with_source_provenance(BinarySourceProvenanceSummary {
        status: "exact".into(),
        exact_mapping_count: 2,
        ambiguous_mapping_count: 1,
        diagnostics: vec![
            "binary source provenance artifact has ambiguous duplicate mapping(s) for 0x401000"
                .into(),
        ],
        source_backpropagation_allowed: false,
    });

    let decompile_value = serde_json::to_value(&report).expect("serialize decompile JSON");
    let decompile_provenance = &decompile_value["source_provenance"];
    assert_eq!(decompile_provenance["status"], "exact");
    assert_eq!(decompile_provenance["exact_mapping_count"], 2);
    assert_eq!(decompile_provenance["ambiguous_mapping_count"], 1);
    assert_eq!(decompile_provenance["source_backpropagation_allowed"], false);
    assert!(
        decompile_provenance["diagnostics"]
            .as_array()
            .expect("source provenance diagnostics")
            .iter()
            .any(|diagnostic| diagnostic
                .as_str()
                .expect("diagnostic string")
                .contains("ambiguous duplicate mapping"))
    );

    let convert_json = serialize_convert_json(&report).expect("serialize convert JSON");
    let convert_value: serde_json::Value =
        serde_json::from_str(&convert_json).expect("parse convert JSON");
    assert_eq!(convert_value["source_provenance"], decompile_value["source_provenance"]);
    assert!(
        convert_value["conversion_gate"]["blockers"]
            .as_array()
            .expect("conversion blockers")
            .iter()
            .any(|blocker| blocker.as_str().expect("blocker").contains("exact-source-provenance"))
    );
}

#[test]
fn test_convert_partial_derived_output_fails_without_proof_grade_claim() {
    let report = DecompileReport {
        binary: "demo.bin".into(),
        format: Some("ELF".into()),
        architecture: Some("x86_64".into()),
        selection: "address".into(),
        entry: Some("0x401000".into()),
        binary_entry: Some("0x401000".into()),
        source_provenance: BinarySourceProvenanceSummary::default(),
        strict: false,
        target: DecompileTarget::TrustCg,
        status: BinaryLiftStatus::Ok,
        output_kind: Some("trust_cg_text".into()),
        output_trust_level: "partial".into(),
        output_validation: "validated_partial".into(),
        validation_note:
            "trust-cg text passed structural validation, but remains partial and is not proof-grade"
                .into(),
        output_content: Some("{\"functions\":[]}".into()),
        production_proof_grade_evidence: None,
        binary_evidence: DecompileBinaryEvidenceReport::default(),
        target_validation_blockers: Vec::new(),
        preserved_symbolic_formulas: Vec::new(),
        functions_decompiled: 1,
        blocks: 1,
        instructions: 1,
        statements: 1,
        memory_facts: 0,
        unsupported: 0,
        failures: 0,
        functions: Vec::new(),
        unsupported_items: Vec::new(),
        failure_items: Vec::new(),
    };

    assert!(!decompile_should_fail(&report));
    assert!(convert_should_fail(&report));
    let rendered = render_convert_terminal(&report);
    assert!(rendered.contains("targo trust convert report\n"));
    assert!(rendered.contains("target: trust-cg\n"));
    assert!(rendered.contains("output kind: trust_cg_text\n"));
    assert!(rendered.contains("output trust: partial\n"));
    assert!(rendered.contains("validated_partial\n"));
    assert!(rendered.contains("remains partial and is not proof-grade"));
    assert!(rendered.contains("conversion gate: rejected\n"));
    assert!(
        rendered.contains("conversion gate detail: target=trust-cg proof_grade_artifact=false")
    );
    assert!(rendered.contains("conversion gate blockers:\n"));

    let gate = build_convert_cli_gate(&report);
    assert!(!gate.accepted);
    assert_eq!(gate.status, "rejected");
    assert_eq!(gate.target, "trust-cg");
    assert!(!gate.proof_grade_artifact);
    assert!(gate.reason.contains("output trust is `partial`"));
    assert!(gate.validation_blockers.iter().any(|blocker| {
        blocker.contains("output validation is `validated_partial`")
            && blocker.contains("translation validation has not accepted")
    }));
    assert!(!gate.reason.contains("conversion backend is unavailable"));

    let json = serialize_convert_json(&report).expect("serialize convert JSON");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse convert JSON");
    assert_eq!(value["conversion_gate"]["accepted"], false);
    assert_eq!(value["conversion_gate"]["status"], "rejected");
    assert_eq!(value["conversion_gate"]["target"], "trust-cg");
    assert_eq!(value["conversion_gate"]["proof_grade_artifact"], false);
    assert!(
        value["conversion_gate"]["reason"].as_str().unwrap().contains("output trust is `partial`")
    );
    assert!(
        value["conversion_gate"]["validation_blockers"]
            .as_array()
            .expect("validation blockers")
            .iter()
            .any(|blocker| blocker.as_str().unwrap().contains("validated_partial"))
    );
}

#[test]
fn test_decompile_trust_ir_source_backpropagation_gate_names_missing_reconstruction_evidence() {
    let report = DecompileReport {
        binary: "demo.bin".into(),
        format: Some("ELF".into()),
        architecture: Some("x86_64".into()),
        selection: "entry".into(),
        entry: None,
        binary_entry: Some("0x401000".into()),
        source_provenance: exact_binary_source_provenance_summary(),
        strict: false,
        target: DecompileTarget::TrustIr,
        status: BinaryLiftStatus::Incomplete,
        output_kind: Some("trust_ir_text".into()),
        output_trust_level: "partial".into(),
        output_validation: "lifted_trust_ir_partial".into(),
        validation_note:
            "TrustIr output is partial; no verification summary is attached proving full coverage"
                .into(),
        output_content: Some("binary format=ELF arch=x86_64 entry=0x401000".into()),
        production_proof_grade_evidence: None,
        binary_evidence: DecompileBinaryEvidenceReport::default(),
        target_validation_blockers: Vec::new(),
        preserved_symbolic_formulas: Vec::new(),
        functions_decompiled: 1,
        blocks: 1,
        instructions: 1,
        statements: 1,
        memory_facts: 0,
        unsupported: 1,
        failures: 0,
        functions: Vec::new(),
        unsupported_items: vec!["trust-lift @ 0x401000: unsupported opcode".into()],
        failure_items: Vec::new(),
    };

    let gate = build_convert_cli_gate(&report);
    assert!(!gate.source_backpropagation_gate.accepted);
    assert_eq!(gate.source_backpropagation_gate.source_provenance, "accepted");
    assert_eq!(gate.source_backpropagation_gate.binary_verification_evidence, "missing");
    assert_eq!(gate.source_backpropagation_gate.reconstruction_evidence, "partial");
    assert_eq!(
        gate.source_backpropagation_gate.checked_certificate_source_backpropagation_gate,
        "missing"
    );
    assert!(
        gate.source_backpropagation_gate.blockers.iter().any(|blocker| {
            blocker.code == "accepted-reconstruction-target-validation-missing"
                && blocker.detail.contains("accepted reconstruction and target validation")
        }),
        "{:?}",
        gate.source_backpropagation_gate.blockers
    );

    let rendered = render_decompile_terminal(&report);
    assert!(rendered.contains("source backpropagation gate: rejected"));
    assert!(rendered.contains("source_provenance=accepted"));
    assert!(rendered.contains("binary_verification=missing"));
    assert!(rendered.contains("reconstruction=partial"));
    assert!(rendered.contains("checked_certificate_source_backpropagation_gate=missing"));
    assert!(rendered.contains("accepted-reconstruction-target-validation-missing"));
    assert!(rendered.contains("checked-certificate-source-backpropagation-gate-missing"));

    let json = serialize_decompile_json_with_checked_certificate_loader(
        &report,
        super::convert_checked_certificate_loader_not_requested(),
    )
    .expect("serialize decompile JSON");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse decompile JSON");
    let source_gate = &value["artifact_gate"]["source_backpropagation_gate"];
    assert_eq!(source_gate["accepted"], false);
    assert_eq!(source_gate["source_provenance"], "accepted");
    assert_eq!(source_gate["binary_verification_evidence"], "missing");
    assert_eq!(source_gate["reconstruction_evidence"], "partial");
    assert_eq!(source_gate["checked_certificate_source_backpropagation_gate"], "missing");
    assert!(
        source_gate["blockers"].as_array().expect("source backprop blockers").iter().any(
            |blocker| blocker["code"] == "accepted-reconstruction-target-validation-missing"
                && blocker["evidence_required"]
                    .as_array()
                    .expect("evidence required")
                    .iter()
                    .any(|item| item.as_str() == Some("accepted_reconstruction"))
        ),
        "{source_gate}"
    );
}

#[test]
fn test_convert_json_preserves_symbolic_formulas_when_trust_cg_gate_rejects() {
    let preserved_formula = trust_types::PreservedSymbolicFormula {
        target: trust_types::DecompileTarget::TrustCg,
        function: Some("entry".into()),
        block: Some(0),
        statement_index: Some(2),
        location: "0x401000:bb0:stmt2".into(),
        formula: Formula::Eq(
            Box::new(Formula::Var("rdi_at_entry".into(), trust_types::Sort::BitVec(64))),
            Box::new(Formula::BitVec { value: 0, width: 64 }),
        ),
    };
    let report = DecompileReport {
        binary: "demo.bin".into(),
        format: Some("ELF".into()),
        architecture: Some("x86_64".into()),
        selection: "address".into(),
        entry: Some("0x401000".into()),
        binary_entry: Some("0x401000".into()),
        strict: true,
        target: DecompileTarget::TrustCg,
        status: BinaryLiftStatus::Ok,
        output_kind: Some("trust_cg_text".into()),
        output_trust_level: "partial".into(),
        output_validation: "validated_partial".into(),
        validation_note:
            "trust-cg text passed structural validation, but remains partial and is not proof-grade"
                .into(),
        output_content: Some(
            r#"{"target_validation_blockers":[{"feature":"missing-refinement-metadata"}],"functions":[{"name":"entry"}]}"#
                .into(),
        ),
        production_proof_grade_evidence: None,
        binary_evidence: DecompileBinaryEvidenceReport::default(),
        source_provenance: BinarySourceProvenanceSummary::default(),
        target_validation_blockers: vec![trust_cg_refinement_blocker()],
        preserved_symbolic_formulas: vec![preserved_formula.clone()],
        functions_decompiled: 1,
        blocks: 1,
        instructions: 1,
        statements: 1,
        memory_facts: 0,
        unsupported: 0,
        failures: 0,
        functions: Vec::new(),
        unsupported_items: Vec::new(),
        failure_items: Vec::new(),
    };

    assert!(!decompile_should_fail(&report));
    assert!(convert_should_fail(&report));

    let json = serialize_convert_json(&report).expect("serialize convert JSON");
    assert!(json.contains("rdi_at_entry"));
    assert!(!json.contains("Undef"));
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse convert JSON");
    assert_eq!(value["conversion_gate"]["accepted"], false);
    assert_eq!(value["conversion_gate"]["status"], "rejected");
    assert_eq!(value["conversion_gate"]["target"], "trust-cg");
    assert_eq!(value["conversion_gate"]["proof_grade_artifact"], false);
    assert!(value["output_content"].is_string());
    assert_eq!(value["trust_cg_output"]["functions"][0]["name"], "entry");
    assert_eq!(
        value["trust_cg_output"]["target_validation_blockers"][0]["feature"],
        "missing-refinement-metadata"
    );
    assert_eq!(value["conversion_gate"]["checked_certificate_evidence"]["status"], "blocked");
    assert_eq!(value["target_validation_blockers"][0]["feature"], "missing-refinement-metadata");
    assert!(
        value["conversion_gate"]["validation_blockers"]
            .as_array()
            .expect("validation blockers")
            .iter()
            .any(|blocker| blocker.as_str().unwrap().contains("validated_partial"))
    );

    let preserved: Vec<trust_types::PreservedSymbolicFormula> =
        serde_json::from_value(value["preserved_symbolic_formulas"].clone())
            .expect("preserved symbolic formulas");
    assert_eq!(preserved, vec![preserved_formula]);
}

#[test]
fn test_decompile_and_convert_json_surface_lower_binary_evidence_blockers() {
    let origin = BinaryOrigin {
        binary_path: Some("fixtures/tiny.bin".to_string()),
        function_entry: Some(0x401000),
        instruction_address: 0x401010,
        instruction_size: Some(1),
        encoding: Some(0x90),
        instruction_bytes: vec![0x90],
        source: Some(SourceSpan::binary_address(0x401010)),
    };
    let mut dispatch = raw_solver_binary_dispatch("trust_cg-lower-evidence:vc0", "entry");
    dispatch.origin = Some(origin.clone());
    dispatch.vc_kind = Some(VcKind::DivisionByZero);
    dispatch.replay = ReplayStatus::NotAttempted;
    dispatch.certificate = ProofCertificateStatus::Present {
        format: "solver-native".to_string(),
        sha256: Some("raw-proof-sha".to_string()),
        artifact_path: Some("target/proofs/raw.bin".to_string()),
    };
    dispatch.binary_artifact_digest_identity = None;
    let unsupported_record = trust_types::UnsupportedRecord {
        stage: "trust-decompile::trust_cg".to_string(),
        architecture: Some("x86-64".to_string()),
        origin: Some(origin.clone()),
        opcode: Some("call".to_string()),
        operand: None,
        feature: "unsupported direct call target requires replay witness".to_string(),
    };
    let unsupported = trust_types::UnsupportedLedger { records: vec![unsupported_record.clone()] };
    let mut verification =
        trust_types::BinaryVerificationSummary::from_solver_dispatch(vec![dispatch]);
    verification.unsupported_ledger = unsupported.clone();
    verification.refresh_from_solver_dispatch();
    verification.proof_certificate = ProofCertificateStatus::Present {
        format: "solver-native".to_string(),
        sha256: Some("aggregate-raw-proof-sha".to_string()),
        artifact_path: None,
    };
    let symbolic_formula = trust_cg_preserved_symbolic_formula();
    let target_blocker = trust_cg_symbolic_formula_blocker();
    let artifact = trust_types::DecompilationArtifact {
        binary: trust_types::BinaryArtifactMetadata {
            path: Some("fixtures/tiny.bin".to_string()),
            format: trust_types::BinaryArtifactFormat::Elf,
            architecture: "x86-64".to_string(),
            entry_point: Some(0x401000),
            ..Default::default()
        },
        target: trust_types::DecompileTarget::TrustCg,
        functions: vec![trust_types::DecompiledFunction {
            name: "entry".to_string(),
            entry: 0x401000,
            origin: Some(origin.clone()),
            instruction_provenance: vec![origin],
            ..Default::default()
        }],
        unsupported: unsupported.clone(),
        source_provenance: exact_binary_source_provenance_summary(),
        verification,
        reconstruction: trust_types::ReconstructionSummary {
            target: trust_types::DecompileTarget::TrustCg,
            validation: trust_types::ReconstructionValidationStatus::Validated,
            trust_level: trust_types::TrustLevel::Rejected,
            outputs: vec![trust_types::DecompiledOutput {
                target: trust_types::DecompileTarget::TrustCg,
                text: Some(r#"{"functions":[{"name":"entry"}],"typed":true}"#.to_string()),
                validation: trust_types::ReconstructionValidationStatus::Validated,
                trust_level: trust_types::TrustLevel::Rejected,
                target_validation_blockers: vec![target_blocker.clone()],
                preserved_symbolic_formulas: vec![symbolic_formula.clone()],
                ..Default::default()
            }],
            ..Default::default()
        },
        trust_level: trust_types::TrustLevel::Rejected,
        ..Default::default()
    };
    let report = build_decompile_report(
        Path::new("fixtures/tiny.bin"),
        Some(0x401000),
        false,
        true,
        DecompileTarget::TrustCg,
        Ok(artifact),
    );

    assert_eq!(report.binary_evidence.proof_certificate.status, "present");
    assert_eq!(report.binary_evidence.replay_status, "not_attempted");
    assert_eq!(report.binary_evidence.unsupported_ledger.total_records, 1);
    assert!(!report.binary_evidence.release_gate.accepted);
    assert!(
        report.binary_evidence.release_gate.blockers.iter().any(|blocker| {
            blocker.code == "checked-certificate-missing"
                && blocker.evidence_required.contains(&"checked_certificate_artifact".to_string())
        }),
        "{:?}",
        report.binary_evidence.release_gate.blockers
    );
    let rendered = render_decompile_terminal(&report);
    assert!(rendered.contains("binary evidence: verification_status=mixed"));
    assert!(rendered.contains("replay=not_attempted"));
    assert!(rendered.contains("proof_certificate=present"));
    assert!(rendered.contains("unsupported_ledger=1"));
    assert!(rendered.contains("binary evidence blockers:"));
    assert!(rendered.contains("checked-certificate-missing"));

    for json in [
        serialize_decompile_json_with_checked_certificate_loader(
            &report,
            super::convert_checked_certificate_loader_not_requested(),
        )
        .expect("serialize decompile JSON"),
        serialize_convert_json(&report).expect("serialize convert JSON"),
    ] {
        let value: serde_json::Value = serde_json::from_str(&json).expect("parse JSON");
        let gate_key = if value.get("conversion_gate").is_some() {
            "conversion_gate"
        } else {
            "artifact_gate"
        };
        assert_eq!(value["target"], "trust-cg");
        assert_eq!(value["binary_evidence"]["proof_certificate"]["status"], "present");
        assert_eq!(value["binary_evidence"]["replay_status"], "not_attempted");
        assert_eq!(
            value["binary_evidence"]["solver_dispatches"][0]["proof_certificate"]["status"],
            "present"
        );
        assert_eq!(
            value["binary_evidence"]["solver_dispatches"][0]["exact_source_provenance"],
            false
        );
        assert_eq!(
            value["binary_evidence"]["solver_dispatches"][0]["replay_digest_identity_accepted"],
            false
        );
        assert_eq!(value["binary_evidence"]["unsupported_ledger"]["total_records"], 1);
        assert_eq!(
            value["binary_evidence"]["unsupported_ledger"]["records"][0]["feature"],
            unsupported_record.feature
        );
        assert_eq!(value["binary_evidence"]["release_gate"]["accepted"], false);
        assert!(
            value["binary_evidence"]["release_gate"]["blockers"]
                .as_array()
                .expect("binary evidence blockers")
                .iter()
                .any(|blocker| blocker["code"] == "exact-machine-replay-missing")
        );
        assert!(
            value["binary_evidence"]["release_gate"]["blockers"]
                .as_array()
                .expect("binary evidence blockers")
                .iter()
                .any(|blocker| blocker["code"] == "unsupported-ledger-nonempty")
        );
        assert_eq!(value["target_evidence"]["target_validation_blocker_count"], 1);
        assert_eq!(value["target_evidence"]["symbolic_formula_preservation"]["preserved_count"], 1);
        assert_eq!(
            value["target_evidence"]["symbolic_formula_preservation"]["consumer_accepted"],
            false
        );
        assert!(
            value["target_evidence"]["blockers"]
                .as_array()
                .expect("target evidence blockers")
                .iter()
                .any(|blocker| { blocker["code"] == "symbolic-formula-preservation-not-consumed" })
        );
        assert_eq!(value[gate_key]["accepted"], false);
        assert_eq!(value[gate_key]["status"], "rejected");
        assert!(
            value[gate_key]["target_proof_consumer_evidence"]["blockers"]
                .as_array()
                .expect("target proof-consumer blockers")
                .iter()
                .any(|blocker| blocker["code"] == "target-semantics-not-consumed")
        );
    }
}

#[test]
fn test_decompile_json_surfaces_aarch64_sync_boundary_release_blocker() {
    let mut dispatch = checked_binary_dispatch("sync-boundary:vc0", "main");
    dispatch.binary_artifact_digest_identity = Some(fixture_binary_artifact_digest_identity());
    if let Some(origin) = dispatch.origin.as_mut() {
        origin.source = Some(SourceSpan {
            file: "src/main.rs".to_string(),
            line_start: 7,
            col_start: 1,
            line_end: 7,
            col_end: 8,
        });
    }

    let origin = BinaryOrigin {
        binary_path: Some("fixtures/tiny.bin".to_string()),
        function_entry: Some(0x401000),
        instruction_address: 0x401014,
        instruction_size: Some(4),
        encoding: Some(0xd503_3bbf),
        instruction_bytes: vec![0xbf, 0x3b, 0x03, 0xd5],
        source: Some(SourceSpan::binary_address(0x401014)),
    };
    let unsupported_record = trust_types::UnsupportedRecord {
        stage: "trust-lift::semantic".to_string(),
        architecture: Some("aarch64".to_string()),
        origin: Some(origin.clone()),
        opcode: Some("DMB".to_string()),
        operand: Some("ish".to_string()),
        feature: "unsupported AArch64 memory-order boundary; kind=DataMemoryBarrier; scope=InnerShareable; ordering=LoadsAndStores; clears_exclusive_monitor=false; raw_option=0xb"
            .to_string(),
    };
    let unsupported = trust_types::UnsupportedLedger { records: vec![unsupported_record.clone()] };
    let digest_identity = fixture_binary_artifact_digest_identity();
    let verification = trust_types::BinaryVerificationSummary {
        status: trust_types::BinaryVerificationStatus::Proved,
        trust_level: trust_types::TrustLevel::ProofGrade,
        total_vcs: 1,
        proved: 1,
        replay: ReplayStatus::Replayed,
        proof_certificate: ProofCertificateStatus::Checked {
            checker: "fixture-checker".to_string(),
            format: "lfsc".to_string(),
            sha256: Some("sync-boundary-vc0-sha256".to_string()),
        },
        solver_dispatch: vec![dispatch],
        ..Default::default()
    };
    let artifact = trust_types::DecompilationArtifact {
        binary: trust_types::BinaryArtifactMetadata {
            path: Some("fixtures/tiny.bin".to_string()),
            format: trust_types::BinaryArtifactFormat::Elf,
            architecture: "aarch64".to_string(),
            entry_point: Some(0x401000),
            byte_len: Some(64),
            root_artifact_digest: digest_identity.root_artifact_digest.clone(),
            selected_image: digest_identity.selected_image.clone(),
            ..Default::default()
        },
        target: trust_types::DecompileTarget::TrustIr,
        functions: vec![trust_types::DecompiledFunction {
            name: "main".to_string(),
            entry: 0x401000,
            origin: Some(origin.clone()),
            instruction_provenance: vec![origin],
            ..Default::default()
        }],
        unsupported,
        source_provenance: exact_binary_source_provenance_summary(),
        verification,
        trust_level: trust_types::TrustLevel::ProofGrade,
        ..Default::default()
    };
    let report = build_decompile_report(
        Path::new("fixtures/tiny.bin"),
        Some(0x401000),
        false,
        true,
        DecompileTarget::TrustIr,
        Ok(artifact),
    );

    assert_eq!(report.binary_evidence.unsupported_ledger.aarch64_sync_boundary_fact_count, 1);
    assert!(!report.binary_evidence.release_gate.accepted);
    assert!(
        report.binary_evidence.release_gate.blockers.iter().any(|blocker| {
            blocker.code == "aarch64-sync-boundary-not-proof-consumed"
                && blocker.feature == "aarch64-sync-boundary-proof-consumption"
                && blocker
                    .evidence_required
                    .contains(&"aarch64_sync_boundary_proof_consumer".to_string())
                && blocker.evidence_required.contains(&"happens-before witness".to_string())
        }),
        "{:?}",
        report.binary_evidence.release_gate.blockers
    );

    let json = serialize_decompile_json_with_checked_certificate_loader(
        &report,
        super::convert_checked_certificate_loader_not_requested(),
    )
    .expect("serialize decompile JSON");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse decompile JSON");
    let fact = &value["binary_evidence"]["unsupported_ledger"]["aarch64_sync_boundary_facts"][0];
    assert_eq!(fact["opcode"], "DMB");
    assert_eq!(fact["operand"], "ish");
    assert_eq!(fact["kind"], "DataMemoryBarrier");
    assert_eq!(fact["scope"], "InnerShareable");
    assert_eq!(fact["ordering"], "LoadsAndStores");
    assert_eq!(fact["raw_option"], 0xb);
    assert_eq!(fact["consumed_by_proof_model"], false);
    assert!(
        fact["missing_witnesses"]
            .as_array()
            .expect("missing witnesses")
            .iter()
            .any(|witness| witness.as_str() == Some("happens-before witness"))
    );
    assert!(
        value["binary_evidence"]["release_gate"]["blockers"]
            .as_array()
            .expect("release blockers")
            .iter()
            .any(|blocker| {
                blocker["code"] == "aarch64-sync-boundary-not-proof-consumed"
                    && blocker["evidence_required"]
                        .as_array()
                        .expect("evidence required")
                        .iter()
                        .any(|item| item.as_str() == Some("shareability scope propagation"))
            }),
        "{value}"
    );
}

#[test]
fn test_convert_rejected_gate_is_process_failure_even_when_decompile_report_is_partial() {
    let report = DecompileReport {
        binary: "demo.bin".into(),
        format: Some("ELF".into()),
        architecture: Some("x86_64".into()),
        selection: "address".into(),
        entry: Some("0x401000".into()),
        binary_entry: Some("0x401000".into()),
        source_provenance: BinarySourceProvenanceSummary::default(),
        strict: false,
        target: DecompileTarget::TrustCg,
        status: BinaryLiftStatus::Ok,
        output_kind: Some("trust_cg_text".into()),
        output_trust_level: "partial".into(),
        output_validation: "validated_partial".into(),
        validation_note:
            "trust-cg text passed structural validation, but remains partial and is not proof-grade"
                .into(),
        output_content: Some("{\"functions\":[]}".into()),
        production_proof_grade_evidence: None,
        binary_evidence: DecompileBinaryEvidenceReport::default(),
        target_validation_blockers: Vec::new(),
        preserved_symbolic_formulas: Vec::new(),
        functions_decompiled: 1,
        blocks: 1,
        instructions: 1,
        statements: 1,
        memory_facts: 0,
        unsupported: 0,
        failures: 0,
        functions: Vec::new(),
        unsupported_items: Vec::new(),
        failure_items: Vec::new(),
    };

    assert!(!decompile_should_fail(&report));
    assert!(convert_should_fail(&report));
}

#[test]
fn test_convert_proof_grade_label_rejects_invalid_binary_source_provenance_handoff() {
    let cases = vec![
        (
            "missing mappings",
            BinarySourceProvenanceSummary {
                status: "exact".into(),
                exact_mapping_count: 0,
                ambiguous_mapping_count: 0,
                diagnostics: Vec::new(),
                source_backpropagation_allowed: true,
            },
            "no accepted address mappings",
        ),
        (
            "missing provenance file",
            BinarySourceProvenanceSummary {
                status: "unavailable".into(),
                exact_mapping_count: 0,
                ambiguous_mapping_count: 0,
                diagnostics: vec![
                    "runtime binary-source provenance artifact missing file: fixtures/missing-provenance.json"
                        .into(),
                ],
                source_backpropagation_allowed: true,
            },
            "missing-provenance.json",
        ),
        (
            "duplicate mappings",
            BinarySourceProvenanceSummary {
                status: "exact".into(),
                exact_mapping_count: 1,
                ambiguous_mapping_count: 1,
                diagnostics: vec![
                    "binary source provenance artifact has ambiguous duplicate mapping(s) for 0x401000"
                        .into(),
                ],
                source_backpropagation_allowed: true,
            },
            "ambiguous duplicate mapping",
        ),
        (
            "wrong artifact kind",
            BinarySourceProvenanceSummary {
                status: "checked_certificate".into(),
                exact_mapping_count: 0,
                ambiguous_mapping_count: 0,
                diagnostics: vec![
                    "wrong artifact kind: checked certificate is not a binary-source provenance mapping artifact"
                        .into(),
                ],
                source_backpropagation_allowed: false,
            },
            "wrong artifact kind",
        ),
        (
            "producer bit cannot override wrong artifact kind",
            BinarySourceProvenanceSummary {
                status: "unsupported".into(),
                exact_mapping_count: 0,
                ambiguous_mapping_count: 0,
                diagnostics: vec![
                    "runtime binary-source provenance artifact kind `checked_binary_certificate` is not `binary_source_provenance`"
                        .into(),
                ],
                source_backpropagation_allowed: true,
            },
            "checked_binary_certificate",
        ),
        (
            "exact-span mismatch",
            BinarySourceProvenanceSummary {
                status: "exact".into(),
                exact_mapping_count: 1,
                ambiguous_mapping_count: 0,
                diagnostics: vec![
                    "exact-span mismatch for binary:0x401000: artifact span src/lib.rs:1:1-1:4 does not match report span src/main.rs:1:1-1:4"
                        .into(),
                ],
                source_backpropagation_allowed: false,
            },
            "exact-span mismatch",
        ),
    ];

    for (case, source_provenance, expected) in cases {
        let report = proof_grade_convert_report_with_source_provenance(source_provenance);

        let gate = build_convert_cli_gate(&report);
        assert!(!gate.accepted, "{case}: {gate:?}");
        assert_eq!(gate.status, "rejected", "{case}");
        assert!(gate.proof_grade_artifact, "{case}");
        assert!(convert_should_fail(&report), "{case}");
        assert!(
            gate.blockers.iter().any(|blocker| {
                blocker.contains("exact-source-provenance") && blocker.contains(expected)
            }),
            "{case}: missing `{expected}` in {:?}",
            gate.blockers
        );
        assert!(
            gate.validation_blockers.iter().any(|blocker| {
                blocker.contains("exact-source-provenance") && blocker.contains(expected)
            }),
            "{case}: missing `{expected}` in {:?}",
            gate.validation_blockers
        );

        let rendered = render_convert_terminal(&report);
        assert!(rendered.contains("source_backpropagation=rejected"), "{case}");
        assert!(rendered.contains("conversion gate: rejected\n"), "{case}");
        assert!(rendered.contains("exact-source-provenance"), "{case}");
        assert!(rendered.contains(expected), "{case}");

        let json = serialize_convert_json(&report).expect("serialize convert JSON");
        let value: serde_json::Value = serde_json::from_str(&json).expect("parse convert JSON");
        assert_eq!(value["conversion_gate"]["accepted"], false, "{case}");
        assert_eq!(value["conversion_gate"]["proof_grade_artifact"], true, "{case}");
        assert!(
            value["conversion_gate"]["blockers"]
                .as_array()
                .expect("conversion blockers")
                .iter()
                .any(|blocker| {
                    let blocker = blocker.as_str().expect("blocker");
                    blocker.contains("exact-source-provenance") && blocker.contains(expected)
                }),
            "{case}: missing `{expected}` in {value}"
        );
    }
}

#[test]
fn test_convert_rejects_proof_grade_label_without_translation_validation() {
    let report = DecompileReport {
        binary: "demo.bin".into(),
        format: Some("ELF".into()),
        architecture: Some("x86_64".into()),
        selection: "address".into(),
        entry: Some("0x401000".into()),
        binary_entry: Some("0x401000".into()),
        source_provenance: exact_binary_source_provenance_summary(),
        strict: true,
        target: DecompileTarget::TrustCg,
        status: BinaryLiftStatus::Ok,
        output_kind: Some("trust_cg_text".into()),
        output_trust_level: "proof_grade".into(),
        output_validation: "inspectable_rejected".into(),
        validation_note:
            "trust-cg structural validation succeeded, but target validation remains rejected"
                .into(),
        output_content: Some("{\"functions\":[]}".into()),
        production_proof_grade_evidence: None,
        binary_evidence: DecompileBinaryEvidenceReport::default(),
        target_validation_blockers: vec![trust_cg_refinement_blocker()],
        preserved_symbolic_formulas: Vec::new(),
        functions_decompiled: 1,
        blocks: 1,
        instructions: 1,
        statements: 1,
        memory_facts: 0,
        unsupported: 0,
        failures: 0,
        functions: Vec::new(),
        unsupported_items: Vec::new(),
        failure_items: Vec::new(),
    };

    assert!(!decompile_should_fail(&report));
    assert!(convert_should_fail(&report));

    let gate = build_convert_cli_gate(&report);
    assert!(!gate.accepted);
    assert_eq!(gate.status, "rejected");
    assert!(gate.proof_grade_artifact);
    assert_eq!(gate.validation, "inspectable_rejected");
    assert_eq!(gate.validation_blockers.len(), 3);
    assert!(gate.validation_blockers[0].contains("translation validation has not accepted"));
    assert!(
        gate.validation_blockers
            .iter()
            .any(|blocker| { blocker.contains("missing-checked-certificate-production-evidence") })
    );
    assert!(
        gate.validation_blockers
            .iter()
            .any(|blocker| blocker.contains("missing-refinement-metadata"))
    );
    assert!(gate.reason.contains("output validation is `inspectable_rejected`"));
    assert!(gate.reason.contains("missing-refinement-metadata"));

    let rendered = render_convert_terminal(&report);
    assert!(rendered.contains("conversion gate: rejected\n"));
    assert!(rendered.contains(
        "conversion gate detail: target=trust-cg proof_grade_artifact=true validation=inspectable_rejected"
    ));
    assert!(rendered.contains("conversion validation blockers:\n"));
    assert!(rendered.contains("translation validation has not accepted this artifact"));
    assert!(rendered.contains("missing-refinement-metadata"));
    assert!(!rendered.contains("conversion gate: accepted"));

    let json = serialize_convert_json(&report).expect("serialize convert JSON");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse convert JSON");
    assert_eq!(value["conversion_gate"]["accepted"], false);
    assert_eq!(value["conversion_gate"]["status"], "rejected");
    assert_eq!(value["conversion_gate"]["proof_grade_artifact"], true);
    assert_eq!(value["conversion_gate"]["validation"], "inspectable_rejected");
    assert!(
        value["target_validation_blockers"]
            .as_array()
            .expect("target validation blockers")
            .iter()
            .any(|blocker| blocker["feature"] == "missing-refinement-metadata")
    );
    assert!(
        value["conversion_gate"]["validation_blockers"]
            .as_array()
            .expect("validation blockers")
            .iter()
            .any(|blocker| blocker
                .as_str()
                .unwrap()
                .contains("translation validation has not accepted"))
    );
    assert!(
        value["conversion_gate"]["validation_blockers"]
            .as_array()
            .expect("validation blockers")
            .iter()
            .any(|blocker| blocker
                .as_str()
                .unwrap()
                .contains("missing-checked-certificate-production-evidence"))
    );
}

#[test]
fn test_convert_json_gate_rejects_binary_derived_trust_cg_without_target_semantics_or_checked_cert()
{
    let report =
        proof_grade_convert_report_with_source_provenance(exact_binary_source_provenance_summary());

    let gate = build_convert_cli_gate(&report);
    assert!(gate.proof_grade_artifact);
    assert!(!gate.accepted);
    assert_eq!(gate.status, "rejected");
    assert!(convert_should_fail(&report));
    for required_blocker in
        ["missing-target-semantic-validation", "missing-checked-proof-certificate"]
    {
        assert!(
            gate.validation_blockers.iter().any(|blocker| blocker.contains(required_blocker)),
            "missing {required_blocker} in {:?}",
            gate.validation_blockers
        );
        assert!(
            gate.reason.contains(required_blocker),
            "missing {required_blocker} in {}",
            gate.reason
        );
    }

    let json = serialize_convert_json(&report).expect("serialize convert JSON");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse convert JSON");
    assert_eq!(value["conversion_gate"]["accepted"], false);
    assert_eq!(value["conversion_gate"]["status"], "rejected");
    assert_ne!(value["conversion_gate"]["reason"], "conversion artifact accepted");
    assert_eq!(value["conversion_gate"]["checked_certificate_evidence"]["required"], true);
    assert_eq!(
        value["conversion_gate"]["checked_certificate_evidence"]["raw_solver_proof_bytes_sufficient"],
        false
    );
    assert!(
        value["conversion_gate"]["checked_certificate_evidence"]["blockers"]
            .as_array()
            .expect("checked certificate evidence blockers")
            .iter()
            .any(|blocker| blocker["code"] == "normalized-solver-proof-export-missing")
    );
    let blockers = value["conversion_gate"]["blockers"].as_array().expect("conversion blockers");
    for required_blocker in
        ["missing-target-semantic-validation", "missing-checked-proof-certificate"]
    {
        assert!(
            blockers.iter().any(|blocker| blocker.as_str().unwrap().contains(required_blocker)),
            "missing {required_blocker} in {value}"
        );
    }
}

#[test]
fn test_convert_json_surfaces_checked_certificate_readback_rows() {
    let (dispatch, canonical_vc_bytes) = importable_binary_dispatch("convert-producer:vc0");
    let artifact = checked_binary_artifact_for_dispatch(&dispatch, &canonical_vc_bytes);
    let root = temp_test_dir("convert-checked-cert-loader");
    let path = persist_checked_certificate_artifact(&root, &artifact)
        .expect("checked artifact should persist");
    let loader = load_convert_checked_certificate_loader_report(&[path.display().to_string()], &[])
        .expect("convert checked-certificate metadata loader should parse artifact rows");
    let mut report =
        proof_grade_convert_report_with_source_provenance(exact_binary_source_provenance_summary());
    report.output_content = Some(r#"{"functions":[{"name":"entry"}],"typed":true}"#.into());

    let json = serialize_convert_json_with_checked_certificate_loader(&report, loader.clone())
        .expect("serialize convert JSON with checked certificate rows");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse convert JSON");

    assert_eq!(value["trust_cg_output"]["functions"][0]["name"], "entry");
    assert_eq!(value["trust_cg_output"]["typed"], true);
    assert_eq!(value["conversion_gate"]["accepted"], false);
    let evidence = &value["conversion_gate"]["checked_certificate_evidence"];
    assert_eq!(&value["checked_certificate_readback"], evidence);
    assert_eq!(evidence["status"], "blocked");
    assert_eq!(evidence["proof_grade_release_accepted"], false);
    assert_eq!(evidence["loader"]["status"], "loaded");
    assert_eq!(evidence["checked_artifact_rows"], 1);
    assert_eq!(evidence["accepted_certificate_rows"], 1);
    assert_eq!(evidence["imported_artifact_rows"], 0);
    assert_eq!(evidence["unmatched_artifact_rows"], 0);
    assert_eq!(evidence["normalized_solver_proof_exports"], 1);
    assert_eq!(evidence["proof_export_readback_rows"], 1);
    assert_eq!(evidence["checked_certificate_readback_rows"], 1);
    assert_eq!(evidence["checker_successes"], 1);
    assert_eq!(evidence["checked_certificates"], 1);
    assert_eq!(evidence["production_checker_evidence_rows"], 0);
    assert_eq!(evidence["production_checked_certificates"], 0);
    assert_eq!(evidence["missing_production_checked_certificates"], 1);
    assert_eq!(evidence["raw_solver_proof_bytes_sufficient"], false);
    assert_eq!(evidence["accepted_certificates"].as_array().unwrap().len(), 1);
    assert_eq!(evidence["accepted_certificates"][0]["source"], "checked_certificate_readback");
    assert_eq!(evidence["artifacts"][0]["status"], "readback");
    assert_eq!(evidence["artifacts"][0]["certificate_sha256"], artifact.certificate_sha256);
    assert_eq!(
        evidence["artifacts"][0]["source_backpropagation_gate"]["source_backpropagation_allowed"],
        false
    );
    assert_eq!(evidence["readback_records"][0]["production_checked"], false);
    assert_eq!(evidence["readback_records"][0]["production_checker_evidence_status"], "missing");
    assert_eq!(evidence["readback_records"][0]["proof_sha256"], artifact.proof_sha256);
    assert_eq!(
        evidence["readback_records"][0]["proof_export_sha256"],
        artifact.proof_export_sha256
    );
    assert_eq!(evidence["readback_records"][0]["certificate_sha256"], artifact.certificate_sha256);
    assert_eq!(
        evidence["readback_records"][0]["source_backpropagation_gate"]["source_backpropagation_allowed"],
        false
    );
    assert!(
        evidence["readback_records"][0]["source_backpropagation_gate"]["blockers"]
            .as_array()
            .expect("readback source-backprop blockers")
            .iter()
            .any(|blocker| blocker == "source_backpropagation_gate_not_evaluated")
    );
    assert_eq!(
        evidence["accepted_certificates"][0]["source_backpropagation_gate"]["source_backpropagation_allowed"],
        false
    );
    assert_eq!(
        value["conversion_gate"]["source_backpropagation_gate"]["accepted"], false,
        "checked certificate readback must remain separate from source rewrite permission"
    );
    assert_eq!(evidence["readback_row_details"][0]["readback_status"], "accepted");
    assert_eq!(evidence["readback_row_details"][0]["proof_grade_release_status"], "rejected");
    assert!(
        evidence["readback_row_details"][0]["blockers"]
            .as_array()
            .expect("readback row blockers")
            .iter()
            .any(|blocker| blocker
                .as_str()
                .expect("row blocker")
                .contains("missing-target-semantic-validation"))
    );
    assert!(
        evidence["proof_grade_release_blockers"]
            .as_array()
            .expect("release blockers")
            .iter()
            .any(|blocker| blocker["code"] == "target-semantic-validation-missing")
    );
    assert!(
        evidence["blockers"]
            .as_array()
            .expect("checked certificate blockers")
            .iter()
            .any(|blocker| blocker["code"] == "target-semantic-validation-missing")
    );
    assert!(
        evidence["blockers"]
            .as_array()
            .expect("checked certificate blockers")
            .iter()
            .any(|blocker| blocker["code"] == "checked-certificate-production-evidence-missing")
    );
    assert!(
        value["conversion_gate"]["blockers"].as_array().expect("conversion blockers").iter().any(
            |blocker| blocker
                .as_str()
                .expect("blocker")
                .contains("missing-target-semantic-validation")
        )
    );
    let terminal = render_convert_terminal_with_checked_certificate_loader(&report, loader.clone());
    assert!(terminal.contains("conversion gate: rejected\n"));
    assert!(terminal.contains("proof_grade_release_accepted=false"));
    assert!(terminal.contains("target-semantic-validation-missing"));
    assert!(!terminal.contains("conversion checked-certificate evidence: status=accepted"));

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_convert_decompile_json_binds_release_transcript_digests_for_readback_rows() {
    let (dispatch, canonical_vc_bytes) = importable_binary_dispatch("release-binding:vc0");
    let artifact = checked_binary_artifact_for_dispatch(&dispatch, &canonical_vc_bytes);
    let root = temp_test_dir("convert-release-transcript-binding");
    let path = persist_checked_certificate_artifact(&root, &artifact)
        .expect("checked artifact should persist");
    let loader = load_convert_checked_certificate_loader_report(&[path.display().to_string()], &[])
        .expect("convert checked-certificate metadata loader should parse artifact rows");
    let mut report =
        proof_grade_convert_report_with_source_provenance(exact_binary_source_provenance_summary());
    report.output_content = Some(accepted_trust_cg_target_proof_consumer_output(&dispatch.id));

    for (gate_key, json) in [
        (
            "conversion_gate",
            serialize_convert_json_with_checked_certificate_loader(&report, loader.clone())
                .expect("serialize convert JSON"),
        ),
        (
            "artifact_gate",
            serialize_decompile_json_with_checked_certificate_loader(&report, loader.clone())
                .expect("serialize decompile JSON"),
        ),
    ] {
        let value: serde_json::Value = serde_json::from_str(&json).expect("parse JSON");
        let evidence = &value["checked_certificate_readback"];
        let binding = &evidence["readback_records"][0]["release_transcript_binding"];
        assert_eq!(binding["schema_version"], "targo-trust-release-transcript-binding.v1");
        assert_eq!(
            binding["binary_sha256"],
            "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
        );
        assert_eq!(
            binding["selected_image_sha256"],
            "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
        );
        assert_eq!(binding["selected_image_file_offset"], 0);
        assert_eq!(binding["selected_image_file_size"], 64);
        assert_eq!(binding["vc_sha256"], artifact.vc_sha256);
        assert_eq!(binding["checked_certificate_sha256"], artifact.certificate_sha256);
        assert_eq!(binding["provenance_sha256"], artifact.origin_sha256);
        assert_json_canonical_sha256(&binding["commit_sha256"], "release transcript commit");
        assert_json_canonical_sha256(
            &binding["target_consumer_evidence_sha256"],
            "target consumer evidence digest",
        );
        assert_json_canonical_sha256(
            &binding["target_consumer_binding_sha256"],
            "target consumer binding digest",
        );
        assert_eq!(binding["status"], "rejected");
        assert!(
            binding["blockers"]
                .as_array()
                .expect("binding blockers")
                .iter()
                .any(|blocker| { blocker.as_str() == Some("replay transcript digest is missing") }),
            "{binding}"
        );
        assert_eq!(&evidence["accepted_certificates"][0]["release_transcript_binding"], binding);
        assert!(
            evidence["proof_grade_release_blockers"]
                .as_array()
                .expect("release blockers")
                .iter()
                .any(|blocker| blocker["code"] == "release-transcript-binding-missing"),
            "{evidence}"
        );
        assert!(
            value[gate_key]["checked_certificate_evidence"]["readback_row_details"][0]["blockers"]
                .as_array()
                .expect("row blockers")
                .iter()
                .any(|blocker| blocker
                    .as_str()
                    .expect("row blocker")
                    .contains("replay transcript digest is missing")),
            "{value}"
        );
    }

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_convert_gate_rejects_checked_readback_without_production_checker_evidence() {
    let (dispatch, canonical_vc_bytes) =
        importable_binary_dispatch("convert-production-evidence:vc0");
    let artifact = checked_binary_artifact_for_dispatch(&dispatch, &canonical_vc_bytes);
    let root = temp_test_dir("convert-production-evidence");
    let path = persist_checked_certificate_artifact(&root, &artifact)
        .expect("checked artifact should persist");
    let loader = load_convert_checked_certificate_loader_report(&[path.display().to_string()], &[])
        .expect("checked certificate readback should parse");
    let mut report =
        proof_grade_convert_report_with_source_provenance(exact_binary_source_provenance_summary());
    report.target = DecompileTarget::TrustIr;
    report.output_kind = Some("trust_ir_json".into());
    report.output_content = Some("{\"functions\":[]}".into());

    let gate = build_convert_cli_gate_with_loader(&report, loader.clone());
    assert!(!gate.accepted);
    assert_eq!(gate.status, "rejected");
    assert!(gate.checked_certificate_evidence.required);
    assert_eq!(gate.checked_certificate_evidence.checked_certificates, 1);
    assert_eq!(gate.checked_certificate_evidence.production_checked_certificates, 0);
    assert!(
        gate.blockers
            .iter()
            .any(|blocker| blocker.contains("missing-checked-certificate-production-evidence")),
        "{:?}",
        gate.blockers
    );
    assert!(
        gate.checked_certificate_evidence
            .blockers
            .iter()
            .any(|blocker| { blocker.code == "checked-certificate-production-evidence-missing" }),
        "{:?}",
        gate.checked_certificate_evidence.blockers
    );

    let json = serialize_convert_json_with_checked_certificate_loader(&report, loader)
        .expect("serialize convert JSON");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse convert JSON");
    assert_eq!(value["conversion_gate"]["accepted"], false);
    assert_eq!(value["conversion_gate"]["checked_certificate_evidence"]["status"], "blocked");
    assert_eq!(
        value["conversion_gate"]["checked_certificate_evidence"]["production_checked_certificates"],
        0
    );
    assert_eq!(
        value["conversion_gate"]["checked_certificate_evidence"]["readback_records"][0]["production_checker_evidence_status"],
        "missing"
    );

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn test_convert_loader_rejects_exit_zero_checker_without_concrete_proof_inputs() {
    let (dispatch, canonical_vc_bytes) = importable_binary_dispatch("convert-external-checker:vc0");
    let artifact = checked_binary_artifact_for_dispatch(&dispatch, &canonical_vc_bytes);
    let root = temp_test_dir("convert-external-checker");
    let path = persist_checked_certificate_artifact(&root, &artifact)
        .expect("checked artifact should persist");
    let checker = write_checker_fixture_script(&root, "checker-fixture.sh", "#!/bin/sh\nexit 0\n");

    let error = load_convert_checked_certificate_loader_report_with_external_checker(
        &[path.display().to_string()],
        &[],
        Some(checker.as_path()),
        1_777_070_402_000,
    )
    .expect_err("an import-only exit-zero checker must not mint production evidence");
    let detail = error.to_string();
    assert!(detail.contains("no authenticated solver-proof metadata/payload inputs"), "{detail}");
    assert!(detail.contains("--checked-cert-export-dir"), "{detail}");

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_convert_loader_external_checker_without_artifacts_fails_closed() {
    let error = load_convert_checked_certificate_loader_report_with_external_checker(
        &[],
        &[],
        Some(Path::new("bin/check-cert")),
        1_777_070_402_000,
    )
    .expect_err("checker-only import request must be rejected");
    assert!(error.to_string().contains("cannot be attached to already-loaded certificate rows"));
}

#[cfg(unix)]
#[test]
fn test_convert_checked_certificate_export_produces_artifact_for_later_readback() {
    let root = temp_test_dir("convert-production-export");
    let proof_bytes = b"normalized checked proof payload";

    let (mut dispatch, _) = importable_binary_dispatch("convert-production-export:vc0");
    dispatch.certificate = ProofCertificateStatus::Present {
        format: "lrat".to_string(),
        sha256: Some(trust_types::digest::stable_sha256_hex(proof_bytes)),
        artifact_path: Some(root.join("placeholder.lrat").display().to_string()),
    };
    let mut decompile_artifact = trust_types::DecompilationArtifact {
        verification: trust_types::BinaryVerificationSummary {
            total_vcs: 1,
            proved: 1,
            solver_dispatch: vec![dispatch],
            ..Default::default()
        },
        reconstruction: trust_types::ReconstructionSummary {
            target: trust_types::DecompileTarget::TrustCg,
            validation: trust_types::ReconstructionValidationStatus::Validated,
            trust_level: trust_types::TrustLevel::ProofGrade,
            outputs: vec![trust_types::DecompiledOutput {
                target: trust_types::DecompileTarget::TrustCg,
                validation: trust_types::ReconstructionValidationStatus::Validated,
                trust_level: trust_types::TrustLevel::ProofGrade,
                preserved_symbolic_formulas: vec![trust_cg_preserved_symbolic_formula()],
                ..Default::default()
            }],
            ..Default::default()
        },
        source_provenance: exact_binary_source_provenance_summary(),
        ..Default::default()
    };
    attach_decompile_normalized_proof_export_artifact(
        &root,
        &mut decompile_artifact,
        proof_bytes,
        None,
    );
    let checker = write_checker_fixture_script(
        &root,
        "production-checker.sh",
        "#!/bin/sh\nprintf 'production ok'\n",
    );
    let export_dir = root.join("checked-certs");

    let produced = produce_convert_checked_certificate_artifacts_for_decompilation(
        &decompile_artifact,
        &export_dir,
        Some(checker.as_path()),
        1_777_070_403_000,
    );

    assert_eq!(produced.report.status, "exported", "{:#?}", produced.report);
    assert_eq!(produced.report.exported_artifacts, 1);
    assert_eq!(produced.report.rejected_dispatches, 0);
    assert_eq!(produced.report.proof_export_candidates, 1);
    assert!(!produced.report.source_backpropagation_gate.source_backpropagation_allowed);
    assert_eq!(produced.report.source_backpropagation_gate.preserved_symbolic_formulas, 1);
    assert!(!produced.report.source_backpropagation_gate.symbolic_formula_consumer_accepted);
    assert!(
        produced
            .report
            .source_backpropagation_gate
            .blockers
            .iter()
            .any(|blocker| blocker == "trust_symbolic_formula_entries_unconsumed")
    );
    assert_eq!(produced.artifact_paths.len(), 1);
    assert!(Path::new(&produced.artifact_paths[0]).exists());
    let manifest_path =
        produced.report.manifest_path.clone().expect("manifest path should be exported");
    assert!(Path::new(&manifest_path).exists());
    assert!(checked_certificate_audit_export_bundle_path(&export_dir).exists());

    let loader = load_convert_checked_certificate_loader_report_with_production_export(
        &[],
        std::slice::from_ref(&manifest_path),
        None,
        1_777_070_403_001,
        Some(produced.report.clone()),
    )
    .expect("produced checked certificate should read back");

    assert_eq!(loader.status, "loaded");
    assert_eq!(loader.requested_artifacts, 0);
    assert_eq!(loader.requested_manifests, 1);
    assert_eq!(loader.loaded_artifacts, 1);
    assert_eq!(loader.readback_records.len(), 1);
    assert_eq!(loader.readback_records[0].status, "readback");
    assert!(loader.readback_records[0].production_checked);
    assert!(loader.readback_records[0].manifest_identity_sha256.is_some());
    assert_eq!(
        loader.readback_records[0].source_backpropagation_gate_sha256,
        produced.report.source_backpropagation_gate_sha256
    );
    assert!(loader.readback_records[0].production_checker_evidence_sha256.is_some());
    assert_eq!(loader.readback_records[0].replay_digest_identity.status, "rejected");
    assert!(!loader.readback_records[0].source_backpropagation_gate.source_backpropagation_allowed);
    assert_eq!(
        loader.production_export.as_ref().expect("production export").artifact_paths,
        produced.artifact_paths
    );
    assert_eq!(
        loader.production_export.as_ref().expect("production export").manifest_path.as_deref(),
        Some(manifest_path.as_str())
    );

    let report =
        proof_grade_convert_report_with_source_provenance(exact_binary_source_provenance_summary());
    for (gate_key, json) in [
        (
            "conversion_gate",
            serialize_convert_json_with_checked_certificate_loader(&report, loader.clone())
                .expect("serialize convert JSON with production manifest readback"),
        ),
        (
            "artifact_gate",
            serialize_decompile_json_with_checked_certificate_loader(&report, loader.clone())
                .expect("serialize decompile JSON with production manifest readback"),
        ),
    ] {
        let value: serde_json::Value =
            serde_json::from_str(&json).expect("parse production readback JSON");
        assert_eq!(value[gate_key]["accepted"], false);
        assert_eq!(value["checked_certificate_readback"]["loader"]["requested_manifests"], 1);
        assert_eq!(
            value["checked_certificate_readback"]["loader"]["production_export"]["manifest_path"],
            manifest_path
        );
        let record = &value["checked_certificate_readback"]["readback_records"][0];
        assert_json_canonical_sha256(
            &record["manifest_identity_sha256"],
            "convert readback manifest identity",
        );
        assert_json_canonical_sha256(
            &record["source_backpropagation_gate_sha256"],
            "convert readback source-backpropagation gate identity",
        );
        assert_json_canonical_sha256(
            &record["production_checker_evidence_sha256"],
            "convert readback checker evidence identity",
        );
        assert_eq!(record["production_checker_evidence_status"], "present");
        assert_eq!(record["production_checked"], true);
        assert_eq!(record["replay_digest_identity"]["status"], "rejected");
        assert!(
            value["checked_certificate_readback"]["proof_grade_release_blockers"]
                .as_array()
                .expect("release blockers")
                .iter()
                .any(|blocker| blocker["code"] == "replay-digest-identity-missing"),
            "{value}"
        );
    }

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_convert_checked_certificate_export_without_checker_fails_closed() {
    let root = temp_test_dir("convert-production-export-no-checker");
    std::fs::create_dir_all(&root).expect("temp root should be created");
    let proof_path = root.join("vc0.lrat");
    let proof_bytes = b"normalized checked proof payload";
    std::fs::write(&proof_path, proof_bytes).expect("proof export should be written");

    let (mut dispatch, _) = importable_binary_dispatch("convert-production-no-checker:vc0");
    dispatch.certificate = ProofCertificateStatus::Present {
        format: "lrat".to_string(),
        sha256: Some(trust_types::digest::stable_sha256_hex(proof_bytes)),
        artifact_path: Some(proof_path.display().to_string()),
    };
    let decompile_artifact = trust_types::DecompilationArtifact {
        verification: trust_types::BinaryVerificationSummary {
            total_vcs: 1,
            proved: 1,
            solver_dispatch: vec![dispatch],
            ..Default::default()
        },
        ..Default::default()
    };

    let produced = produce_convert_checked_certificate_artifacts_for_decompilation(
        &decompile_artifact,
        &root.join("checked-certs"),
        None,
        1_777_070_403_000,
    );

    assert_eq!(produced.report.status, "blocked");
    assert_eq!(produced.report.exported_artifacts, 0);
    assert_eq!(produced.report.rejected_dispatches, 1);
    assert!(produced.artifact_paths.is_empty());
    assert!(
        produced.report.blockers.iter().any(|blocker| blocker.code == "checker-selection-missing")
    );

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_convert_json_surfaces_trust_cg_target_proof_consumer_evidence() {
    let (dispatch, canonical_vc_bytes) = importable_binary_dispatch("convert-target-consumer:vc0");
    let artifact = checked_binary_artifact_for_dispatch(&dispatch, &canonical_vc_bytes);
    let root = temp_test_dir("convert-target-proof-consumer");
    let path = persist_checked_certificate_artifact(&root, &artifact)
        .expect("checked artifact should persist");
    let loader = load_convert_checked_certificate_loader_report(&[path.display().to_string()], &[])
        .expect("convert checked-certificate metadata loader should parse artifact rows");
    let mut report =
        proof_grade_convert_report_with_source_provenance(exact_binary_source_provenance_summary());
    report.preserved_symbolic_formulas = vec![trust_cg_preserved_symbolic_formula()];

    let json = serialize_convert_json_with_checked_certificate_loader(&report, loader)
        .expect("serialize convert JSON with target proof-consumer evidence");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse convert JSON");
    let evidence = &value["target_proof_consumer_evidence"];

    assert_eq!(evidence["target"], "trust-cg");
    assert_eq!(evidence["status"], "rejected");
    assert_eq!(evidence["target_semantics_consumed"], false);
    assert_eq!(&value["conversion_gate"]["target_proof_consumer_evidence"], evidence);
    for required_kind in
        ["target_semantics", "symbolic_formula", "checked_certificate", "proof_replay"]
    {
        assert!(
            evidence["records"]
                .as_array()
                .expect("target proof-consumer records")
                .iter()
                .any(|record| record["kind"] == required_kind && record["accepted"] == false),
            "missing rejected {required_kind} in {evidence}"
        );
    }
    for required_code in [
        "target-semantics-not-consumed",
        "symbolic-formula-not-consumed-by-target-semantics",
        "checked-certificate-not-consumed-by-target-semantics",
        "proof-replay-not-consumed-by-target-semantics",
    ] {
        assert!(
            evidence["blockers"]
                .as_array()
                .expect("target proof-consumer blockers")
                .iter()
                .any(|blocker| blocker["code"] == required_code),
            "missing {required_code} in {evidence}"
        );
        assert!(
            value["conversion_gate"]["validation_blockers"]
                .as_array()
                .expect("validation blockers")
                .iter()
                .any(|blocker| blocker.as_str().expect("blocker").contains(required_code)),
            "missing {required_code} in {}",
            value["conversion_gate"]
        );
    }
    assert_eq!(value["conversion_gate"]["accepted"], false);
    assert_eq!(value["conversion_gate"]["status"], "rejected");
    let symbolic_record = evidence["records"]
        .as_array()
        .expect("target proof-consumer records")
        .iter()
        .find(|record| record["kind"] == "symbolic_formula")
        .expect("symbolic formula record");
    assert_eq!(symbolic_record["formula_schema"], "trust-types.Formula@1");
    assert_eq!(symbolic_record["formula_sort"], "Int");
    assert_json_canonical_sha256(&symbolic_record["formula_digest"], "formula digest");
    assert!(
        symbolic_record["formula_origin"]
            .as_str()
            .expect("formula origin")
            .contains("target=trust-cg;function=symbolic_blocked")
    );

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_convert_json_rejects_symbolic_formula_consumer_without_schema_identity() {
    let mut report =
        proof_grade_convert_report_with_source_provenance(exact_binary_source_provenance_summary());
    let formula = trust_cg_preserved_symbolic_formula();
    let formula_evidence = formula.evidence();
    let formula_id = super::target_proof_consumer_formula_identifier(&formula);
    let target_output = "trust_cg-lir:function:symbolic_blocked:return:i32";
    let provenance_id = "binary_provenance:symbolic_blocked@0x401000";
    report.preserved_symbolic_formulas = vec![formula];
    report.output_content = Some(
        serde_json::json!({
            "functions": [{"name": "symbolic_blocked"}],
            "target_proof_consumer_evidence": {
                "target": "trust-cg",
                "status": "accepted",
                "target_semantics_consumed": true,
                "records": [
                    {
                        "kind": "target_semantics",
                        "identifier": "trust_cg-lir",
                        "accepted": true,
                        "detail": "trust-cg target semantics consumed conversion proof inputs"
                    },
                    {
                        "kind": "symbolic_formula",
                        "identifier": formula_id,
                        "accepted": true,
                        "detail": "generic formula consumer marker without schema identity"
                    },
                    {
                        "kind": "binary_provenance",
                        "identifier": provenance_id,
                        "accepted": true,
                        "detail": "binary provenance consumed"
                    },
                    {
                        "kind": "checked_certificate",
                        "identifier": "vc0",
                        "accepted": true,
                        "detail": "checked certificate consumed"
                    },
                    {
                        "kind": "proof_replay",
                        "identifier": "vc0",
                        "accepted": true,
                        "detail": "proof replay consumed"
                    }
                ],
                "binding": {
                    "target": "trust-cg",
                    "target_output": target_output,
                    "status": "accepted",
                    "target_semantics_consumed": true,
                    "inputs": [
                        {
                            "kind": "symbolic_formula",
                            "identifier": formula_id,
                            "canonical_source": "trust_symbolic.formula",
                            "target_output": target_output,
                            "consumed_by_target_semantics": true,
                            "detail": "symbolic formula is bound to emitted trust_cg output"
                        },
                        {
                            "kind": "binary_provenance",
                            "identifier": provenance_id,
                            "canonical_source": "trust_binary.provenance",
                            "target_output": target_output,
                            "consumed_by_target_semantics": true,
                            "detail": "binary provenance is bound to emitted trust_cg output"
                        },
                        {
                            "kind": "checked_certificate",
                            "identifier": "vc0",
                            "canonical_source": "trust_proof.checked_certificate",
                            "target_output": target_output,
                            "consumed_by_target_semantics": true,
                            "detail": "checked certificate is bound to emitted trust_cg output"
                        },
                        {
                            "kind": "proof_replay",
                            "identifier": "vc0",
                            "canonical_source": "trust_proof.proof_replay",
                            "target_output": target_output,
                            "consumed_by_target_semantics": true,
                            "detail": "proof replay is bound to emitted trust_cg output"
                        }
                    ],
                    "blockers": []
                },
                "blockers": []
            }
        })
        .to_string(),
    );

    let json = serialize_convert_json(&report)
        .expect("serialize convert JSON with malformed formula consumer evidence");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse convert JSON");
    let evidence = &value["target_proof_consumer_evidence"];

    assert_eq!(evidence["status"], "rejected");
    assert_eq!(evidence["target_semantics_consumed"], false);
    assert!(
        evidence["blockers"].as_array().expect("target proof-consumer blockers").iter().any(
            |blocker| {
                blocker["code"] == "symbolic-formula-schema-aware-consumer-missing"
                    && blocker["detail"]
                        .as_str()
                        .expect("schema-aware blocker detail")
                        .contains(&formula_evidence.digest)
            }
        ),
        "{evidence}"
    );
    assert_eq!(
        value["target_evidence"]["symbolic_formula_preservation"]["consumer_accepted"],
        false
    );
    assert_eq!(
        value["target_evidence"]["symbolic_formula_preservation"]["formula_evidence"][0]["schema"],
        formula_evidence.schema.as_str()
    );
    assert_eq!(
        value["target_evidence"]["symbolic_formula_preservation"]["formula_evidence"][0]["sort"],
        formula_evidence.sort.as_str()
    );
    assert_eq!(
        value["target_evidence"]["symbolic_formula_preservation"]["formula_evidence"][0]["digest"],
        formula_evidence.digest.as_str()
    );
    assert_eq!(
        value["target_evidence"]["symbolic_formula_preservation"]["formula_evidence"][0]["origin"],
        formula_evidence.origin.as_str()
    );
}

#[test]
fn test_convert_json_accepts_schema_aware_symbolic_formula_consumer_evidence() {
    let mut report =
        proof_grade_convert_report_with_source_provenance(exact_binary_source_provenance_summary());
    let formula = trust_cg_preserved_symbolic_formula();
    let formula_evidence = formula.evidence();
    let formula_id = super::target_proof_consumer_formula_identifier(&formula);
    let target_output = "trust_cg-lir:function:symbolic_blocked:return:i32";
    let provenance_id = "binary_provenance:symbolic_blocked@0x401000";
    report.preserved_symbolic_formulas = vec![formula];
    report.output_content = Some(
        serde_json::json!({
            "functions": [{"name": "symbolic_blocked"}],
            "target_proof_consumer_evidence": {
                "target": "trust-cg",
                "status": "accepted",
                "target_semantics_consumed": true,
                "records": [
                    {
                        "kind": "target_semantics",
                        "identifier": "trust_cg-lir",
                        "accepted": true,
                        "detail": "trust-cg target semantics consumed conversion proof inputs"
                    },
                    {
                        "kind": "symbolic_formula",
                        "identifier": formula_id,
                        "accepted": true,
                        "detail": "schema-aware symbolic formula consumer accepted exact payload identity",
                        "formula_schema": formula_evidence.schema,
                        "formula_sort": formula_evidence.sort,
                        "formula_digest": formula_evidence.digest,
                        "formula_origin": formula_evidence.origin
                    },
                    {
                        "kind": "binary_provenance",
                        "identifier": provenance_id,
                        "accepted": true,
                        "detail": "binary provenance consumed"
                    },
                    {
                        "kind": "checked_certificate",
                        "identifier": "vc0",
                        "accepted": true,
                        "detail": "checked certificate consumed"
                    },
                    {
                        "kind": "proof_replay",
                        "identifier": "vc0",
                        "accepted": true,
                        "detail": "proof replay consumed"
                    }
                ],
                "binding": {
                    "target": "trust-cg",
                    "target_output": target_output,
                    "status": "accepted",
                    "target_semantics_consumed": true,
                    "inputs": [
                        {
                            "kind": "symbolic_formula",
                            "identifier": formula_id,
                            "canonical_source": "trust_symbolic.formula",
                            "target_output": target_output,
                            "consumed_by_target_semantics": true,
                            "detail": "symbolic formula is bound to emitted trust_cg output"
                        },
                        {
                            "kind": "binary_provenance",
                            "identifier": provenance_id,
                            "canonical_source": "trust_binary.provenance",
                            "target_output": target_output,
                            "consumed_by_target_semantics": true,
                            "detail": "binary provenance is bound to emitted trust_cg output"
                        },
                        {
                            "kind": "checked_certificate",
                            "identifier": "vc0",
                            "canonical_source": "trust_proof.checked_certificate",
                            "target_output": target_output,
                            "consumed_by_target_semantics": true,
                            "detail": "checked certificate is bound to emitted trust_cg output"
                        },
                        {
                            "kind": "proof_replay",
                            "identifier": "vc0",
                            "canonical_source": "trust_proof.proof_replay",
                            "target_output": target_output,
                            "consumed_by_target_semantics": true,
                            "detail": "proof replay is bound to emitted trust_cg output"
                        }
                    ],
                    "blockers": []
                },
                "blockers": []
            }
        })
        .to_string(),
    );

    let json = serialize_convert_json(&report)
        .expect("serialize convert JSON with schema-aware formula consumer evidence");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse convert JSON");
    let evidence = &value["target_proof_consumer_evidence"];

    assert_eq!(evidence["status"], "accepted");
    assert_eq!(evidence["target_semantics_consumed"], true);
    assert_eq!(evidence["records"][1]["formula_schema"], "trust-types.Formula@1");
    assert_eq!(
        value["target_evidence"]["symbolic_formula_preservation"]["consumer_accepted"],
        true
    );
    assert!(
        !evidence["blockers"]
            .as_array()
            .expect("target proof-consumer blockers")
            .iter()
            .any(|blocker| { blocker["code"] == "symbolic-formula-schema-aware-consumer-missing" }),
        "{evidence}"
    );
}

#[cfg(unix)]
#[test]
fn test_trust_cg_json_synthetic_release_acceptance_fails_closed_without_production_cli_golden() {
    let (dispatch, canonical_vc_bytes) =
        importable_binary_dispatch("trust_cg-release-positive:vc0");
    let checked_artifact = checked_binary_artifact_for_dispatch(&dispatch, &canonical_vc_bytes);
    let root = temp_test_dir("trust_cg-release-positive-source-backprop");
    let path = persist_checked_certificate_artifact(&root, &checked_artifact)
        .expect("production checked artifact should persist");
    let loader = load_convert_checked_certificate_loader_report_with_external_checker(
        &[path.display().to_string()],
        &[],
        None,
        1_777_070_404_000,
    )
    .expect("convert checked-certificate metadata loader should preserve audit-only readback");
    assert_eq!(loader.readback_records.len(), 1);
    assert!(!loader.readback_records[0].production_checked);

    let mut report =
        proof_grade_convert_report_with_source_provenance(exact_binary_source_provenance_summary());
    report.output_content = Some(accepted_trust_cg_target_proof_consumer_output(&dispatch.id));

    let mut observed_golden = serde_json::Map::new();
    for (mode, gate_key, json) in [
        (
            "convert",
            "conversion_gate",
            serialize_convert_json_with_checked_certificate_loader(&report, loader.clone())
                .expect("serialize fail-closed convert JSON"),
        ),
        (
            "decompile",
            "artifact_gate",
            serialize_decompile_json_with_checked_certificate_loader(&report, loader.clone())
                .expect("serialize fail-closed decompile JSON"),
        ),
    ] {
        let value: serde_json::Value = serde_json::from_str(&json).expect("parse JSON");
        assert_eq!(value[gate_key]["accepted"], false, "{value}");
        assert_eq!(value[gate_key]["status"], "rejected", "{value}");
        assert_eq!(value["checked_certificate_readback"]["proof_grade_release_accepted"], false);
        assert_eq!(value["checked_certificate_readback"]["status"], "blocked");
        assert_eq!(value["checked_certificate_readback"]["production_checked_certificates"], 0);
        assert_json_canonical_sha256(
            &value["target_proof_consumer_evidence"]["binding_sha256"],
            "target proof-consumer binding digest",
        );
        assert_eq!(
            value["checked_certificate_readback"]["readback_records"][0]["production_checked"],
            false
        );
        assert_eq!(value["target_proof_consumer_evidence"]["target_semantics_consumed"], true);
        assert_eq!(
            value.get("production_proof_grade_evidence").cloned().unwrap_or_default(),
            serde_json::Value::Null
        );
        assert!(
            value[gate_key]["blockers"].as_array().expect("gate blockers").iter().any(|blocker| {
                blocker
                    .as_str()
                    .expect("blocker")
                    .contains("missing-checked-certificate-production-evidence")
            }),
            "{value}"
        );
        assert!(
            value["checked_certificate_readback"]["proof_grade_release_blockers"]
                .as_array()
                .expect("release blockers")
                .iter()
                .any(|blocker| {
                    blocker["code"] == "checked-certificate-production-evidence-missing"
                        && blocker["evidence_required"]
                            .as_array()
                            .expect("evidence required")
                            .iter()
                            .any(|item| item.as_str() == Some("production_checker_evidence"))
                }),
            "{value}"
        );
        let release_blocker_codes =
            value["checked_certificate_readback"]["proof_grade_release_blockers"]
                .as_array()
                .expect("release blockers")
                .iter()
                .map(|blocker| blocker["code"].as_str().expect("release blocker code"))
                .collect::<BTreeSet<_>>();
        for required_code in [
            "checked-certificate-manifest-identity-missing",
            "checked-certificate-source-backpropagation-gate-identity-missing",
            "replay-digest-identity-missing",
        ] {
            assert!(
                release_blocker_codes.contains(required_code),
                "missing {required_code} in {value}"
            );
        }
        let inventory =
            &value["checked_certificate_readback"]["production_positive_golden_inventory"];
        assert_eq!(inventory["required"], true);
        assert_eq!(inventory["status"], "blocked");
        assert_eq!(inventory["target"], "trust-cg");
        let missing_artifacts = inventory["missing_artifacts"]
            .as_array()
            .expect("missing production-positive artifacts");
        let missing_names = missing_artifacts
            .iter()
            .map(|artifact| artifact["artifact"].as_str().expect("artifact name"))
            .collect::<BTreeSet<_>>();
        for required_artifact in [
            "decompile --to trust-cg --json",
            "decompile -> convert --to trust-cg --json",
            "checked cert manifest",
            "replay identity",
            "unsupported-ledger elimination",
        ] {
            assert!(
                missing_names.contains(required_artifact),
                "missing {required_artifact} in {inventory}"
            );
        }
        assert!(
            missing_artifacts.iter().any(|artifact| {
                artifact["artifact"] == "checked cert manifest"
                    && artifact["evidence_required"]
                        .as_array()
                        .expect("manifest evidence")
                        .iter()
                        .any(|item| item.as_str() == Some("--checked-cert-manifest"))
            }),
            "{inventory}"
        );

        let source_gate = &value[gate_key]["source_backpropagation_gate"];
        assert_eq!(source_gate["accepted"], false, "{source_gate}");
        assert_eq!(source_gate["status"], "rejected");
        assert_eq!(source_gate["source_provenance"], "accepted");
        assert_eq!(source_gate["binary_verification_evidence"], "missing");
        assert_eq!(source_gate["reconstruction_evidence"], "accepted");
        assert_eq!(source_gate["checked_certificate_source_backpropagation_gate"], "rejected");
        assert!(
            source_gate["blockers"].as_array().expect("source-backprop blockers").iter().any(
                |blocker| {
                    blocker["code"] == "proof-grade-binary-verification-missing"
                        && blocker["evidence_required"]
                            .as_array()
                            .expect("source blocker evidence")
                            .iter()
                            .any(|item| item.as_str() == Some("checked_certificate_identity"))
                }
            ),
            "{source_gate}"
        );
        assert!(
            source_gate["blockers"].as_array().expect("source-backprop blockers").iter().any(
                |blocker| {
                    blocker["code"] == "checked-certificate-source-backpropagation-gate-rejected"
                        && blocker["evidence_required"]
                            .as_array()
                            .expect("source gate evidence")
                            .iter()
                            .any(|item| {
                                item.as_str()
                                    == Some("checked_certificate_source_backpropagation_gate")
                            })
                }
            ),
            "{source_gate}"
        );
        assert_eq!(
            value["checked_certificate_readback"]["readback_records"][0]["source_backpropagation_gate"]
                ["source_backpropagation_allowed"],
            false,
            "checked certificate rows remain audit/release evidence, not source rewrite permission"
        );
        assert_eq!(
            value["checked_certificate_readback"]["accepted_certificates"][0]["source_backpropagation_gate"]
                ["source_backpropagation_allowed"],
            false
        );

        observed_golden.insert(
            mode.to_string(),
            serde_json::json!({
                gate_key: {
                    "accepted": value[gate_key]["accepted"].clone(),
                    "status": value[gate_key]["status"].clone(),
                    "blockers": value[gate_key]["blockers"].clone(),
                    "validation_blockers": value[gate_key]["validation_blockers"].clone()
                },
                "checked_certificate_readback": {
                    "status": value["checked_certificate_readback"]["status"].clone(),
                    "proof_grade_release_accepted": value["checked_certificate_readback"]["proof_grade_release_accepted"].clone(),
                    "production_checked_certificates": value["checked_certificate_readback"]["production_checked_certificates"].clone(),
                    "production_positive_golden_inventory": value["checked_certificate_readback"]["production_positive_golden_inventory"].clone(),
                    "proof_grade_release_blockers": value["checked_certificate_readback"]["proof_grade_release_blockers"]
                        .as_array()
                        .expect("release blockers")
                        .iter()
                        .filter(|blocker| {
                            blocker["code"] == "checked-certificate-production-evidence-missing"
                                && blocker["stage"] == "targo-trust::convert-release-gate"
                        })
                        .cloned()
                        .collect::<Vec<_>>()
                },
                "production_proof_grade_evidence": value
                    .get("production_proof_grade_evidence")
                    .cloned()
                    .unwrap_or(serde_json::Value::Null),
                "target_proof_consumer_evidence": {
                    "status": value["target_proof_consumer_evidence"]["status"].clone(),
                    "target_semantics_consumed": value["target_proof_consumer_evidence"]["target_semantics_consumed"].clone(),
                    "binding_sha256": value["target_proof_consumer_evidence"]["binding_sha256"].clone()
                }
            }),
        );
    }
    let expected_golden: serde_json::Value = serde_json::from_str(include_str!(
        "fixtures/decompile_convert_trust_cg_synthetic_proof_grade_fail_closed_golden.json"
    ))
    .expect("parse synthetic trust_cg fail-closed golden");
    assert_eq!(serde_json::Value::Object(observed_golden), expected_golden);

    let rejected_terminal =
        render_convert_terminal_with_checked_certificate_loader(&report, loader.clone());
    assert!(rejected_terminal.contains("checked_certificate_source_backpropagation_gate=rejected"));
    assert!(rejected_terminal.contains("checked-certificate-source-backpropagation-gate-rejected"));
    assert!(rejected_terminal.contains("checked-certificate-production-evidence-missing"));
    assert!(rejected_terminal.contains("production-positive golden inventory: status=blocked"));
    assert!(rejected_terminal.contains("decompile --to trust-cg --json"));
    assert!(rejected_terminal.contains("decompile -> convert --to trust-cg --json"));
    assert!(rejected_terminal.contains("checked cert manifest"));
    assert!(rejected_terminal.contains("replay identity"));
    assert!(rejected_terminal.contains("unsupported-ledger elimination"));

    let mut unconsumed_symbolic_loader = loader.clone();
    let unconsumed_symbolic_gate = unconsumed_symbolic_checked_source_gate();
    unconsumed_symbolic_loader.readback_records[0].source_backpropagation_gate =
        unconsumed_symbolic_gate.clone();
    unconsumed_symbolic_loader.artifacts[0].source_backpropagation_gate =
        unconsumed_symbolic_gate.clone();
    let unconsumed_json =
        serialize_convert_json_with_checked_certificate_loader(&report, unconsumed_symbolic_loader)
            .expect("serialize convert JSON with unconsumed symbolic source gate");
    let unconsumed_value: serde_json::Value =
        serde_json::from_str(&unconsumed_json).expect("parse unconsumed source gate JSON");
    let readback_source_gate = &unconsumed_value["checked_certificate_readback"]["readback_records"]
        [0]["source_backpropagation_gate"];
    assert_eq!(readback_source_gate["source_backpropagation_allowed"], false);
    assert_eq!(readback_source_gate["preserved_symbolic_formulas"], 1);
    assert!(
        readback_source_gate["blockers"]
            .as_array()
            .expect("source gate blockers")
            .iter()
            .any(|blocker| blocker.as_str() == Some("trust_symbolic_formula_entries_unconsumed")),
        "{readback_source_gate}"
    );
    assert_eq!(
        unconsumed_value["conversion_gate"]["source_backpropagation_gate"]["checked_certificate_source_backpropagation_gate"],
        "rejected"
    );

    let mut accepted_source_gate_loader = loader.clone();
    let accepted_source_gate = consumed_symbolic_checked_source_gate();
    accepted_source_gate_loader.readback_records[0].source_backpropagation_gate =
        accepted_source_gate.clone();
    accepted_source_gate_loader.artifacts[0].source_backpropagation_gate =
        accepted_source_gate.clone();

    for (gate_key, json) in [
        (
            "conversion_gate",
            serialize_convert_json_with_checked_certificate_loader(
                &report,
                accepted_source_gate_loader.clone(),
            )
            .expect("serialize convert JSON with accepted source-backprop checked gate"),
        ),
        (
            "artifact_gate",
            serialize_decompile_json_with_checked_certificate_loader(
                &report,
                accepted_source_gate_loader.clone(),
            )
            .expect("serialize decompile JSON with accepted source-backprop checked gate"),
        ),
    ] {
        let value: serde_json::Value = serde_json::from_str(&json).expect("parse JSON");
        let source_gate = &value[gate_key]["source_backpropagation_gate"];
        assert_eq!(source_gate["accepted"], false, "{source_gate}");
        assert_eq!(source_gate["binary_verification_evidence"], "missing");
        assert_eq!(source_gate["reconstruction_evidence"], "accepted");
        assert_eq!(source_gate["checked_certificate_source_backpropagation_gate"], "accepted");
        assert!(
            !source_gate["blockers"].as_array().expect("source-backprop blockers").iter().any(
                |blocker| blocker["code"]
                    .as_str()
                    .expect("blocker code")
                    .starts_with("checked-certificate-source-backpropagation-gate")
            ),
            "{source_gate}"
        );
        assert_eq!(
            value["checked_certificate_readback"]["readback_records"][0]["source_backpropagation_gate"]
                ["source_backpropagation_allowed"],
            true
        );
        assert_eq!(
            value["checked_certificate_readback"]["readback_records"][0]["source_backpropagation_gate"]
                ["preserved_symbolic_formulas"],
            1
        );
        assert_eq!(
            value["checked_certificate_readback"]["readback_records"][0]["source_backpropagation_gate"]
                ["symbolic_formula_consumer_accepted"],
            true
        );
    }

    let accepted_terminal = render_convert_terminal_with_checked_certificate_loader(
        &report,
        accepted_source_gate_loader,
    );
    assert!(accepted_terminal.contains("checked_certificate_source_backpropagation_gate=accepted"));
    assert!(
        !accepted_terminal.contains("checked-certificate-source-backpropagation-gate-rejected")
    );

    let (current_dispatch, _) = importable_binary_dispatch("trust_cg-release-current:vc0");
    let mut proof_evidence =
        VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![current_dispatch]);
    let import_report = proof_evidence
        .load_and_import_checked_certificate_artifacts([path.as_path()])
        .expect("persisted checked artifact should import into verify-binary evidence");
    let mut verify_report = build_verify_binary_report(
        Path::new("fixtures/tiny.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 1 }],
            }],
            solver_results: Vec::new(),
            proof_evidence,
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );
    verify_report.checked_certificate_import = Some(import_report);
    verify_report
        .checked_certificate_import
        .as_mut()
        .expect("checked certificate import report")
        .artifacts[0]
        .source_backpropagation_gate = unconsumed_symbolic_checked_source_gate();
    verify_report.trust_level = "proof_grade".to_string();

    let verify_json = serialize_verify_binary_json(&verify_report)
        .expect("serialize verify-binary JSON with checked certificate import");
    let verify_value: serde_json::Value =
        serde_json::from_str(&verify_json).expect("parse verify-binary JSON");
    assert_eq!(verify_value["proof_grade_gate"]["accepted"], false);
    assert!(
        verify_value["proof_grade_gate"]["blockers"]
            .as_array()
            .expect("verify release blockers")
            .iter()
            .any(|blocker| {
                blocker["code"] == "checked-certificate-source-backpropagation-handoff-missing"
            }),
        "{}",
        verify_value["proof_grade_gate"]
    );
    assert_eq!(verify_value["checked_certificate_evidence"]["status"], "accepted");
    assert_eq!(
        verify_value["checked_certificate_evidence"]["accepted_certificates"][0]["source_backpropagation_gate"]
            ["source_backpropagation_allowed"],
        false
    );
    assert_eq!(
        verify_value["checked_certificate_evidence"]["accepted_certificates"][0]["source_backpropagation_gate"]
            ["preserved_symbolic_formulas"],
        1
    );
    assert!(
        verify_value["checked_certificate_evidence"]["accepted_certificates"][0]
            ["source_backpropagation_gate"]["blockers"]
            .as_array()
            .expect("verify import source gate blockers")
            .iter()
            .any(|blocker| {
                blocker.as_str() == Some("trust_symbolic_formula_entries_unconsumed")
            })
    );
    let verify_source_gate = &verify_value["source_backpropagation_gate"];
    assert_eq!(verify_source_gate["accepted"], false, "{verify_source_gate}");
    assert_eq!(verify_source_gate["status"], "rejected");
    assert_eq!(verify_source_gate["source_provenance"], "missing");
    assert_eq!(verify_source_gate["binary_verification_evidence"], "partial");
    assert_eq!(verify_source_gate["reconstruction_evidence"], "missing");
    assert_eq!(verify_source_gate["checked_certificate_source_backpropagation_gate"], "rejected");
    for required_code in [
        "exact-source-provenance-missing",
        "proof-grade-binary-verification-missing",
        "accepted-reconstruction-target-validation-missing",
        "checked-certificate-source-backpropagation-gate-rejected",
    ] {
        assert!(
            verify_source_gate["blockers"]
                .as_array()
                .expect("verify source-backprop blockers")
                .iter()
                .any(|blocker| blocker["code"] == required_code),
            "missing {required_code} in {verify_source_gate}"
        );
    }

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_convert_json_uses_trust_cg_output_target_proof_consumer_evidence() {
    let mut report =
        proof_grade_convert_report_with_source_provenance(exact_binary_source_provenance_summary());
    report.output_content = Some(
        serde_json::json!({
            "functions": [{"name": "entry"}],
            "target_proof_consumer_evidence": {
                "target": "trust-cg",
                "status": "rejected",
                "target_semantics_consumed": false,
                "records": [
                    {
                        "kind": "symbolic_formula",
                        "identifier": "entry::bb0::stmt0::use",
                        "accepted": false,
                        "detail": "bridge-preserved symbolic formula was not consumed"
                    }
                ],
                "blockers": [
                    {
                        "code": "symbolic-formula-not-consumed-by-target-semantics",
                        "detail": "bridge proof-consumer blocker"
                    }
                ]
            }
        })
        .to_string(),
    );

    let json = serialize_convert_json(&report)
        .expect("serialize convert JSON with bridge target proof-consumer evidence");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse convert JSON");
    let evidence = &value["target_proof_consumer_evidence"];

    assert_eq!(evidence["target"], "trust-cg");
    assert_eq!(evidence["records"][0]["identifier"], "entry::bb0::stmt0::use");
    assert_eq!(
        evidence["records"][0]["detail"],
        "bridge-preserved symbolic formula was not consumed"
    );
    assert_eq!(evidence["blockers"][0]["detail"], "bridge proof-consumer blocker");
    assert_eq!(&value["conversion_gate"]["target_proof_consumer_evidence"], evidence);
    assert_eq!(value["conversion_gate"]["accepted"], false);
    assert!(
        value["conversion_gate"]["validation_blockers"]
            .as_array()
            .expect("validation blockers")
            .iter()
            .any(|blocker| blocker
                .as_str()
                .expect("blocker")
                .contains("symbolic-formula-not-consumed-by-target-semantics"))
    );
}

#[test]
fn test_convert_json_rejects_accepted_target_consumer_without_binding() {
    let mut report =
        proof_grade_convert_report_with_source_provenance(exact_binary_source_provenance_summary());
    report.output_content = Some(
        serde_json::json!({
            "functions": [{"name": "entry", "return_type": "i32"}],
            "typed": true,
            "target_proof_consumer_evidence": {
                "target": "trust-cg",
                "status": "accepted",
                "target_semantics_consumed": true,
                "records": [
                    {
                        "kind": "target_semantics",
                        "identifier": "trust_cg-lir",
                        "accepted": true,
                        "detail": "trust-cg target semantics consumed conversion proof inputs"
                    },
                    {
                        "kind": "binary_provenance",
                        "identifier": "binary_provenance:entry@0x401000",
                        "accepted": true,
                        "detail": "binary provenance consumed by target proof consumer"
                    },
                    {
                        "kind": "checked_certificate",
                        "identifier": "vc0",
                        "accepted": true,
                        "detail": "checked certificate consumed by target proof consumer"
                    },
                    {
                        "kind": "proof_replay",
                        "identifier": "vc0",
                        "accepted": true,
                        "detail": "proof replay consumed by target proof consumer"
                    }
                ],
                "blockers": []
            }
        })
        .to_string(),
    );

    let json = serialize_convert_json(&report)
        .expect("serialize convert JSON with unbound target proof-consumer evidence");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse convert JSON");
    let evidence = &value["target_proof_consumer_evidence"];

    assert_eq!(evidence["target"], "trust-cg");
    assert_eq!(evidence["status"], "rejected");
    assert_eq!(evidence.get("binding_sha256"), None);
    assert!(
        evidence["blockers"]
            .as_array()
            .expect("target proof-consumer blockers")
            .iter()
            .any(|blocker| blocker["code"] == "target-proof-consumer-binding-missing"),
        "{evidence}"
    );
    assert_eq!(&value["conversion_gate"]["target_proof_consumer_evidence"], evidence);
    assert_eq!(value["conversion_gate"]["accepted"], false);
    assert!(
        value["conversion_gate"]["validation_blockers"]
            .as_array()
            .expect("validation blockers")
            .iter()
            .any(|blocker| blocker
                .as_str()
                .expect("validation blocker")
                .contains("target-proof-consumer-binding-missing")),
        "{}",
        value["conversion_gate"]
    );
}

#[test]
fn test_decompile_and_convert_json_preserve_wasm_scalar_target_proof_binding() {
    let mut report =
        proof_grade_convert_report_with_source_provenance(exact_binary_source_provenance_summary());
    report.target = DecompileTarget::Wasm;
    report.output_kind = Some("wasm_text".into());
    report.output_content = Some(accepted_wasm_scalar_target_proof_consumer_output());

    for (gate_key, json) in [
        (
            "conversion_gate",
            serialize_convert_json(&report)
                .expect("serialize convert JSON with Wasm target proof binding"),
        ),
        (
            "artifact_gate",
            serialize_decompile_json_with_checked_certificate_loader(
                &report,
                super::convert_checked_certificate_loader_not_requested(),
            )
            .expect("serialize decompile JSON with Wasm target proof binding"),
        ),
    ] {
        let value: serde_json::Value =
            serde_json::from_str(&json).expect("parse Wasm target proof binding JSON");
        let evidence = &value["target_proof_consumer_evidence"];
        let binding = &evidence["binding"];

        assert_eq!(evidence["target"], "wasm");
        assert_eq!(evidence["status"], "accepted");
        assert_eq!(evidence["target_semantics_consumed"], true);
        assert_eq!(evidence["blockers"].as_array().expect("consumer blockers").len(), 0);
        assert_eq!(binding["target"], "wasm");
        assert_eq!(binding["target_output"], "wat:emitted:guard:i32.const:1");
        assert_eq!(binding["status"], "accepted");
        assert_eq!(binding["target_semantics_consumed"], true);
        assert_json_canonical_sha256(
            &evidence["binding_sha256"],
            "Wasm target proof-consumer binding digest",
        );
        let normalized_binding: super::TargetProofBindingReport =
            serde_json::from_value(binding.clone())
                .expect("target proof binding should deserialize for digest");
        assert_eq!(
            evidence["binding_sha256"],
            super::stable_json_sha256(&normalized_binding)
                .expect("target proof binding should serialize for digest")
        );
        assert_eq!(&value[gate_key]["target_proof_consumer_evidence"], evidence);
        assert_eq!(&value["target_evidence"]["target_proof_consumer_evidence"], evidence);
        assert!(
            evidence["records"].as_array().expect("target proof-consumer records").iter().any(
                |record| record["kind"] == "binary_provenance"
                    && record["accepted"] == true
                    && record["identifier"]
                        .as_str()
                        .expect("binary provenance identifier")
                        .contains("0x1004")
            ),
            "{evidence}"
        );
        for (kind, canonical_source) in [
            ("canonical_trust_ir_formula", "trust_symbolic.formula"),
            ("binary_provenance", "trust_binary.provenance"),
            ("checked_certificate", "trust_proof.checked_certificate"),
            ("proof_replay", "trust_proof.proof_replay"),
        ] {
            assert!(
                binding["inputs"].as_array().expect("target proof binding inputs").iter().any(
                    |input| input["kind"] == kind
                        && input["canonical_source"] == canonical_source
                        && input["consumed_by_target_semantics"] == true
                ),
                "missing {kind}/{canonical_source} in {binding}"
            );
        }
        assert!(
            !value[gate_key]["validation_blockers"]
                .as_array()
                .expect("validation blockers")
                .iter()
                .any(|blocker| blocker
                    .as_str()
                    .expect("validation blocker")
                    .contains("target-proof-consumer")),
            "{value}"
        );
    }
}

#[test]
fn test_convert_json_surfaces_bounded_target_consumer_blockers_and_digest_identity() {
    for (target, blocker_code, blocker_detail) in [
        (
            DecompileTarget::TrustCg,
            "bounded-empty-slice-replay-not-canonical",
            "bounded trust_cg target proof-consumer slice rejects replay metadata that is non-canonical, not replayed, missing an artifact digest, or not exact",
        ),
        (
            DecompileTarget::Wasm,
            "bounded-empty-slice-checked-certificate-not-canonical",
            "bounded Wasm target proof-consumer slice rejects checked-certificate metadata that is non-canonical or lacks checked identity",
        ),
    ] {
        let label = target.label();
        let (dispatch, canonical_vc_bytes) =
            importable_binary_dispatch(&format!("{label}-bounded-target:vc0"));
        let checked_artifact = checked_binary_artifact_for_dispatch(&dispatch, &canonical_vc_bytes);
        let root = temp_test_dir(&format!("convert-{label}-bounded-target"));
        let path = persist_checked_certificate_artifact(&root, &checked_artifact)
            .expect("checked artifact should persist");
        let loader =
            load_convert_checked_certificate_loader_report(&[path.display().to_string()], &[])
                .expect("convert checked-certificate metadata loader should parse artifact rows");
        let mut report = proof_grade_convert_report_with_source_provenance(
            exact_binary_source_provenance_summary(),
        );
        report.target = target;
        report.output_kind = Some(
            if target == DecompileTarget::TrustCg { "trust_cg_text" } else { "wasm_text" }.into(),
        );
        report.output_content = Some(
            serde_json::json!({
                "functions": [],
                "target_proof_consumer_evidence": {
                    "target": label,
                    "status": "rejected",
                    "target_semantics_consumed": false,
                    "records": [
                        {
                            "kind": "target_semantics",
                            "identifier": format!("{label}-bounded-empty"),
                            "accepted": false,
                            "detail": blocker_detail
                        },
                        {
                            "kind": "checked_certificate",
                            "identifier": "bounded-target:vc0",
                            "accepted": false,
                            "detail": "checked certificate metadata is present but only partial target-consumer evidence exists"
                        },
                        {
                            "kind": "proof_replay",
                            "identifier": "bounded-target:vc0",
                            "accepted": false,
                            "detail": "replay metadata is present but not accepted by the bounded target consumer"
                        }
                    ],
                    "blockers": [
                        {
                            "code": blocker_code,
                            "detail": blocker_detail
                        }
                    ]
                }
            })
            .to_string(),
        );

        let json = serialize_convert_json_with_checked_certificate_loader(&report, loader)
            .expect("serialize convert JSON with bounded target-consumer blocker");
        let value: serde_json::Value = serde_json::from_str(&json).expect("parse convert JSON");
        assert_eq!(value["target"], label);
        assert_eq!(value["conversion_gate"]["target"], label);
        assert_eq!(value["target_proof_consumer_evidence"]["blockers"][0]["code"], blocker_code);
        assert_eq!(
            value["conversion_gate"]["target_proof_consumer_evidence"]["blockers"][0]["code"],
            blocker_code
        );
        assert_eq!(value["conversion_gate"]["accepted"], false);
        assert_eq!(value["conversion_gate"]["status"], "rejected");
        assert_eq!(
            value["conversion_gate"]["checked_certificate_evidence"]["proof_grade_release_accepted"],
            false
        );
        assert!(
            value["conversion_gate"]["validation_blockers"]
                .as_array()
                .expect("validation blockers")
                .iter()
                .any(|blocker| blocker.as_str().expect("blocker").contains(blocker_code)),
            "{value}"
        );
        assert!(
            value["conversion_gate"]["checked_certificate_evidence"]
                ["proof_grade_release_blockers"]
                .as_array()
                .expect("release blockers")
                .iter()
                .any(|blocker| blocker["code"] == "target-semantic-validation-missing"
                    && blocker["detail"].as_str().expect("detail").contains(blocker_code)),
            "{value}"
        );
        assert_eq!(
            value["checked_certificate_readback"]["readback_records"][0]["binary_artifact_digest_identity"]
                ["root_artifact_digest"]["value"],
            "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
        );
        assert_eq!(
            value["checked_certificate_readback"]["artifacts"][0]["binary_artifact_digest_identity"]
                ["selected_image"]["sha256"],
            "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
        );

        let _ = std::fs::remove_dir_all(root);
    }
}

#[test]
fn test_decompile_json_surfaces_wasm_target_proof_consumer_evidence() {
    let report = DecompileReport {
        binary: "demo.bin".into(),
        format: Some("ELF".into()),
        architecture: Some("x86_64".into()),
        selection: "address".into(),
        entry: Some("0x401000".into()),
        binary_entry: Some("0x401000".into()),
        source_provenance: exact_binary_source_provenance_summary(),
        strict: true,
        target: DecompileTarget::Wasm,
        status: BinaryLiftStatus::Ok,
        output_kind: Some("wasm_text".into()),
        output_trust_level: "proof_grade".into(),
        output_validation: "translation_validated".into(),
        validation_note: "synthetic target validation accepted".into(),
        output_content: Some("(module (func (result i32) i32.const 0))".into()),
        production_proof_grade_evidence: None,
        binary_evidence: DecompileBinaryEvidenceReport::default(),
        target_validation_blockers: Vec::new(),
        preserved_symbolic_formulas: Vec::new(),
        functions_decompiled: 1,
        blocks: 1,
        instructions: 1,
        statements: 1,
        memory_facts: 0,
        unsupported: 0,
        failures: 0,
        functions: Vec::new(),
        unsupported_items: Vec::new(),
        failure_items: Vec::new(),
    };

    let json = serialize_decompile_json_with_checked_certificate_loader(
        &report,
        super::convert_checked_certificate_loader_not_requested(),
    )
    .expect("serialize decompile JSON with target proof-consumer evidence");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse decompile JSON");
    let evidence = &value["target_proof_consumer_evidence"];

    assert_eq!(evidence["target"], "wasm");
    assert_eq!(evidence["status"], "rejected");
    assert_eq!(evidence["target_semantics_consumed"], false);
    assert_eq!(&value["artifact_gate"]["target_proof_consumer_evidence"], evidence);
    assert!(
        evidence["records"]
            .as_array()
            .expect("target proof-consumer records")
            .iter()
            .any(|record| record["kind"] == "checked_certificate"
                && record["identifier"] == "missing")
    );
    assert!(
        evidence["records"]
            .as_array()
            .expect("target proof-consumer records")
            .iter()
            .any(|record| record["kind"] == "proof_replay" && record["identifier"] == "missing")
    );
    for required_code in [
        "target-semantics-not-consumed",
        "missing-checked-proof-certificate",
        "missing-proof-replay-metadata",
    ] {
        assert!(
            evidence["blockers"]
                .as_array()
                .expect("target proof-consumer blockers")
                .iter()
                .any(|blocker| blocker["code"] == required_code),
            "missing {required_code} in {evidence}"
        );
    }
    assert_eq!(value["artifact_gate"]["accepted"], false);
    assert_eq!(value["artifact_gate"]["status"], "rejected");
}

#[test]
fn test_decompile_trust_cg_convert_readback_rejects_target_replay_source_blockers() {
    let (dispatch, canonical_vc_bytes) = importable_binary_dispatch("decompile-convert:vc0");
    let checked_artifact = checked_binary_artifact_for_dispatch(&dispatch, &canonical_vc_bytes);
    let root = temp_test_dir("decompile-convert-trust_cg-checked-cert");
    let path = persist_checked_certificate_artifact(&root, &checked_artifact)
        .expect("checked artifact should persist");
    let loader = load_convert_checked_certificate_loader_report(&[path.display().to_string()], &[])
        .expect("convert checked-certificate metadata loader should parse artifact rows");
    let raw_proof_blocker = TargetValidationBlocker {
        target: trust_types::DecompileTarget::TrustCg,
        function: Some("entry".to_string()),
        stage: "trust-cg-bridge::target-validation".to_string(),
        feature: "raw-solver-proof-bytes-audit-only".to_string(),
        reason:
            "raw solver proof bytes were preserved for audit, but cannot satisfy checked-certificate evidence"
                .to_string(),
        diagnostics: vec![
            "required-evidence=normalized_solver_proof_export".to_string(),
            "required-evidence=checker_success".to_string(),
            "required-evidence=checked_certificate_artifact".to_string(),
        ],
        ..Default::default()
    };
    let target_semantics_blocker = TargetValidationBlocker {
        target: trust_types::DecompileTarget::TrustCg,
        function: Some("entry".to_string()),
        stage: "trust-cg-bridge::target-validation".to_string(),
        feature: "target-semantic-validation".to_string(),
        reason: "trust-cg target semantics validation has not discharged emitted obligations"
            .to_string(),
        diagnostics: vec!["required-evidence=target_semantic_validation".to_string()],
        ..Default::default()
    };
    let replay_blocker = TargetValidationBlocker {
        target: trust_types::DecompileTarget::TrustCg,
        function: Some("entry".to_string()),
        stage: "trust-cg-bridge::target-validation".to_string(),
        feature: "exact-machine-replay".to_string(),
        reason: "exact machine replay has not covered emitted trust_cg obligations".to_string(),
        diagnostics: vec!["required-evidence=machine_replay_transcript".to_string()],
        ..Default::default()
    };
    let source_blocker = TargetValidationBlocker {
        target: trust_types::DecompileTarget::TrustCg,
        function: Some("entry".to_string()),
        stage: "trust-cg-bridge::target-validation".to_string(),
        feature: "exact-source-provenance".to_string(),
        reason: "exact source provenance has not been consumed by the trust_cg handoff".to_string(),
        diagnostics: vec!["required-evidence=source_provenance_handoff".to_string()],
        ..Default::default()
    };
    let trust_cg_text = serde_json::json!({
        "typed": true,
        "functions": [
            {
                "name": "entry",
                "return_type": "i32"
            }
        ],
        "validation": {
            "status": "inspectable_rejected",
            "trust_level": "rejected",
            "proof_grade": false
        },
        "target_validation_blockers": [
            {
                "feature": "raw-solver-proof-bytes-audit-only"
            },
            {
                "feature": "target-semantic-validation"
            },
            {
                "feature": "exact-machine-replay"
            },
            {
                "feature": "exact-source-provenance"
            }
        ]
    })
    .to_string();
    let decompile_artifact = trust_types::DecompilationArtifact {
        binary: trust_types::BinaryArtifactMetadata {
            path: Some("fixtures/tiny.bin".to_string()),
            format: trust_types::BinaryArtifactFormat::Elf,
            architecture: "x86-64".to_string(),
            entry_point: Some(0x401000),
            ..Default::default()
        },
        target: trust_types::DecompileTarget::TrustCg,
        functions: vec![trust_types::DecompiledFunction {
            name: "entry".to_string(),
            entry: 0x401000,
            coverage: trust_types::BinaryCoverageSummary {
                instructions_lifted: 1,
                ..Default::default()
            },
            ..Default::default()
        }],
        source_provenance: exact_binary_source_provenance_summary(),
        reconstruction: trust_types::ReconstructionSummary {
            target: trust_types::DecompileTarget::TrustCg,
            validation: trust_types::ReconstructionValidationStatus::Validated,
            trust_level: trust_types::TrustLevel::Rejected,
            outputs: vec![trust_types::DecompiledOutput {
                target: trust_types::DecompileTarget::TrustCg,
                text: Some(trust_cg_text),
                validation: trust_types::ReconstructionValidationStatus::Validated,
                trust_level: trust_types::TrustLevel::Rejected,
                target_validation_blockers: vec![
                    raw_proof_blocker.clone(),
                    target_semantics_blocker.clone(),
                    replay_blocker.clone(),
                    source_blocker.clone(),
                ],
                diagnostics: vec![
                    "format=trust_cg-lir-json".to_string(),
                    "trust_cg-validation=inspectable-rejected".to_string(),
                ],
                ..Default::default()
            }],
            ..Default::default()
        },
        trust_level: trust_types::TrustLevel::Rejected,
        ..Default::default()
    };
    let mut report = build_decompile_report(
        Path::new("fixtures/tiny.bin"),
        Some(0x401000),
        false,
        true,
        DecompileTarget::TrustCg,
        Ok(decompile_artifact),
    );
    report.output_trust_level = "proof_grade".to_string();
    report.output_validation = "translation_validated".to_string();
    report.validation_note =
        "synthetic target validation accepted, but release gates remain blocked".to_string();

    assert_eq!(report.target, DecompileTarget::TrustCg);
    assert_eq!(report.output_kind.as_deref(), Some("trust_cg_text"));
    assert_eq!(report.output_validation, "translation_validated");
    assert_eq!(report.output_trust_level, "proof_grade");
    assert_eq!(
        report.target_validation_blockers,
        vec![
            raw_proof_blocker.clone(),
            target_semantics_blocker.clone(),
            replay_blocker.clone(),
            source_blocker.clone(),
        ]
    );
    assert!(!decompile_should_fail(&report));
    assert!(convert_should_fail(&report));

    let decompile_value = serde_json::to_value(&report).expect("serialize decompile report");
    assert_eq!(decompile_value["target"], "trust-cg");
    assert_eq!(decompile_value["output_kind"], "trust_cg_text");
    assert_eq!(
        decompile_value["target_validation_blockers"][0]["feature"],
        raw_proof_blocker.feature
    );

    let decompile_json =
        serialize_decompile_json_with_checked_certificate_loader(&report, loader.clone())
            .expect("serialize decompile JSON with checked certificate rows");
    let decompile_readback_value: serde_json::Value =
        serde_json::from_str(&decompile_json).expect("parse decompile JSON");
    assert_eq!(decompile_readback_value["trust_cg_output"]["typed"], true);
    assert_eq!(decompile_readback_value["artifact_gate"]["accepted"], false);
    assert_eq!(decompile_readback_value["artifact_gate"]["status"], "rejected");
    assert_eq!(
        decompile_readback_value["checked_certificate_readback"]["readback_records"][0]["certificate_sha256"],
        checked_artifact.certificate_sha256
    );
    assert_eq!(
        decompile_readback_value["checked_certificate_readback"]["readback_row_details"][0]["readback_status"],
        "accepted"
    );
    assert_eq!(
        decompile_readback_value["checked_certificate_readback"]["readback_row_details"][0]["proof_grade_release_status"],
        "rejected"
    );
    assert!(
        decompile_readback_value["artifact_gate"]["validation_blockers"]
            .as_array()
            .expect("decompile artifact gate validation blockers")
            .iter()
            .any(|blocker| blocker
                .as_str()
                .expect("validation blocker")
                .contains("exact-source-provenance"))
    );

    let json = serialize_convert_json_with_checked_certificate_loader(&report, loader)
        .expect("serialize convert JSON with decompile-built trust_cg output");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse convert JSON");

    assert_eq!(value["trust_cg_output"]["typed"], true);
    assert_eq!(value["trust_cg_output"]["functions"][0]["name"], "entry");
    assert_eq!(value["trust_cg_output"]["functions"][0]["return_type"], "i32");
    assert_eq!(value["trust_cg_output"]["validation"]["proof_grade"], false);
    assert_eq!(value["conversion_gate"]["accepted"], false);
    assert_eq!(value["conversion_gate"]["status"], "rejected");
    assert!(
        value["conversion_gate"]["validation_blockers"]
            .as_array()
            .expect("validation blockers")
            .iter()
            .any(|blocker| blocker
                .as_str()
                .expect("validation blocker")
                .contains("raw-solver-proof-bytes-audit-only"))
    );
    assert!(
        value["conversion_gate"]["validation_blockers"]
            .as_array()
            .expect("validation blockers")
            .iter()
            .any(|blocker| blocker
                .as_str()
                .expect("validation blocker")
                .contains("target-semantic-validation"))
    );
    assert!(
        value["conversion_gate"]["validation_blockers"]
            .as_array()
            .expect("validation blockers")
            .iter()
            .any(|blocker| blocker
                .as_str()
                .expect("validation blocker")
                .contains("exact-machine-replay"))
    );
    assert!(
        value["conversion_gate"]["validation_blockers"]
            .as_array()
            .expect("validation blockers")
            .iter()
            .any(|blocker| blocker
                .as_str()
                .expect("validation blocker")
                .contains("exact-source-provenance"))
    );

    let evidence = &value["conversion_gate"]["checked_certificate_evidence"];
    assert_eq!(&value["checked_certificate_readback"], evidence);
    assert_eq!(evidence["required"], true);
    assert_eq!(evidence["status"], "blocked");
    assert_eq!(evidence["proof_grade_release_accepted"], false);
    assert_eq!(evidence["loader"]["status"], "loaded");
    assert_eq!(evidence["checked_artifact_rows"], 1);
    assert_eq!(evidence["accepted_certificate_rows"], 1);
    assert_eq!(evidence["imported_artifact_rows"], 0);
    assert_eq!(evidence["unmatched_artifact_rows"], 0);
    assert_eq!(evidence["normalized_solver_proof_exports"], 1);
    assert_eq!(evidence["proof_export_readback_rows"], 1);
    assert_eq!(evidence["checked_certificate_readback_rows"], 1);
    assert_eq!(evidence["checker_successes"], 1);
    assert_eq!(evidence["checked_certificates"], 1);
    assert_eq!(evidence["raw_solver_proof_bytes_sufficient"], false);
    assert_eq!(evidence["accepted_certificates"][0]["source"], "checked_certificate_readback");
    assert_eq!(evidence["artifacts"][0]["status"], "readback");
    assert_eq!(evidence["artifacts"][0]["certificate_sha256"], checked_artifact.certificate_sha256);
    assert_eq!(
        evidence["readback_records"][0]["proof_export_sha256"],
        checked_artifact.proof_export_sha256
    );
    assert_eq!(
        evidence["readback_records"][0]["replay"], "not_attempted",
        "certificate-only UNSAT readback is audit evidence for convert, not target replay acceptance"
    );
    assert_eq!(evidence["readback_row_details"][0]["readback_status"], "accepted");
    assert_eq!(evidence["readback_row_details"][0]["proof_grade_release_status"], "rejected");
    for required_blocker in [
        "raw-solver-proof-bytes-audit-only",
        "target-semantic-validation",
        "exact-machine-replay",
        "exact-source-provenance",
    ] {
        assert!(
            evidence["readback_row_details"][0]["blockers"]
                .as_array()
                .expect("readback row blockers")
                .iter()
                .any(|blocker| blocker.as_str().expect("row blocker").contains(required_blocker)),
            "missing {required_blocker} in {}",
            evidence["readback_row_details"][0]
        );
    }
    let evidence_blockers =
        evidence["blockers"].as_array().expect("checked certificate evidence blockers");
    assert!(
        evidence_blockers
            .iter()
            .any(|blocker| blocker["code"] == "raw-solver-proof-bytes-audit-only")
    );
    let release_blockers =
        evidence["proof_grade_release_blockers"].as_array().expect("release blockers");
    for required_code in [
        "raw-solver-proof-bytes-audit-only",
        "target-semantic-validation-missing",
        "exact-machine-replay-missing",
        "exact-source-provenance-missing",
    ] {
        assert!(
            release_blockers.iter().any(|blocker| blocker["code"] == required_code),
            "missing {required_code} in {}",
            evidence["proof_grade_release_blockers"]
        );
    }

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_convert_release_blocker_classifies_rust_compile_back_roundtrip_evidence() {
    let blocker = convert_checked_certificate_release_blocker(
        "Rust compile-back artifact digest binding not accepted: \
         compile-back-artifact-digests-bound evidence is missing for source-to-binary roundtrip",
    );

    assert_eq!(blocker.code, "source-to-binary-roundtrip-evidence-missing");
    assert_eq!(blocker.stage, "targo-trust::convert-release-gate");
    assert_eq!(blocker.feature, "source-to-binary-roundtrip");
    assert!(blocker.detail.contains("Rust compile-back artifact digest binding not accepted"));
    for required in [
        "compile-back-artifact-digests-bound",
        "compile-back-lifted-binary-trust_ir-bound",
        "compile-back-reconstructed-trust_ir-sha256",
        "compile-back-root-artifact-sha256",
        "compile-back-selected-image-sha256",
        "bidirectional_trust_ir_refinement",
    ] {
        assert!(
            blocker.evidence_required.iter().any(|evidence| evidence == required),
            "missing {required} in {:?}",
            blocker.evidence_required
        );
    }
}

#[test]
fn test_convert_decompile_json_gate_surfaces_replay_artifact_digest_identity_blocker() {
    let (dispatch, canonical_vc_bytes) = importable_binary_dispatch("replay-digest:vc0");
    let checked_artifact = checked_binary_artifact_for_dispatch(&dispatch, &canonical_vc_bytes);
    let root = temp_test_dir("decompile-convert-replay-digest");
    let path = persist_checked_certificate_artifact(&root, &checked_artifact)
        .expect("checked artifact should persist");
    let loader = load_convert_checked_certificate_loader_report(&[path.display().to_string()], &[])
        .expect("convert checked-certificate metadata loader should parse artifact rows");
    let replay_digest_blocker = TargetValidationBlocker {
        target: trust_types::DecompileTarget::TrustCg,
        function: Some("entry".to_string()),
        stage: "binary-release-gate".to_string(),
        feature: "replay-artifact-digest-identity".to_string(),
        reason: "normalized witness omitted root binary artifact digest; exact binary artifact digest identity is required before machine replay can satisfy proof-grade evidence"
            .to_string(),
        diagnostics: vec![
            "required-evidence=binary_artifact_digest_identity".to_string(),
            "required-evidence=machine_replay_transcript".to_string(),
        ],
        ..Default::default()
    };
    let mut report =
        proof_grade_convert_report_with_source_provenance(exact_binary_source_provenance_summary());
    report.output_content = Some(r#"{"functions":[{"name":"entry"}],"typed":true}"#.into());
    report.target_validation_blockers = vec![replay_digest_blocker];

    let gate = build_convert_cli_gate_with_loader(&report, loader.clone());
    assert!(!gate.accepted);
    assert_eq!(gate.status, "rejected");
    assert!(
        gate.blockers.iter().any(|blocker| {
            blocker.contains("replay-artifact-digest-identity")
                && blocker.contains("root binary artifact digest")
        }),
        "{:?}",
        gate.blockers
    );
    assert!(
        gate.checked_certificate_evidence.proof_grade_release_blockers.iter().any(|blocker| {
            blocker.code == "replay-artifact-digest-identity-missing"
                && blocker.feature == "replay-artifact-digest-identity"
                && blocker
                    .evidence_required
                    .contains(&"binary_artifact_digest_identity".to_string())
                && blocker.evidence_required.contains(&"machine_replay_transcript".to_string())
        }),
        "{:?}",
        gate.checked_certificate_evidence.proof_grade_release_blockers
    );

    let decompile_json =
        serialize_decompile_json_with_checked_certificate_loader(&report, loader.clone())
            .expect("serialize decompile JSON with replay digest blocker");
    let decompile_value: serde_json::Value =
        serde_json::from_str(&decompile_json).expect("parse decompile JSON");
    assert!(
        decompile_value["artifact_gate"]["validation_blockers"]
            .as_array()
            .expect("decompile artifact gate validation blockers")
            .iter()
            .any(|blocker| blocker
                .as_str()
                .expect("validation blocker")
                .contains("replay-artifact-digest-identity"))
    );
    assert!(
        decompile_value["checked_certificate_readback"]["proof_grade_release_blockers"]
            .as_array()
            .expect("decompile release blockers")
            .iter()
            .any(|blocker| {
                blocker["code"] == "replay-artifact-digest-identity-missing"
                    && blocker["evidence_required"]
                        .as_array()
                        .expect("evidence required")
                        .iter()
                        .any(|evidence| {
                            evidence.as_str() == Some("binary_artifact_digest_identity")
                        })
            }),
        "{decompile_value}"
    );

    let convert_json = serialize_convert_json_with_checked_certificate_loader(&report, loader)
        .expect("serialize convert JSON with replay digest blocker");
    let convert_value: serde_json::Value =
        serde_json::from_str(&convert_json).expect("parse convert JSON");
    assert!(
        convert_value["conversion_gate"]["validation_blockers"]
            .as_array()
            .expect("convert validation blockers")
            .iter()
            .any(|blocker| blocker
                .as_str()
                .expect("validation blocker")
                .contains("root binary artifact digest"))
    );
    assert!(
        convert_value["conversion_gate"]["checked_certificate_evidence"]
            ["proof_grade_release_blockers"]
            .as_array()
            .expect("convert release blockers")
            .iter()
            .any(|blocker| {
                blocker["code"] == "replay-artifact-digest-identity-missing"
                    && blocker["feature"] == "replay-artifact-digest-identity"
            }),
        "{convert_value}"
    );

    let terminal = render_convert_terminal(&report);
    assert!(terminal.contains("conversion gate: rejected\n"));
    assert!(terminal.contains("replay-artifact-digest-identity"));
    assert!(terminal.contains("root binary artifact digest"));

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_convert_decompile_json_release_gate_surfaces_all_proof_grade_blocker_classes() {
    let (dispatch, canonical_vc_bytes) = importable_binary_dispatch("all-blockers:vc0");
    let checked_artifact = checked_binary_artifact_for_dispatch(&dispatch, &canonical_vc_bytes);
    let root = temp_test_dir("decompile-convert-all-release-blockers");
    let path = persist_checked_certificate_artifact(&root, &checked_artifact)
        .expect("checked artifact should persist");
    let loader = load_convert_checked_certificate_loader_report(&[path.display().to_string()], &[])
        .expect("convert checked-certificate metadata loader should parse artifact rows");

    let mut report =
        proof_grade_convert_report_with_source_provenance(exact_binary_source_provenance_summary());
    report.unsupported = 1;
    report.unsupported_items =
        vec!["binary-release-gate: unsupported ledger entry remains".to_string()];
    report.preserved_symbolic_formulas = vec![trust_cg_preserved_symbolic_formula()];
    report.target_validation_blockers = vec![
        TargetValidationBlocker {
            target: trust_types::DecompileTarget::TrustCg,
            function: Some("entry".to_string()),
            stage: "binary-release-gate".to_string(),
            feature: "selected-image-replay-identity".to_string(),
            reason: "selected image digest/range is missing from replay identity; selected-image replay must match the decompiled binary slice".to_string(),
            diagnostics: vec![
                "required-evidence=selected_image_digest_identity".to_string(),
                "required-evidence=machine_replay_transcript".to_string(),
            ],
            ..Default::default()
        },
        TargetValidationBlocker {
            target: trust_types::DecompileTarget::TrustCg,
            function: Some("entry".to_string()),
            stage: "binary-release-gate".to_string(),
            feature: "exact-source-provenance".to_string(),
            reason: "exact provenance handoff was not consumed by the trust_cg target".to_string(),
            diagnostics: vec!["required-evidence=source_provenance_handoff".to_string()],
            ..Default::default()
        },
        TargetValidationBlocker {
            target: trust_types::DecompileTarget::TrustCg,
            function: Some("entry".to_string()),
            stage: "binary-release-gate".to_string(),
            feature: "target-semantic-validation".to_string(),
            reason: "trust-cg target semantics have not consumed replay metadata or emitted obligations".to_string(),
            diagnostics: vec!["required-evidence=target_semantic_validation".to_string()],
            ..Default::default()
        },
        TargetValidationBlocker {
            target: trust_types::DecompileTarget::TrustCg,
            function: Some("symbolic_blocked".to_string()),
            stage: "binary-release-gate".to_string(),
            feature: "symbolic-formula-preservation".to_string(),
            reason: "symbolic formula preservation is audit-only until the trust_cg target consumes the preserved formula".to_string(),
            diagnostics: vec![
                "required-evidence=preserved_symbolic_formula".to_string(),
                "required-evidence=target_semantic_validation".to_string(),
            ],
            ..Default::default()
        },
        TargetValidationBlocker {
            target: trust_types::DecompileTarget::TrustCg,
            stage: "binary-release-gate".to_string(),
            feature: "supported-ledger".to_string(),
            reason: "unsupported binary/decompilation ledger entries remain".to_string(),
            diagnostics: vec!["required-evidence=empty_unsupported_ledger".to_string()],
            ..Default::default()
        },
    ];

    let gate = build_convert_cli_gate_with_loader(&report, loader.clone());
    assert!(!gate.accepted);
    assert_eq!(gate.status, "rejected");
    assert_eq!(gate.checked_certificate_evidence.checked_certificate_readback_rows, 1);
    assert_eq!(gate.checked_certificate_evidence.production_checked_certificates, 0);
    assert_eq!(gate.checked_certificate_evidence.missing_production_checked_certificates, 1);

    let release_codes = gate
        .checked_certificate_evidence
        .proof_grade_release_blockers
        .iter()
        .map(|blocker| blocker.code.as_str())
        .collect::<BTreeSet<_>>();
    for required_code in [
        "checked-certificate-production-evidence-missing",
        "checked-certificate-manifest-identity-missing",
        "checked-certificate-source-backpropagation-gate-identity-missing",
        "replay-digest-identity-missing",
        "selected-image-replay-identity-missing",
        "exact-source-provenance-missing",
        "target-semantic-validation-missing",
        "unsupported-ledger-nonempty",
        "symbolic-formula-preservation-not-consumed",
    ] {
        assert!(
            release_codes.contains(required_code),
            "missing {required_code} in {:?}",
            gate.checked_certificate_evidence.proof_grade_release_blockers
        );
    }

    for json in [
        serialize_decompile_json_with_checked_certificate_loader(&report, loader.clone())
            .expect("serialize decompile JSON"),
        serialize_convert_json_with_checked_certificate_loader(&report, loader)
            .expect("serialize convert JSON"),
    ] {
        let value: serde_json::Value = serde_json::from_str(&json).expect("parse JSON gate");
        let gate_key = if value.get("conversion_gate").is_some() {
            "conversion_gate"
        } else {
            "artifact_gate"
        };
        assert_eq!(value[gate_key]["accepted"], false);
        assert_eq!(value[gate_key]["status"], "rejected");
        assert_eq!(value["checked_certificate_readback"]["checked_certificate_readback_rows"], 1);
        assert_eq!(value["checked_certificate_readback"]["production_checked_certificates"], 0);
        assert_eq!(
            value["checked_certificate_readback"]["missing_production_checked_certificates"],
            1
        );
        assert_eq!(
            value["checked_certificate_readback"]["readback_records"][0]["certificate_sha256"],
            checked_artifact.certificate_sha256
        );
        assert_eq!(
            value["checked_certificate_readback"]["readback_row_details"][0]["proof_grade_release_status"],
            "rejected"
        );
        assert_eq!(value["source_provenance"]["status"], "exact");
        assert_eq!(value["unsupported"], 1);
        assert!(
            value["preserved_symbolic_formulas"]
                .as_array()
                .expect("preserved formulas")
                .iter()
                .any(|formula| formula["function"] == "symbolic_blocked")
        );

        let release_blockers =
            value["checked_certificate_readback"]["proof_grade_release_blockers"]
                .as_array()
                .expect("release blockers");
        for required_code in [
            "checked-certificate-production-evidence-missing",
            "checked-certificate-manifest-identity-missing",
            "checked-certificate-source-backpropagation-gate-identity-missing",
            "replay-digest-identity-missing",
            "selected-image-replay-identity-missing",
            "exact-source-provenance-missing",
            "target-semantic-validation-missing",
            "unsupported-ledger-nonempty",
            "symbolic-formula-preservation-not-consumed",
        ] {
            assert!(
                release_blockers.iter().any(|blocker| blocker["code"] == required_code),
                "missing {required_code} in {value}"
            );
        }
    }

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_cli_json_release_gate_rejects_proof_grade_with_stale_binary_prerequisites() {
    let (producer_dispatch, canonical_vc_bytes) = importable_binary_dispatch("json-contract:vc0");
    let checked_artifact =
        checked_binary_artifact_for_dispatch(&producer_dispatch, &canonical_vc_bytes);
    let root = temp_test_dir("cli-release-gate-json-contract");
    let path = persist_checked_certificate_artifact(&root, &checked_artifact)
        .expect("checked artifact should persist");

    let (current_dispatch, _) = importable_binary_dispatch("json-contract-current:vc0");
    let mut proof_evidence =
        VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![current_dispatch]);
    let import_report = proof_evidence
        .load_and_import_checked_certificate_artifacts([path.as_path()])
        .expect("audit-only checked artifact should import");
    let mut verify_report = build_verify_binary_report(
        Path::new("fixtures/tiny.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 1 }],
            }],
            solver_results: Vec::new(),
            proof_evidence,
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );
    verify_report.checked_certificate_import = Some(import_report);
    verify_report.trust_level = "proof_grade".into();

    let verify_json =
        serialize_verify_binary_json(&verify_report).expect("serialize verify-binary JSON");
    let verify_value: serde_json::Value =
        serde_json::from_str(&verify_json).expect("parse verify-binary JSON");
    let verify_gate = &verify_value["proof_grade_gate"];
    assert_eq!(verify_gate["final_trust_level"], "proof_grade");
    assert_eq!(verify_gate["accepted"], false);
    assert_eq!(verify_gate["status"], "rejected");
    assert_eq!(verify_gate["checked_certificates_for_all_required_vcs"], true);
    assert_eq!(verify_gate["checked_certificate_readback_for_all_required_vcs"], false);
    assert_eq!(verify_gate["replay_attestation_for_all_required_vcs"], false);
    assert_eq!(verify_gate["source_backpropagation_handoff_for_all_required_vcs"], false);
    assert_eq!(verify_value["checked_certificate_evidence"]["status"], "accepted");
    let verify_blocker_codes = verify_gate["blockers"]
        .as_array()
        .expect("verify proof-grade blockers")
        .iter()
        .map(|blocker| blocker["code"].as_str().expect("verify blocker code").to_string())
        .collect::<BTreeSet<_>>();
    for required_code in [
        "checked-certificate-readback-missing",
        "replay-attestation-missing",
        "checked-certificate-source-backpropagation-handoff-missing",
    ] {
        assert!(
            verify_blocker_codes.contains(required_code),
            "missing {required_code} in {verify_gate}"
        );
    }

    let loader = load_convert_checked_certificate_loader_report(&[path.display().to_string()], &[])
        .expect("convert checked-certificate metadata loader should parse artifact rows");
    let mut report =
        proof_grade_convert_report_with_source_provenance(exact_binary_source_provenance_summary());
    report.target_validation_blockers = vec![trust_cg_refinement_blocker()];
    report.unsupported = 1;
    report.unsupported_items =
        vec!["binary-release-gate: unsupported ledger entry remains".to_string()];

    for (gate_key, json) in [
        (
            "artifact_gate",
            serialize_decompile_json_with_checked_certificate_loader(&report, loader.clone())
                .expect("serialize decompile JSON"),
        ),
        (
            "conversion_gate",
            serialize_convert_json_with_checked_certificate_loader(&report, loader)
                .expect("serialize convert JSON"),
        ),
    ] {
        let value: serde_json::Value = serde_json::from_str(&json).expect("parse JSON gate");
        assert_eq!(value[gate_key]["accepted"], false, "{value}");
        assert_eq!(value[gate_key]["status"], "rejected", "{value}");
        assert_eq!(value[gate_key]["proof_grade_artifact"], true, "{value}");
        assert_eq!(value["checked_certificate_readback"]["proof_grade_release_accepted"], false);
        assert_eq!(
            value["checked_certificate_readback"]["readback_records"][0]["replay_digest_identity"]
                ["status"],
            "rejected"
        );
        assert!(
            value["target_evidence"]["blockers"]
                .as_array()
                .expect("target evidence blockers")
                .iter()
                .any(|blocker| blocker["code"] == "missing-refinement-metadata"),
            "{value}"
        );
        let release_codes = value["checked_certificate_readback"]["proof_grade_release_blockers"]
            .as_array()
            .expect("release blockers")
            .iter()
            .map(|blocker| blocker["code"].as_str().expect("release blocker code").to_string())
            .collect::<BTreeSet<_>>();
        for required_code in [
            "checked-certificate-production-evidence-missing",
            "checked-certificate-manifest-identity-missing",
            "checked-certificate-source-backpropagation-gate-identity-missing",
            "replay-digest-identity-missing",
            "target-refinement-consumer-missing",
            "unsupported-ledger-nonempty",
        ] {
            assert!(release_codes.contains(required_code), "missing {required_code} in {value}");
        }
    }

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_convert_trust_cg_json_surfaces_checked_certificate_loader_failure_and_typed_output() {
    let loader = convert_checked_certificate_loader_failure_report(
        &["missing-cert.json".to_string()],
        &["missing-manifest.json".to_string()],
        "checked certificate manifest was not readable",
    );
    let mut report =
        proof_grade_convert_report_with_source_provenance(exact_binary_source_provenance_summary());
    report.output_content =
        Some(r#"{"functions":[{"name":"entry","return_type":"i32"}],"typed":true}"#.into());

    let json = serialize_convert_json_with_checked_certificate_loader(&report, loader)
        .expect("serialize convert JSON with loader failure");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse convert JSON");

    assert_eq!(value["trust_cg_output"]["functions"][0]["name"], "entry");
    assert_eq!(value["trust_cg_output"]["functions"][0]["return_type"], "i32");
    assert_eq!(value["trust_cg_output"]["typed"], true);
    let evidence = &value["conversion_gate"]["checked_certificate_evidence"];
    assert_eq!(evidence["status"], "blocked");
    assert_eq!(evidence["loader"]["status"], "load_failed");
    assert_eq!(evidence["loader"]["requested_artifacts"], 1);
    assert_eq!(evidence["loader"]["requested_manifests"], 1);
    assert_eq!(evidence["loader"]["blocker"]["code"], "convert-checked-certificate-load-failed");
    assert_eq!(evidence["checked_artifact_rows"], 0);
    assert_eq!(evidence["accepted_certificate_rows"], 0);
    assert_eq!(evidence["accepted_certificates"].as_array().unwrap().len(), 0);
    assert!(
        evidence["blockers"]
            .as_array()
            .expect("convert checked certificate blockers")
            .iter()
            .any(|blocker| blocker["code"] == "convert-checked-certificate-load-failed")
    );
    assert_eq!(value["conversion_gate"]["accepted"], false);
}

#[test]
fn test_convert_json_blocks_proof_grade_runtime_binary_source_provenance_failures() {
    let cases = vec![
        (
            "missing-file",
            BinarySourceProvenanceSummary {
                status: "unavailable".into(),
                exact_mapping_count: 0,
                ambiguous_mapping_count: 0,
                diagnostics: vec![
                    "runtime binary-source provenance artifact missing file: fixtures/missing-provenance.json"
                        .into(),
                ],
                source_backpropagation_allowed: true,
            },
            vec!["missing file", "missing-provenance.json"],
        ),
        (
            "wrong-kind",
            BinarySourceProvenanceSummary {
                status: "unsupported".into(),
                exact_mapping_count: 0,
                ambiguous_mapping_count: 0,
                diagnostics: vec![
                    "runtime binary-source provenance artifact kind `checked_binary_certificate` is not `binary_source_provenance`"
                        .into(),
                ],
                source_backpropagation_allowed: true,
            },
            vec!["artifact kind", "checked_binary_certificate", "binary_source_provenance"],
        ),
        (
            "duplicate-mapping",
            BinarySourceProvenanceSummary {
                status: "exact".into(),
                exact_mapping_count: 2,
                ambiguous_mapping_count: 1,
                diagnostics: vec![
                    "runtime binary-source provenance artifact has duplicate mapping for address 0x401010"
                        .into(),
                ],
                source_backpropagation_allowed: true,
            },
            vec!["duplicate mapping", "0x401010"],
        ),
        (
            "mismatched-exact-span",
            BinarySourceProvenanceSummary {
                status: "exact".into(),
                exact_mapping_count: 1,
                ambiguous_mapping_count: 0,
                diagnostics: vec![
                    "runtime binary-source provenance artifact exact span mismatch for address 0x401010: artifact points at src/lib.rs:9:1 but runtime failure is src/lib.rs:10:1"
                        .into(),
                ],
                source_backpropagation_allowed: false,
            },
            vec!["exact span mismatch", "src/lib.rs:10:1"],
        ),
    ];

    for (name, source_provenance, expected_fragments) in cases {
        let report = DecompileReport {
            binary: format!("{name}.bin"),
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            selection: "address".into(),
            entry: Some("0x401000".into()),
            binary_entry: Some("0x401000".into()),
            source_provenance,
            strict: true,
            target: DecompileTarget::Rust,
            status: BinaryLiftStatus::Ok,
            output_kind: Some("rust".into()),
            output_trust_level: "proof_grade".into(),
            output_validation: "translation_validated".into(),
            validation_note: "translation validation accepted".into(),
            output_content: Some("fn main() {}".into()),
            production_proof_grade_evidence: None,
            binary_evidence: DecompileBinaryEvidenceReport::default(),
            target_validation_blockers: Vec::new(),
            preserved_symbolic_formulas: Vec::new(),
            functions_decompiled: 1,
            blocks: 1,
            instructions: 1,
            statements: 1,
            memory_facts: 0,
            unsupported: 0,
            failures: 0,
            functions: Vec::new(),
            unsupported_items: Vec::new(),
            failure_items: Vec::new(),
        };

        let gate = build_convert_cli_gate(&report);
        assert!(!gate.accepted, "{name} should not proof-grade");
        assert_eq!(gate.status, "rejected");
        assert!(gate.proof_grade_artifact);
        assert!(
            gate.validation_blockers
                .iter()
                .any(|blocker| blocker.contains("binary source provenance blocked proof-grade")),
            "{name} should expose a source provenance blocker: {:?}",
            gate.validation_blockers
        );
        for fragment in expected_fragments {
            assert!(gate.reason.contains(fragment), "{name} missing `{fragment}`: {}", gate.reason);
        }

        let json = serialize_convert_json(&report).expect("serialize convert JSON");
        let value: serde_json::Value = serde_json::from_str(&json).expect("parse convert JSON");
        assert_eq!(value["conversion_gate"]["accepted"], false, "{name}");
        assert_eq!(value["conversion_gate"]["status"], "rejected", "{name}");
        assert_eq!(value["conversion_gate"]["proof_grade_artifact"], true, "{name}");
        assert!(
            value["conversion_gate"]["blockers"]
                .as_array()
                .expect("conversion blockers")
                .iter()
                .any(|blocker| blocker
                    .as_str()
                    .expect("blocker string")
                    .contains("binary source provenance blocked proof-grade")),
            "{name} should serialize provenance blockers"
        );
    }
}

#[test]
fn test_convert_rejects_proof_grade_label_until_all_binary_release_gate_conditions_hold() {
    let gate_blockers = vec![
        TargetValidationBlocker {
            target: trust_types::DecompileTarget::TrustCg,
            stage: "binary-release-gate".into(),
            feature: "checked-certificate-coverage".into(),
            reason: "checked certificates are missing for required binary VCs".into(),
            ..Default::default()
        },
        TargetValidationBlocker {
            target: trust_types::DecompileTarget::TrustCg,
            stage: "binary-release-gate".into(),
            feature: "exact-machine-replay".into(),
            reason: "exact replay has not covered every required binary VC".into(),
            ..Default::default()
        },
        TargetValidationBlocker {
            target: trust_types::DecompileTarget::TrustCg,
            stage: "binary-release-gate".into(),
            feature: "exact-source-provenance".into(),
            reason:
                "exact debug/source provenance is not available for proof-grade backpropagation"
                    .into(),
            ..Default::default()
        },
        TargetValidationBlocker {
            target: trust_types::DecompileTarget::TrustCg,
            stage: "binary-release-gate".into(),
            feature: "supported-ledger".into(),
            reason: "unsupported binary/decompilation ledger entries remain".into(),
            ..Default::default()
        },
    ];
    let report = DecompileReport {
        binary: "demo.bin".into(),
        format: Some("ELF".into()),
        architecture: Some("x86_64".into()),
        selection: "address".into(),
        entry: Some("0x401000".into()),
        binary_entry: Some("0x401000".into()),
        source_provenance: BinarySourceProvenanceSummary::default(),
        strict: true,
        target: DecompileTarget::TrustCg,
        status: BinaryLiftStatus::Ok,
        output_kind: Some("trust_cg_text".into()),
        output_trust_level: "proof_grade".into(),
        output_validation: "translation_validated".into(),
        validation_note: "synthetic target validation accepted".into(),
        output_content: Some("{\"functions\":[]}".into()),
        production_proof_grade_evidence: None,
        binary_evidence: DecompileBinaryEvidenceReport::default(),
        target_validation_blockers: gate_blockers,
        preserved_symbolic_formulas: Vec::new(),
        functions_decompiled: 1,
        blocks: 1,
        instructions: 1,
        statements: 1,
        memory_facts: 0,
        unsupported: 0,
        failures: 0,
        functions: Vec::new(),
        unsupported_items: Vec::new(),
        failure_items: Vec::new(),
    };

    let gate = build_convert_cli_gate(&report);
    assert!(!gate.accepted);
    assert_eq!(gate.status, "rejected");
    assert!(gate.proof_grade_artifact);
    assert_eq!(gate.validation, "translation_validated");
    for required_blocker in [
        "checked-certificate-coverage",
        "exact-machine-replay",
        "exact-source-provenance",
        "supported-ledger",
    ] {
        assert!(
            gate.blockers.iter().any(|blocker| blocker.contains(required_blocker)),
            "missing {required_blocker} in {:?}",
            gate.blockers
        );
    }

    let rendered = render_convert_terminal(&report);
    assert!(rendered.contains("conversion gate: rejected\n"));
    assert!(rendered.contains(
        "conversion gate detail: target=trust-cg proof_grade_artifact=true validation=translation_validated"
    ));
    assert!(rendered.contains("checked-certificate-coverage"));
    assert!(rendered.contains("exact-machine-replay"));
    assert!(rendered.contains("exact-source-provenance"));
    assert!(rendered.contains("supported-ledger"));

    let json = serialize_convert_json(&report).expect("serialize convert JSON");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse convert JSON");
    assert_eq!(value["conversion_gate"]["accepted"], false);
    assert_eq!(value["conversion_gate"]["proof_grade_artifact"], true);
    let blockers = value["conversion_gate"]["blockers"].as_array().expect("conversion blockers");
    assert_eq!(blockers.len(), 5);
    assert!(
        blockers.iter().any(|blocker| {
            blocker.as_str().expect("blocker").contains("exact-source-provenance")
        })
    );
    assert!(blockers.iter().any(|blocker| {
        blocker.as_str().expect("blocker").contains("binary source provenance blocked proof-grade")
    }));
}

#[test]
fn test_convert_report_surfaces_symbolic_formula_metadata_in_json_and_terminal() {
    let report = DecompileReport {
        binary: "demo.bin".into(),
        format: Some("ELF".into()),
        architecture: Some("x86_64".into()),
        selection: "address".into(),
        entry: Some("0x401000".into()),
        binary_entry: Some("0x401000".into()),
        source_provenance: BinarySourceProvenanceSummary::default(),
        strict: true,
        target: DecompileTarget::TrustCg,
        status: BinaryLiftStatus::Ok,
        output_kind: Some("trust_cg_text".into()),
        output_trust_level: "rejected".into(),
        output_validation: "inspectable_rejected".into(),
        validation_note:
            "trust-cg structural validation succeeded, but target validation remains rejected"
                .into(),
        output_content: Some("{\"functions\":[]}".into()),
        production_proof_grade_evidence: None,
        binary_evidence: DecompileBinaryEvidenceReport::default(),
        target_validation_blockers: vec![trust_cg_symbolic_formula_blocker()],
        preserved_symbolic_formulas: vec![trust_cg_preserved_symbolic_formula()],
        functions_decompiled: 1,
        blocks: 1,
        instructions: 1,
        statements: 1,
        memory_facts: 0,
        unsupported: 0,
        failures: 0,
        functions: Vec::new(),
        unsupported_items: Vec::new(),
        failure_items: Vec::new(),
    };

    let rendered = render_convert_terminal(&report);
    assert!(rendered.contains("target validation blockers:\n"));
    assert!(rendered.contains("symbolic-formula-proof-semantics function `symbolic_blocked`"));
    assert!(rendered.contains("preserved symbolic formulas:\n"));
    assert!(rendered.contains("trust-cg function `symbolic_blocked` bb0 stmt0 statement.assign"));
    assert!(rendered.contains("Var(\"lifted_rax\", Int)"));
    assert!(rendered.contains("conversion validation blockers:\n"));
    assert!(rendered.contains("target proof semantics are not discharged"));

    let gate = build_convert_cli_gate(&report);
    assert!(!gate.accepted);
    assert!(gate.validation_blockers.iter().any(|blocker| {
        blocker.contains("symbolic-formula-proof-semantics") && blocker.contains("symbolic_blocked")
    }));

    let json = serialize_convert_json(&report).expect("serialize convert JSON");
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse convert JSON");
    assert!(
        value["preserved_symbolic_formulas"]
            .as_array()
            .expect("preserved symbolic formulas")
            .iter()
            .any(|formula| formula["target"] == "TrustCg"
                && formula["function"] == "symbolic_blocked")
    );
    assert!(
        value["conversion_gate"]["validation_blockers"]
            .as_array()
            .expect("conversion validation blockers")
            .iter()
            .any(|blocker| blocker
                .as_str()
                .expect("validation blocker")
                .contains("symbolic-formula-proof-semantics"))
    );
}

#[test]
fn test_decompile_rust_report_labels_exploratory_output() {
    let report = DecompileReport {
        binary: "demo.bin".into(),
        format: Some("ELF".into()),
        architecture: Some("x86_64".into()),
        selection: "address".into(),
        entry: Some("0x401000".into()),
        binary_entry: Some("0x401000".into()),
        source_provenance: BinarySourceProvenanceSummary::default(),
        strict: true,
        target: DecompileTarget::Rust,
        status: BinaryLiftStatus::Ok,
        output_kind: Some("rust_skeleton".into()),
        output_trust_level: "exploratory".into(),
        output_validation: "exploratory_not_validated".into(),
        validation_note:
            "Rust output is exploratory/not validated; no reconstruction validation was performed"
                .into(),
        output_content: Some("// Exploratory partial Rust skeleton".into()),
        production_proof_grade_evidence: None,
        binary_evidence: DecompileBinaryEvidenceReport::default(),
        target_validation_blockers: Vec::new(),
        preserved_symbolic_formulas: Vec::new(),
        functions_decompiled: 1,
        blocks: 2,
        instructions: 4,
        statements: 7,
        memory_facts: 1,
        unsupported: 0,
        failures: 0,
        functions: vec![DecompileFunctionReport {
            name: "main".into(),
            entry: "0x401000".into(),
            blocks: 2,
            instructions: 4,
            statements: 7,
            memory_facts: 1,
            unsupported: 0,
            instruction_provenance: Vec::new(),
        }],
        unsupported_items: Vec::new(),
        failure_items: Vec::new(),
    };

    assert!(!decompile_should_fail(&report));
    let rendered = render_decompile_terminal(&report);
    assert!(rendered.contains("targo trust decompile report\n"));
    assert!(rendered.contains("target: rust\n"));
    assert!(rendered.contains("output trust: exploratory\n"));
    assert!(rendered.contains("output validation: exploratory_not_validated\n"));
    assert!(rendered.contains("exploratory/not validated"));
    assert!(rendered.contains(
        "  - main @ 0x401000: blocks=2 instructions=4 statements=7 memory_facts=1 unsupported=0\n"
    ));
}

#[test]
fn test_decompile_trust_ir_report_labels_partial_without_verification_summary() {
    let report = DecompileReport {
        binary: "demo.bin".into(),
        format: Some("ELF".into()),
        architecture: Some("x86_64".into()),
        selection: "entry".into(),
        entry: None,
        binary_entry: Some("0x401000".into()),
        source_provenance: BinarySourceProvenanceSummary::default(),
        strict: false,
        target: DecompileTarget::TrustIr,
        status: BinaryLiftStatus::Incomplete,
        output_kind: Some("trust_ir_text".into()),
        output_trust_level: "partial".into(),
        output_validation: "lifted_trust_ir_partial".into(),
        validation_note:
            "TrustIr output is partial; no verification summary is attached proving full coverage"
                .into(),
        output_content: Some("binary format=ELF arch=x86_64 entry=0x401000".into()),
        production_proof_grade_evidence: None,
        binary_evidence: DecompileBinaryEvidenceReport::default(),
        target_validation_blockers: Vec::new(),
        preserved_symbolic_formulas: Vec::new(),
        functions_decompiled: 1,
        blocks: 1,
        instructions: 1,
        statements: 1,
        memory_facts: 0,
        unsupported: 1,
        failures: 0,
        functions: Vec::new(),
        unsupported_items: vec!["trust-lift @ 0x401000: unsupported opcode".into()],
        failure_items: Vec::new(),
    };

    assert!(!decompile_should_fail(&report));
    let rendered = render_decompile_terminal(&report);
    assert!(rendered.contains("target: trust_ir\n"));
    assert!(rendered.contains("output trust: partial\n"));
    assert!(rendered.contains("output validation: lifted_trust_ir_partial\n"));
    assert!(rendered.contains("no verification summary is attached proving full coverage"));
    assert!(
        rendered.contains("unsupported items:\n  - trust-lift @ 0x401000: unsupported opcode\n")
    );
}

#[test]
fn test_decompile_trust_ir_json_surfaces_checked_certificate_digest_identity_without_proof_grade() {
    let (dispatch, canonical_vc_bytes) = importable_binary_dispatch("trust_ir-digest:vc0");
    let checked_artifact = checked_binary_artifact_for_dispatch(&dispatch, &canonical_vc_bytes);
    let root = temp_test_dir("decompile-trust_ir-checked-cert-digest");
    let path = persist_checked_certificate_artifact(&root, &checked_artifact)
        .expect("checked artifact should persist");
    let loader = load_convert_checked_certificate_loader_report(&[path.display().to_string()], &[])
        .expect("convert checked-certificate metadata loader should parse artifact rows");
    let report = DecompileReport {
        binary: "demo.bin".into(),
        format: Some("ELF".into()),
        architecture: Some("x86_64".into()),
        selection: "entry".into(),
        entry: None,
        binary_entry: Some("0x401000".into()),
        source_provenance: BinarySourceProvenanceSummary::default(),
        strict: false,
        target: DecompileTarget::TrustIr,
        status: BinaryLiftStatus::Incomplete,
        output_kind: Some("trust_ir_text".into()),
        output_trust_level: "partial".into(),
        output_validation: "lifted_trust_ir_partial".into(),
        validation_note:
            "TrustIr output is partial; no verification summary is attached proving full coverage"
                .into(),
        output_content: Some("binary format=ELF arch=x86_64 entry=0x401000".into()),
        production_proof_grade_evidence: None,
        binary_evidence: DecompileBinaryEvidenceReport::default(),
        target_validation_blockers: Vec::new(),
        preserved_symbolic_formulas: Vec::new(),
        functions_decompiled: 1,
        blocks: 1,
        instructions: 1,
        statements: 1,
        memory_facts: 0,
        unsupported: 1,
        failures: 0,
        functions: Vec::new(),
        unsupported_items: vec!["trust-lift @ 0x401000: unsupported opcode".into()],
        failure_items: Vec::new(),
    };

    let json = serialize_decompile_json_with_checked_certificate_loader(&report, loader)
        .expect("serialize trust_ir decompile JSON with checked certificate identity");
    let value: serde_json::Value =
        serde_json::from_str(&json).expect("parse trust_ir decompile JSON");
    assert_eq!(value["target"], "trust_ir");
    assert_eq!(value["output_trust_level"], "partial");
    assert_eq!(value["artifact_gate"]["accepted"], false);
    assert_eq!(value["artifact_gate"]["proof_grade_artifact"], false);
    assert_eq!(value["checked_certificate_readback"]["proof_grade_release_accepted"], false);
    assert_eq!(
        value["checked_certificate_readback"]["artifacts"][0]["binary_artifact_digest_identity"]["root_artifact_digest"]
            ["value"],
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
    );
    assert_eq!(
        value["checked_certificate_readback"]["readback_records"][0]["binary_artifact_digest_identity"]
            ["selected_image"]["file_size"],
        64
    );
    assert!(
        value["checked_certificate_readback"]["readback_row_details"][0]["detail"]
            .as_str()
            .expect("readback detail")
            .contains("output is not labeled proof-grade")
    );

    let _ = std::fs::remove_dir_all(root);
}

fn trust_ir_identity_output_content(name: &str, entry: u64) -> String {
    serde_json::json!({
        "metadata": {
            "format": "Elf",
            "architecture": "x86-64",
            "byte_len": 64
        },
        "module": {
            "name": "demo.bin",
            "functions": [name]
        },
        "functions": [
            {
                "name": name,
                "entry": entry,
                "lifted": {
                    "def_path": format!("binary::{name}")
                }
            }
        ],
        "unsupported": {
            "records": []
        },
        "trust_level": "Partial"
    })
    .to_string()
}

fn trust_ir_identity_report(output_content: String, function_entry: u64) -> DecompileReport {
    DecompileReport {
        binary: "demo.bin".into(),
        format: Some("ELF".into()),
        architecture: Some("x86-64".into()),
        selection: "address".into(),
        entry: Some(format!("0x{function_entry:x}")),
        binary_entry: Some(format!("0x{function_entry:x}")),
        source_provenance: BinarySourceProvenanceSummary::default(),
        strict: true,
        target: DecompileTarget::TrustIr,
        status: BinaryLiftStatus::Ok,
        output_kind: Some("trust_ir_json".into()),
        output_trust_level: "partial".into(),
        output_validation: "lifted_trust_ir_partial".into(),
        validation_note:
            "TrustIr output is partial; no verification summary is attached proving full coverage"
                .into(),
        output_content: Some(output_content),
        production_proof_grade_evidence: None,
        binary_evidence: DecompileBinaryEvidenceReport::default(),
        target_validation_blockers: Vec::new(),
        preserved_symbolic_formulas: Vec::new(),
        functions_decompiled: 1,
        blocks: 1,
        instructions: 1,
        statements: 1,
        memory_facts: 0,
        unsupported: 0,
        failures: 0,
        functions: vec![DecompileFunctionReport {
            name: "entry".into(),
            entry: format!("0x{function_entry:x}"),
            blocks: 1,
            instructions: 1,
            statements: 1,
            memory_facts: 0,
            unsupported: 0,
            instruction_provenance: Vec::new(),
        }],
        unsupported_items: Vec::new(),
        failure_items: Vec::new(),
    }
}

#[test]
fn test_decompile_trust_ir_json_emits_content_addressed_target_consumer_evidence() {
    let output_content = trust_ir_identity_output_content("entry", 0x401000);
    let expected_output = format!("trust_ir-json:sha256:{}", trust_types::digest::stable_sha256_hex(output_content.as_bytes()));
    let report = trust_ir_identity_report(output_content, 0x401000);

    let json = serialize_decompile_json_with_checked_certificate_loader(
        &report,
        super::convert_checked_certificate_loader_not_requested(),
    )
    .expect("serialize trust_ir decompile JSON with target consumer identity");
    let value: serde_json::Value =
        serde_json::from_str(&json).expect("parse trust_ir decompile JSON");
    let evidence = &value["target_proof_consumer_evidence"];
    let records = evidence["records"].as_array().expect("target proof records");
    let binding = &evidence["binding"];

    assert_eq!(evidence["target"], "trust_ir");
    assert_eq!(evidence["status"], "accepted");
    assert_eq!(evidence["target_semantics_consumed"], true);
    assert_eq!(evidence["blockers"].as_array().expect("target blockers").len(), 0);
    assert_eq!(binding["target_output"].as_str(), Some(expected_output.as_str()));
    assert_eq!(binding["status"], "accepted");
    assert_eq!(binding["target_semantics_consumed"], true);
    for kind in [
        "target_semantics",
        "target_artifact",
        "lifted_binary_trust_ir",
        "reconstruction_refinement",
    ] {
        assert!(
            records.iter().any(|record| {
                record["kind"] == kind && record["accepted"].as_bool() == Some(true)
            }),
            "missing accepted {kind} record in {evidence}"
        );
    }
    assert!(
        records.iter().any(|record| {
            record["kind"] == "target_artifact"
                && record["identifier"].as_str() == Some(expected_output.as_str())
                && record["accepted"].as_bool() == Some(true)
        }),
        "{evidence}"
    );
    assert_eq!(&value["artifact_gate"]["target_proof_consumer_evidence"], evidence);
    assert_eq!(&value["target_evidence"]["target_proof_consumer_evidence"], evidence);
    assert_eq!(value["artifact_gate"]["accepted"], false);
    assert_eq!(value["artifact_gate"]["proof_grade_artifact"], false);
    assert_eq!(value["checked_certificate_readback"]["proof_grade_release_accepted"], false);
}

#[test]
fn test_decompile_trust_ir_json_rejects_stale_target_consumer_digest() {
    let stale_output = format!("trust_ir-json:sha256:{}", "0".repeat(64));
    let output_content = serde_json::json!({
        "metadata": {
            "format": "Elf",
            "architecture": "x86-64",
            "byte_len": 64
        },
        "module": {
            "name": "demo.bin",
            "functions": ["entry"]
        },
        "functions": [
            {
                "name": "entry",
                "entry": 0x401000u64,
                "lifted": {
                    "def_path": "binary::entry"
                }
            }
        ],
        "unsupported": {
            "records": []
        },
        "trust_level": "Partial",
        "target_proof_consumer_evidence": {
            "target": "trust_ir",
            "status": "accepted",
            "target_semantics_consumed": true,
            "records": [
                {
                    "kind": "target_semantics",
                    "identifier": "trust_ir-identity-consumer",
                    "accepted": true,
                    "detail": "stale accepted evidence"
                },
                {
                    "kind": "target_artifact",
                    "identifier": stale_output,
                    "accepted": true,
                    "detail": "stale target artifact digest"
                }
            ],
            "binding": {
                "target": "trust_ir",
                "target_output": stale_output,
                "status": "accepted",
                "target_semantics_consumed": true,
                "inputs": [
                    {
                        "kind": "target_artifact",
                        "identifier": stale_output,
                        "canonical_source": "targo_trust.decompile.output_content",
                        "target_output": stale_output,
                        "consumed_by_target_semantics": true,
                        "detail": "stale target artifact digest"
                    }
                ],
                "blockers": []
            },
            "blockers": []
        }
    })
    .to_string();
    let report = trust_ir_identity_report(output_content, 0x401000);

    let json = serialize_decompile_json_with_checked_certificate_loader(
        &report,
        super::convert_checked_certificate_loader_not_requested(),
    )
    .expect("serialize trust_ir decompile JSON with stale target consumer identity");
    let value: serde_json::Value =
        serde_json::from_str(&json).expect("parse trust_ir decompile JSON");
    let evidence = &value["target_proof_consumer_evidence"];

    assert_eq!(evidence["target"], "trust_ir");
    assert_eq!(evidence["status"], "rejected");
    assert_eq!(evidence["target_semantics_consumed"], false);
    assert!(
        evidence["blockers"]
            .as_array()
            .expect("target blockers")
            .iter()
            .any(|blocker| blocker["code"] == "trust_ir-target-output-digest-mismatch"),
        "{evidence}"
    );
    assert_eq!(value["artifact_gate"]["accepted"], false);
}

#[test]
fn test_decompile_trust_ir_json_rejects_wrong_target_consumer_evidence() {
    let output_content = serde_json::json!({
        "metadata": {
            "format": "Elf",
            "architecture": "x86-64",
            "byte_len": 64
        },
        "module": {
            "name": "demo.bin",
            "functions": ["entry"]
        },
        "functions": [
            {
                "name": "entry",
                "entry": 0x401000u64,
                "lifted": {
                    "def_path": "binary::entry"
                }
            }
        ],
        "unsupported": {
            "records": []
        },
        "trust_level": "Partial",
        "target_proof_consumer_evidence": {
            "target": "wasm",
            "status": "accepted",
            "target_semantics_consumed": true,
            "records": [],
            "binding": null,
            "blockers": []
        }
    })
    .to_string();
    let report = trust_ir_identity_report(output_content, 0x401000);

    let json = serialize_decompile_json_with_checked_certificate_loader(
        &report,
        super::convert_checked_certificate_loader_not_requested(),
    )
    .expect("serialize trust_ir decompile JSON with wrong target consumer evidence");
    let value: serde_json::Value =
        serde_json::from_str(&json).expect("parse trust_ir decompile JSON");
    let evidence = &value["target_proof_consumer_evidence"];

    assert_eq!(evidence["target"], "wasm");
    assert_eq!(evidence["status"], "rejected");
    assert_eq!(evidence["target_semantics_consumed"], false);
    assert!(
        evidence["blockers"]
            .as_array()
            .expect("target blockers")
            .iter()
            .any(|blocker| blocker["code"] == "target-proof-consumer-target-mismatch"),
        "{evidence}"
    );
    assert_eq!(value["artifact_gate"]["accepted"], false);
}

#[test]
fn test_decompile_trust_ir_json_rejects_wrong_lifted_artifact_identity() {
    let output_content = trust_ir_identity_output_content("entry", 0x401001);
    let report = trust_ir_identity_report(output_content, 0x401000);

    let json = serialize_decompile_json_with_checked_certificate_loader(
        &report,
        super::convert_checked_certificate_loader_not_requested(),
    )
    .expect("serialize trust_ir decompile JSON with mismatched lifted artifact identity");
    let value: serde_json::Value =
        serde_json::from_str(&json).expect("parse trust_ir decompile JSON");
    let evidence = &value["target_proof_consumer_evidence"];

    assert_eq!(evidence["target"], "trust_ir");
    assert_eq!(evidence["status"], "rejected");
    assert_eq!(evidence["target_semantics_consumed"], false);
    assert!(
        evidence["blockers"]
            .as_array()
            .expect("target blockers")
            .iter()
            .any(|blocker| blocker["code"] == "trust_ir-lifted-artifact-mismatch"),
        "{evidence}"
    );
    assert!(
        evidence["records"].as_array().expect("target records").iter().any(|record| {
            record["kind"] == "lifted_binary_trust_ir"
                && record["accepted"].as_bool() == Some(false)
        }),
        "{evidence}"
    );
    assert_eq!(value["artifact_gate"]["accepted"], false);
}

#[test]
fn test_parse_exploit_find_target_args() {
    let args: Vec<String> =
        vec!["demo.bin".into(), "--target".into(), "lifter".into(), "--json".into()];
    let result = parse_exploit_find_args(&args).expect("should parse exploit-find args");

    assert_eq!(result.input, "demo.bin");
    assert_eq!(result.target, ExploitFindTarget::Lifter);
    assert_eq!(result.format, OutputFormat::Json);
    assert!(result.entry.is_none());
    assert!(!result.all_functions);
    assert!(result.strict);
    assert_eq!(ExploitFindTarget::from_str("compiler").unwrap(), ExploitFindTarget::Compiler);
    assert_eq!(ExploitFindTarget::from_str("verifier").unwrap(), ExploitFindTarget::Verifier);
    assert!(parse_exploit_find_args(&["demo.bin".into()]).is_err());
    assert!(parse_exploit_find_args(&["demo.bin".into(), "--target=html".into()]).is_err());
}

#[test]
fn test_parse_exploit_find_binary_options() {
    let args: Vec<String> = vec![
        "demo.bin".into(),
        "--target=verifier".into(),
        "--entry".into(),
        "0x401000".into(),
        "--allow-unsupported".into(),
    ];
    let result = parse_exploit_find_args(&args).expect("should parse exploit-find binary args");

    assert_eq!(result.entry.as_deref(), Some("0x401000"));
    assert!(!result.all_functions);
    assert!(!result.strict);

    let args: Vec<String> = vec!["demo.bin".into(), "--target=lifter".into(), "--all".into()];
    let result = parse_exploit_find_args(&args).expect("should parse exploit-find --all");
    assert!(result.all_functions);
}

#[test]
fn test_exploit_find_help_mentions_targets() {
    let help = exploit_find_usage_text();
    assert!(help.contains("targo trust exploit-find <input> --target compiler|verifier|lifter"));
    assert!(help.contains("[--strict|--allow-unsupported]"));
    assert!(help.contains("independent refutation"));
    assert!(help.contains("unconfirmed candidate"));
    assert!(usage_text().contains("targo trust exploit-find <input> --target"));
}

#[test]
fn test_binary_command_help_uses_current_trust_language() {
    let lift = lift_usage_text();
    assert!(lift.contains("ELF x86-64/AArch64"));
    assert!(lift.contains("AArch64 currently supports conservative lift/decompile coverage"));
    assert!(lift.contains("AArch32, i386/32-bit x86, Mach-O x86-64"));

    let verify = verify_binary_usage_text();
    assert!(verify.contains("--solver ay"));
    assert!(verify.contains("--checked-cert-manifest <path>"));
    assert!(verify.contains("incremental ay binary VC route"));
    assert!(verify.contains("unsupported binary coverage"));
    assert!(verify.contains("ELF x86-64/AArch64"));
    assert!(verify.contains(
        "proof-grade replay, checked certificates, exact provenance, source-backprop reconstruction"
    ));
    assert!(verify.contains("JSON includes source_backpropagation_gate"));
    assert!(
        verify.contains("verified binary evidence alone does not grant source backpropagation")
    );

    let decompile = decompile_usage_text();
    assert!(decompile.contains("--to trust_ir|rust|trust-cg|wasm"));
    assert!(
        decompile
            .contains("trust_ir, trust-cg, and wasm text outputs are partial unless validated")
    );
    assert!(decompile.contains("rust output is exploratory/not validated"));
    assert!(decompile.contains("AArch32, i386/32-bit x86, Mach-O x86-64"));
    assert!(decompile.contains("artifact_gate.source_backpropagation_gate"));
    assert!(decompile.contains("accepted reconstruction/target validation requirements"));
    assert!(
        usage_text().contains("targo trust decompile <binary> --to trust_ir|rust|trust-cg|wasm")
    );
    assert!(usage_text().contains("Binary target support:"));
    assert!(
        usage_text().contains("little-endian ELF x86-64/AArch64 and little-endian Mach-O AArch64")
    );
    assert!(usage_text().contains("source_backpropagation_gate"));
    assert!(usage_text().contains("proof_grade_release_*"));

    let convert = convert_usage_text();
    assert!(
        convert.contains("trust_ir, trust-cg, and wasm text outputs are partial unless validated")
    );
    assert!(convert.contains("rust output is exploratory"));
    assert!(convert.contains("trust-codegen/wasm outputs are rejected"));
    assert!(convert.contains("ELF x86-64/AArch64"));
    assert!(convert.contains("conversion_gate.source_backpropagation_gate"));
    assert!(convert.contains("checked_certificate_readback.proof_grade_release_*"));
}

#[test]
fn test_exploit_find_rejects_html_format() {
    let args: Vec<String> =
        vec!["demo.bin".into(), "--target=lifter".into(), "--format=html".into()];
    assert_eq!(run_exploit_find_subcommand(&args), ExitCode::from(2));
}

#[test]
fn test_exploit_find_report_captures_phase_diagnostics_without_claiming_exploit() {
    let binary_report = build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 2,
                statements: 7,
                vcs: 2,
                vc_counts: vec![BinaryVcKindCount {
                    kind: "binary_memory_write_oob".into(),
                    count: 2,
                }],
            }],
            solver_results: Vec::new(),
            proof_evidence: verify_binary_evidence_for_vcs(2),
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );
    let report = build_exploit_find_report(ExploitFindTarget::Verifier, binary_report);

    assert_eq!(report.target, ExploitFindTarget::Verifier);
    assert_eq!(report.status, ExploitFindStatus::Unsupported);
    assert!(!report.exploit_found);
    assert_eq!(report.binary_status, BinaryLiftStatus::Ok);
    assert_eq!(report.verification_status, "unknown");
    assert_eq!(report.functions_analyzed, 1);
    assert_eq!(report.vcs, 2);
    assert_eq!(
        report.vc_counts,
        vec![BinaryVcKindCount { kind: "binary_memory_write_oob".into(), count: 2 }]
    );
    assert_eq!(report.solver_results.status, "unknown");
    assert_eq!(report.solver_results.total, 2);
    assert_eq!(report.solver_results.unknown, 2);
    assert_eq!(report.synthesis_status, ExploitFindStatus::Unsupported);
    assert_eq!(report.replay_status, ExploitFindStatus::NotRun);
    assert_eq!(report.independent_refutation_status, ExploitFindStatus::NotRun);
    assert_eq!(report.reducer_status, ExploitFindStatus::NotRun);
    assert!(report.independent_refutation_note.contains("no exploit claim was captured"));
    assert!(report.reducer_note.contains("no exploit candidate was captured"));
    assert!(report.synthesis_note.contains("not implemented"));
    assert!(report.replay_note.contains("no normalized exploit witness"));
    assert!(report.reason.contains("fails closed"));
    assert!(report.reason.contains("unproved"));
    assert!(report.notes.iter().any(|note| note.contains("phase.claim_capture.status=not_run")));
    assert!(
        report
            .notes
            .iter()
            .any(|note| note.contains("phase.independent_refutation.status=not_run"))
    );
    assert!(
        report.notes.iter().any(|note| note.contains("phase.replay_requirement.status=not_run"))
    );
    assert!(report.notes.iter().any(|note| note.contains("phase.reduction.status=not_run")));
    assert!(report.notes.iter().any(|note| note.contains("phase.attribution.status=not_run")));
    assert!(
        report.notes.iter().any(|note| note.contains("phase.regression_emission.status=not_run"))
    );
    assert!(
        report.notes.iter().any(|note| note.contains("phase.evidence_gate.status=unsupported"))
    );
    let stage_records = exploit_analyzer_stage_records(report.target, &report.binary_report);
    assert_eq!(stage_records.len(), 7);
    let independent_refutation = stage_records
        .iter()
        .find(|record| record.stage == "independent_refutation")
        .expect("independent refutation stage");
    assert_eq!(independent_refutation.status, "not_run");
    assert_eq!(independent_refutation.target, "verifier");
    assert!(independent_refutation.claim_ids.is_empty());
    assert_eq!(
        independent_refutation.evidence_required,
        vec!["independent_refutation", "checked_unsat_evidence_bound_to_claim"]
    );
    assert!(!independent_refutation.evidence_present);
    assert!(independent_refutation.blocks_exploit_confirmation);
    let regression_emission = stage_records
        .iter()
        .find(|record| record.stage == "regression_emission")
        .expect("regression emission stage");
    assert_eq!(regression_emission.status, "not_run");
    assert_eq!(regression_emission.evidence_required, vec!["regression_test_emission"]);
    assert!(exploit_find_should_fail(&report));

    let rendered = render_exploit_find_terminal(&report);
    assert!(rendered.contains("targo trust exploit-find report\n"));
    assert!(rendered.contains("target: verifier\n"));
    assert!(rendered.contains("status: unsupported\n"));
    assert!(rendered.contains("exploit_found: false\n"));
    assert!(rendered.contains("binary status: ok\n"));
    assert!(rendered.contains("verification status: unknown\n"));
    assert!(rendered.contains("vcs generated: 2\n"));
    assert!(rendered.contains("solver counts: total=2 proved=0 failed=0 unknown=2 timeout=0\n"));
    assert!(rendered.contains("  - binary_memory_write_oob: 2\n"));
    assert!(rendered.contains("synthesis: unsupported\n"));
    assert!(rendered.contains("replay: not_run\n"));
    assert!(rendered.contains("independent refutation: not_run\n"));
    assert!(rendered.contains("reducer: not_run\n"));
    assert!(rendered.contains("evidence gate: rejected\n"));
    assert!(rendered.contains(
        "evidence gate detail: proof_grade_complete=false unsupported_evidence_blocks_completion=false claim_capture=not_run replay=not_run"
    ));
    assert!(rendered.contains("evidence gate blockers:\n"));
    assert!(rendered.contains("exploit_found is false"));
    assert!(rendered.contains("analyzer stage records:\n"));
    assert!(rendered.contains(
        "independent_refutation: status=not_run target=verifier evidence_required=independent_refutation,checked_unsat_evidence_bound_to_claim evidence_present=false blocks_exploit_confirmation=true"
    ));
    assert!(rendered.contains("phase diagnostics:\n"));
    assert!(rendered.contains("phase.claim_capture.status=not_run"));
    assert!(rendered.contains("phase.regression_emission.status=not_run"));
    assert!(rendered.contains("No exploit witness is produced"));

    let json = serde_json::to_string(&report).expect("serialize exploit-find report");
    assert!(json.contains("\"status\":\"unsupported\""));
    assert!(json.contains("\"binary_status\":\"ok\""));
    assert!(json.contains("\"verification_status\":\"unknown\""));
    assert!(json.contains("\"solver_results\""));
    assert!(json.contains("\"binary_report\""));
    assert!(json.contains("\"synthesis_status\":\"unsupported\""));
    assert!(json.contains("\"replay_status\":\"not_run\""));
    assert!(json.contains("\"independent_refutation_status\":\"not_run\""));
    assert!(json.contains("\"reducer_status\":\"not_run\""));
    assert!(json.contains("phase.claim_capture.status=not_run"));
    assert!(json.contains("phase.evidence_gate.status=unsupported"));
    assert!(json.contains("\"exploit_found\":false"));
    assert!(!json.contains("\"exploit_found\":true"));

    let evidence_gate = build_exploit_evidence_gate(&report);
    assert!(!evidence_gate.accepted);
    assert!(!evidence_gate.proof_grade_complete);
    assert!(!evidence_gate.unsupported_evidence_blocks_completion);
    assert_eq!(evidence_gate.status, "rejected");
    assert_eq!(evidence_gate.claim_capture, "not_run");
    assert_eq!(evidence_gate.replay, "not_run");
    assert_eq!(evidence_gate.independent_refutation, "not_run");
    assert_eq!(evidence_gate.regression_emission, "not_run");
    assert_eq!(
        evidence_gate.required_evidence,
        vec![
            "normalized_exploit_claim",
            "machine_code_replay",
            "independent_refutation",
            "minimized_replayable_witness",
            "target_attribution",
            "regression_test_emission",
        ]
    );
    assert!(
        evidence_gate.blockers.iter().any(|blocker| blocker.contains("claim_capture is `not_run`"))
    );
    assert!(
        evidence_gate
            .blockers
            .iter()
            .any(|blocker| blocker.contains("proof-grade exploit evidence requires"))
    );

    let wrapped_json = serialize_exploit_find_json(&report).expect("serialize exploit-find JSON");
    let value: serde_json::Value = serde_json::from_str(&wrapped_json).expect("parse JSON");
    assert_eq!(value["evidence_gate"]["accepted"], false);
    assert_eq!(value["evidence_gate"]["status"], "rejected");
    assert_eq!(value["evidence_gate"]["proof_grade_complete"], false);
    assert_eq!(value["evidence_gate"]["unsupported_evidence_blocks_completion"], false);
    assert_eq!(value["evidence_gate"]["claim_capture"], "not_run");
    assert_eq!(value["evidence_gate"]["exploit_found"], false);
    assert_eq!(value["evidence_gate"]["required_evidence"][0], "normalized_exploit_claim");
    assert!(
        value["evidence_gate"]["blockers"]
            .as_array()
            .expect("gate blockers")
            .iter()
            .any(|blocker| blocker.as_str().unwrap().contains("claim_capture is `not_run`"))
    );
    assert!(value["claim_capture_records"].as_array().unwrap().is_empty());
    assert_eq!(value["analyzer_stage_records"].as_array().unwrap().len(), 7);
    assert_eq!(value["analyzer_stage_records"][2]["stage"], "independent_refutation");
    assert_eq!(value["analyzer_stage_records"][2]["status"], "not_run");
    assert_eq!(
        value["analyzer_stage_records"][2]["evidence_required"][0],
        "independent_refutation"
    );
    assert_eq!(
        value["analyzer_stage_records"][2]["evidence_required"][1],
        "checked_unsat_evidence_bound_to_claim"
    );
    assert_eq!(value["analyzer_stage_records"][2]["evidence_present"], false);
    assert_eq!(value["analyzer_stage_records"][2]["blocks_exploit_confirmation"], true);
}

#[test]
fn test_exploit_find_raw_solver_failure_requires_replay_before_confirmation() {
    let counterexample = trust_types::Counterexample::new(vec![(
        "ptr".into(),
        trust_types::CounterexampleValue::Uint(0xdead_beef),
    )]);
    let solver_item = binary_solver_result_report(
        "main",
        "binary_memory_read_invalid".into(),
        Some("0x401030".into()),
        &trust_types::VerificationResult::Failed {
            solver: "ay-incremental".into(),
            time_ms: 9,
            counterexample: Some(counterexample),
        },
    );
    let binary_report = build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount {
                    kind: "binary_memory_read_invalid".into(),
                    count: 1,
                }],
            }],
            solver_results: vec![solver_item],
            proof_evidence: verify_binary_evidence_for_vcs(1),
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );

    let report = build_exploit_find_report(ExploitFindTarget::Lifter, binary_report);

    assert_eq!(report.solver_results.status, "failed");
    assert_eq!(report.synthesis_status, ExploitFindStatus::Unsupported);
    assert_eq!(report.replay_status, ExploitFindStatus::Unsupported);
    assert_eq!(report.independent_refutation_status, ExploitFindStatus::Unsupported);
    assert_eq!(report.reducer_status, ExploitFindStatus::Unsupported);
    assert!(!report.exploit_found);
    assert!(report.reason.contains("raw failed result"));
    assert!(report.reason.contains("require replay"));
    let claim_records = exploit_claim_capture_records(report.target, &report.binary_report);
    assert_eq!(claim_records.len(), 1);
    assert_eq!(claim_records[0].claim_id, "raw-solver-candidate-1");
    assert_eq!(claim_records[0].status, "unconfirmed");
    assert_eq!(claim_records[0].source, "binary_solver_failed_result");
    assert_eq!(claim_records[0].target, "lifter");
    assert_eq!(claim_records[0].function, "main");
    assert_eq!(claim_records[0].vc_kind, "binary_memory_read_invalid");
    assert_eq!(claim_records[0].location.as_deref(), Some("0x401030"));
    assert!(claim_records[0].raw_counterexample_present);
    assert!(claim_records[0].replay_required);
    assert!(claim_records[0].independent_refutation_required);
    assert!(claim_records[0].diagnostic.contains("independent refutation"));
    let stage_records = exploit_analyzer_stage_records(report.target, &report.binary_report);
    let independent_refutation = stage_records
        .iter()
        .find(|record| record.stage == "independent_refutation")
        .expect("independent refutation stage");
    assert_eq!(independent_refutation.status, "unsupported");
    assert_eq!(independent_refutation.claim_ids, vec!["raw-solver-candidate-1"]);
    assert_eq!(
        independent_refutation.evidence_required,
        vec!["independent_refutation", "checked_unsat_evidence_bound_to_claim"]
    );
    assert!(!independent_refutation.evidence_present);
    assert!(independent_refutation.blocks_exploit_confirmation);
    let reduction =
        stage_records.iter().find(|record| record.stage == "reduction").expect("reduction stage");
    assert_eq!(reduction.status, "unsupported");
    assert_eq!(reduction.evidence_required, vec!["minimized_replayable_witness"]);
    let attribution = stage_records
        .iter()
        .find(|record| record.stage == "attribution")
        .expect("attribution stage");
    assert_eq!(attribution.status, "unsupported");
    assert_eq!(attribution.evidence_required, vec!["target_attribution"]);
    let regression_emission = stage_records
        .iter()
        .find(|record| record.stage == "regression_emission")
        .expect("regression emission stage");
    assert_eq!(regression_emission.status, "unsupported");
    assert_eq!(regression_emission.evidence_required, vec!["regression_test_emission"]);
    assert!(
        report.notes.iter().any(|note| note.contains("phase.claim_capture.status=unsupported"))
    );
    assert!(report.notes.iter().any(|note| {
        note.contains("claim_capture_record.raw-solver-candidate-1.status=unconfirmed")
            && note.contains("independent_refutation_required=true")
    }));
    assert!(
        report
            .notes
            .iter()
            .any(|note| note.contains("phase.replay_requirement.status=unsupported"))
    );
    assert!(report.notes.iter().any(|note| note.contains("phase.attribution.status=unsupported")));
    assert!(
        report
            .notes
            .iter()
            .any(|note| note.contains("phase.regression_emission.status=unsupported"))
    );
    assert!(report.replay_note.contains("0/1 have exact replay evidence"));
    assert!(report.independent_refutation_note.contains("no replay-backed claim exists"));
    assert!(exploit_find_should_fail(&report));

    let rendered = render_exploit_find_terminal(&report);
    assert!(rendered.contains("exploit_found: false\n"));
    assert!(rendered.contains("replay: unsupported\n"));
    assert!(rendered.contains("analyzer stage records:\n"));
    assert!(rendered.contains(
        "independent_refutation: status=unsupported target=lifter evidence_required=independent_refutation,checked_unsat_evidence_bound_to_claim evidence_present=false blocks_exploit_confirmation=true claim_ids=raw-solver-candidate-1"
    ));
    assert!(rendered.contains(
        "reduction: status=unsupported target=lifter evidence_required=minimized_replayable_witness evidence_present=false blocks_exploit_confirmation=true claim_ids=raw-solver-candidate-1"
    ));
    assert!(rendered.contains(
        "attribution: status=unsupported target=lifter evidence_required=target_attribution evidence_present=false blocks_exploit_confirmation=true claim_ids=raw-solver-candidate-1"
    ));
    assert!(rendered.contains("claim capture records:\n"));
    assert!(rendered.contains("raw-solver-candidate-1: status=unconfirmed"));
    assert!(rendered.contains("independent_refutation_required=true"));
    assert!(rendered.contains("phase.replay_requirement.status=unsupported"));
    assert!(rendered.contains("claim capture diagnostics:\n"));
    assert!(!rendered.contains("confirmed exploit"));

    let report_json = serde_json::to_string(&report).expect("serialize exploit-find report");
    assert!(report_json.contains("\"exploit_found\":false"));
    assert!(report_json.contains("\"replay_status\":\"unsupported\""));
    assert!(report_json.contains("phase.regression_emission.status=unsupported"));
    assert!(report_json.contains("claim_capture_record.raw-solver-candidate-1.status=unconfirmed"));
    assert!(!report_json.contains("\"exploit_found\":true"));
    assert!(!report_json.contains("confirmed exploit"));

    let wrapped_json = serialize_exploit_find_json(&report).expect("serialize exploit-find JSON");
    let value: serde_json::Value = serde_json::from_str(&wrapped_json).expect("parse JSON");
    assert_eq!(value["exploit_found"], false);
    assert!(value.get("typed_scaffold").is_some());
    assert!(value.get("claim_capture_records").is_some());
    assert!(value.get("analyzer_stage_records").is_some());
    assert!(value.get("evidence_gate").is_some());
    assert_eq!(value["typed_scaffold"]["exploit_found"], false);
    assert_eq!(value["typed_scaffold"]["claims"][0]["claim_id"], "raw-solver-candidate-1");
    assert_eq!(value["typed_scaffold"]["replay"]["status"], "unsupported");
    assert_eq!(value["typed_scaffold"]["reduction"]["status"], "unsupported");
    assert_eq!(value["typed_scaffold"]["reduction"]["reduced"], false);
    assert_eq!(
        value["typed_scaffold"]["reduction"]["evidence_required"][0],
        "minimized_replayable_witness"
    );
    assert_eq!(value["typed_scaffold"]["attribution"]["status"], "unsupported");
    assert_eq!(value["typed_scaffold"]["attribution"]["attributed"], false);
    assert_eq!(value["evidence_gate"]["accepted"], false);
    assert_eq!(value["evidence_gate"]["proof_grade_complete"], false);
    assert_eq!(value["evidence_gate"]["unsupported_evidence_blocks_completion"], true);
    assert_eq!(value["evidence_gate"]["exploit_found"], false);
    assert!(value["evidence_gate"]["blockers"].as_array().expect("gate blockers").iter().any(
        |blocker| {
            blocker
                .as_str()
                .unwrap()
                .contains("unsupported evidence cannot satisfy proof-grade completion")
        }
    ));
    assert!(
        value["typed_scaffold"]["evidence_gate"]["blockers"]
            .as_array()
            .expect("typed blockers")
            .iter()
            .any(|blocker| blocker["stage"] == "reduction"
                && blocker["evidence_required"][0] == "minimized_replayable_witness"
                && blocker["diagnostic"].as_str().unwrap().contains("reduction is blocked"))
    );
    assert!(
        value["typed_scaffold"]["evidence_gate"]["blockers"]
            .as_array()
            .expect("typed blockers")
            .iter()
            .any(|blocker| blocker["stage"] == "attribution"
                && blocker["evidence_required"][0] == "target_attribution"
                && blocker["diagnostic"]
                    .as_str()
                    .unwrap()
                    .contains("target attribution is blocked"))
    );
    assert_eq!(value["claim_capture_records"][0]["claim_id"], "raw-solver-candidate-1");
    assert_eq!(value["claim_capture_records"][0]["status"], "unconfirmed");
    assert_eq!(value["claim_capture_records"][0]["source"], "binary_solver_failed_result");
    assert_eq!(value["claim_capture_records"][0]["replay_required"], true);
    assert_eq!(value["claim_capture_records"][0]["independent_refutation_required"], true);
    assert_eq!(value["claim_capture_records"][0]["raw_counterexample_present"], true);
    assert_eq!(value["claim_capture_records"][0]["solver_status"], "failed");
    assert_eq!(value["analyzer_stage_records"][2]["stage"], "independent_refutation");
    assert_eq!(value["analyzer_stage_records"][2]["status"], "unsupported");
    assert_eq!(value["analyzer_stage_records"][2]["claim_ids"][0], "raw-solver-candidate-1");
    assert_eq!(
        value["analyzer_stage_records"][2]["evidence_required"][0],
        "independent_refutation"
    );
    assert_eq!(
        value["analyzer_stage_records"][2]["evidence_required"][1],
        "checked_unsat_evidence_bound_to_claim"
    );
    assert_eq!(value["analyzer_stage_records"][3]["stage"], "reduction");
    assert_eq!(
        value["analyzer_stage_records"][3]["evidence_required"][0],
        "minimized_replayable_witness"
    );
    assert_eq!(value["analyzer_stage_records"][4]["stage"], "attribution");
    assert_eq!(value["analyzer_stage_records"][4]["evidence_required"][0], "target_attribution");
    assert_eq!(value["analyzer_stage_records"][5]["stage"], "regression_emission");
    assert_eq!(
        value["analyzer_stage_records"][5]["evidence_required"][0],
        "regression_test_emission"
    );
}

#[test]
fn test_exploit_find_checked_unsat_certificate_without_claim_does_not_satisfy_refutation() {
    let solver_item = binary_solver_result_report(
        "main",
        "division_by_zero".into(),
        Some("0x401010".into()),
        &trust_types::VerificationResult::Proved {
            solver: "ay-smtlib".into(),
            time_ms: 3,
            strength: trust_types::ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        },
    );
    let binary_report = build_verify_binary_report(
        Path::new("demo.bin"),
        None,
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 1 }],
            }],
            solver_results: vec![solver_item],
            proof_evidence: VerifyBinaryEvidence::from_solver_dispatch_records(
                1,
                vec![checked_certificate_only_binary_dispatch("vc-unsat", "main")],
            ),
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );

    let report = build_exploit_find_report(ExploitFindTarget::Verifier, binary_report);

    assert_eq!(report.solver_results.status, "proved");
    assert_eq!(report.replay_status, ExploitFindStatus::NotRun);
    assert_eq!(report.independent_refutation_status, ExploitFindStatus::NotRun);
    assert_eq!(report.reducer_status, ExploitFindStatus::NotRun);
    assert!(!report.exploit_found);
    assert!(
        report
            .independent_refutation_note
            .contains("checked UNSAT certificate evidence proves verification VCs")
    );
    assert!(report.reason.contains("captured no replay-backed exploit claim"));
    assert!(exploit_find_should_fail(&report));

    let stage_records = exploit_analyzer_stage_records(report.target, &report.binary_report);
    let independent_refutation = stage_records
        .iter()
        .find(|record| record.stage == "independent_refutation")
        .expect("independent refutation stage");
    assert_eq!(independent_refutation.status, "not_run");
    assert!(!independent_refutation.evidence_present);
    assert!(independent_refutation.blocks_exploit_confirmation);

    let reduction =
        stage_records.iter().find(|record| record.stage == "reduction").expect("reduction stage");
    assert_eq!(reduction.status, "not_run");
    assert!(!reduction.evidence_present);
    assert!(reduction.blocks_exploit_confirmation);
    let attribution = stage_records
        .iter()
        .find(|record| record.stage == "attribution")
        .expect("attribution stage");
    assert_eq!(attribution.status, "not_run");
    assert!(attribution.blocks_exploit_confirmation);

    let evidence_gate = build_exploit_evidence_gate(&report);
    assert!(!evidence_gate.accepted);
    assert!(!evidence_gate.proof_grade_complete);
    assert!(!evidence_gate.unsupported_evidence_blocks_completion);
    assert_eq!(evidence_gate.independent_refutation, "not_run");
    assert_eq!(evidence_gate.replay, "not_run");
    assert_eq!(evidence_gate.reduction, "not_run");
    assert_eq!(evidence_gate.attribution, "not_run");
    assert!(
        evidence_gate
            .blockers
            .iter()
            .any(|blocker| blocker.contains("independent_refutation is `not_run`"))
    );

    let wrapped_json = serialize_exploit_find_json(&report).expect("serialize exploit-find JSON");
    let value: serde_json::Value = serde_json::from_str(&wrapped_json).expect("parse JSON");
    let refutation_accounting = &value["checked_certificate_refutation_accounting"];
    assert_eq!(refutation_accounting["required_vcs"], 1);
    assert_eq!(refutation_accounting["solver_dispatches"], 1);
    assert_eq!(refutation_accounting["proved_vcs"], 1);
    assert_eq!(refutation_accounting["checked_unsat_refutations"], 1);
    assert_eq!(refutation_accounting["missing_checked_unsat_refutations"], 0);
    assert_eq!(refutation_accounting["all_required_vcs_checked_unsat"], true);
    assert_eq!(refutation_accounting["raw_solver_candidates"], 0);
    assert_eq!(refutation_accounting["exact_replayed_candidates"], 0);
    assert_eq!(refutation_accounting["independent_refutation_status"], "not_run");
    assert_eq!(refutation_accounting["independent_refutation_satisfied"], false);
    assert!(
        refutation_accounting["diagnostic"]
            .as_str()
            .expect("refutation accounting diagnostic")
            .contains("checked UNSAT certificate evidence proves verification VCs")
    );
    assert_eq!(value["independent_refutation_status"], "not_run");
    assert_eq!(value["evidence_gate"]["independent_refutation"], "not_run");
    assert_eq!(value["evidence_gate"]["proof_grade_complete"], false);
    assert_eq!(value["evidence_gate"]["unsupported_evidence_blocks_completion"], false);
    assert_eq!(value["typed_scaffold"]["refutation"]["status"], "not_run");
    assert_eq!(value["typed_scaffold"]["refutation"]["independently_refuted"], false);
    assert_eq!(
        value["typed_scaffold"]["refutation"]["evidence_required"][1],
        "checked_unsat_evidence_bound_to_claim"
    );
    assert_eq!(value["typed_scaffold"]["reduction"]["status"], "not_run");
    assert_eq!(value["typed_scaffold"]["reduction"]["reduced"], false);
    assert_eq!(value["typed_scaffold"]["attribution"]["status"], "not_run");
    assert_eq!(value["typed_scaffold"]["attribution"]["attributed"], false);
    assert!(
        value["typed_scaffold"]["evidence_gate"]["blockers"]
            .as_array()
            .expect("typed blockers")
            .iter()
            .any(|blocker| blocker["stage"] == "independent_refutation"
                && blocker["diagnostic"]
                    .as_str()
                    .unwrap()
                    .contains("checked UNSAT certificate evidence proves verification VCs"))
    );
    assert!(
        value["typed_scaffold"]["evidence_gate"]["blockers"]
            .as_array()
            .expect("typed blockers")
            .iter()
            .all(|blocker| blocker["stage"] != "checked_unsat_refutation")
    );
    assert_eq!(value["evidence_gate"]["accepted"], false);

    let rendered = render_exploit_find_terminal(&report);
    assert!(rendered.contains("exploit_found: false\n"));
    assert!(rendered.contains("independent refutation: not_run\n"));
    assert!(rendered.contains(
        "reduction: status=not_run target=verifier evidence_required=minimized_replayable_witness evidence_present=false blocks_exploit_confirmation=true"
    ));
    assert!(rendered.contains(
        "attribution: status=not_run target=verifier evidence_required=target_attribution evidence_present=false blocks_exploit_confirmation=true"
    ));
    assert!(!rendered.contains("exploit_found: true"));
}

#[test]
fn test_exploit_find_sat_candidate_requires_exact_replay_even_with_checked_unsat_evidence() {
    let counterexample = trust_types::Counterexample::new(vec![(
        "ptr".into(),
        trust_types::CounterexampleValue::Uint(0xdead_beef),
    )]);
    let solver_item = binary_solver_result_report(
        "main",
        "binary_memory_read_invalid".into(),
        Some("0x401030".into()),
        &trust_types::VerificationResult::Failed {
            solver: "ay-incremental".into(),
            time_ms: 9,
            counterexample: Some(counterexample),
        },
    );
    let binary_report = build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 2,
                vc_counts: vec![BinaryVcKindCount {
                    kind: "binary_memory_read_invalid".into(),
                    count: 2,
                }],
            }],
            solver_results: vec![solver_item],
            proof_evidence: VerifyBinaryEvidence::from_solver_dispatch_records(
                2,
                vec![
                    sat_unreplayed_binary_dispatch("vc-sat", "main"),
                    checked_certificate_only_binary_dispatch("vc-unsat", "main"),
                ],
            ),
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );

    let report = build_exploit_find_report(ExploitFindTarget::Lifter, binary_report);

    assert_eq!(report.solver_results.status, "failed");
    assert_eq!(report.replay_status, ExploitFindStatus::Unsupported);
    assert_eq!(report.independent_refutation_status, ExploitFindStatus::Unsupported);
    assert!(report.replay_note.contains("0/1 have exact replay evidence"));
    assert!(report.independent_refutation_note.contains("no replay-backed claim exists"));
    assert!(!report.exploit_found);
    assert!(exploit_find_should_fail(&report));

    let stage_records = exploit_analyzer_stage_records(report.target, &report.binary_report);
    let replay = stage_records
        .iter()
        .find(|record| record.stage == "replay_requirement")
        .expect("replay stage");
    assert_eq!(replay.status, "unsupported");
    assert!(!replay.evidence_present);
    assert!(replay.blocks_exploit_confirmation);
    let independent_refutation = stage_records
        .iter()
        .find(|record| record.stage == "independent_refutation")
        .expect("independent refutation stage");
    assert_eq!(independent_refutation.status, "unsupported");
    assert!(!independent_refutation.evidence_present);
    assert!(independent_refutation.blocks_exploit_confirmation);
}

#[test]
fn test_exploit_find_replayed_sat_candidate_without_checked_refutation_stays_blocked() {
    let counterexample = trust_types::Counterexample::new(vec![(
        "ptr".into(),
        trust_types::CounterexampleValue::Uint(0xfeed_face),
    )]);
    let mut solver_item = binary_solver_result_report(
        "main",
        "binary_memory_read_invalid".into(),
        Some("0x401030".into()),
        &trust_types::VerificationResult::Failed {
            solver: "ay-incremental".into(),
            time_ms: 9,
            counterexample: Some(counterexample),
        },
    );
    solver_item.replay_status = Some("replayed".into());
    solver_item.replay_detail = Some("machine_replay_confirmed: fixture".into());
    let binary_report = build_verify_binary_report(
        Path::new("demo.bin"),
        Some(0x401000),
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount {
                    kind: "binary_memory_read_invalid".into(),
                    count: 1,
                }],
            }],
            solver_results: vec![solver_item],
            proof_evidence: VerifyBinaryEvidence::from_solver_dispatch_records(
                1,
                vec![sat_replayed_binary_dispatch("vc-sat", "main")],
            ),
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );

    let report = build_exploit_find_report(ExploitFindTarget::Lifter, binary_report);

    assert_eq!(report.replay_status, ExploitFindStatus::Satisfied);
    assert_eq!(report.independent_refutation_status, ExploitFindStatus::Unsupported);
    assert_eq!(report.reducer_status, ExploitFindStatus::Unsupported);
    assert!(report.replay_note.contains("1/1 raw solver candidate"));
    assert!(report.reducer_note.contains("checked independent-refutation evidence"));
    assert!(report.reason.contains("checked independent refutation"));
    assert!(
        report
            .independent_refutation_note
            .contains("checked UNSAT evidence bound to the replayed candidate")
    );
    assert!(!report.exploit_found);
    assert!(exploit_find_should_fail(&report));

    let stage_records = exploit_analyzer_stage_records(report.target, &report.binary_report);
    let replay = stage_records
        .iter()
        .find(|record| record.stage == "replay_requirement")
        .expect("replay stage");
    assert_eq!(replay.status, "satisfied");
    assert!(replay.evidence_present);
    assert!(!replay.blocks_exploit_confirmation);
    let independent_refutation = stage_records
        .iter()
        .find(|record| record.stage == "independent_refutation")
        .expect("independent refutation stage");
    assert_eq!(independent_refutation.status, "unsupported");
    assert!(!independent_refutation.evidence_present);
    assert!(independent_refutation.blocks_exploit_confirmation);
    let reduction =
        stage_records.iter().find(|record| record.stage == "reduction").expect("reduction stage");
    assert_eq!(reduction.status, "unsupported");
    assert!(!reduction.evidence_present);
    assert!(reduction.blocks_exploit_confirmation);
    assert!(reduction.diagnostic.contains("checked independent-refutation evidence"));
    let attribution = stage_records
        .iter()
        .find(|record| record.stage == "attribution")
        .expect("attribution stage");
    assert_eq!(attribution.status, "unsupported");
    assert!(!attribution.evidence_present);
    assert!(attribution.blocks_exploit_confirmation);
    assert!(attribution.diagnostic.contains("checked independent-refutation evidence"));

    let evidence_gate = build_exploit_evidence_gate(&report);
    assert!(!evidence_gate.accepted);
    assert!(!evidence_gate.proof_grade_complete);
    assert!(evidence_gate.unsupported_evidence_blocks_completion);
    assert_eq!(evidence_gate.replay, "satisfied");
    assert_eq!(evidence_gate.independent_refutation, "unsupported");
    assert_eq!(evidence_gate.reduction, "unsupported");
    assert_eq!(evidence_gate.attribution, "unsupported");
    assert!(
        evidence_gate
            .blockers
            .iter()
            .any(|blocker| blocker.contains("independent_refutation is `unsupported`"))
    );
    assert!(
        evidence_gate
            .blockers
            .iter()
            .any(|blocker| blocker.contains("regression_emission is `unsupported`"))
    );

    let wrapped_json = serialize_exploit_find_json(&report).expect("serialize exploit-find JSON");
    let value: serde_json::Value = serde_json::from_str(&wrapped_json).expect("parse JSON");
    assert_eq!(value["typed_scaffold"]["replay"]["status"], "satisfied");
    assert_eq!(value["typed_scaffold"]["refutation"]["status"], "unsupported");
    assert_eq!(value["typed_scaffold"]["refutation"]["independently_refuted"], false);
    assert_eq!(value["typed_scaffold"]["refutation"]["evidence"].as_array().unwrap().len(), 0);
    assert_eq!(
        value["typed_scaffold"]["refutation"]["evidence_required"][1],
        "checked_unsat_evidence_bound_to_claim"
    );
    assert_eq!(value["typed_scaffold"]["reduction"]["status"], "unsupported");
    assert_eq!(value["typed_scaffold"]["reduction"]["reduced"], false);
    assert_eq!(value["typed_scaffold"]["reduction"]["evidence"].as_array().unwrap().len(), 0);
    assert_eq!(value["typed_scaffold"]["attribution"]["status"], "unsupported");
    assert_eq!(value["typed_scaffold"]["attribution"]["attributed"], false);
    assert_eq!(value["typed_scaffold"]["attribution"]["evidence"].as_array().unwrap().len(), 0);
    assert_eq!(value["typed_scaffold"]["regression"]["emitted"], false);
    assert_eq!(value["typed_scaffold"]["regression"]["placeholder_emitted"], true);
    assert_eq!(value["typed_scaffold"]["regression"]["proof_grade_accepted"], false);
    assert_eq!(
        value["typed_scaffold"]["regression"]["artifacts"][0]["schema"],
        "trust.exploit_regression.v1"
    );
    assert_eq!(value["typed_scaffold"]["regression"]["artifacts"][0]["status"], "candidate");
    assert_eq!(
        value["typed_scaffold"]["regression"]["artifacts"][0]["claim_id"],
        "raw-solver-candidate-1"
    );
    assert_eq!(value["typed_scaffold"]["regression"]["artifacts"][0]["target"], "lifter");
    assert_eq!(
        value["typed_scaffold"]["regression"]["artifacts"][0]["claim_kind"],
        "lift_semantics"
    );
    assert_eq!(
        value["typed_scaffold"]["regression"]["artifacts"][0]["input"]["address_range"][0],
        "0x401030"
    );
    assert_eq!(
        value["typed_scaffold"]["regression"]["artifacts"][0]["test"]["command"],
        serde_json::Value::Null
    );
    assert_eq!(value["typed_scaffold"]["regression"]["artifacts"][0]["executable"], false);
    assert!(
        value["typed_scaffold"]["regression"]["artifacts"][0]["missing_evidence"]
            .as_array()
            .expect("missing regression evidence")
            .iter()
            .any(|evidence| evidence == "independent_refutation")
    );
    assert!(
        value["typed_scaffold"]["regression"]["artifacts"][0]["missing_evidence"]
            .as_array()
            .expect("missing regression evidence")
            .iter()
            .any(|evidence| evidence == "executable_regression_test_command")
    );
    assert!(
        value["typed_scaffold"]["evidence_gate"]["blockers"]
            .as_array()
            .expect("typed blockers")
            .iter()
            .any(|blocker| blocker["stage"] == "checked_unsat_refutation"
                && blocker["diagnostic"]
                    .as_str()
                    .unwrap()
                    .contains("without checked UNSAT evidence"))
    );
    assert!(
        value["typed_scaffold"]["evidence_gate"]["blockers"]
            .as_array()
            .expect("typed blockers")
            .iter()
            .any(|blocker| blocker["stage"] == "reduction"
                && blocker["diagnostic"].as_str().unwrap().contains("independently refuted"))
    );
    assert_eq!(value["evidence_gate"]["attribution"], "unsupported");
    assert_eq!(value["evidence_gate"]["reduction"], "unsupported");
    assert_eq!(value["evidence_gate"]["accepted"], false);
    assert_eq!(value["evidence_gate"]["proof_grade_complete"], false);
    assert_eq!(value["evidence_gate"]["unsupported_evidence_blocks_completion"], true);
    assert!(value["evidence_gate"]["blockers"].as_array().expect("gate blockers").iter().any(
        |blocker| blocker.as_str().unwrap().contains("real executable regression test command")
    ));
    assert!(
        value["evidence_gate"]["blockers"].as_array().expect("gate blockers").iter().any(
            |blocker| blocker.as_str().unwrap().contains("regression_emission is `unsupported`")
        )
    );
    assert_eq!(value["exploit_found"], false);

    let rendered = render_exploit_find_terminal(&report);
    assert!(rendered.contains("exploit_found: false\n"));
    assert!(rendered.contains("replay: satisfied\n"));
    assert!(rendered.contains("reducer: unsupported\n"));
    assert!(rendered.contains(
        "independent_refutation: status=unsupported target=lifter evidence_required=independent_refutation,checked_unsat_evidence_bound_to_claim evidence_present=false blocks_exploit_confirmation=true claim_ids=raw-solver-candidate-1"
    ));
    assert!(rendered.contains(
        "reduction: status=unsupported target=lifter evidence_required=minimized_replayable_witness evidence_present=false blocks_exploit_confirmation=true claim_ids=raw-solver-candidate-1"
    ));
    assert!(rendered.contains(
        "attribution: status=unsupported target=lifter evidence_required=target_attribution evidence_present=false blocks_exploit_confirmation=true claim_ids=raw-solver-candidate-1"
    ));
    assert!(!rendered.contains("exploit_found: true"));
}

#[test]
fn test_exploit_find_fails_even_when_binary_vcs_are_proved() {
    let solver_item = binary_solver_result_report(
        "main",
        "division_by_zero".into(),
        Some("0x401010".into()),
        &trust_types::VerificationResult::Proved {
            solver: "ay-smtlib".into(),
            time_ms: 3,
            strength: trust_types::ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        },
    );
    let binary_report = build_verify_binary_report(
        Path::new("demo.bin"),
        None,
        false,
        true,
        VerifyBinaryReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![VerifiedBinaryFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 1,
                statements: 1,
                vcs: 1,
                vc_counts: vec![BinaryVcKindCount { kind: "division_by_zero".into(), count: 1 }],
            }],
            solver_results: vec![solver_item],
            proof_evidence: verify_binary_evidence_for_vcs(1),
            unsupported: Vec::new(),
            failures: Vec::new(),
        },
    );
    assert_eq!(binary_report.solver_results.status, "proved");

    let report = build_exploit_find_report(ExploitFindTarget::Lifter, binary_report);

    assert_eq!(report.verification_status, "proved");
    assert_eq!(report.solver_results.status, "proved");
    assert_eq!(report.status, ExploitFindStatus::Unsupported);
    assert!(
        report.reason.contains(
            "binary VCs were proved only as verification conditions, not exploit evidence"
        )
    );
    assert!(report.notes.iter().any(|note| note.contains("phase.claim_capture.status=not_run")));
    assert!(exploit_find_should_fail(&report));
}

// -- Rewrite flag parsing tests --

#[test]
fn test_parse_args_rewrite_flag() {
    let args: Vec<String> = vec!["--rewrite".into()];
    let result = parse_subcommand_args(&args).expect("should parse --rewrite");
    assert!(result.rewrite);
    assert_eq!(result.max_iterations, 10); // default
}

#[test]
fn test_parse_args_rewrite_with_max_iterations() {
    let args: Vec<String> = vec!["--rewrite".into(), "--max-iterations".into(), "5".into()];
    let result = parse_subcommand_args(&args).expect("should parse --rewrite --max-iterations 5");
    assert!(result.rewrite);
    assert_eq!(result.max_iterations, 5);
}

#[test]
fn test_parse_args_max_iterations_equals() {
    let args: Vec<String> = vec!["--max-iterations=3".into()];
    let result = parse_subcommand_args(&args).expect("should parse --max-iterations=3");
    assert_eq!(result.max_iterations, 3);
}

#[test]
fn test_parse_args_max_iterations_zero_fails() {
    let args: Vec<String> = vec!["--max-iterations".into(), "0".into()];
    assert!(parse_subcommand_args(&args).is_err());
}

#[test]
fn test_parse_args_max_iterations_invalid_fails() {
    let args: Vec<String> = vec!["--max-iterations".into(), "abc".into()];
    assert!(parse_subcommand_args(&args).is_err());
}

#[test]
fn test_parse_args_no_rewrite_by_default() {
    let args: Vec<String> = vec!["--format".into(), "json".into()];
    let result = parse_subcommand_args(&args).expect("should parse without --rewrite");
    assert!(!result.rewrite);
}

#[test]
fn test_parse_args_removed_fresh_flag_fails_loudly() {
    let args: Vec<String> = vec!["--fresh".into()];
    let error = parse_subcommand_args(&args).expect_err("removed --fresh must not be a no-op");
    assert!(error.to_string().contains("always collect fresh structured evidence"));

    let joined = vec!["--fresh=true".into()];
    assert!(parse_subcommand_args(&joined).is_err());
}

// -- Baseline argument parsing tests --

#[test]
fn test_parse_args_baseline_flag() {
    let args: Vec<String> = vec!["--baseline".into(), "report.json".into()];
    let result = parse_subcommand_args(&args).expect("should parse --baseline");
    assert_eq!(result.baseline.as_deref(), Some("report.json"));
}

#[test]
fn test_parse_args_baseline_equals() {
    let args: Vec<String> = vec!["--baseline=/tmp/base.json".into()];
    let result = parse_subcommand_args(&args).expect("should parse --baseline=path");
    assert_eq!(result.baseline.as_deref(), Some("/tmp/base.json"));
}

#[test]
fn test_parse_args_baseline_missing_value() {
    let args: Vec<String> = vec!["--baseline".into()];
    assert!(parse_subcommand_args(&args).is_err());
}

#[test]
fn test_parse_args_no_baseline_by_default() {
    let args: Vec<String> = vec!["test.rs".into()];
    let result = parse_subcommand_args(&args).expect("should parse without --baseline");
    assert!(result.baseline.is_none());
}

#[test]
fn test_parse_args_baseline_with_format_and_file() {
    let args: Vec<String> = vec![
        "test.rs".into(),
        "--baseline".into(),
        "base.json".into(),
        "--format".into(),
        "json".into(),
    ];
    let result = parse_subcommand_args(&args).expect("should parse combined args");
    assert_eq!(result.baseline.as_deref(), Some("base.json"));
    assert_eq!(result.format, OutputFormat::Json);
    assert!(result.is_single_file);
    assert_eq!(result.passthrough, vec!["test.rs"]);
}

#[test]
fn test_resolve_project_root_prefers_manifest_path() {
    let cwd = temp_test_dir("project-root-manifest");
    let args: Vec<String> = vec!["--manifest-path".into(), "workspace/member/Cargo.toml".into()];
    let sub_args = parse_subcommand_args(&args).expect("should parse args");

    let resolved = resolve_project_root_from(&sub_args, &cwd);
    assert_eq!(resolved.root, cwd.join("workspace/member"));
    assert_eq!(resolved.manifest_path, Some(cwd.join("workspace/member/Cargo.toml")));
    assert_eq!(resolved.single_file_path, None);
}

#[test]
fn test_resolve_project_root_uses_single_file_parent() {
    let cwd = temp_test_dir("project-root-file");
    let args: Vec<String> = vec!["src/bin/demo.rs".into()];
    let sub_args = parse_subcommand_args(&args).expect("should parse args");

    let resolved = resolve_project_root_from(&sub_args, &cwd);
    assert_eq!(resolved.root, cwd.join("src/bin"));
    assert_eq!(resolved.manifest_path, None);
    assert_eq!(resolved.single_file_path, Some(cwd.join("src/bin/demo.rs")));
}

#[test]
fn test_resolve_project_root_walks_up_to_manifest_ancestor() {
    let root = temp_test_dir("project-root-ancestor");
    let cwd = root.join("member/src/nested");
    std::fs::create_dir_all(&cwd).expect("should create nested cwd");
    std::fs::write(
        root.join("member/Cargo.toml"),
        r#"
[package]
name = "member"
version = "0.1.0"
edition = "2021"
"#,
    )
    .expect("should write Cargo.toml");

    let sub_args = parse_subcommand_args(&[]).expect("should parse empty args");
    let resolved = resolve_project_root_from(&sub_args, &cwd);
    assert_eq!(resolved.root, root.join("member"));
    assert_eq!(resolved.manifest_path, Some(root.join("member/Cargo.toml")));

    let _ = std::fs::remove_dir_all(&root);
}

// -- Current flag parsing tests --

#[test]
fn test_parse_args_current_flag() {
    let args: Vec<String> = vec!["--current".into(), "current.json".into()];
    let result = parse_subcommand_args(&args).expect("should parse --current");
    assert_eq!(result.current.as_deref(), Some("current.json"));
}

#[test]
fn test_parse_args_current_equals() {
    let args: Vec<String> = vec!["--current=/tmp/cur.json".into()];
    let result = parse_subcommand_args(&args).expect("should parse --current=path");
    assert_eq!(result.current.as_deref(), Some("/tmp/cur.json"));
}

#[test]
fn test_parse_args_current_missing_value() {
    let args: Vec<String> = vec!["--current".into()];
    assert!(parse_subcommand_args(&args).is_err());
}

#[test]
fn test_parse_args_no_current_by_default() {
    let args: Vec<String> = vec!["test.rs".into()];
    let result = parse_subcommand_args(&args).expect("should parse without --current");
    assert!(result.current.is_none());
}

#[test]
fn test_parse_args_baseline_and_current() {
    let args: Vec<String> = vec![
        "--baseline".into(),
        "base.json".into(),
        "--current".into(),
        "cur.json".into(),
        "--format".into(),
        "json".into(),
    ];
    let result = parse_subcommand_args(&args).expect("should parse combined args");
    assert_eq!(result.baseline.as_deref(), Some("base.json"));
    assert_eq!(result.current.as_deref(), Some("cur.json"));
    assert_eq!(result.format, OutputFormat::Json);
}

// -- Trust note parsing tests --

#[test]
fn test_parse_trust_note_proved_em_dash() {
    let line =
        "note: Trust [overflow:add]: arithmetic overflow (Add) \u{2014} PROVED (ay-smtlib, 8ms)";
    let result = parse_trust_note(line).expect("should parse proved note");
    assert_eq!(result.kind, "overflow:add");
    assert_eq!(result.message, "arithmetic overflow (Add)");
    assert_eq!(result.outcome, VerificationOutcome::Proved);
    assert_eq!(result.backend, "ay-smtlib");
    assert_eq!(result.time_ms, Some(8));
}

#[test]
fn test_parse_trust_note_failed_ascii_dash() {
    let line = "note: Trust [overflow:add]: arithmetic overflow (Add) -- FAILED (ay-smtlib, 12ms)";
    let result = parse_trust_note(line).expect("should parse failed note");
    assert_eq!(result.kind, "overflow:add");
    assert_eq!(result.message, "arithmetic overflow (Add)");
    assert_eq!(result.outcome, VerificationOutcome::Failed);
    assert_eq!(result.backend, "ay-smtlib");
    assert_eq!(result.time_ms, Some(12));
}

#[test]
fn test_parse_trust_note_div_by_zero() {
    let line = "note: Trust [div_by_zero]: division by zero (Div) -- PROVED (ay-smtlib, 3ms)";
    let result = parse_trust_note(line).expect("should parse div note");
    assert_eq!(result.kind, "div_by_zero");
    assert_eq!(result.outcome, VerificationOutcome::Proved);
    assert_eq!(result.time_ms, Some(3));
}

#[test]
fn test_parse_trust_note_no_time() {
    let line = "note: Trust [bounds]: array index out of bounds -- PROVED (mock)";
    let result = parse_trust_note(line).expect("should parse note without time");
    assert_eq!(result.kind, "bounds");
    assert_eq!(result.outcome, VerificationOutcome::Proved);
    assert_eq!(result.backend, "mock");
    assert_eq!(result.time_ms, None);
}

#[test]
fn test_parse_trust_note_not_a_trust_line() {
    assert!(parse_trust_note("error[E0308]: mismatched types").is_none());
    assert!(parse_trust_note("warning: unused variable").is_none());
    assert!(parse_trust_note("").is_none());
}

#[test]
fn test_parse_trust_note_with_prefix_whitespace() {
    let line = "   note: Trust [overflow:add]: msg -- PROVED (ay-smtlib, 1ms)";
    let result = parse_trust_note(line).expect("should parse with leading spaces");
    assert_eq!(result.outcome, VerificationOutcome::Proved);
}

#[test]
fn test_transport_to_verification_result_preserves_structure() {
    let span = trust_types::SourceSpan {
        file: "src/lib.rs".into(),
        line_start: 7,
        col_start: 5,
        line_end: 7,
        col_end: 16,
    };
    let counterexample = trust_types::Counterexample::new(vec![(
        "divisor".into(),
        trust_types::CounterexampleValue::Int(0),
    )]);
    let transport = trust_types::TransportObligationResult {
        obligation_id: None,
        claim_digest_sha256: None,
        kind: "div_by_zero".into(),
        typed_kind: None,
        description: "division by zero".into(),
        location: Some(span.clone()),
        outcome: trust_types::Outcome::Failed,
        solver: "ay-smtlib".into(),
        time_ms: 9,
        counterexample: Some("divisor = 0".into()),
        counterexample_model: Some(counterexample.clone()),
        reason: Some("solver produced a concrete witness".into()),
        design_mandate: false,
        native_trust_ir: None,
        proof_evidence: None,
        monitor: None,
    };

    let result = transport_to_verification_result("crate::math::divide", &transport);
    assert_eq!(result.function, "crate::math::divide");
    assert_eq!(result.location, Some(span));
    assert_eq!(
        result.counterexample.as_ref().map(ToString::to_string),
        Some(counterexample.to_string())
    );
    assert_eq!(result.reason.as_deref(), Some("solver produced a concrete witness"));
    assert!(crate::types::structured_transport_evidence(&result).is_none());
}

#[test]
fn test_transport_to_verification_result_preserves_monitor_only_evidence() {
    let monitor = trust_types::TransportMonitorEvidence {
        status: trust_types::TransportMonitorStatus::Unmonitored,
        reason: "quantified propositions have no finite runtime monitor".into(),
        predicate_digest: format!("sha256:{}", "d".repeat(64)),
    };
    let transport = trust_types::TransportObligationResult {
        obligation_id: None,
        claim_digest_sha256: None,
        kind: "postcondition".into(),
        typed_kind: None,
        description: "quantified postcondition".into(),
        location: None,
        outcome: trust_types::Outcome::Unknown,
        solver: "trust-full-verifier".into(),
        time_ms: 0,
        counterexample: None,
        counterexample_model: None,
        reason: Some("static proof remains open".into()),
        design_mandate: false,
        native_trust_ir: None,
        proof_evidence: None,
        monitor: Some(monitor.clone()),
    };

    let result = transport_to_verification_result("crate::quantified", &transport);
    assert!(!result.raw_line.is_empty(), "monitor-only evidence needs a structured envelope");
    let structured = crate::types::structured_transport_evidence(&result)
        .expect("monitor-only structured transport evidence");
    assert_eq!(structured.monitor, Some(monitor));
    assert!(structured.obligation_id.is_none());
    assert!(structured.native_trust_ir.is_none());
    assert!(structured.proof_evidence.is_none());
}

#[test]
fn test_transport_to_verification_result_rejects_nested_proved_when_top_level_unknown() {
    let transport = trust_types::TransportObligationResult {
        obligation_id: Some("obl-cache".into()),
        claim_digest_sha256: None,
        kind: "postcondition".into(),
        typed_kind: None,
        description: "cached proof-looking row".into(),
        location: None,
        outcome: trust_types::Outcome::Unknown,
        solver: "trust-full-verifier".into(),
        time_ms: 9,
        counterexample: None,
        counterexample_model: None,
        reason: Some("cache replay row".into()),
        design_mandate: false,
        native_trust_ir: None,
        proof_evidence: Some(trust_types::TransportProofEvidence {
            suite: "trust-wp".into(),
            backend: "trust-full-verifier".into(),
            request_id: Some("req-cache".into()),
            proof_id: Some("proof-cache".into()),
            native_id: Some("native-cache".into()),
            status: trust_types::TransportProofStatus::Proved,
            strength: Some(trust_types::ProofStrength::deductive()),
            evidence: Some(trust_types::ProofEvidence::from(
                trust_types::ProofStrength::deductive(),
            )),
            artifacts: Vec::new(),
            diagnostics: Vec::new(),
        }),
        monitor: None,
    };

    let result = transport_to_verification_result("crate::math::cached", &transport);

    assert_eq!(result.outcome, VerificationOutcome::Unknown);
    assert_eq!(result.reason.as_deref(), Some("cache replay row"));
}

// -- Config tests --

#[test]
fn test_trust_config_default() {
    let config = TrustConfig::default();
    assert!(config.enabled);
    // Strict-by-default doctrine: default level is L2 (dial down via [trust]).
    assert_eq!(config.level, "L2");
    assert_eq!(config.timeout_ms, 5000);
    assert_eq!(config.function_budget_ms, 120_000);
    assert!(config.codegen_backend.is_none());
    assert_eq!(config.hardened, None);
    assert!(config.trust_profile.is_none());
}

#[test]
fn test_trust_config_load_nonexistent() {
    let config = TrustConfig::load_for_verification(Path::new("/nonexistent/path"), None)
        .expect("a missing policy file uses verified defaults");
    assert!(config.enabled);
    assert_eq!(config.level, "L2");
    assert_eq!(config.hardened, None);
    assert!(config.trust_profile.is_none());
}

#[test]
fn test_trust_config_rejects_removed_verify_functions_key() {
    let root = temp_test_dir("removed-verify-functions-config");
    write_trust_table(&root, "verify_functions = [\"critical::\"]\n");

    let error = TrustConfig::load_for_verification(&root, None)
        .expect_err("the removed, never-wired verify_functions key must fail closed");

    assert_eq!(error.action, "validate");
    assert!(
        error.detail.contains("unknown field `verify_functions`"),
        "unexpected validation error: {error}"
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_trust_config_rejects_removed_solver_memory_limit_key() {
    let root = temp_test_dir("removed-solver-memory-limit-config");
    write_trust_table(&root, "solver_memory_limit_mb = 2048\n");

    let error = TrustConfig::load_for_verification(&root, None)
        .expect_err("the unwired solver_memory_limit_mb key must fail closed");

    assert_eq!(error.action, "validate");
    assert!(
        error.detail.contains("unknown field `solver_memory_limit_mb`"),
        "unexpected validation error: {error}"
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_trust_config_rejects_zero_timeout() {
    let root = temp_test_dir("zero-timeout-config");
    write_trust_table(&root, "timeout_ms = 0\n");

    let error = TrustConfig::load_for_verification(&root, None)
        .expect_err("a zero verifier timeout must fail closed");

    assert_eq!(error.action, "parse");
    assert!(
        error.detail.contains("timeout_ms must be greater than zero"),
        "unexpected parse error: {error}"
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_trust_config_loads_and_validates_function_budget() {
    let root = temp_test_dir("function-budget-config");
    write_trust_table(&root, "function_budget_ms = 45000\n");

    let config = TrustConfig::load_for_verification(&root, None)
        .expect("a positive tracked function budget must load");
    assert_eq!(config.function_budget_ms, 45_000);

    write_trust_table(&root, "function_budget_ms = 0\n");
    let error = TrustConfig::load_for_verification(&root, None)
        .expect_err("a zero whole-function budget must fail closed");
    assert_eq!(error.action, "parse");
    assert!(
        error.detail.contains("function_budget_ms must be greater than zero"),
        "unexpected parse error: {error}"
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_trust_config_loads_trust_profile() {
    let root = temp_test_dir("trust-profile-config");
    write_trust_table(&root, "trust_profile = \"coreutils_hardened\"\n");

    let config = TrustConfig::load_for_verification(&root, None).expect("valid trust profile config");

    assert_eq!(config.trust_profile.as_deref(), Some("coreutils_hardened"));

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_trust_config_loads_hardened_opt_out() {
    let root = temp_test_dir("trust-hardened-config");
    write_trust_table(
        &root,
        "hardened = false\ntrust_profile = \"coreutils_hardened\"\n",
    );

    let config = TrustConfig::load_for_verification(&root, None).expect("valid hardened config");

    assert_eq!(config.hardened, Some(false));
    assert_eq!(config.trust_profile.as_deref(), Some("coreutils_hardened"));

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

// -- Utility tests --

#[test]
fn test_level_to_num() {
    assert_eq!(level_to_num("L0"), 0);
    assert_eq!(level_to_num("L1"), 1);
    assert_eq!(level_to_num("L2"), 2);
    assert_eq!(level_to_num("unknown"), 0);
}

fn args_include_z_flag(args: &[String], flag: &str) -> bool {
    args.windows(2).any(|pair| pair[0] == "-Z" && pair[1] == flag)
        || args.iter().any(|arg| arg == &format!("-Z{flag}"))
}

fn args_include_z_option_prefix(args: &[String], prefix: &str) -> bool {
    args.windows(2).any(|pair| pair[0] == "-Z" && pair[1].starts_with(prefix))
        || args
            .iter()
            .any(|arg| arg.strip_prefix("-Z").is_some_and(|option| option.starts_with(prefix)))
}

fn codegen_option_values(args: &[String], name: &str) -> Vec<String> {
    let mut values = Vec::new();
    let mut index = 0;
    while index < args.len() {
        let option = if args[index] == "-C" {
            index += 1;
            args.get(index).map(String::as_str)
        } else {
            args[index].strip_prefix("-C").filter(|option| !option.is_empty())
        };
        if let Some(value) = option.and_then(|option| option.strip_prefix(&format!("{name}="))) {
            values.push(value.to_string());
        }
        index += 1;
    }
    values
}

#[test]
fn test_build_native_command_default_uses_raw_unscoped_batteries_on_policy() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    let sub_args = parse_subcommand_args(&["examples/midpoint.rs".into()])
        .expect("should parse single-file args");
    let cmd = build_native_command(rustc, Subcommand::Check, &sub_args, &config);

    assert!(
        cmd.iter().any(|arg| arg.starts_with("trust-verify-level=")),
        "default targo-trust checks must still configure the verification level: {cmd:?}"
    );
    assert!(!args_include_z_option_prefix(&cmd, "trust-verify-crate-role="));
    assert!(!args_include_z_option_prefix(&cmd, "trust-verify-package-name="));
    assert!(
        !args_include_z_flag(&cmd, "trust-policy=advisory"),
        "the default lane is strict, never advisory: {cmd:?}"
    );
    assert_eq!(codegen_option_values(&cmd, "overflow-checks"), ["yes"]);
    assert_eq!(codegen_option_values(&cmd, "debug-assertions"), ["yes"]);
}

#[test]
fn test_build_native_command_explicit_crate_name_remains_raw_unscoped() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    let sub_args = parse_subcommand_args(&[
        "examples/midpoint.rs".into(),
        "--crate-name".into(),
        "renamed_midpoint".into(),
    ])
    .expect("should parse explicit crate name");
    let cmd = build_native_command(rustc, Subcommand::Check, &sub_args, &config);

    assert!(cmd.windows(2).any(|pair| pair[0] == "--crate-name" && pair[1] == "renamed_midpoint"));
    assert!(!args_include_z_option_prefix(&cmd, "trust-verify-crate-role="));
    assert!(!args_include_z_option_prefix(&cmd, "trust-verify-package-name="));
}

#[test]
fn test_build_native_command_rejects_strict_single_file_safety_overrides() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    for override_args in [
        vec!["examples/midpoint.rs".into(), "-Coverflow-checks=no".into()],
        vec!["examples/midpoint.rs".into(), "-C".into(), "debug-assertions=false".into()],
    ] {
        let sub_args = parse_subcommand_args(&override_args).expect("parse direct rustc args");
        let error = build_native_command_with_json_transport(
            rustc,
            Subcommand::Check,
            &sub_args,
            &config,
            None,
            true,
        )
        .expect_err("strict safety-check codegen policy is reserved");
        assert!(error.contains("conflicts with strict verification"), "{error}");
    }
}

#[test]
fn test_build_native_command_rejects_uninspectable_single_file_argfiles() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    for hidden in [
        "@disable-verification.args",
        "@level.args",
        "@backend.args",
        "@output-gate.args",
        "@allow_l0_gaps.args",
        "@shell:policy.args",
        "@",
    ] {
        let sub_args = parse_subcommand_args(&["examples/midpoint.rs".into(), hidden.into()])
            .expect("parse direct rustc argfile fixture");
        let error = build_native_command_with_json_transport(
            rustc,
            Subcommand::Check,
            &sub_args,
            &config,
            Some("trust-cg"),
            true,
        )
        .expect_err("an unexpanded argfile must never enter an evidence-grade rustc command");
        assert!(error.contains("argfiles"), "{hidden}: {error}");
    }
}

#[test]
fn test_build_native_command_rejects_single_file_semantic_separator() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    // The first `--` is targo-trust's wrapper boundary and is consumed by the
    // parser. The second would reach rustc and could strand canonical `-C`
    // policy outside rustc's option parser.
    let sub_args = parse_subcommand_args(&[
        "examples/midpoint.rs".into(),
        "--".into(),
        "--".into(),
        "-Ztrust-verify=off".into(),
    ])
    .expect("parse nested separator fixture");
    let error = build_native_command_with_json_transport(
        rustc,
        Subcommand::Check,
        &sub_args,
        &config,
        None,
        true,
    )
    .expect_err("semantic rustc separator must fail closed");
    assert!(error.contains("semantic `--` separator"), "{error}");
}

#[test]
fn test_build_native_command_rejects_retired_single_file_valtree_limit_spellings() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    for retired in [
        vec!["-Zvaltree-node-limit=200000".into()],
        vec!["-Z".into(), "valtree-node-limit=200000".into()],
        vec!["-Zvaltree_node_limit=200000".into()],
        vec!["-Z".into(), "valtree_node_limit=200000".into()],
    ] {
        let mut args = vec!["examples/midpoint.rs".into(), "--crate-name=trust_ir".into()];
        args.extend(retired);
        let sub_args = parse_subcommand_args(&args).expect("parse retired valtree option fixture");
        let error = build_native_command_with_json_transport(
            rustc,
            Subcommand::Check,
            &sub_args,
            &config,
            None,
            true,
        )
        .expect_err("retired valtree limit must not reach direct trustc");
        assert!(error.contains("retired `-Zvaltree-node-limit`"), "{error}");
        assert!(error.contains("fixed valtree resource limit"), "{error}");
    }
}

#[test]
fn test_build_native_command_rejects_in_process_llvm_extension_channels() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    for extension_args in [
        vec!["-Zllvm_plugins=/tmp/forged.dylib".into()],
        vec!["-Z".into(), "llvm-plugins=/tmp/forged.dylib".into()],
        vec!["--codegen=llvm_args=-load=/tmp/forged.dylib".into()],
        vec!["--codegen".into(), "llvm-args=-load=/tmp/forged.dylib".into()],
    ] {
        let mut args = vec!["examples/midpoint.rs".into()];
        args.extend(extension_args);
        let sub_args = parse_subcommand_args(&args).expect("parse LLVM extension fixture");
        let error = build_native_command_with_json_transport(
            rustc,
            Subcommand::Check,
            &sub_args,
            &config,
            None,
            true,
        )
        .expect_err("in-process extension channel must fail closed");
        assert!(error.contains("in-process extension"), "{error}");
    }
}

#[test]
fn test_direct_custom_target_rejects_nonempty_llvm_args() {
    let root = temp_test_dir("direct-custom-target-llvm-args");
    std::fs::create_dir_all(&root).expect("create custom-target fixture directory");
    let target = root.join("forged.json");
    std::fs::write(
        &target,
        r#"{"llvm-target":"x86_64-unknown-linux-gnu","llvm-args":["-load=/tmp/forged.dylib"]}"#,
    )
    .expect("write custom-target fixture");

    let args = vec!["examples/midpoint.rs".into(), format!("--target={}", target.display())];
    let sub_args = parse_subcommand_args(&args).expect("parse custom-target fixture");
    let error = build_native_command_with_json_transport(
        Path::new("/tmp/rustc"),
        Subcommand::Check,
        &sub_args,
        &TrustConfig::default(),
        None,
        true,
    )
    .expect_err("custom target LLVM arguments must fail closed");
    assert!(error.contains("custom-target `llvm-args`"), "{error}");
    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn test_build_native_command_rejects_unauthenticated_direct_extern_proc_macro_boundary() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    for extern_args in [
        vec!["--extern=maybe_macro=/tmp/libmaybe_macro.so".into()],
        vec!["--extern".into(), "maybe_macro=/tmp/libmaybe_macro.so".into()],
    ] {
        let mut args = vec!["examples/midpoint.rs".into()];
        args.extend(extern_args);
        let sub_args = parse_subcommand_args(&args).expect("parse direct extern fixture");
        let error = build_native_command_with_json_transport(
            rustc,
            Subcommand::Check,
            &sub_args,
            &config,
            None,
            true,
        )
        .expect_err("raw transport cannot distinguish an in-process proc macro extern");
        assert!(error.contains("proc macro"), "{error}");
        assert!(error.contains("TRUSTJSON"), "{error}");
        assert!(error.contains("no-proc-macro TCB boundary"), "{error}");
    }
}

#[test]
fn test_build_native_command_rejects_direct_compiler_early_exit_controls() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    for early_exit in [
        vec!["--help".into()],
        vec!["--version".into()],
        vec!["--print=cfg".into()],
        vec!["--emit=dep-info".into()],
        vec!["--emit".into(), "dep-info=fixture.d".into()],
        vec!["-Zno-analysis".into()],
        vec!["-Zno_analysis".into()],
        vec!["-Z".into(), "parse-crate-root-only".into()],
        vec!["-Z".into(), "parse_crate_root_only".into()],
        vec!["-Ztrust-dump=mir-only:<dir>".into()],
        vec!["-Ztrust_dump=mir-only:<dir>".into()],
        vec!["-Chelp".into()],
        vec!["--codegen".into(), "help".into()],
        vec!["-Whelp".into()],
    ] {
        let mut args = vec!["examples/midpoint.rs".into()];
        args.extend(early_exit.iter().cloned());
        let sub_args = parse_subcommand_args(&args).expect("parse early-exit fixture");
        let error = build_native_command_with_json_transport(
            rustc,
            Subcommand::Check,
            &sub_args,
            &config,
            None,
            true,
        )
        .expect_err("evidence-grade direct compilation must reach verification coverage");
        assert!(
            error.contains("exits before authenticated Trust coverage"),
            "{early_exit:?}: {error}"
        );
    }
}

#[test]
fn test_build_native_command_allows_dep_info_alongside_a_real_output() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    let sub_args =
        parse_subcommand_args(&["examples/midpoint.rs".into(), "--emit=dep-info,metadata".into()])
            .expect("parse multi-output fixture");
    let command = build_native_command_with_json_transport(
        rustc,
        Subcommand::Check,
        &sub_args,
        &config,
        None,
        true,
    )
    .expect("a real compiler output reaches analysis and verification");
    assert!(command.iter().any(|arg| arg == "--emit=dep-info,metadata"));
}

#[test]
fn test_build_native_command_rejects_all_direct_owned_policy_spellings() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    for override_args in [
        vec!["examples/midpoint.rs".into(), "-Ztrust-verify=off".into()],
        vec!["examples/midpoint.rs".into(), "-Z".into(), "trust-verify-level=0".into()],
        vec!["examples/midpoint.rs".into(), "-Ztrust_verify_level=0".into()],
        vec!["examples/midpoint.rs".into(), "-Zcodegen-backend=llvm".into()],
        vec!["examples/midpoint.rs".into(), "-Zcodegen_backend=llvm".into()],
        vec!["examples/midpoint.rs".into(), "-Ztrust-cg-output-gate=allow-unknown".into()],
        vec!["examples/midpoint.rs".into(), "-Ztrust-policy=advisory".into()],
    ] {
        let sub_args = parse_subcommand_args(&override_args).expect("parse policy override");
        let error = build_native_command_with_json_transport(
            rustc,
            Subcommand::Check,
            &sub_args,
            &config,
            Some("trust-cg"),
            true,
        )
        .expect_err("direct caller cannot own verifier policy");
        assert!(error.contains("conflicts with targo-trust's verifier policy"), "{error}");
    }
}

#[test]
fn test_build_native_command_canonicalizes_matching_single_file_safety_flags() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    let sub_args = parse_subcommand_args(&[
        "examples/midpoint.rs".into(),
        "-Coverflow-checks=true".into(),
        "-C".into(),
        "debug-assertions=on".into(),
        "--codegen=overflow_checks=yes".into(),
        "--codegen".into(),
        "debug_assertions=true".into(),
    ])
    .expect("parse matching direct rustc safety flags");
    let cmd = build_native_command_with_json_transport(
        rustc,
        Subcommand::Check,
        &sub_args,
        &config,
        None,
        true,
    )
    .expect("matching strict safety policy should canonicalize");

    assert_eq!(codegen_option_values(&cmd, "overflow-checks"), ["yes"]);
    assert_eq!(codegen_option_values(&cmd, "debug-assertions"), ["yes"]);
}

#[test]
fn test_build_native_command_allow_l0_gaps_omits_full_verifier_for_single_file() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    let sub_args =
        parse_subcommand_args(&["--allow-l0-gaps".into(), "examples/midpoint.rs".into()])
            .expect("should parse --allow-l0-gaps with single-file args");
    let cmd = build_native_command(rustc, Subcommand::Check, &sub_args, &config);

    assert!(!args_include_z_flag(&cmd, "trust-verify"));
    assert!(
        cmd.iter().any(|arg| arg.starts_with("trust-verify-level=")),
        "--allow-l0-gaps should still configure the verification level: {cmd:?}"
    );
    assert!(
        !args_include_z_flag(&cmd, "trust-verify-full"),
        "--allow-l0-gaps should run raw warning mode instead of full verifier mode: {cmd:?}"
    );
    // Trust (assumption ledger): --allow-l0-gaps now delivers its documented
    // "warning mode" semantics via advisory allow_l0_gaps mode.
    assert!(
        args_include_z_flag(&cmd, "trust-policy=advisory"),
        "--allow-l0-gaps selects advisory -Z trust-policy=advisory: {cmd:?}"
    );
    assert!(codegen_option_values(&cmd, "overflow-checks").is_empty());
    assert!(codegen_option_values(&cmd, "debug-assertions").is_empty());
}

#[test]
fn test_full_verifier_flag_is_rejected_batteries_on() {
    // Batteries-on: the full verifier runs by default; there is no enable flag. `--full-verifier`
    // was an enable/tightener flag whose compiler injection was already a no-op, so it
    // is REMOVED — flags may only remove power, never grant it.
    let err = parse_subcommand_args(&["--full-verifier".into(), "examples/midpoint.rs".into()])
        .expect_err("--full-verifier must be rejected (batteries-on default)");
    assert!(
        err.to_string().contains("--full-verifier has been removed"),
        "rejection must name the removed flag: {err}"
    );
}

#[test]
fn test_merged_rustflags_empty_env() {
    let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let _rustflags = TestEnvVar::unset("RUSTFLAGS");
    let flags = merged_rustflags("L1");
    assert!(!args_include_z_flag(
        &flags.split_whitespace().map(str::to_string).collect::<Vec<_>>(),
        "trust-verify"
    ));
    assert!(flags.contains("trust-verify-level=1"));
    assert!(flags.contains("trust-verify-output=json"));
    assert!(flags.contains("codegen-backend=llvm"));
}

#[test]
fn test_default_backend_is_pinned_against_plain_and_encoded_ambient_aliases() {
    let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());

    {
        let _encoded = TestEnvVar::unset("CARGO_ENCODED_RUSTFLAGS");
        let _plain = TestEnvVar::set(
            "RUSTFLAGS",
            "-Zcodegen_backend=trust_cg -Zllvm_plugins=/tmp/forged.dylib --codegen=llvm_args=-load=/tmp/forged.dylib",
        );
        let CargoRustflags::Plain(flags) =
            merged_cargo_rustflags_with_options("L1", None, true, true, false)
        else {
            panic!("plain ambient flags should remain plain");
        };
        assert!(flags.contains("codegen-backend=llvm"), "{flags}");
        assert!(!flags.contains("codegen_backend=trust_cg"), "{flags}");
        assert!(!flags.contains("forged.dylib"), "{flags}");
        assert!(!flags.contains("llvm_args"), "{flags}");
    }

    {
        let _plain = TestEnvVar::set("RUSTFLAGS", "-C opt-level=2");
        let _encoded = TestEnvVar::set(
            "CARGO_ENCODED_RUSTFLAGS",
            "-Zcodegen-backend=trust_cg\x1f-Zllvm-plugins=/tmp/forged.dylib\x1f--codegen\x1fllvm-args=-load=/tmp/forged.dylib",
        );
        let CargoRustflags::Encoded(flags) =
            merged_cargo_rustflags_with_options("L1", None, true, true, false)
        else {
            panic!("encoded ambient flags should remain encoded");
        };
        assert!(flags.contains("codegen-backend=llvm"), "{flags}");
        assert!(!flags.contains("codegen-backend=trust_cg"), "{flags}");
        assert!(!flags.contains("forged.dylib"), "{flags}");
        assert!(!flags.contains("llvm-args"), "{flags}");
    }
}

#[test]
fn test_merged_rustflags_without_json_transport() {
    let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let _rustflags = TestEnvVar::unset("RUSTFLAGS");
    let flags = merged_rustflags_with_json_transport("L1", None, false);
    assert!(!args_include_z_flag(
        &flags.split_whitespace().map(str::to_string).collect::<Vec<_>>(),
        "trust-verify"
    ));
    assert!(flags.contains("trust-verify-level=1"));
    assert!(!flags.contains("trust-verify-output=json"));
}

#[test]
fn test_merged_rustflags_with_explicit_codegen_backend() {
    let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let _rustflags = TestEnvVar::unset("RUSTFLAGS");
    let flags = merged_rustflags_with_backend("L1", Some("trust-cg"));
    assert!(flags.contains("codegen-backend=trust-cg"));
    assert!(flags.contains("trust-cg-output-gate=strict"));
}

#[test]
fn test_trust_cg_output_gate_tracks_plain_and_encoded_verifier_lanes() {
    let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let _plain = TestEnvVar::unset("RUSTFLAGS");
    let _encoded = TestEnvVar::unset("CARGO_ENCODED_RUSTFLAGS");

    let strict = merged_rustflags_with_options("L2", Some("trust-cg"), true, true, false);
    assert!(strict.contains("trust-cg-output-gate=strict"));
    assert!(!strict.contains("trust-cg-output-gate=allow-unknown"));
    let strict_args = strict.split_whitespace().map(str::to_string).collect::<Vec<_>>();
    assert_eq!(codegen_option_values(&strict_args, "overflow-checks"), ["yes"]);
    assert_eq!(codegen_option_values(&strict_args, "debug-assertions"), ["yes"]);

    let advisory = merged_rustflags_with_options("L2", Some("trust-cg"), true, false, true);
    assert!(advisory.contains("trust-cg-output-gate=allow-unknown"));
    assert!(!advisory.contains("trust-cg-output-gate=strict"));
    let advisory_args = advisory.split_whitespace().map(str::to_string).collect::<Vec<_>>();
    assert!(codegen_option_values(&advisory_args, "overflow-checks").is_empty());
    assert!(codegen_option_values(&advisory_args, "debug-assertions").is_empty());

    let _encoded = TestEnvVar::set(
        "CARGO_ENCODED_RUSTFLAGS",
        "--codegen=incremental=/tmp/hostile-cache\x1f--codegen\x1fcodegen_units=8\x1f-C\x1fdebuginfo=1",
    );
    let CargoRustflags::Encoded(encoded) =
        merged_cargo_rustflags_with_options("L2", Some("trust-cg"), true, true, false)
    else {
        panic!("encoded Cargo flags must remain encoded");
    };
    assert!(encoded.contains("\x1ftrust-cg-output-gate=strict"));
    assert!(!encoded.contains("trust-cg-output-gate=allow-unknown"));
    assert!(!encoded.contains("hostile-cache"));
    assert!(!encoded.contains("codegen_units=8"));
}

#[test]
fn test_merged_full_rustflags_replace_ambient_safety_check_bypasses() {
    let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let _encoded = TestEnvVar::unset("CARGO_ENCODED_RUSTFLAGS");
    let _plain = TestEnvVar::set(
        "RUSTFLAGS",
        "--codegen=overflow_checks=no --codegen debug_assertions=off -C opt-level=2",
    );

    let flags = merged_rustflags_with_options("L2", None, true, true, false);
    let args = flags.split_whitespace().map(str::to_string).collect::<Vec<_>>();
    assert_eq!(codegen_option_values(&args, "overflow-checks"), ["yes"]);
    assert_eq!(codegen_option_values(&args, "debug-assertions"), ["yes"]);
    assert!(args.windows(2).any(|pair| pair[0] == "-C" && pair[1] == "opt-level=2"));
}

#[test]
fn test_merged_rustflags_stale_full_verifier_disable_cannot_suppress_verification() {
    // Batteries-on: `-Z trust-verify-full` was DELETED from the compiler (strict is
    // the crate-under-check default; there is no enable flag), so a stale
    // `-Z trust-verify-full=false` inherited via RUSTFLAGS must neither suppress
    // targo's verification configuration nor trick targo into appending the deleted
    // positive flag. (This replaces the old assertion that targo re-appends a bare
    // `-Z trust-verify-full` — nothing emits that flag anymore and the compiler no
    // longer parses it.)
    let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let _rustflags = TestEnvVar::set("RUSTFLAGS", "-C debuginfo=1 -Z trust-verify-full=false");
    let flags = merged_rustflags_with_options("L1", None, true, true, false);

    assert!(
        flags.contains("trust-verify-level="),
        "a stale inherited full-verifier disable flag must not suppress targo's \
         verification configuration: {flags}"
    );
    assert!(
        !args_include_z_flag(
            &flags.split_whitespace().map(str::to_string).collect::<Vec<_>>(),
            "trust-verify-full"
        ),
        "targo must never emit the deleted bare `-Z trust-verify-full`: {flags}"
    );
}

#[test]
fn test_merged_rustflags_strips_retired_and_cargo_owned_scope_metadata() {
    let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let _rustflags = TestEnvVar::set(
        "RUSTFLAGS",
        "-Ztrust-verify-target=forged -Ztrust-verify-crate-role=primary \
         -Ztrust-verify-package-name=forged",
    );

    let flags = merged_rustflags_with_options("L1", None, true, true, false);
    for reserved in ["trust-verify-target", "trust-verify-crate-role", "trust-verify-package-name"]
    {
        assert!(!flags.contains(reserved), "reserved scope metadata survived: {flags}");
    }
}

#[test]
fn test_merged_rustflags_preserves_retired_valtree_limit_for_targo_rejection() {
    let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());

    {
        let _encoded = TestEnvVar::unset("CARGO_ENCODED_RUSTFLAGS");
        let _plain = TestEnvVar::set("RUSTFLAGS", "-Z valtree-node-limit=200000");
        let CargoRustflags::Plain(plain) =
            merged_cargo_rustflags_with_options("L1", None, true, true, false)
        else {
            panic!("plain ambient rustflags must remain plain");
        };
        let args = plain.split_whitespace().collect::<Vec<_>>();
        assert!(
            args.windows(2).any(|pair| pair == ["-Z", "valtree-node-limit=200000"]),
            "targo-trust silently removed the retired option before Targo could reject it: {args:?}"
        );
    }

    {
        let _plain = TestEnvVar::set("RUSTFLAGS", "-C opt-level=0");
        let _encoded = TestEnvVar::set("CARGO_ENCODED_RUSTFLAGS", "-Zvaltree-node-limit=300000");
        let CargoRustflags::Encoded(encoded) =
            merged_cargo_rustflags_with_options("L1", None, true, true, false)
        else {
            panic!("encoded ambient rustflags must remain encoded");
        };
        let args = encoded.split('\x1f').collect::<Vec<_>>();
        assert!(
            args.contains(&"-Zvaltree-node-limit=300000"),
            "targo-trust silently removed the retired encoded option before Targo could reject it: {args:?}"
        );
    }
}

#[test]
fn test_merged_rustflags_replaces_ambient_targo_owned_policy() {
    let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let _rustflags = TestEnvVar::set(
        "RUSTFLAGS",
        "-C opt-level=2 -Ztrust-verify-level=0 -Z trust-verify-output=human \
         -Ztrust-verify-target=wrong -Ztrust-policy=advisory -Zcodegen-backend=llvm \
         -Ztrust-cg-output-gate=allow-unknown \
         -Ztrust-proof-artifact-root=/tmp/forged",
    );

    let flags = merged_rustflags_with_options("L2", Some("trust-cg"), true, true, false);
    assert!(flags.contains("-C opt-level=2"));
    assert!(flags.contains("trust-verify-level=2"));
    assert!(flags.contains("trust-verify-output=json"));
    assert!(!flags.contains("trust-verify-target"));
    assert!(flags.contains("codegen-backend=trust-cg"));
    assert!(flags.contains("trust-cg-output-gate=strict"));
    for stale in [
        "trust-verify-level=0",
        "trust-verify-output=human",
        "trust-verify-target=wrong",
        "trust-policy=advisory",
        "codegen-backend=llvm",
        "trust-cg-output-gate=allow-unknown",
        "trust-proof-artifact-root=/tmp/forged",
    ] {
        assert!(!flags.contains(stale), "stale ambient policy survived: {flags}");
    }
}

#[test]
fn test_merged_cargo_rustflags_prefers_encoded_env_and_adds_full_verifier() {
    let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let _encoded = TestEnvVar::set(
        "CARGO_ENCODED_RUSTFLAGS",
        "-C\x1fdebuginfo=1\x1f-Coverflow-checks=no\x1f-C\x1fdebug-assertions=false",
    );
    let _plain = TestEnvVar::set("RUSTFLAGS", "-C opt-level=0");

    let flags = merged_cargo_rustflags_with_options("L1", Some("trust-cg"), true, true, false);
    let CargoRustflags::Encoded(encoded) = flags else {
        panic!("encoded Cargo flags must stay encoded when inherited encoded flags are present");
    };
    let args = encoded.split('\x1f').map(str::to_string).collect::<Vec<_>>();

    assert!(args.windows(2).any(|pair| pair[0] == "-C" && pair[1] == "debuginfo=0"));
    assert!(
        !args.windows(2).any(|pair| pair[0] == "-C" && pair[1] == "debuginfo=1"),
        "Trust-CG must replace inherited debuginfo with its supported disabled policy: {args:?}"
    );
    assert!(
        !args.windows(2).any(|pair| pair[0] == "-C" && pair[1] == "opt-level=0"),
        "encoded Cargo rustflags must take precedence over plain RUSTFLAGS: {args:?}"
    );
    assert!(
        !args_include_z_flag(&args, "trust-verify"),
        "full verifier mode activates verification without the advisory flag: {args:?}"
    );
    // Strict verification is batteries-on; no positive activation flag is emitted.
    assert!(!args_include_z_flag(&args, "trust-verify-full"));
    assert!(args.windows(2).any(|pair| pair[0] == "-Z" && pair[1] == "trust-verify-level=1"));
    assert!(args.windows(2).any(|pair| pair[0] == "-Z" && pair[1] == "trust-verify-output=json"));
    assert!(args.windows(2).any(|pair| pair[0] == "-Z" && pair[1] == "codegen-backend=trust-cg"));
    assert_eq!(codegen_option_values(&args, "overflow-checks"), ["yes"]);
    assert_eq!(codegen_option_values(&args, "debug-assertions"), ["yes"]);
}

#[test]
fn test_rejects_passthrough_trust_verify_disable_flags() {
    let separated = vec!["--release".into(), "-Z".into(), "trust-verify=off".into()];
    assert_eq!(find_trust_verify_disable_arg(&separated).as_deref(), Some("-Z trust-verify=off"));

    let combined = vec!["-Ztrust-verify=false".into()];
    assert_eq!(find_trust_verify_disable_arg(&combined).as_deref(), Some("-Z trust-verify=false"));

    let underscore = vec!["-Ztrust_verify=false".into()];
    assert_eq!(
        find_trust_verify_disable_arg(&underscore).as_deref(),
        Some("-Z trust-verify=false")
    );

    let full_false = vec!["-Z".into(), "trust-verify-full=false".into()];
    assert_eq!(
        find_trust_verify_disable_arg(&full_false).as_deref(),
        Some("-Z trust-verify-full=false")
    );

    let full_off = vec!["-Ztrust-verify-full=off".into()];
    assert_eq!(
        find_trust_verify_disable_arg(&full_off).as_deref(),
        Some("-Z trust-verify-full=false")
    );

    for retired in [
        vec!["-Zcontract-checks".into()],
        vec!["-Zcontract-checks=yes".into()],
        vec!["-Zcontract_checks=unexpected".into()],
        vec!["-Z".into(), "contract_checks=no".into()],
    ] {
        assert_eq!(
            find_trust_verify_disable_arg(&retired).as_deref(),
            Some("-Z contract-checks"),
            "the legacy exec projection must be rejected for either value"
        );
    }

    for cargo_value in [
        vec!["--package".into(), "trust-verify=off".into()],
        vec!["--package".into(), "trust-verify=false".into()],
        vec!["--config".into(), "trust-verify-full=false".into()],
    ] {
        assert_eq!(
            find_trust_verify_disable_arg(&cargo_value),
            None,
            "Cargo values are not rustc -Z option bodies: {cargo_value:?}"
        );
    }
}

#[test]
fn test_cargo_context_z_options_are_not_misclassified_as_rustc_policy() {
    let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let _plain = TestEnvVar::unset("RUSTFLAGS");
    let _encoded = TestEnvVar::unset("CARGO_ENCODED_RUSTFLAGS");
    let cargo_args = vec!["-Zcodegen-backend".into(), "--package".into(), "trust-verify=off".into()];
    assert_eq!(
        trust_verify_disable_diagnostic(&cargo_args, false),
        None,
        "Cargo CLI -Z/options must remain distinct from rustc's -Z stream"
    );
}

#[test]
fn test_rejects_passthrough_overrides_of_targo_owned_policy() {
    for args in [
        vec!["-Ztrust-verify-level=0".into()],
        vec!["-Ztrust_verify_level=0".into()],
        vec!["-Z".into(), "trust-verify-output=human".into()],
        vec!["-Ztrust-verify-target=other".into()],
        vec!["-Ztrust-policy=advisory".into()],
        vec!["-Zcodegen-backend=llvm".into()],
        vec!["-Ztrust-proof-artifact-root=/tmp/forged".into()],
    ] {
        let diagnostic = trust_verify_disable_diagnostic(&args, true)
            .unwrap_or_else(|| panic!("policy override should be rejected: {args:?}"));
        assert!(diagnostic.contains("conflicts with targo-trust's verifier policy"));
    }
}

#[test]
fn test_rejects_retired_ambient_function_budget() {
    let _lock = crate::TEST_ENV_LOCK.lock().expect("environment lock");
    let _plain = TestEnvVar::unset("RUSTFLAGS");
    let _encoded = TestEnvVar::unset("CARGO_ENCODED_RUSTFLAGS");
    let _budget = TestEnvVar::set("TRUST_VERIFY_FN_BUDGET_MS", "1");

    let diagnostic = trust_verify_disable_diagnostic(&[], true)
        .expect("retired ambient budget must be rejected before compiler dispatch");
    assert!(diagnostic.contains("function_budget_ms"));
    assert!(diagnostic.contains("[trust]"));
}

#[test]
fn test_rejects_ambient_rustflags_trust_verify_false() {
    assert_eq!(
        find_trust_verify_disable_in_rustflags("-C debuginfo=1 -Z trust-verify=false").as_deref(),
        Some("-Z trust-verify=false")
    );
    assert_eq!(
        find_trust_verify_disable_in_rustflags("-Ztrust-verify=off").as_deref(),
        Some("-Z trust-verify=off")
    );
    assert_eq!(
        find_trust_verify_disable_in_rustflags("-Z trust-verify-full=false").as_deref(),
        Some("-Z trust-verify-full=false")
    );
    assert_eq!(
        find_trust_verify_disable_in_rustflags("-Ztrust_verify_full=false").as_deref(),
        Some("-Z trust-verify-full=false")
    );
    assert_eq!(
        find_trust_verify_disable_in_rustflags("-C opt-level=2 -Zcontract_checks=no").as_deref(),
        Some("-Z contract-checks")
    );
    assert_eq!(
        find_trust_verify_disable_in_rustflags("-Z contract-checks").as_deref(),
        Some("-Z contract-checks")
    );
}

#[test]
fn test_rejects_ambient_contract_checks_in_all_compiler_flag_channels() {
    let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());

    {
        let _encoded = TestEnvVar::unset("CARGO_ENCODED_RUSTFLAGS");
        let _plain = TestEnvVar::set("RUSTFLAGS", "-C opt-level=2 -Zcontract-checks=yes");
        let diagnostic = trust_verify_disable_diagnostic(&[], true)
            .expect("plain ambient legacy exec projection must be rejected");
        assert!(diagnostic.contains("RUSTFLAGS contains `-Z contract-checks`"), "{diagnostic}");
    }

    {
        let _plain = TestEnvVar::unset("RUSTFLAGS");
        let _encoded = TestEnvVar::set(
            "CARGO_ENCODED_RUSTFLAGS",
            "-C\x1fopt-level=2\x1f-Z\x1fcontract_checks=no",
        );
        let diagnostic = trust_verify_disable_diagnostic(&[], true)
            .expect("encoded ambient legacy exec projection must be rejected");
        assert!(
            diagnostic.contains("CARGO_ENCODED_RUSTFLAGS contains `-Z contract-checks`"),
            "{diagnostic}"
        );
    }

    {
        let _plain = TestEnvVar::unset("RUSTFLAGS");
        let _encoded = TestEnvVar::set(
            "CARGO_ENCODED_RUSTFLAGS",
            "-C\x1fopt-level=2\x1f-Zcontract-checks=unexpected",
        );
        let diagnostic = trust_verify_disable_diagnostic(&[], true)
            .expect("compact encoded legacy exec projection must be rejected regardless of value");
        assert!(
            diagnostic.contains("CARGO_ENCODED_RUSTFLAGS contains `-Z contract-checks`"),
            "{diagnostic}"
        );
    }

    {
        let _plain = TestEnvVar::unset("RUSTFLAGS");
        let _encoded = TestEnvVar::unset("CARGO_ENCODED_RUSTFLAGS");
        let _encoded_doc = TestEnvVar::unset("CARGO_ENCODED_RUSTDOCFLAGS");
        let _doc = TestEnvVar::set("RUSTDOCFLAGS", "-Ztrust-verify=off -Zcontract_checks=off");
        let diagnostic = trust_verify_disable_diagnostic(&[], true)
            .expect("plain rustdoc legacy exec projection must be rejected");
        assert!(diagnostic.contains("RUSTDOCFLAGS contains `-Z contract-checks`"), "{diagnostic}");
    }

    {
        let _plain = TestEnvVar::unset("RUSTFLAGS");
        let _encoded = TestEnvVar::unset("CARGO_ENCODED_RUSTFLAGS");
        let _doc = TestEnvVar::unset("RUSTDOCFLAGS");
        let _encoded_doc = TestEnvVar::set(
            "CARGO_ENCODED_RUSTDOCFLAGS",
            "-Ztrust-verify=off\x1f-Z\x1fcontract-checks=unexpected",
        );
        let diagnostic = trust_verify_disable_diagnostic(&[], true)
            .expect("encoded rustdoc legacy exec projection must be rejected");
        assert!(
            diagnostic.contains("CARGO_ENCODED_RUSTDOCFLAGS contains `-Z contract-checks`"),
            "{diagnostic}"
        );
    }

    {
        let _plain = TestEnvVar::unset("RUSTFLAGS");
        let _encoded = TestEnvVar::unset("CARGO_ENCODED_RUSTFLAGS");
        let _encoded_doc = TestEnvVar::unset("CARGO_ENCODED_RUSTDOCFLAGS");
        let _doc = TestEnvVar::set("RUSTDOCFLAGS", "-Ztrust-verify=off");
        assert_eq!(
            trust_verify_disable_diagnostic(&[], true),
            None,
            "this retirement patch must not broaden Targo's rustdoc policy surface"
        );
    }
}

#[cfg(unix)]
#[test]
fn test_non_unicode_command_arguments_fail_closed_without_panicking() {
    use std::ffi::OsString;
    use std::os::unix::ffi::OsStringExt;

    let error = unicode_command_arguments([
        OsString::from("targo-trust"),
        OsString::from_vec(b"source-\xff.rs".to_vec()),
    ])
    .expect_err("non-Unicode direct compiler argument must reject");
    assert!(error.contains("argument 1 is not valid Unicode"), "{error}");
    assert!(error.contains("evidence-grade"), "{error}");
}

#[test]
fn test_html_escape() {
    assert_eq!(html_escape("<b>test</b>"), "&lt;b&gt;test&lt;/b&gt;");
    assert_eq!(html_escape("a & b"), "a &amp; b");
}

#[test]
fn test_output_format_from_str() {
    assert_eq!(OutputFormat::from_str("terminal").unwrap(), OutputFormat::Terminal);
    assert_eq!(OutputFormat::from_str("json").unwrap(), OutputFormat::Json);
    assert_eq!(OutputFormat::from_str("html").unwrap(), OutputFormat::Html);
    assert!(OutputFormat::from_str("csv").is_err());
}

fn temp_test_dir(label: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock should be after epoch")
        .as_nanos();
    std::env::temp_dir().join(format!("targo-trust-{label}-{}-{unique}", std::process::id()))
}

fn write_executable_marker(path: &Path) {
    std::fs::write(path, "").expect("should create executable marker");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        let mut permissions =
            std::fs::metadata(path).expect("executable marker should have metadata").permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(path, permissions)
            .expect("executable marker should be executable");
    }
}

#[cfg(unix)]
fn write_checker_fixture_script(dir: &Path, name: &str, body: &str) -> PathBuf {
    use std::os::unix::fs::PermissionsExt;

    std::fs::create_dir_all(dir).expect("checker fixture dir should be writable");
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

fn write_trust_toml(dir: &Path, contents: &str) {
    std::fs::create_dir_all(dir).expect("should create temp dir");
    std::fs::write(dir.join("trust.toml"), contents).expect("should write trust.toml");
}

/// Write the canonical surface: a manifest carrying a `[trust]` table.
fn write_trust_table(dir: &Path, contents: &str) {
    std::fs::create_dir_all(dir).expect("should create temp dir");
    let manifest = format!("[package]\nname = \"fixture\"\nversion = \"0.1.0\"\n\n[trust]\n{contents}");
    std::fs::write(dir.join("Cargo.toml"), manifest).expect("should write manifest");
}

#[test]
fn test_select_native_compiler_discovery_uses_repo_local_without_sibling() {
    let root = temp_test_dir("repo-local-native-selection");
    let trustc =
        root.join("build/stage2/bin").join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
    std::fs::create_dir_all(trustc.parent().expect("trustc parent"))
        .expect("create repo-local compiler directory");
    write_executable_marker(&trustc);
    let repo = vec![NativeRustcDiscovery {
        rustc: trustc.clone(),
        source: NativeRustcDiscoverySource::RepoLocalStage2,
    }];

    let selected = select_native_rustc_discovery(None, repo)
        .expect("should discover repo-local trustc when no sibling exists");

    assert_eq!(selected.rustc, trustc);
    assert_eq!(selected.source, NativeRustcDiscoverySource::RepoLocalStage2);
    std::fs::remove_dir_all(root).expect("remove repo-local selection fixture");
}

#[test]
fn test_select_native_rustc_discovery_prefers_sibling_over_repo_local() {
    let root = temp_test_dir("sibling-native-selection");
    let sibling =
        root.join("install/bin").join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
    let repo_trustc = root.join("repo/build/stage2/bin").join(if cfg!(windows) {
        "trustc.exe"
    } else {
        "trustc"
    });
    std::fs::create_dir_all(sibling.parent().expect("sibling parent"))
        .expect("create sibling compiler directory");
    std::fs::create_dir_all(repo_trustc.parent().expect("repo trustc parent"))
        .expect("create repo compiler directory");
    write_executable_marker(&sibling);
    write_executable_marker(&repo_trustc);
    let repo = vec![NativeRustcDiscovery {
        rustc: repo_trustc,
        source: NativeRustcDiscoverySource::RepoLocalStage2,
    }];

    let selected =
        select_native_rustc_discovery(Some(sibling.clone()), repo).expect("should discover trustc");

    assert_eq!(selected.rustc, sibling);
    assert_eq!(selected.source, NativeRustcDiscoverySource::SiblingTCargoTrust);
    std::fs::remove_dir_all(root).expect("remove sibling selection fixture");
}

#[test]
fn test_select_native_rustc_discovery_returns_none_when_no_candidates_exist() {
    let selected = select_native_rustc_discovery(None, Vec::new());

    assert!(selected.is_none());
}

#[test]
fn test_native_rustc_discovery_source_labels_match_doctor_output() {
    assert_eq!(
        NativeRustcDiscoverySource::SiblingTCargoTrust.label(),
        "sibling trustc next to `targo-trust`"
    );
    assert_eq!(
        NativeRustcDiscoverySource::RepoLocalStage2.label(),
        "repo-local stage2 canonical trustc"
    );
    assert_eq!(
        NativeRustcDiscoverySource::RepoLocalStage3.label(),
        "repo-local stage3 canonical trustc"
    );
}

#[test]
fn test_linked_trust_toolchain_status_visibility_depends_on_status_kind() {
    let visible = LinkedTrustToolchainStatus {
        status: LinkedTrustToolchainStatusKind::Visible,
        rustc: Some(PathBuf::from("/tmp/trust/bin/trustc")),
        detail: None,
    };
    let missing = LinkedTrustToolchainStatus {
        status: LinkedTrustToolchainStatusKind::Missing,
        rustc: None,
        detail: Some("toolchain not linked".into()),
    };
    assert!(visible.is_visible());
    assert!(!missing.is_visible());
}

#[test]
fn test_build_native_command_uses_sibling_targo_for_crates() {
    let root = temp_test_dir("sibling-targo");
    let bin_dir = root.join("stage1").join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create bin dir");

    let rustc = bin_dir.join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
    let targo = bin_dir.join(if cfg!(windows) { "targo.exe" } else { "targo" });
    write_executable_marker(&rustc);
    write_executable_marker(&targo);

    let sub_args = parse_subcommand_args(&[]).expect("should parse empty passthrough");
    let cmd_args =
        build_native_command(&rustc, Subcommand::Build, &sub_args, &TrustConfig::default());

    // Deliberately uncanonicalized: resolving a `targo` symlink would rename
    // the spawned program (e.g. stage2 `targo -> cargo`) and defeat the
    // downstream is_cargo_program crate-mode check.
    assert_eq!(cmd_args[0], targo.to_string_lossy().to_string());
    assert_eq!(cmd_args[1], "build");

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_build_native_command_uses_test_mode_for_crate_tests() {
    let root = temp_test_dir("sibling-targo-test");
    let bin_dir = root.join("stage1").join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create bin dir");

    let rustc = bin_dir.join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
    let targo = bin_dir.join(if cfg!(windows) { "targo.exe" } else { "targo" });
    write_executable_marker(&rustc);
    write_executable_marker(&targo);

    let sub_args = parse_subcommand_args(&[]).expect("should parse empty passthrough");
    let cmd_args =
        build_native_command(&rustc, Subcommand::Test, &sub_args, &TrustConfig::default());

    assert_eq!(cmd_args[0], targo.to_string_lossy().to_string());
    assert_eq!(cmd_args[1], "test");

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_rewrite_mode_rejects_test_before_execution() {
    let sub_args = parse_subcommand_args(&["--rewrite".into()]).expect("parse rewrite flag");
    assert_eq!(
        rewrite_request_error(Subcommand::Test, &sub_args),
        Some("--rewrite is only supported by `targo trust check`, `build`, and `loop`")
    );
    assert_eq!(rewrite_request_error(Subcommand::Check, &sub_args), None);
    assert_eq!(rewrite_request_error(Subcommand::Build, &sub_args), None);
}

#[test]
fn test_build_native_command_rejects_path_targo_fallback_when_sibling_missing() {
    let root = temp_test_dir("path-targo-rejected");
    let bin_dir = root.join("stage1").join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create bin dir");

    let rustc = bin_dir.join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
    write_executable_marker(&rustc);

    let sub_args = parse_subcommand_args(&[]).expect("should parse empty passthrough");
    let error = build_native_command_with_json_transport(
        &rustc,
        Subcommand::Check,
        &sub_args,
        &TrustConfig::default(),
        None,
        true,
    )
    .expect_err("missing sibling targo should fail closed");

    assert!(error.contains("linked Trust Cargo frontend is missing"), "{error}");
    assert!(error.contains("will not use PATH fallback"), "{error}");

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_crate_mode_configures_verification_by_default_no_enable_flag() {
    // Batteries-on: with NO flags, crate-mode verification is fully configured (the
    // level flags are broadcast; verification is on by default). `--full-verifier`
    // is REJECTED — there is no enable flag. Replaces the old test that parsed
    // `--full-verifier` to exercise a now-unreachable explicit-enable path.
    let root = temp_test_dir("targo-full-verifier");
    let bin_dir = root.join("stage1").join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create bin dir");

    let rustc = bin_dir.join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
    let targo = bin_dir.join(if cfg!(windows) { "targo.exe" } else { "targo" });
    write_executable_marker(&rustc);
    write_executable_marker(&targo);

    assert!(
        parse_subcommand_args(&["--full-verifier".into()]).is_err(),
        "--full-verifier must be rejected (batteries-on: verification is on by default)"
    );

    let sub_args = parse_subcommand_args(&[]).expect("should parse empty args");
    let cmd_args =
        build_native_command(&rustc, Subcommand::Check, &sub_args, &TrustConfig::default());
    let flags = merged_rustflags_with_options(
        "L1",
        None,
        true,
        sub_args.strict_artifact_policy(),
        sub_args.allow_l0_gaps_lane(),
    );

    assert_eq!(cmd_args[0], targo.to_string_lossy().to_string());
    assert!(
        flags.contains("trust-verify-level="),
        "crate mode must configure the verification level by default: {flags}"
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_build_native_command_uses_build_mode_for_crate_check_and_report() {
    let root = temp_test_dir("crate-mode-build-command");
    let bin_dir = root.join("stage1").join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create bin dir");
    let rustc = bin_dir.join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
    let targo = bin_dir.join(if cfg!(windows) { "targo.exe" } else { "targo" });
    write_executable_marker(&rustc);
    write_executable_marker(&targo);

    let sub_args = parse_subcommand_args(&[]).expect("should parse empty passthrough");

    let check_cmd =
        build_native_command(&rustc, Subcommand::Check, &sub_args, &TrustConfig::default());
    let report_cmd =
        build_native_command(&rustc, Subcommand::Report, &sub_args, &TrustConfig::default());

    assert_eq!(check_cmd[1], "build");
    assert_eq!(report_cmd[1], "build");

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[cfg(unix)]
fn write_trust_cg_preflight_toolchain(
    root: &Path,
    target_kind: &str,
    crate_type: &str,
) -> (PathBuf, PathBuf) {
    let bin_dir = root.join("bin");
    std::fs::create_dir_all(&bin_dir).expect("create fake Trust toolchain");
    let rustc = bin_dir.join("trustc");
    let targo = bin_dir.join("targo");
    write_checker_fixture_script(
        &bin_dir,
        "trustc",
        "#!/bin/sh\nif [ \"$1\" = \"-vV\" ]; then\n  printf '%s\\n' 'rustc 1.99.0-dev' 'host: x86_64-unknown-linux-gnu'\n  exit 0\nfi\nexit 97\n",
    );
    let metadata_path = root.join("metadata.json");
    let package_id = format!("path+file://{}#fixture@0.1.0", root.display());
    let metadata = serde_json::json!({
        "packages": [{
            "id": package_id.clone(),
            "name": "fixture",
            "version": "0.1.0",
            "manifest_path": root.join("Cargo.toml"),
            "targets": [{
                "name": "fixture",
                "kind": [target_kind],
                "crate_types": [crate_type]
            }]
        }],
        "workspace_members": [package_id],
        "workspace_default_members": [package_id],
        "target_directory": root.join("target")
    });
    std::fs::write(&metadata_path, serde_json::to_vec(&metadata).expect("serialize fake metadata"))
        .expect("write fake metadata");
    let unit_graph_path = root.join("unit-graph.json");
    let unit_graph = serde_json::json!({
        "version": 1,
        "units": [{
            "pkg_id": package_id,
            "target": {
                "name": "fixture",
                "kind": [target_kind],
                "crate_types": [crate_type]
            },
            "mode": "build",
            "platform": "x86_64-unknown-linux-gnu"
        }],
        "roots": [0]
    });
    std::fs::write(
        &unit_graph_path,
        serde_json::to_vec(&unit_graph).expect("serialize fake unit graph"),
    )
    .expect("write fake unit graph");
    let script = format!(
        "#!/bin/sh\ncase \"$*\" in\n  *\"config get build.target\"*)\n    printf '%s\\n' 'error: config value `build.target` is not set' >&2\n    exit 101\n    ;;\n  *\"--unit-graph\"*)\n    exec /bin/cat '{}'\n    ;;\n  *\"metadata --format-version 1\"*)\n    exec /bin/cat '{}'\n    ;;\nesac\nexit 98\n",
        unit_graph_path.display(),
        metadata_path.display(),
    );
    write_checker_fixture_script(&bin_dir, "targo", &script);
    (rustc, targo)
}

#[cfg(unix)]
#[test]
fn test_trust_cg_crate_preflight_admits_minimal_rlib_in_dev_and_release() {
    let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let _target = TestEnvVar::unset("CARGO_BUILD_TARGET");
    let root = temp_test_dir("trust-cg-rlib-preflight");
    let (rustc, _) = write_trust_cg_preflight_toolchain(&root, "lib", "lib");

    for passthrough in [Vec::new(), vec!["--release".to_string()]] {
        let sub_args = parse_subcommand_args(&passthrough).expect("parse Cargo arguments");
        let command = build_native_command_with_json_transport(
            &rustc,
            Subcommand::Build,
            &sub_args,
            &TrustConfig::default(),
            Some("trust-cg"),
            true,
        )
        .expect("minimal rlib must pass trust-cg preflight");
        assert!(
            command
                .windows(2)
                .any(|pair| pair[0] == "--target" && pair[1] == "x86_64-unknown-linux-gnu"),
            "implicit host target was not made explicit: {command:?}"
        );
        assert_eq!(command.iter().filter(|arg| arg.as_str() == "--target").count(), 1);
    }

    std::fs::remove_dir_all(root).expect("remove trust-cg rlib fixture");
}

#[cfg(unix)]
#[test]
fn test_trust_cg_crate_preflight_rejects_binary_before_returning_build_command() {
    let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let _target = TestEnvVar::unset("CARGO_BUILD_TARGET");
    let root = temp_test_dir("trust-cg-bin-preflight");
    let (rustc, _) = write_trust_cg_preflight_toolchain(&root, "bin", "bin");
    let error = build_native_command_with_json_transport(
        &rustc,
        Subcommand::Build,
        &parse_subcommand_args(&[]).expect("default Cargo selection"),
        &TrustConfig::default(),
        Some("trust-cg"),
        true,
    )
    .expect_err("unsupported binary must be rejected before a build command is returned");
    assert!(error.contains("only selected rlib library targets"), "{error}");
    assert!(error.contains("kind=bin"), "{error}");

    std::fs::remove_dir_all(root).expect("remove trust-cg binary fixture");
}

#[cfg(unix)]
fn copied_real_targo_for_contract_e2e(root: &Path) -> PathBuf {
    let source = std::env::var_os("TRUST_REAL_TARGO_E2E").map(PathBuf::from).unwrap_or_else(|| {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("repository root")
            .join("src/tools/targo/target/debug/cargo")
    });
    assert!(
        source.is_file(),
        "build current Targo first or set TRUST_REAL_TARGO_E2E: {}",
        source.display()
    );
    let bin = root.join("toolchain");
    std::fs::create_dir_all(&bin).expect("create branded Targo directory");
    let targo = bin.join("targo");
    std::fs::copy(&source, &targo).expect("copy current Targo under its branded executable name");
    targo
}

/// Full Cargo integration for `targo trust test`: a normal library target is
/// compiled with certified monitors, then linked into an integration-test
/// binary. The arithmetic clause is deliberately outside the public verifier
/// API's machine-arithmetic fragment, so this also exercises the exact typed
/// proposition digest carried by the contract-bound unsupported marker. The
/// first sentinel proves the test body ran; the missing second sentinel proves
/// the violated library clause aborted at the monitor rather than merely
/// failing static compilation or being left uninstrumented.
///
/// This is ignored in the ordinary crate-only test pass because it requires a
/// freshly built in-tree trustc + branded Targo pair. It is a mandatory manual
/// release/integration gate and can be run directly after `./x.py build`.
#[cfg(any(
    all(target_os = "linux", any(target_arch = "x86_64", target_arch = "aarch64")),
    all(target_os = "macos", any(target_arch = "x86_64", target_arch = "aarch64"))
))]
#[test]
#[ignore = "requires a freshly built in-tree trustc and Targo"]
fn real_targo_test_instruments_library_used_by_integration_test() {
    let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let root = temp_test_dir("certified-monitor-cargo-test");
    std::fs::create_dir_all(root.join("src")).expect("create library source directory");
    std::fs::create_dir_all(root.join("tests")).expect("create integration-test directory");
    std::fs::write(
        root.join("Cargo.toml"),
        "[package]\nname='certified-monitor-fixture'\nversion='0.1.0'\nedition='2021'\n\n[lib]\ncrate-type=['rlib']\n",
    )
    .expect("write monitor fixture manifest");
    std::fs::write(
        root.join("src/lib.rs"),
        r#"pub fn bad_identity(x: u8) -> u8
    ensures result == x + x
{
    x
}
"#,
    )
    .expect("write monitored library");
    let started = root.join("test-started");
    let returned = root.join("monitor-returned");
    std::fs::write(
        root.join("tests/violation.rs"),
        format!(
            r#"#[test]
fn violated_library_clause_aborts() {{
    std::fs::write({started:?}, b"started").unwrap();
    let _ = certified_monitor_fixture::bad_identity(7);
    std::fs::write({returned:?}, b"returned").unwrap();
}}
"#
        ),
    )
    .expect("write monitor integration test");

    let args = vec![
        "--allow-l0-gaps".to_string(),
        "--manifest-path".to_string(),
        root.join("Cargo.toml").display().to_string(),
        "--target-dir".to_string(),
        root.join("target").display().to_string(),
    ];
    let status = run_subcommand(Subcommand::Test, &args);
    assert_ne!(status, ExitCode::SUCCESS, "the violated certified monitor must fail Cargo test");
    assert!(started.is_file(), "integration test did not execute; this was only a compile failure");
    assert!(
        !returned.exists(),
        "violated library clause returned normally; the linked library was not instrumented"
    );

    std::fs::remove_dir_all(root).expect("remove certified monitor Cargo fixture");
}

/// Positive companion to the violated-monitor fixture above.  This proves
/// that authenticated phase-A transport reaches the fresh-only phase-B replay
/// and that the exact authorized integration-test executable is actually run;
/// the negative fixture separately proves that its linked library is
/// instrumented.
#[cfg(any(
    all(target_os = "linux", any(target_arch = "x86_64", target_arch = "aarch64")),
    all(target_os = "macos", any(target_arch = "x86_64", target_arch = "aarch64"))
))]
#[test]
#[ignore = "requires a freshly built in-tree trustc and Targo"]
fn real_targo_test_executes_authorized_satisfying_integration_test() {
    let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let root = temp_test_dir("certified-monitor-cargo-test-success");
    std::fs::create_dir_all(root.join("src")).expect("create library source directory");
    std::fs::create_dir_all(root.join("tests")).expect("create integration-test directory");
    std::fs::write(
        root.join("Cargo.toml"),
        "[package]\nname='certified-monitor-success-fixture'\nversion='0.1.0'\nedition='2021'\n\n[lib]\ncrate-type=['rlib']\n",
    )
    .expect("write monitor fixture manifest");
    std::fs::write(
        root.join("src/lib.rs"),
        r#"pub fn identity(x: u8) -> u8
    ensures result == x
{
    x
}
"#,
    )
    .expect("write monitored library");
    let started = root.join("test-started");
    let returned = root.join("test-returned");
    let report_dir = root.join("report");
    std::fs::write(
        root.join("tests/satisfying.rs"),
        format!(
            r#"#[test]
fn satisfying_library_clause_returns() {{
    std::fs::write({started:?}, b"started").unwrap();
    assert_eq!(certified_monitor_success_fixture::identity(7), 7);
    std::fs::write({returned:?}, b"returned").unwrap();
}}
"#
        ),
    )
    .expect("write satisfying integration test");

    let args = vec![
        "--allow-l0-gaps".to_string(),
        "--manifest-path".to_string(),
        root.join("Cargo.toml").display().to_string(),
        "--target-dir".to_string(),
        root.join("target").display().to_string(),
        "--report-dir".to_string(),
        report_dir.display().to_string(),
    ];
    let status = run_subcommand(Subcommand::Test, &args);
    assert_eq!(status, ExitCode::SUCCESS, "authenticated satisfying Cargo test must pass");
    assert!(started.is_file(), "authorized integration test did not begin execution");
    assert!(returned.is_file(), "satisfying monitored library call did not return");
    let report: serde_json::Value = serde_json::from_slice(
        &std::fs::read(report_dir.join("report.json")).expect("read certified test report"),
    )
    .expect("parse certified test report");
    let subject = report
        .get("crate_name")
        .and_then(serde_json::Value::as_str)
        .expect("authenticated Cargo subject");
    assert!(subject.contains("compile_mode=\"build\""), "normal library view missing: {subject}");
    assert!(subject.contains("compile_mode=\"test\""), "cfg(test) library view missing: {subject}");
    let execution = &report["verification_gate"]["test_execution"];
    assert_eq!(execution["schema"], trust_types::CERTIFIED_TEST_EXECUTION_SCHEMA_VERSION);
    assert_eq!(execution["completion_scope"], "top-level-cargo-child-exit-only-v1");
    assert_eq!(execution["phase_b_state"], "cargo-invocation-exited");
    assert_eq!(execution["phase_b_exit"], 0);
    assert_eq!(execution["requested"], true);
    assert_eq!(execution["compile_only"], false);
    assert_eq!(execution["phase_a_status"], 0);
    assert_eq!(execution["phase_a_success"], true);
    assert!(execution["blocker"].is_null(), "successful execution retained a blocker: {execution}");
    let inventory_sha256 = execution["authorized_inventory_sha256"]
        .as_str()
        .expect("phase B must report its exact session-bound execution inventory digest");
    assert_eq!(inventory_sha256.len(), 64);
    assert!(
        inventory_sha256.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
        "execution inventory digest is not canonical SHA-256: {inventory_sha256}"
    );
    let authorized = execution["authorized_executables"]
        .as_array()
        .expect("phase B must report the sealed executable inventory");
    assert!(!authorized.is_empty(), "phase B reported no authorized executable: {execution}");
    for executable in authorized {
        assert!(
            executable["size"].as_u64().is_some_and(|size| size > 0),
            "authorized executable has no byte size: {executable}"
        );
        let digest = executable["sha256"].as_str().expect("authorized executable SHA-256 identity");
        assert_eq!(digest.len(), 64, "authorized executable digest: {executable}");
        assert!(
            digest.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
            "authorized executable digest is not canonical: {executable}"
        );
    }
    assert!(
        execution["target_directory"].as_str().is_some_and(|path| !path.is_empty()),
        "phase B omitted its authenticated target directory: {execution}"
    );
    assert_eq!(
        execution["scope"],
        trust_types::CERTIFIED_TEST_EXECUTION_SCOPE,
        "report must state the exact limited completion claim: {execution}"
    );

    std::fs::remove_dir_all(root).expect("remove satisfying monitor Cargo fixture");
}

/// `harness = false` replaces libtest with an arbitrary target `main`, so it
/// cannot claim the evidence-grade phase-B test-harness boundary.
#[cfg(any(
    all(target_os = "linux", any(target_arch = "x86_64", target_arch = "aarch64")),
    all(target_os = "macos", any(target_arch = "x86_64", target_arch = "aarch64"))
))]
#[test]
#[ignore = "requires a freshly built in-tree trustc and Targo"]
fn real_targo_test_rejects_unharnessed_test_target_before_execution() {
    let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let root = temp_test_dir("certified-monitor-unharnessed-test");
    std::fs::create_dir_all(root.join("tests")).expect("create test source directory");
    std::fs::write(
        root.join("Cargo.toml"),
        "[package]\nname='certified-monitor-unharnessed-fixture'\nversion='0.1.0'\nedition='2021'\n\n[[test]]\nname='arbitrary-main'\npath='tests/arbitrary_main.rs'\nharness=false\n",
    )
    .expect("write unharnessed fixture manifest");
    let executed = root.join("arbitrary-main-executed");
    std::fs::write(
        root.join("tests/arbitrary_main.rs"),
        format!("fn main() {{ std::fs::write({executed:?}, b\"executed\").unwrap(); }}\n"),
    )
    .expect("write arbitrary test main");

    let status = run_subcommand(
        Subcommand::Test,
        &[
            "--allow-l0-gaps".to_string(),
            "--manifest-path".to_string(),
            root.join("Cargo.toml").display().to_string(),
            "--target-dir".to_string(),
            root.join("target").display().to_string(),
        ],
    );
    assert_ne!(status, ExitCode::SUCCESS, "harness=false must fail closed");
    assert!(!executed.exists(), "arbitrary target main ran outside the certified libtest boundary");

    std::fs::remove_dir_all(root).expect("remove unharnessed monitor fixture");
}

#[cfg(unix)]
fn rustc_option_values(args: &[String], class: &str, name: &str) -> Vec<String> {
    let mut values = Vec::new();
    let mut index = 0;
    while index < args.len() {
        let option = if args[index] == class {
            index += 1;
            args.get(index).map(String::as_str)
        } else {
            args[index].strip_prefix(class).filter(|value| !value.is_empty())
        };
        if let Some(value) = option.and_then(|option| option.strip_prefix(&format!("{name}="))) {
            values.push(value.to_string());
        }
        index += 1;
    }
    values
}

#[cfg(unix)]
fn read_logged_rustc_invocations(path: &Path) -> Vec<Vec<String>> {
    let mut entries = std::fs::read_dir(path)
        .expect("read rustc argv log directory")
        .map(|entry| entry.expect("read rustc argv log entry").path())
        .collect::<Vec<_>>();
    entries.sort();
    entries
        .into_iter()
        .map(|entry| std::fs::read_to_string(entry).expect("read rustc argv log"))
        .filter(|line| !line.is_empty())
        .map(|line| line.trim_end_matches('\n').split('\t').skip(1).map(str::to_string).collect())
        .collect()
}

#[cfg(unix)]
fn logged_crate_invocation<'a>(invocations: &'a [Vec<String>], crate_name: &str) -> &'a [String] {
    invocations
        .iter()
        .rev()
        .find(|args| args.windows(2).any(|pair| pair[0] == "--crate-name" && pair[1] == crate_name))
        .unwrap_or_else(|| panic!("missing rustc invocation for `{crate_name}`: {invocations:#?}"))
}

/// This uses a real, freshly-built Targo and real rustc compilation. The
/// wrapper only removes Trust-private -Z options immediately before forwarding
/// to the stock compiler; its log therefore captures the exact argv Targo
/// constructed, including profile ordering and host/target separation.
#[cfg(unix)]
#[test]
#[ignore = "run after building current src/tools/targo binary; set TRUST_REAL_TARGO_E2E if it is elsewhere"]
fn real_targo_trust_cg_dev_release_contract_with_host_units() {
    let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let root = temp_test_dir("real-targo-trust-cg-contract");
    std::fs::create_dir_all(root.join("src")).expect("create root source dir");
    std::fs::create_dir_all(root.join("fixture-macro/src")).expect("create proc-macro source dir");
    std::fs::write(
        root.join("Cargo.toml"),
        "[package]\nname='fixture'\nversion='0.1.0'\nedition='2021'\nbuild='build.rs'\n\n[lib]\ncrate-type=['rlib']\n",
    )
    .expect("write root manifest");
    std::fs::write(
        root.join("src/lib.rs"),
        "pub extern \"C\" fn add_one(x: u64) -> u64 { x + 1 }\n",
    )
    .expect("write root library");
    std::fs::write(
        root.join("build.rs"),
        r#"fn main() {
    let log = std::env::var_os("TRUST_BUILD_SCRIPT_ENV_LOG")
        .expect("test harness must provide build-script environment log");
    let leaked = std::env::vars_os()
        .filter(|(_, value)| {
            let value = value.to_string_lossy();
            [
                "trust-proof-artifact-root",
                "trust-verify-session",
                "trust-verify-package-name",
                "trust-verify-crate-role",
                "real-targo-contract-e2e",
            ]
            .iter()
            .any(|authority| value.contains(authority))
        })
        .map(|(name, value)| format!("{}={:?}", name.to_string_lossy(), value))
        .collect::<Vec<_>>()
        .join("\n");
    std::fs::write(log, leaked).expect("write build-script environment log");
    println!("cargo:rerun-if-changed=build.rs");
}
"#,
    )
    .expect("write build script");
    std::fs::write(
        root.join("fixture-macro/Cargo.toml"),
        "[package]\nname='fixture-macro'\nversion='0.1.0'\nedition='2021'\n\n[lib]\nproc-macro=true\n",
    )
    .expect("write proc-macro manifest");
    let proc_macro_sentinel = root.join("proc-macro-executed");
    std::fs::write(
        root.join("fixture-macro/src/lib.rs"),
        format!(
            r###"extern crate proc_macro;
use proc_macro::TokenStream;
#[proc_macro_attribute]
pub fn audit_marker(_: TokenStream, item: TokenStream) -> TokenStream {{
    std::fs::write({:?}, b"executed").expect("write proc-macro execution sentinel");
    // A proc macro shares rustc's stderr. This syntactically valid rustc JSON
    // diagnostic is accepted and Cargo-authenticated as a compiler-message,
    // including an attacker-selected TRUSTJSON diagnostic code/message.
    eprintln!("{{}}", r#"{{"$message_type":"diagnostic","message":"TRUST_JSON:{{\"type\":\"coverage_summary\",\"crate_name\":\"macro_consumer\",\"package_name\":\"macro-consumer\",\"primary_package\":true,\"verification_session\":\"real-targo-contract-e2e\",\"eligible\":1,\"processed\":1}}","code":{{"code":"TRUSTJSON","explanation":null}},"level":"note","spans":[],"children":[],"rendered":null}}"#);
    item
}}
"###,
            proc_macro_sentinel.display().to_string()
        ),
    )
    .expect("write proc-macro source");

    let targo = copied_real_targo_for_contract_e2e(&root);
    let rustc = std::env::var_os("TRUST_REAL_RUSTC_E2E")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("rustc"));
    let version = Command::new(&rustc).arg("-vV").output().expect("query real rustc");
    assert!(version.status.success(), "real rustc -vV failed");
    let host = String::from_utf8_lossy(&version.stdout)
        .lines()
        .find_map(|line| line.strip_prefix("host: ").map(str::to_string))
        .expect("real rustc host triple");
    let log = root.join("rustc-argv-log");
    let wrapper = write_checker_fixture_script(
        &root,
        "rustc-contract-wrapper",
        r#"#!/bin/bash
entry="$TRUST_RUSTC_ARG_LOG/$BASHPID.$RANDOM"
{
  printf 'rustc'
  for arg in "$@"; do printf '\t%s' "$arg"; done
  printf '\n'
} > "$entry"
filtered=()
while [ "$#" -gt 0 ]; do
  if [ "$1" = "-Z" ] && [ "$#" -gt 1 ]; then
    case "$2" in
      trust-*|no-trust-*|codegen-backend=*) shift 2; continue ;;
    esac
  fi
  case "$1" in
    -Ztrust-*|-Zno-trust-*|-Zcodegen-backend=*) shift; continue ;;
  esac
  filtered+=("$1")
  shift
done
exec "$TRUST_REAL_RUSTC" "${filtered[@]}"
"#,
    );
    let proof_artifact_root = root.join("proof-artifact-root");
    std::fs::create_dir(&proof_artifact_root).expect("create private proof artifact root");
    {
        use std::os::unix::fs::PermissionsExt as _;

        let mut permissions = std::fs::metadata(&proof_artifact_root)
            .expect("proof artifact root metadata")
            .permissions();
        permissions.set_mode(0o700);
        std::fs::set_permissions(&proof_artifact_root, permissions)
            .expect("make proof artifact root private");
    }
    let mut encoded_policy = [
        "-Z",
        "trust-verify-level=1",
        "-Z",
        "trust-verify-output=json",
        "-Z",
        "trust-verify-session=real-targo-contract-e2e",
        "-Z",
        "codegen-backend=trust-cg",
        "-Z",
        "trust-cg-output-gate=strict",
        "-C",
        "panic=abort",
        "-C",
        "debuginfo=0",
        "-C",
        "codegen-units=1",
        "-C",
        "overflow-checks=yes",
        "-C",
        "debug-assertions=yes",
    ]
    .join("\x1f");
    encoded_policy.push_str("\x1f-Z\x1ftrust-proof-artifact-root=");
    encoded_policy.push_str(
        proof_artifact_root.to_str().expect("temporary proof artifact root must be UTF-8"),
    );
    let inherited_rustdoc_policy =
        format!("-Z\x1ftrust-proof-artifact-root={}", proof_artifact_root.display());
    let inherited_bootstrap_policy =
        format!("-Z trust-proof-artifact-root={}", proof_artifact_root.display());

    for (profile, release) in [("dev", false), ("release", true)] {
        if log.exists() {
            std::fs::remove_dir_all(&log).expect("remove old argv log directory");
        }
        std::fs::create_dir(&log).expect("create argv log directory");
        let target_dir = root.join(format!("target-{profile}"));
        let build_script_env_log = root.join(format!("build-script-env-{profile}.log"));
        let mut command = Command::new(&targo);
        command
            .current_dir(&root)
            .args(["build", "--lib", "--target", &host, "--target-dir"])
            .arg(&target_dir);
        if release {
            command.arg("--release");
        }
        let output = command
            .env("RUSTC", &wrapper)
            .env("TRUST_REAL_RUSTC", &rustc)
            .env("TRUST_RUSTC_ARG_LOG", &log)
            .env("TRUST_BUILD_SCRIPT_ENV_LOG", &build_script_env_log)
            .env("TRUST_TARGO_VERIFY", "1")
            .env("CARGO_ENCODED_RUSTFLAGS", &encoded_policy)
            // These alternate compiler-flag spellings are not consumed by
            // this `build` but would otherwise be inherited verbatim by the
            // untrusted build script and disclose the same private root.
            .env("CARGO_ENCODED_RUSTDOCFLAGS", &inherited_rustdoc_policy)
            .env("RUSTFLAGS_BOOTSTRAP", &inherited_bootstrap_policy)
            .env_remove("RUSTFLAGS")
            .env("CARGO_INCREMENTAL", "0")
            .env("TRUST_NO_MIGRATE_WARN", "1")
            .output()
            .expect("run real Targo contract build");
        assert!(
            output.status.success(),
            "real Targo {profile} build failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );

        let leaked_build_script_env = std::fs::read_to_string(&build_script_env_log)
            .expect("read executed build-script environment log");
        assert!(
            leaked_build_script_env.is_empty(),
            "{profile}: executed build.rs inherited private proof-store authority:\n{leaked_build_script_env}"
        );

        let invocations = read_logged_rustc_invocations(&log);
        let target = logged_crate_invocation(&invocations, "fixture");
        assert_eq!(
            rustc_option_values(target, "-Z", "codegen-backend").last().map(String::as_str),
            Some("trust-cg")
        );
        assert_eq!(
            rustc_option_values(target, "-C", "panic").last().map(String::as_str),
            Some("abort")
        );
        assert_eq!(
            rustc_option_values(target, "-C", "debuginfo").last().map(String::as_str),
            Some("0")
        );
        assert_eq!(
            rustc_option_values(target, "-C", "codegen-units").last().map(String::as_str),
            Some("1")
        );
        assert_eq!(
            rustc_option_values(target, "-Z", "trust-proof-artifact-root")
                .last()
                .map(String::as_str),
            proof_artifact_root.to_str()
        );
        assert_eq!(
            rustc_option_values(target, "-Z", "trust-verify-session").as_slice(),
            ["real-targo-contract-e2e"]
        );
        assert_eq!(
            rustc_option_values(target, "-Z", "trust-verify-crate-role").as_slice(),
            ["primary"]
        );
        assert_eq!(
            rustc_option_values(target, "-Z", "trust-verify-package-name").as_slice(),
            ["fixture"]
        );
        assert!(
            rustc_option_values(target, "-C", "incremental").is_empty(),
            "{profile}: {target:?}"
        );

        for host_crate in ["build_script_build"] {
            let host_args = logged_crate_invocation(&invocations, host_crate);
            assert_eq!(
                rustc_option_values(host_args, "-Z", "codegen-backend").last().map(String::as_str),
                Some("llvm"),
                "{profile} {host_crate}: {host_args:?}"
            );
            assert!(
                !rustc_option_values(host_args, "-Z", "codegen-backend")
                    .iter()
                    .any(|value| value == "trust-cg"),
                "{profile} {host_crate}: {host_args:?}"
            );
            assert_eq!(
                rustc_option_values(host_args, "-Z", "trust-proof-artifact-root")
                    .last()
                    .map(String::as_str),
                proof_artifact_root.to_str(),
                "{profile} {host_crate}: {host_args:?}"
            );
            assert_eq!(
                rustc_option_values(host_args, "-Z", "trust-verify-session").as_slice(),
                ["real-targo-contract-e2e"],
                "{profile} {host_crate}: {host_args:?}"
            );
            assert_eq!(
                rustc_option_values(host_args, "-Z", "trust-verify-crate-role").as_slice(),
                ["build-script"],
                "{profile} {host_crate}: {host_args:?}"
            );
            assert_eq!(
                rustc_option_values(host_args, "-Z", "trust-verify-package-name").as_slice(),
                ["fixture"],
                "{profile} {host_crate}: {host_args:?}"
            );
        }
    }

    let macro_consumer = root.join("macro-consumer");
    std::fs::create_dir_all(macro_consumer.join("src"))
        .expect("create proc-macro consumer source dir");
    std::fs::write(
        macro_consumer.join("Cargo.toml"),
        "[package]\nname='macro-consumer'\nversion='0.1.0'\nedition='2021'\n\n[lib]\ncrate-type=['rlib']\n\n[dependencies]\nfixture-macro={path='../fixture-macro'}\n",
    )
    .expect("write proc-macro consumer manifest");
    std::fs::write(
        macro_consumer.join("src/lib.rs"),
        "#[fixture_macro::audit_marker]\npub fn macro_expanded() {}\n",
    )
    .expect("write proc-macro consumer source");

    let verified_macro_output = Command::new(&targo)
        .current_dir(&macro_consumer)
        .args(["build", "--lib", "--target", &host, "--target-dir"])
        .arg(root.join("target-verified-proc-macro"))
        .env("RUSTC", &wrapper)
        .env("TRUST_REAL_RUSTC", &rustc)
        .env("TRUST_RUSTC_ARG_LOG", &log)
        .env("TRUST_TARGO_VERIFY", "1")
        .env("CARGO_ENCODED_RUSTFLAGS", &encoded_policy)
        .env_remove("RUSTFLAGS")
        .env("CARGO_INCREMENTAL", "0")
        .env("TRUST_NO_MIGRATE_WARN", "1")
        .output()
        .expect("run verified proc-macro boundary fixture");
    assert!(
        !verified_macro_output.status.success(),
        "verified Targo executed an in-process proc macro:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&verified_macro_output.stdout),
        String::from_utf8_lossy(&verified_macro_output.stderr)
    );
    let verified_macro_stderr = String::from_utf8_lossy(&verified_macro_output.stderr);
    assert!(
        verified_macro_stderr.contains("no-proc-macro TCB boundary")
            && verified_macro_stderr.contains("compiler-message/TRUSTJSON"),
        "verified proc-macro rejection did not name the enforced transport boundary: {verified_macro_stderr}"
    );
    assert!(
        !proc_macro_sentinel.exists(),
        "verified Targo rejected only after executing attacker-controlled proc-macro code"
    );

    // Demonstrate why the boundary is mandatory using ordinary Cargo: the
    // same proc macro writes a rustc-shaped diagnostic directly to shared
    // stderr, and Cargo authenticates it with the selected package/target
    // compiler-message envelope and attacker-selected TRUSTJSON code.
    let plain_cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let plain_macro_output = Command::new(plain_cargo)
        .current_dir(&macro_consumer)
        .args(["check", "--message-format=json", "--target-dir"])
        .arg(root.join("target-ordinary-proc-macro"))
        .env("RUSTC", &rustc)
        .env_remove("RUSTC_WRAPPER")
        .env_remove("RUSTC_WORKSPACE_WRAPPER")
        .env_remove("TRUST_TARGO_VERIFY")
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .env_remove("RUSTDOCFLAGS")
        .env_remove("CARGO_ENCODED_RUSTDOCFLAGS")
        .env_remove("RUSTFLAGS_BOOTSTRAP")
        .output()
        .expect("run ordinary Cargo proc-macro forgery demonstration");
    assert!(
        plain_macro_output.status.success(),
        "ordinary Cargo proc-macro demonstration failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&plain_macro_output.stdout),
        String::from_utf8_lossy(&plain_macro_output.stderr)
    );
    assert!(
        proc_macro_sentinel.is_file(),
        "ordinary Cargo did not execute the proc-macro forgery fixture"
    );
    let forged_compiler_message = String::from_utf8_lossy(&plain_macro_output.stdout)
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .find(|value| {
            value["reason"] == "compiler-message"
                && value["message"]["code"]["code"] == "TRUSTJSON"
                && value["message"]["message"]
                    .as_str()
                    .is_some_and(|message| message.starts_with(trust_types::TRANSPORT_PREFIX))
        });
    assert!(
        forged_compiler_message.is_some(),
        "Cargo did not envelope the proc-macro-forged TRUSTJSON diagnostic:\n{}",
        String::from_utf8_lossy(&plain_macro_output.stdout)
    );

    let bin_root = root.join("bin-fixture");
    std::fs::create_dir_all(bin_root.join("src")).expect("create bin source dir");
    std::fs::write(
        bin_root.join("Cargo.toml"),
        "[package]\nname='bin-fixture'\nversion='0.1.0'\nedition='2021'\n",
    )
    .expect("write bin manifest");
    std::fs::write(bin_root.join("src/main.rs"), "fn main() {}\n").expect("write bin source");
    // The fixture forwards to stock rustc, so retain its private-option
    // stripping wrapper for Targo's explicit dry no-verification query too.
    let real_rustc = rustc.to_string_lossy().into_owned();
    let argv_log = log.to_string_lossy().into_owned();
    let _real_rustc = TestEnvVar::set("TRUST_REAL_RUSTC", &real_rustc);
    let _argv_log = TestEnvVar::set("TRUST_RUSTC_ARG_LOG", &argv_log);
    let error = crate::pipeline::cargo_selection::preflight_trust_cg_cargo_targets_with_targo(
        &[
            "--manifest-path".to_string(),
            bin_root.join("Cargo.toml").display().to_string(),
            "--target".to_string(),
            host,
        ],
        &targo,
        &wrapper,
    )
    .expect_err("real Targo-selected binary must be rejected by preflight");
    assert!(error.contains("kind=bin"), "{error}");

    std::fs::remove_dir_all(root).expect("remove real Targo contract fixture");
}

#[test]
fn test_is_cargo_program_accepts_absolute_cargo_paths() {
    assert!(is_cargo_program("/tmp/stage2/bin/targo"));
    assert!(is_cargo_program("targo"));
    assert!(!is_cargo_program("/tmp/stage1/bin/cargo"));
    assert!(!is_cargo_program("cargo"));
    assert!(!is_cargo_program("/tmp/stage1/bin/rustc"));
}

#[test]
fn test_has_output_path_flag() {
    assert!(has_output_path_flag(&["-o".into(), "out.bin".into()]));
    assert!(has_output_path_flag(&["-oout.bin".into()]));
    assert!(has_output_path_flag(&["--out-dir".into(), "target/tmp".into()]));
    assert!(has_output_path_flag(&["--out-dir=target/tmp".into()]));
    assert!(!has_output_path_flag(&["--edition".into(), "2021".into(), "main.rs".into()]));
}

#[test]
fn test_build_native_command_injects_temp_output_for_single_file_checks() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    let sub_args = parse_subcommand_args(&["examples/midpoint.rs".into()])
        .expect("should parse single-file args");
    let cmd = build_native_command(rustc, Subcommand::Check, &sub_args, &config);

    let output_idx = cmd.iter().position(|arg| arg == "-o").expect("missing -o");
    let output_path = &cmd[output_idx + 1];
    let output_path = Path::new(output_path);
    assert_eq!(output_path.file_stem().and_then(|name| name.to_str()), Some("midpoint"));
    assert!(
        output_path
            .parent()
            .and_then(Path::file_name)
            .and_then(|name| name.to_str())
            .is_some_and(|name| name.starts_with("targo-trust-single-"))
    );
    assert!(
        !args_include_z_flag(&cmd, "trust-verify"),
        "default full verifier mode should not duplicate its activator: {cmd:?}"
    );
    assert!(args_include_z_flag(&cmd, "trust-verify-output=json"));
}

#[test]
fn test_build_native_command_preserves_rustc_default_edition_for_single_file_checks() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    let sub_args = parse_subcommand_args(&["examples/midpoint.rs".into()])
        .expect("should parse single-file args");
    let cmd = build_native_command(rustc, Subcommand::Check, &sub_args, &config);

    assert!(
        !cmd.iter().any(|arg| arg == "--edition" || arg.starts_with("--edition=")),
        "single-file checks should preserve rustc's default edition instead of injecting one: {cmd:?}"
    );
}

#[test]
fn test_build_native_command_preserves_explicit_single_file_edition() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    let sub_args =
        parse_subcommand_args(&["examples/midpoint.rs".into(), "--edition".into(), "2015".into()])
            .expect("should parse single-file args with explicit edition");
    let cmd = build_native_command(rustc, Subcommand::Check, &sub_args, &config);

    assert_eq!(cmd.iter().filter(|arg| arg.as_str() == "--edition").count(), 1);
    assert!(cmd.windows(2).any(|pair| pair[0] == "--edition" && pair[1] == "2015"));
}

#[test]
fn test_build_native_command_can_omit_json_transport_flag() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    let sub_args = parse_subcommand_args(&["examples/midpoint.rs".into()])
        .expect("should parse single-file args");
    let cmd = build_native_command_with_json_transport(
        rustc,
        Subcommand::Check,
        &sub_args,
        &config,
        None,
        false,
    )
    .expect("single-file command should not require sibling targo");

    assert!(
        !args_include_z_flag(&cmd, "trust-verify"),
        "default full verifier mode should not duplicate its activator: {cmd:?}"
    );
    assert!(!args_include_z_flag(&cmd, "trust-verify-output=json"));
}

#[test]
fn test_build_native_command_includes_explicit_codegen_backend() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    let sub_args =
        parse_subcommand_args(&["examples/midpoint.rs".into(), "--crate-type=rlib".into()])
            .expect("should parse single-file args");
    let cmd = build_native_command_with_json_transport(
        rustc,
        Subcommand::Build,
        &sub_args,
        &config,
        Some("trust-cg"),
        true,
    )
    .expect("single-file command should not require sibling targo");

    assert!(cmd.iter().any(|arg| arg == "codegen-backend=trust-cg"));
    assert!(cmd.iter().any(|arg| arg == "trust-cg-output-gate=strict"));
    assert_eq!(codegen_option_values(&cmd, "panic"), ["abort"]);
    assert_eq!(codegen_option_values(&cmd, "debuginfo"), ["0"]);
    assert_eq!(codegen_option_values(&cmd, "codegen-units"), ["1"]);
}

#[test]
fn test_single_file_advisory_trust_cg_allows_unknown_output_only_explicitly() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    let sub_args = parse_subcommand_args(&[
        "--allow-l0-gaps".into(),
        "examples/midpoint.rs".into(),
        "--crate-type=rlib".into(),
    ])
    .expect("should parse explicit advisory single-file args");
    let cmd = build_native_command_with_json_transport(
        rustc,
        Subcommand::Build,
        &sub_args,
        &config,
        Some("trust-cg"),
        true,
    )
    .expect("single-file command should not require sibling targo");

    assert!(cmd.iter().any(|arg| arg == "trust-cg-output-gate=allow-unknown"));
    assert!(!cmd.iter().any(|arg| arg == "trust-cg-output-gate=strict"));
}

#[test]
fn test_direct_trust_cg_rejects_default_binary_before_command_construction() {
    let sub_args = parse_subcommand_args(&["examples/midpoint.rs".into()])
        .expect("parse direct source target");
    let error = build_native_command_with_json_transport(
        Path::new("/tmp/rustc"),
        Subcommand::Build,
        &sub_args,
        &TrustConfig::default(),
        Some("trust-cg"),
        true,
    )
    .expect_err("the implicit direct-rustc executable must fail before spawn");
    assert!(error.contains("only an explicit rlib target"), "{error}");
    assert!(error.contains("--crate-type=rlib"), "{error}");
}

#[test]
fn test_direct_trust_cg_rejects_conflicting_codegen_contract() {
    for conflict in
        ["-Cpanic=unwind", "-Cdebuginfo=1", "-Ccodegen-units=8", "-Cincremental=/tmp/cache", "-g"]
    {
        let sub_args = parse_subcommand_args(&[
            "examples/midpoint.rs".into(),
            "--crate-type=rlib".into(),
            conflict.into(),
        ])
        .expect("parse direct trust-cg override");
        let error = build_native_command_with_json_transport(
            Path::new("/tmp/rustc"),
            Subcommand::Build,
            &sub_args,
            &TrustConfig::default(),
            Some("trust-cg"),
            true,
        )
        .expect_err("conflicting trust-cg codegen policy must fail before spawn");
        assert!(error.contains("conflicts with trust-cg's required"), "{conflict}: {error}");
    }
}

#[test]
fn test_direct_trust_cg_preflights_explicit_cross_target_matrix() {
    let accepted = parse_subcommand_args(&[
        "examples/midpoint.rs".into(),
        "--crate-type=rlib".into(),
        "--target=aarch64-unknown-linux-musl".into(),
    ])
    .expect("parse audited cross-target request");
    build_native_command_with_json_transport(
        Path::new("/tmp/rustc"),
        Subcommand::Build,
        &accepted,
        &TrustConfig::default(),
        Some("trust-cg"),
        true,
    )
    .expect("audited cross-target should reach the compiler's availability checks");

    for target_args in [
        vec!["--target=wasm32-unknown-unknown".into()],
        vec!["--target".into(), "/tmp/lookalike.json".into()],
    ] {
        let mut args = vec!["examples/midpoint.rs".into(), "--crate-type=rlib".into()];
        args.extend(target_args);
        let parsed = parse_subcommand_args(&args).expect("parse unsupported cross target");
        let error = build_native_command_with_json_transport(
            Path::new("/tmp/rustc"),
            Subcommand::Build,
            &parsed,
            &TrustConfig::default(),
            Some("trust-cg"),
            true,
        )
        .expect_err("unsupported Trust-CG target must fail before compiler spawn");
        assert!(error.contains("unsupported Trust-CG compile target"), "{error}");
    }
}

#[test]
fn test_build_native_command_preserves_default_output_for_single_file_builds() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    let sub_args = parse_subcommand_args(&["examples/midpoint.rs".into()])
        .expect("should parse single-file args");
    let cmd = build_native_command(rustc, Subcommand::Build, &sub_args, &config);

    assert!(!cmd.iter().any(|arg| arg == "-o"));
}

#[test]
fn test_build_native_command_respects_explicit_output_for_single_file_checks() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    let sub_args = parse_subcommand_args(&[
        "examples/midpoint.rs".into(),
        "-o".into(),
        "custom-midpoint".into(),
    ])
    .expect("should parse single-file args with explicit output");
    let cmd = build_native_command(rustc, Subcommand::Check, &sub_args, &config);

    let outputs = cmd.iter().filter(|arg| arg.as_str() == "-o").count();
    assert_eq!(outputs, 1);
    assert!(cmd.iter().any(|arg| arg == "custom-midpoint"));
}

#[test]
fn test_compiler_help_supports_option_detects_expected_flags() {
    let help = "  -Z trust-verify=val\n  -Z trust-verify-output=val\n";
    assert!(compiler_help_supports_option(help, "trust-verify="));
    assert!(compiler_help_supports_option(help, "trust-verify-output="));
    assert!(!compiler_help_supports_option(help, "no-such-flag="));
}

#[test]
fn test_report_json_serialization() {
    let report = VerificationReport {
        report_subject: "test-report".to_string(),
        success: true,
        exit_code: 0,
        proved: 1,
        failed: 0,
        unknown: 0,
        runtime_checked: 0,
        assumed: 0,
        mandated: 0,
        contract_panics: 0,
        cached: 0,
        total: 1,
        results: vec![VerificationResult {
            function: "crate::midpoint".into(),
            kind: "overflow:add".into(),
            message: "arithmetic overflow".into(),
            outcome: VerificationOutcome::Proved,
            backend: "ay-smtlib".into(),
            time_ms: Some(8),
            location: None,
            counterexample: None,
            reason: None,
            raw_line: "note: Trust [overflow:add]: arithmetic overflow -- PROVED (ay-smtlib, 8ms)"
                .into(),
        }],
        zero_obligation_functions: Vec::new(),
        compiler_diagnostics: vec![],
        duration_ms: 42,
        config: ReportConfig {
            level: "L0".into(),
            timeout_ms: 5000,
            function_budget_ms: 120_000,
            enabled: true,
            hardened: false,
            trust_profile: None,
        },
        dep_assumptions: Vec::new(),
        gate: None,
        coverage: None,
        test_execution: None,
        cargo_proof_inventory: None,
        proof_artifact_root: None,
        live_transport_authority: None,
    };
    let json = serde_json::to_string(&report).expect("should serialize report");
    assert!(json.contains("\"success\":true"));
    assert!(json.contains("\"proved\":1"));
    assert!(json.contains("overflow:add"));
    assert!(json.contains("\"function_budget_ms\":120000"));
}

#[test]
fn test_report_success_logic() {
    // No failures, compiler exit 0 => success
    let report = VerificationReport {
        report_subject: "test-report".to_string(),
        success: true,
        exit_code: 0,
        proved: 2,
        failed: 0,
        unknown: 0,
        runtime_checked: 0,
        assumed: 0,
        mandated: 0,
        contract_panics: 0,
        cached: 0,
        total: 2,
        results: vec![],
        zero_obligation_functions: Vec::new(),
        compiler_diagnostics: vec![],
        duration_ms: 10,
        config: ReportConfig {
            level: "L0".into(),
            timeout_ms: 5000,
            function_budget_ms: 120_000,
            enabled: true,
            hardened: false,
            trust_profile: None,
        },
        dep_assumptions: Vec::new(),
        gate: None,
        coverage: None,
        test_execution: None,
        cargo_proof_inventory: None,
        proof_artifact_root: None,
        live_transport_authority: None,
    };
    assert!(report.success);

    // Has failures => not success even with exit 0
    let report2 = VerificationReport {
        report_subject: "test-report".to_string(),
        success: false,
        exit_code: 0,
        proved: 1,
        failed: 1,
        unknown: 0,
        runtime_checked: 0,
        assumed: 0,
        mandated: 0,
        contract_panics: 0,
        cached: 0,
        total: 2,
        results: vec![],
        zero_obligation_functions: Vec::new(),
        compiler_diagnostics: vec![],
        duration_ms: 10,
        config: ReportConfig {
            level: "L0".into(),
            timeout_ms: 5000,
            function_budget_ms: 120_000,
            enabled: true,
            hardened: false,
            trust_profile: None,
        },
        dep_assumptions: Vec::new(),
        gate: None,
        coverage: None,
        test_execution: None,
        cargo_proof_inventory: None,
        proof_artifact_root: None,
        live_transport_authority: None,
    };
    assert!(!report2.success);
}

// -- Doctor helper tests --

#[test]
fn test_backend_status_prefers_cli_override_over_trust_toml() {
    let args =
        parse_subcommand_args(&["--backend".into(), "llvm".into()]).expect("should parse args");
    let config = TrustConfig { codegen_backend: Some("trust-cg".into()), ..TrustConfig::default() };

    let status = backend_status(&args, &config);

    assert_eq!(status.selected, "llvm");
    assert_eq!(status.source.label(), "CLI override");
}

#[test]
fn test_backend_status_uses_trust_toml_then_default() {
    let args = parse_subcommand_args(&[]).expect("should parse empty args");

    let configured = backend_status(
        &args,
        &TrustConfig { codegen_backend: Some("trust-cg".into()), ..TrustConfig::default() },
    );
    assert_eq!(configured.selected, "trust-cg");
    assert_eq!(configured.source.label(), "project configuration");

    let defaulted = backend_status(&args, &TrustConfig::default());
    assert_eq!(defaulted.selected, DEFAULT_CODEGEN_BACKEND);
    assert_eq!(defaulted.source.label(), "default");
}

#[test]
fn test_apply_configured_trust_profile_enables_hardened_when_cli_absent() {
    let mut args = parse_subcommand_args(&[]).expect("should parse empty args");
    let config = TrustConfig::default();

    apply_configured_trust_profile(&mut args, &config);

    assert!(args.hardened);
    assert_eq!(args.trust_profile.as_deref(), Some(DEFAULT_TRUST_PROFILE));
}

#[test]
fn test_apply_configured_trust_profile_uses_configured_profile_by_default() {
    let mut args = parse_subcommand_args(&[]).expect("should parse empty args");
    let config =
        TrustConfig { trust_profile: Some("coreutils_hardened".into()), ..TrustConfig::default() };

    apply_configured_trust_profile(&mut args, &config);

    assert!(args.hardened);
    assert_eq!(args.trust_profile.as_deref(), Some("coreutils_hardened"));
}

#[test]
fn test_apply_configured_trust_profile_honors_no_hardened_cli() {
    let mut args =
        parse_subcommand_args(&["--no-hardened".into()]).expect("should parse no-hardened args");
    let config =
        TrustConfig { trust_profile: Some("coreutils_hardened".into()), ..TrustConfig::default() };

    apply_configured_trust_profile(&mut args, &config);

    assert!(!args.hardened);
    assert_eq!(args.trust_profile, None);
}

#[test]
fn test_apply_configured_trust_profile_honors_trust_toml_opt_out() {
    let mut args = parse_subcommand_args(&[]).expect("should parse empty args");
    let config = TrustConfig {
        hardened: Some(false),
        trust_profile: Some("coreutils_hardened".into()),
        ..TrustConfig::default()
    };

    apply_configured_trust_profile(&mut args, &config);

    assert!(!args.hardened);
    assert_eq!(args.trust_profile, None);
}

#[test]
fn test_apply_configured_trust_profile_preserves_hardened_cli_default() {
    let mut args =
        parse_subcommand_args(&["--hardened".into()]).expect("should parse hardened args");
    let config =
        TrustConfig { trust_profile: Some("coreutils_hardened".into()), ..TrustConfig::default() };

    apply_configured_trust_profile(&mut args, &config);

    assert!(args.hardened);
    assert_eq!(args.trust_profile.as_deref(), Some(DEFAULT_TRUST_PROFILE));
}

#[test]
fn test_apply_configured_trust_profile_preserves_explicit_cli_profile() {
    let mut args = parse_subcommand_args(&["--trust-profile=cli_hardened".into()])
        .expect("should parse trust profile args");
    let config =
        TrustConfig { trust_profile: Some("coreutils_hardened".into()), ..TrustConfig::default() };

    apply_configured_trust_profile(&mut args, &config);

    assert!(args.hardened);
    assert_eq!(args.trust_profile.as_deref(), Some("cli_hardened"));
}

#[test]
fn test_load_doctor_config_reports_an_undeclared_policy() {
    let root = temp_test_dir("doctor-config-missing");
    std::fs::create_dir_all(&root).expect("should create temp dir");

    let (config, status) = load_doctor_config(&root);

    assert_eq!(config.level, TrustConfig::default().level);
    assert_eq!(config.timeout_ms, TrustConfig::default().timeout_ms);
    assert_eq!(config.function_budget_ms, TrustConfig::default().function_budget_ms);
    assert_eq!(status.function_budget_ms, TrustConfig::default().function_budget_ms);
    assert_eq!(status.path, root);
    assert_eq!(status.source.label(), "defaults");
    assert_eq!(status.detail.as_deref(), Some("no [trust] table declared"));
    assert_eq!(
        describe_config_source(&status),
        format!("defaults at {}: no [trust] table declared", status.path.display())
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_load_doctor_config_normalizes_known_backend() {
    let root = temp_test_dir("doctor-config-valid");
    write_trust_table(
        &root,
        r#"enabled = false
level = "L2"
timeout_ms = 42
function_budget_ms = 45000
codegen_backend = "trust-cg"
hardened = false
trust_profile = "coreutils_hardened"
"#,
    );

    let (config, status) = load_doctor_config(&root);

    assert!(!config.enabled);
    assert_eq!(config.level, "L2");
    assert_eq!(config.timeout_ms, 42);
    assert_eq!(config.function_budget_ms, 45_000);
    assert_eq!(status.function_budget_ms, 45_000);
    assert_eq!(config.codegen_backend.as_deref(), Some("trust-cg"));
    assert_eq!(config.hardened, Some(false));
    assert_eq!(config.trust_profile.as_deref(), Some("coreutils_hardened"));
    assert_eq!(status.source.label(), "manifest [trust] table");
    assert_eq!(status.path, root.join("Cargo.toml"));
    assert_eq!(status.configured_codegen_backend.as_deref(), Some("trust-cg"));
    assert_eq!(status.configured_hardened, Some(false));
    assert_eq!(status.configured_trust_profile.as_deref(), Some("coreutils_hardened"));
    assert!(status.detail.is_none());
    assert_eq!(
        describe_config_source(&status),
        format!("manifest [trust] table ({})", status.path.display())
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_load_doctor_config_reports_an_unknown_backend_as_invalid() {
    let root = temp_test_dir("doctor-config-unknown-backend");
    write_trust_table(
        &root,
        r#"level = "L0"
codegen_backend = "cranelift"
"#,
    );

    let (config, status) = load_doctor_config(&root);

    // The doctor and the front door agree on what is valid: a backend nobody
    // can select is not a policy that can be honoured at a lower volume.
    assert_eq!(config.level, TrustConfig::default().level);
    assert!(config.codegen_backend.is_none());
    assert!(status.source.has_error());
    assert_eq!(status.source.label(), "defaults (invalid configuration)");
    let detail = status.detail.expect("should explain the rejected backend");
    assert!(detail.contains("unknown codegen backend `cranelift`"), "{detail}");

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_load_doctor_config_invalid_table_falls_back_to_defaults() {
    let root = temp_test_dir("doctor-config-invalid");
    write_trust_table(
        &root,
        r#"enabled = true
unexpected = "value"
"#,
    );

    let (config, status) = load_doctor_config(&root);

    assert_eq!(config.level, TrustConfig::default().level);
    assert_eq!(config.timeout_ms, TrustConfig::default().timeout_ms);
    assert_eq!(config.function_budget_ms, TrustConfig::default().function_budget_ms);
    assert_eq!(status.source.label(), "defaults (invalid configuration)");
    assert!(status.source.has_error());
    let detail = status.detail.clone().expect("should explain the unknown key");
    assert!(detail.contains("unknown field `unexpected`"), "{detail}");
    let description = describe_config_source(&status);
    assert!(description.contains("defaults (invalid configuration)"));
    assert!(description.contains("Cargo.toml"));

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_load_doctor_config_names_the_deprecated_file_and_its_replacement() {
    let root = temp_test_dir("doctor-config-legacy");
    write_trust_toml(&root, "level = \"L1\"\n");

    let (config, status) = load_doctor_config(&root);

    assert_eq!(config.level, "L1");
    assert_eq!(status.source.label(), "trust.toml (deprecated)");
    assert!(!status.source.has_error());
    let detail = status.detail.expect("deprecation must be stated where the policy is reported");
    assert!(detail.contains("[trust]"), "{detail}");
    assert!(detail.contains("Targo.toml"), "{detail}");

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_describe_capability_covers_all_states() {
    assert_eq!(describe_capability(Some(true)), "supported");
    assert_eq!(describe_capability(Some(false)), "not supported");
    assert_eq!(describe_capability(None), "unknown");
}

#[test]
fn test_verifier_suite_statuses_probe_in_process_adapters() {
    let suites = verifier_suite_statuses();

    assert_eq!(suites.len(), 3);
    for suite in &suites {
        assert!(suite.adapter_compiled, "{} adapter should be compiled", suite.name);
        assert!(
            !suite.in_process_available,
            "{} placeholder adapter must not be reported as proof-grade available",
            suite.name
        );
        assert_eq!(suite.in_process_status, "unavailable");
        assert!(
            suite.in_process_detail.is_some(),
            "{} unavailable suite should explain why proof-grade smoke evidence is unavailable",
            suite.name
        );
        assert_eq!(suite.manifest.name, suite.name);
        assert!(!suite.manifest.version.is_empty());
        assert!(!suite.manifest.api_version.is_empty());
        assert!(
            !suite.manifest.capabilities.is_empty(),
            "{} manifest should expose owned obligation capabilities",
            suite.name
        );
    }
    let trust_vc = suites.iter().find(|suite| suite.name == "trust-vc").expect("trust-vc suite");
    assert_eq!(
        trust_vc.capability_available,
        cfg!(feature = "trust-vc-in-process"),
        "trust-vc must advertise capability exactly when its native bridge is compiled"
    );
}

fn present_surface_tool(name: &str, path: &str, required: bool) -> LinkedTrustSurfaceToolStatus {
    let path = PathBuf::from(path);
    let bin_dir = path.parent().map(Path::to_path_buf);
    let sysroot = path.parent().and_then(Path::parent).map(Path::to_path_buf);
    LinkedTrustSurfaceToolStatus {
        name: name.to_string(),
        required,
        status: LinkedTrustSurfaceToolStatusKind::Present,
        path: Some(path),
        sysroot,
        bin_dir,
        detail: None,
    }
}

#[test]
fn test_doctor_report_json_exposes_native_reporting_contract() {
    let rustc = PathBuf::from("/opt/trust/bin/trustc");
    let report = DoctorReport {
        ready: true,
        status: "ready",
        compiler: DoctorCompilerStatus {
            path: Some(rustc.clone()),
            discovery_source: Some(NativeRustcDiscoverySource::SiblingTCargoTrust),
            discovery_error: None,
            linked_toolchain_status: LinkedTrustToolchainStatusKind::Visible,
            linked_toolchain_path: Some(rustc.clone()),
            linked_toolchain_detail: None,
            daily_driver: DoctorDailyDriverStatus {
                surface_kind: LinkedTrustCargoSurfaceKind::InstalledReady,
                ready: true,
                detail: None,
                linked_targo_path: Some(PathBuf::from("/opt/trust/bin/targo")),
                linked_targo_trust_path: Some(PathBuf::from("/opt/trust/bin/targo-trust")),
                required_tools: vec![
                    present_surface_tool("trustc", "/opt/trust/bin/trustc", true),
                    present_surface_tool("targo", "/opt/trust/bin/targo", true),
                    present_surface_tool("targo-trust", "/opt/trust/bin/targo-trust", true),
                    present_surface_tool("trustd", "/opt/trust/bin/trustd", true),
                    present_surface_tool("trustdoc", "/opt/trust/bin/trustdoc", true),
                    present_surface_tool("trustfmt", "/opt/trust/bin/trustfmt", true),
                    present_surface_tool("targo-fmt", "/opt/trust/bin/targo-fmt", true),
                    present_surface_tool("tippy", "/opt/trust/bin/tippy", true),
                    present_surface_tool("targo-tippy", "/opt/trust/bin/targo-tippy", true),
                    present_surface_tool("tippy-driver", "/opt/trust/bin/tippy-driver", true),
                    present_surface_tool("trust-analyzer", "/opt/trust/bin/trust-analyzer", true),
                ],
                optional_tools: vec![LinkedTrustSurfaceToolStatus {
                    name: "trust-miri".to_string(),
                    required: false,
                    status: LinkedTrustSurfaceToolStatusKind::OptionalMissing,
                    path: None,
                    sysroot: None,
                    bin_dir: None,
                    detail: Some("Miri component not shipped".to_string()),
                }],
            },
            trust_verify: Some(true),
            json_transport: Some(true),
            check_report_mode: DoctorCheckReportMode::NativeCompiler,
        },
        backend: DoctorBackendStatus {
            selected: DEFAULT_CODEGEN_BACKEND.to_string(),
            source: DoctorBackendSource::Default,
        },
        config: DoctorConfigStatus {
            source: DoctorConfigSourceKind::Defaults,
            path: PathBuf::from("Cargo.toml"),
            detail: None,
            enabled: true,
            level: "L1".to_string(),
            timeout_ms: 5_000,
            function_budget_ms: 120_000,
            configured_codegen_backend: None,
            configured_hardened: None,
            configured_trust_profile: None,
        },
        solvers: DoctorSolverStatus {
            requested: None,
            external_available: 0,
            native_suite_available: 0,
            available: 0,
            routed_available: 0,
            total: 0,
            solvers: vec![],
        },
        verifier_suites: verifier_suite_statuses(),
    };

    let json = serde_json::to_value(&report).expect("doctor report should serialize");
    let compiler = &json["compiler"];

    assert_eq!(compiler["path"], rustc.to_string_lossy().as_ref());
    assert_eq!(compiler["discovery_source"], "sibling_trustc");
    assert_eq!(compiler["linked_toolchain_status"], "visible");
    assert_eq!(compiler["linked_toolchain_path"], rustc.to_string_lossy().as_ref());
    assert_eq!(compiler["daily_driver"]["surface_kind"], "installed_ready");
    assert_eq!(compiler["daily_driver"]["ready"], true);
    assert_eq!(compiler["daily_driver"]["linked_targo_path"], "/opt/trust/bin/targo");
    assert_eq!(compiler["daily_driver"]["linked_targo_trust_path"], "/opt/trust/bin/targo-trust");
    let required_tools =
        compiler["daily_driver"]["required_tools"].as_array().expect("required tool matrix");
    for tool in [
        "trustc",
        "targo",
        "targo-trust",
        "trustd",
        "trustdoc",
        "trustfmt",
        "targo-fmt",
        "tippy",
        "targo-tippy",
        "tippy-driver",
        "trust-analyzer",
    ] {
        assert!(
            required_tools
                .iter()
                .any(|entry| entry["name"] == tool && entry["status"] == "present"),
            "doctor JSON should expose required canonical surface tool {tool}: {required_tools:?}"
        );
    }
    let optional_tools =
        compiler["daily_driver"]["optional_tools"].as_array().expect("optional tool matrix");
    assert!(
        optional_tools.iter().any(|entry| {
            entry["name"] == "trust-miri" && entry["status"] == "optional_missing"
        }),
        "doctor JSON should expose optional Miri surface status: {optional_tools:?}"
    );
    assert_eq!(compiler["trust_verify"], true);
    assert_eq!(compiler["json_transport"], true);
    assert_eq!(compiler["check_report_mode"], "native_compiler");
    assert_eq!(json["solvers"]["routed_available"], 0);
    assert_eq!(json["verifier_suites"][0]["name"], "trust-mc");
    assert_eq!(json["verifier_suites"][1]["name"], "trust-wp");
    assert_eq!(json["verifier_suites"][2]["name"], "trust-vc");
    assert_eq!(json["verifier_suites"][0]["adapter_compiled"], true);
    assert_eq!(json["verifier_suites"][0]["in_process_available"], false);
    assert_eq!(json["verifier_suites"][1]["in_process_available"], false);
    assert_eq!(json["verifier_suites"][2]["in_process_available"], false);
    // `capability_available` is the truthful "is this batteries-on adapter wired/
    // capable?" signal (manifest declares a Supported obligation kind), distinct
    // from the contentless-smoke `in_process_available`. It must be present and
    // must equal "the manifest declares Supported" for each suite (robust to build
    // features: computed from the same JSON).
    for i in 0..3 {
        let suite = &json["verifier_suites"][i];
        assert!(
            suite["capability_available"].is_boolean(),
            "verifier_suites[{i}].capability_available must be a bool"
        );
        // Honest "wired/capable" predicate: a Supported (or Preferred) capability.
        // Excludes `Experimental` (object form `{"Experimental": {...}}`) and
        // `Unsupported`, matching the field's Supported/Preferred check. The
        // shipped build enables trust-vc-in-process, so its live typed bridge
        // advertises Supported; minimal developer builds remain Experimental.
        let manifest_declares_supported =
            suite["manifest"]["capabilities"].as_array().is_some_and(|caps| {
                caps.iter().any(|c| c["support"] == "Supported" || c["support"] == "Preferred")
            });
        assert_eq!(
            suite["capability_available"], manifest_declares_supported,
            "capability_available must equal manifest-declares-Supported for suite {i}"
        );
    }
    assert_eq!(json["verifier_suites"][0]["in_process_status"], "unavailable");
    assert_eq!(json["verifier_suites"][1]["in_process_status"], "unavailable");
    assert_eq!(json["verifier_suites"][2]["in_process_status"], "unavailable");
    assert!(json["verifier_suites"][0]["in_process_detail"].is_string());
    assert_eq!(json["verifier_suites"][0]["manifest"]["name"], "trust-mc");
    assert_eq!(json["verifier_suites"][1]["manifest"]["name"], "trust-wp");
    assert_eq!(json["verifier_suites"][2]["manifest"]["name"], "trust-vc");
    assert!(
        json["verifier_suites"][0]
            .get("external_executable_available")
            .expect("external availability field should be stable")
            .is_boolean()
    );
}

#[test]
fn test_doctor_report_json_exposes_native_required_contract() {
    let report = DoctorReport {
        ready: false,
        status: "needs_attention",
        compiler: DoctorCompilerStatus {
            path: None,
            discovery_source: None,
            discovery_error: None,
            linked_toolchain_status: LinkedTrustToolchainStatusKind::Missing,
            linked_toolchain_path: None,
            linked_toolchain_detail: Some("toolchain `trust` is not installed".to_string()),
            daily_driver: DoctorDailyDriverStatus {
                surface_kind: LinkedTrustCargoSurfaceKind::Missing,
                ready: false,
                detail: Some("toolchain `trust` is not installed".to_string()),
                linked_targo_path: None,
                linked_targo_trust_path: None,
                required_tools: vec![],
                optional_tools: vec![],
            },
            trust_verify: None,
            json_transport: None,
            check_report_mode: DoctorCheckReportMode::NativeRequired,
        },
        backend: DoctorBackendStatus {
            selected: DEFAULT_CODEGEN_BACKEND.to_string(),
            source: DoctorBackendSource::Default,
        },
        config: DoctorConfigStatus {
            source: DoctorConfigSourceKind::Defaults,
            path: PathBuf::from("Cargo.toml"),
            detail: Some("no [trust] table declared".to_string()),
            enabled: true,
            level: "L1".to_string(),
            timeout_ms: 5_000,
            function_budget_ms: 120_000,
            configured_codegen_backend: None,
            configured_hardened: None,
            configured_trust_profile: None,
        },
        solvers: DoctorSolverStatus {
            requested: None,
            external_available: 0,
            native_suite_available: 0,
            available: 0,
            routed_available: 0,
            total: 0,
            solvers: vec![],
        },
        verifier_suites: verifier_suite_statuses(),
    };

    let json = serde_json::to_value(&report).expect("doctor report should serialize");
    let compiler = &json["compiler"];

    assert!(compiler.get("path").expect("path field should be stable").is_null());
    assert!(
        compiler
            .get("discovery_source")
            .expect("discovery_source field should be stable")
            .is_null()
    );
    assert_eq!(compiler["linked_toolchain_status"], "missing");
    assert_eq!(compiler["daily_driver"]["surface_kind"], "missing");
    assert_eq!(compiler["daily_driver"]["ready"], false);
    assert!(
        compiler
            .get("linked_toolchain_path")
            .expect("linked_toolchain_path field should be stable")
            .is_null()
    );
    assert_eq!(compiler["linked_toolchain_detail"], "toolchain `trust` is not installed");
    assert!(compiler.get("trust_verify").expect("trust_verify field should be stable").is_null());
    assert!(
        compiler.get("json_transport").expect("json_transport field should be stable").is_null()
    );
    assert_eq!(compiler["check_report_mode"], "native_required");
}

#[test]
fn test_parse_compiler_stderr_strips_raw_trust_json_transport() {
    let transport_json = r#"{"type":"function_result","function":"crate::midpoint","results":[{"kind":"divzero","description":"division by zero","outcome":"proved","solver":"ay-smtlib","time_ms":8}],"proved":1,"failed":0,"unknown":0,"runtime_checked":0,"total":1}"#;
    let stderr = format!(
        "{}{}\nwarning: ordinary compiler warning\nnote: Trust [overflow:add]: arithmetic overflow -- FAILED (ay-smtlib, 3ms)\n",
        trust_types::TRANSPORT_PREFIX,
        transport_json
    );

    let parsed = parse_compiler_stderr(std::io::Cursor::new(stderr), false);

    assert_eq!(parsed.verification_results.len(), 1);
    let result = &parsed.verification_results[0];
    assert_eq!(result.function, "crate::midpoint");
    assert_eq!(result.kind, "divzero");
    assert_eq!(result.outcome, VerificationOutcome::Proved);
    assert_eq!(result.backend, "ay-smtlib");
    assert_eq!(result.time_ms, Some(8));
    assert!(result.raw_line.is_empty());

    assert_eq!(parsed.compiler_diagnostics.len(), 1);
    assert_eq!(parsed.compiler_diagnostics[0].level, "warning");
    assert!(!parsed.compiler_diagnostics[0].message.contains(trust_types::TRANSPORT_PREFIX));
}

// -- Solver flag parsing tests --

#[test]
fn test_parse_args_solver_flag() {
    let args: Vec<String> = vec!["--solver".into(), "ay".into()];
    let result = parse_subcommand_args(&args).expect("should parse --solver ay");
    assert_eq!(result.solver.as_deref(), Some("ay"));
}

#[test]
fn test_parse_args_backend_flag() {
    let args: Vec<String> = vec!["--backend".into(), "trust-cg".into()];
    let result = parse_subcommand_args(&args).expect("should parse --backend trust_cg");
    assert_eq!(result.backend.as_deref(), Some("trust-cg"));
}

#[test]
fn test_usage_text_mentions_backend_and_trust_cg() {
    let usage = usage_text();
    assert!(usage.contains("--backend <name>"));
    assert!(usage.contains("trust-cg"));
    assert!(usage.contains("targo trust doctor"));
}

#[test]
fn test_usage_text_describes_solver_as_request_not_force() {
    let usage = usage_text();
    assert!(usage.contains("Request source solver routing"));
    assert!(usage.contains("currently ay"));
    assert!(!usage.contains("Force a specific solver"));
}

#[test]
fn test_parse_args_backend_equals() {
    let args: Vec<String> = vec!["--backend=llvm".into()];
    let result = parse_subcommand_args(&args).expect("should parse --backend=llvm");
    assert_eq!(result.backend.as_deref(), Some("llvm"));
}

#[test]
fn test_parse_args_backend_unknown_fails() {
    let args: Vec<String> = vec!["--backend".into(), "cranelift".into()];
    assert!(parse_subcommand_args(&args).is_err());
}

#[test]
fn test_parse_args_solver_equals() {
    let args: Vec<String> = vec!["--solver=trust-mc".into()];
    let result = parse_subcommand_args(&args).expect("should parse --solver=trust-mc");
    assert_eq!(result.solver.as_deref(), Some("trust-mc"));
}

#[test]
fn test_parse_args_solver_unknown_fails() {
    let args: Vec<String> = vec!["--solver".into(), "nonexistent".into()];
    assert!(parse_subcommand_args(&args).is_err());
}

#[test]
fn test_parse_args_solver_missing_value() {
    let args: Vec<String> = vec!["--solver".into()];
    assert!(parse_subcommand_args(&args).is_err());
}

#[test]
fn test_parse_args_no_solver_by_default() {
    let args: Vec<String> = vec!["test.rs".into()];
    let result = parse_subcommand_args(&args).expect("should parse without --solver");
    assert!(result.solver.is_none());
}

#[test]
fn test_parse_args_solver_with_format() {
    let args: Vec<String> = vec![
        "--solver".into(),
        "trust-wp".into(),
        "--format".into(),
        "json".into(),
        "test.rs".into(),
    ];
    let result = parse_subcommand_args(&args).expect("should parse combined args");
    assert_eq!(result.solver.as_deref(), Some("trust-wp"));
    assert_eq!(result.format, OutputFormat::Json);
    assert!(result.is_single_file);
}

#[test]
fn test_check_rejects_detected_but_unwired_solver_request() {
    let args: Vec<String> = vec!["--solver".into(), "clean".into()];
    assert_eq!(run_subcommand(Subcommand::Check, &args), ExitCode::from(2));
}

#[test]
fn test_parse_args_all_known_solvers() {
    for name in &["ay", "trust-mc", "trust-wp", "trust-vc", "ty", "clean"] {
        let args: Vec<String> = vec!["--solver".into(), name.to_string()];
        let result =
            parse_subcommand_args(&args).unwrap_or_else(|_| panic!("should parse --solver {name}"));
        assert_eq!(result.solver.as_deref(), Some(*name));
    }
}

#[test]
fn test_parse_args_trust_profile_rejects_empty_or_flag_value() {
    for args in [
        vec!["--trust-profile".to_string()],
        vec!["--trust-profile=".to_string()],
        vec!["--trust-profile".to_string(), "--release".to_string()],
    ] {
        assert!(
            parse_subcommand_args(&args).is_err(),
            "--trust-profile should reject missing/empty/flag-looking values: {args:?}"
        );
    }
}

#[test]
fn test_parse_args_hardened_profile_do_not_passthrough() {
    let args = vec![
        "--hardened".into(),
        "--trust-profile=coreutils_hardened".into(),
        "--manifest-path".into(),
        "examples/hardened/Cargo.toml".into(),
        "--release".into(),
    ];
    let parsed = parse_subcommand_args(&args).expect("should parse hardened profile args");

    assert!(parsed.hardened);
    assert_eq!(parsed.hardened_override, Some(true));
    assert_eq!(parsed.trust_profile.as_deref(), Some("coreutils_hardened"));
    assert_eq!(parsed.manifest_path.as_deref(), Some("examples/hardened/Cargo.toml"));
    assert_eq!(
        parsed.passthrough,
        vec!["--manifest-path", "examples/hardened/Cargo.toml", "--release"]
    );
}

#[test]
fn test_parse_args_no_hardened_does_not_passthrough() {
    let args = vec![
        "--no-hardened".into(),
        "--manifest-path".into(),
        "Cargo.toml".into(),
        "--release".into(),
    ];
    let parsed = parse_subcommand_args(&args).expect("should parse no-hardened args");

    assert!(!parsed.hardened);
    assert_eq!(parsed.hardened_override, Some(false));
    assert_eq!(parsed.trust_profile, None);
    assert_eq!(parsed.passthrough, vec!["--manifest-path", "Cargo.toml", "--release"]);
}

// -- Report helper tests --

#[test]
fn test_parse_vc_kind_maps_known_aliases() {
    assert!(matches!(parse_vc_kind("divzero"), VcKind::DivisionByZero));
    assert!(matches!(parse_vc_kind("div_by_zero"), VcKind::DivisionByZero));
    assert!(matches!(parse_vc_kind("division_by_zero"), VcKind::DivisionByZero));
    assert!(matches!(parse_vc_kind("remzero"), VcKind::RemainderByZero));
    assert!(matches!(parse_vc_kind("bounds"), VcKind::IndexOutOfBounds));
    assert!(matches!(parse_vc_kind("slice"), VcKind::SliceBoundsCheck));
    assert!(matches!(parse_vc_kind("slice_bounds_check"), VcKind::SliceBoundsCheck));
    assert!(matches!(parse_vc_kind("postcond"), VcKind::Postcondition));
    assert!(matches!(parse_vc_kind("unreach"), VcKind::Unreachable));
    assert!(matches!(
        parse_vc_kind("hardened_byte_loss"),
        VcKind::HardenedBoundary { category: HardenedVcCategory::ByteLoss, .. }
    ));
    assert!(matches!(
        parse_vc_kind("hardened::raw_path_api"),
        VcKind::HardenedBoundary { category: HardenedVcCategory::RawPathApi, .. }
    ));
}

#[test]
fn test_parse_vc_kind_maps_all_hardened_category_tags() {
    for (tag, category) in [
        ("raw_path_api", HardenedVcCategory::RawPathApi),
        ("path_identity", HardenedVcCategory::PathIdentity),
        ("permission_change", HardenedVcCategory::PermissionChange),
        ("permission_create", HardenedVcCategory::PermissionCreate),
        ("permission_window", HardenedVcCategory::PermissionWindow),
        ("utf8_reject", HardenedVcCategory::Utf8Reject),
        ("byte_loss", HardenedVcCategory::ByteLoss),
        ("error_discard", HardenedVcCategory::ErrorDiscard),
        ("panic_boundary", HardenedVcCategory::PanicBoundary),
        ("compat_observable", HardenedVcCategory::CompatObservable),
        ("process_semantics", HardenedVcCategory::ProcessSemantics),
        ("trust_domain", HardenedVcCategory::TrustDomain),
        ("trust_domain_order", HardenedVcCategory::TrustDomainOrder),
        ("unsafe_operation", HardenedVcCategory::UnsafeOperation),
        ("ffi_boundary", HardenedVcCategory::FfiBoundary),
    ] {
        for spelling in [format!("hardened_{tag}"), format!("hardened::{tag}")] {
            let kind = parse_vc_kind(&spelling);
            assert_eq!(kind.hardened_category(), Some(category), "{spelling}");
            assert_eq!(kind.hardened_family_tag(), Some(format!("hardened_{tag}")));
        }
    }
}

#[test]
fn test_parse_vc_kind_rejects_lossy_tags_and_keeps_unknown_assertions() {
    assert!(matches!(parse_vc_kind("overflow:sub"), VcKind::UnsupportedMir { .. }));
    assert!(matches!(parse_vc_kind("arithmetic_overflow:mul"), VcKind::UnsupportedMir { .. }));
    assert!(matches!(parse_vc_kind("temporal"), VcKind::UnsupportedMir { .. }));
    assert!(matches!(parse_vc_kind("unknown"), VcKind::UnsupportedMir { .. }));

    match parse_vc_kind("custom::check") {
        VcKind::Assertion { message } => assert_eq!(message, "custom::check"),
        other => panic!("expected assertion fallback, got {other:?}"),
    }
}
