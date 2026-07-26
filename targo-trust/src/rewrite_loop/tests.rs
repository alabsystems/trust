// Tests for the rewrite loop.

use trust_backprop::file_io::FileRewriteResult;
use trust_backprop::{
    ApprovalPolicy, ApprovalStatus, AuditTrail, BinarySourceBackpropagationGateDetails,
    SourceRewrite, format_unified, generate_diff,
};
use trust_strengthen::{Proposal, ProposalKind};
use trust_types::{
    BinaryArtifactDigest, BinaryArtifactDigestIdentity, BinarySelectedImageIdentity,
    BinarySourceProvenanceSummary, BinaryVerificationStatus, BinaryVerificationSummary,
    DecompileTarget, DecompiledOutput, ProofCertificateProductionCheckerEvidenceRef,
    ProofCertificateStatus, ReconstructionSummary, ReconstructionValidationStatus, ReplayStatus,
    SolverDispatchRecord, SolverDispatchStatus, SourceSpan, TrustLevel,
};

use super::ownership::{
    EXACT_SOURCE_TYPE_OWNERSHIP_SCHEMA_VERSION, RuntimeExactSourceTypeOwnershipProofIdentifiers,
    RuntimeExactSourceTypeOwnershipRow,
};
use super::proposal::{
    extract_file_path, extract_function_name, propose_rewrites, to_strengthen_proposal,
};
use super::types::RepairRewriteRecord;
use super::*;
use crate::types::{VerificationOutcome, VerificationResult};

fn make_result(kind: &str, outcome: VerificationOutcome) -> VerificationResult {
    VerificationResult {
        function: "crate::test_fn".into(),
        kind: kind.into(),
        message: format!("{kind} test"),
        outcome,
        backend: "ay-smtlib".into(),
        time_ms: Some(5),
        location: None,
        counterexample: None,
        reason: None,
        raw_line: format!(
            "note: Trust [{kind}]: {kind} test -- {} (ay-smtlib, 5ms)",
            outcome.label()
        ),
    }
}

const SOURCE_PROVENANCE_ARTIFACT_DIGEST: &str =
    "sha256:7777777777777777777777777777777777777777777777777777777777777777";
const SOURCE_PROVENANCE_RECORD_DIGEST: &str =
    "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee";
const TYPE_FACT_DIGEST: &str =
    "sha256:2222222222222222222222222222222222222222222222222222222222222222";
const EXACT_OWNERSHIP_ARTIFACT_DIGEST: &str =
    "sha256:9999999999999999999999999999999999999999999999999999999999999999";

fn exact_binary_source_provenance_for(
    binary_address: u64,
    source: SourceSpan,
) -> RuntimeBinarySourceProvenance {
    let summary = exact_binary_source_summary();
    let mapping = exact_runtime_binary_source_mapping(binary_address, source);
    let verification = proof_grade_binary_verification_for(&mapping);
    let reconstruction = validated_reconstruction();
    let checked_binary_identity = RuntimeBinarySourceIdentity {
        binary_path: mapping.binary_path.clone(),
        binary_sha256: mapping
            .binary_artifact_digest_identity
            .as_ref()
            .and_then(|identity| identity.root_artifact_digest.as_ref())
            .map(|digest| digest.value.clone()),
        selected_image_sha256: mapping
            .binary_artifact_digest_identity
            .as_ref()
            .and_then(|identity| identity.selected_image.as_ref())
            .map(|selected| selected.sha256.clone()),
        function_entry: mapping.function_entry,
    };
    let source_gate = accepted_source_gate(summary.clone());
    RuntimeBinarySourceProvenance::new_with_checked_binary_identity(
        summary,
        checked_binary_identity,
        vec![mapping],
    )
    .with_checked_binary_backpropagation_evidence(&verification, &reconstruction, &source_gate)
    .with_exact_source_type_ownership_artifact(
        Some(exact_source_type_ownership_artifact_for(
            verification
                .solver_dispatch
                .first()
                .expect("test verification should have one dispatch")
                .origin
                .as_ref()
                .expect("test dispatch should have origin")
                .instruction_address,
            verification
                .solver_dispatch
                .first()
                .expect("test verification should have one dispatch")
                .origin
                .as_ref()
                .expect("test dispatch should have origin")
                .source
                .clone()
                .expect("test dispatch should have source"),
        )),
        Some(SOURCE_PROVENANCE_ARTIFACT_DIGEST),
        &verification,
    )
}

fn exact_binary_source_summary() -> BinarySourceProvenanceSummary {
    BinarySourceProvenanceSummary {
        status: "exact".into(),
        exact_mapping_count: 1,
        ambiguous_mapping_count: 0,
        diagnostics: Vec::new(),
        source_backpropagation_allowed: true,
    }
}

fn accepted_source_gate(
    summary: BinarySourceProvenanceSummary,
) -> BinarySourceBackpropagationGateDetails {
    BinarySourceBackpropagationGateDetails::evaluated(summary, true, true, true, true, true, true)
        .with_checked_source_provenance_binary_identity(replay_grade_artifact_identity())
}

fn exact_runtime_binary_source_mapping(
    binary_address: u64,
    source: SourceSpan,
) -> RuntimeBinarySourceMapping {
    RuntimeBinarySourceMapping {
        binary_address,
        binary_path: Some("fixtures/tiny.bin".into()),
        function_entry: Some(0x401000),
        instruction_size: Some(1),
        instruction_bytes: vec![0x90],
        binary_artifact_digest_identity: Some(replay_grade_artifact_identity()),
        source_status: Some("exact".into()),
        provenance_status: Some("checked_exact".into()),
        provenance_record_digest: Some(SOURCE_PROVENANCE_RECORD_DIGEST.into()),
        proof_evidence: RuntimeBinarySourceProofEvidence {
            solver_dispatch_id: Some("test-vc".into()),
            certificate_sha256: Some(
                "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".into(),
            ),
            production_checker_evidence_sha256: Some(
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into(),
            ),
            source_backpropagation_gate_sha256: Some(
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff".into(),
            ),
            replay_transcript_digest: Some(
                "1111111111111111111111111111111111111111111111111111111111111111".into(),
            ),
        },
        source,
    }
}

fn exact_source_type_ownership_artifact_for(
    binary_address: u64,
    source: SourceSpan,
) -> RuntimeExactSourceTypeOwnershipArtifact {
    RuntimeExactSourceTypeOwnershipArtifact {
        schema_version: EXACT_SOURCE_TYPE_OWNERSHIP_SCHEMA_VERSION.to_string(),
        status: "accepted".to_string(),
        artifact_digest: Some(EXACT_OWNERSHIP_ARTIFACT_DIGEST.to_string()),
        binary_digest: Some(
            "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc".to_string(),
        ),
        selected_image: Some(BinarySelectedImageIdentity {
            file_offset: 0,
            file_size: 16,
            sha256: "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd".into(),
        }),
        source_provenance_artifact_digest: Some(SOURCE_PROVENANCE_ARTIFACT_DIGEST.to_string()),
        type_fact_digests: vec![TYPE_FACT_DIGEST.to_string()],
        checked_proof_identifiers: RuntimeExactSourceTypeOwnershipProofIdentifiers {
            solver_dispatch_ids: vec!["test-vc".to_string()],
            checked_certificate_sha256: vec![
                "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
                    .to_string(),
            ],
            production_checker_evidence_sha256: vec![
                "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                    .to_string(),
            ],
            source_backpropagation_gate_sha256: vec![
                "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
                    .to_string(),
            ],
            replay_transcript_digests: vec![
                "sha256:1111111111111111111111111111111111111111111111111111111111111111"
                    .to_string(),
            ],
        },
        ownership_rows: vec![RuntimeExactSourceTypeOwnershipRow {
            binary_address,
            source: Some(source),
            source_provenance_record_digest: Some(format!(
                "sha256:{SOURCE_PROVENANCE_RECORD_DIGEST}"
            )),
            type_fact_digest: Some(TYPE_FACT_DIGEST.to_string()),
            solver_dispatch_id: Some("test-vc".to_string()),
        }],
        ambiguous_ownership_count: 0,
        blockers: Vec::new(),
    }
}

fn checked_certificate() -> ProofCertificateStatus {
    let checker_evidence = ProofCertificateProductionCheckerEvidenceRef::new(
        "test-checker",
        "1.0.0",
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    )
    .expect("production checker evidence should be valid");
    ProofCertificateStatus::Checked {
        checker: checker_evidence.legacy_checker_status(),
        format: "test-cert".into(),
        sha256: Some("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".into()),
    }
}

fn replay_grade_artifact_identity() -> BinaryArtifactDigestIdentity {
    BinaryArtifactDigestIdentity {
        root_artifact_digest: Some(BinaryArtifactDigest::sha256(
            "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
        )),
        selected_image: Some(BinarySelectedImageIdentity {
            file_offset: 0,
            file_size: 16,
            sha256: "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd".into(),
        }),
    }
}

fn proof_grade_binary_verification() -> BinaryVerificationSummary {
    let mapping = exact_runtime_binary_source_mapping(
        0x401000,
        SourceSpan {
            file: "/tmp/recovered.rs".into(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 10,
        },
    );
    proof_grade_binary_verification_for(&mapping)
}

fn proof_grade_binary_verification_for(
    mapping: &RuntimeBinarySourceMapping,
) -> BinaryVerificationSummary {
    let certificate = checked_certificate();
    BinaryVerificationSummary {
        status: BinaryVerificationStatus::Proved,
        trust_level: TrustLevel::ProofGrade,
        total_vcs: 1,
        proved: 1,
        solver_dispatch: vec![SolverDispatchRecord {
            id: "test-vc".into(),
            solver: "test-solver".into(),
            status: SolverDispatchStatus::Unsat,
            origin: Some(mapping.canonical_origin()),
            binary_artifact_digest_identity: mapping.binary_artifact_digest_identity.clone(),
            replay: ReplayStatus::Replayed,
            certificate: certificate.clone(),
            ..Default::default()
        }],
        proof_certificate: certificate,
        replay: ReplayStatus::Replayed,
        ..Default::default()
    }
}

fn validated_reconstruction() -> ReconstructionSummary {
    ReconstructionSummary {
        target: DecompileTarget::TrustIr,
        validation: ReconstructionValidationStatus::Validated,
        trust_level: TrustLevel::ProofGrade,
        outputs: vec![DecompiledOutput {
            target: DecompileTarget::TrustIr,
            validation: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        }],
        ..Default::default()
    }
}

fn exact_binary_source_provenance() -> RuntimeBinarySourceProvenance {
    exact_binary_source_provenance_for(
        0x401000,
        SourceSpan {
            file: "/tmp/recovered.rs".into(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 10,
        },
    )
}

#[test]
fn test_proof_frontier_from_results() {
    let results = vec![
        make_result("overflow:add", VerificationOutcome::Proved),
        make_result("div_by_zero", VerificationOutcome::Failed),
        make_result("bounds", VerificationOutcome::Unknown),
    ];
    let frontier = ProofFrontier::from_results(&results);
    assert_eq!(frontier.proved, 1);
    assert_eq!(frontier.failed, 1);
    assert_eq!(frontier.unknown, 1);
    assert_eq!(frontier.total(), 3);
}

#[test]
fn test_convergence_first_iteration_continues() {
    let mut tracker = ConvergenceTracker::new(10);
    let decision = tracker.observe(ProofFrontier { proved: 1, failed: 2, unknown: 0 });
    assert!(matches!(decision, LoopDecision::Continue { .. }));
}

#[test]
fn test_convergence_stable_converges() {
    let mut tracker = ConvergenceTracker::new(10);
    let frontier = ProofFrontier { proved: 3, failed: 0, unknown: 1 };
    tracker.observe(frontier.clone());
    let decision = tracker.observe(frontier);
    assert!(matches!(decision, LoopDecision::Converged { stable_rounds: 2 }));
}

#[test]
fn test_convergence_regression_fewer_proofs() {
    let mut tracker = ConvergenceTracker::new(10);
    tracker.observe(ProofFrontier { proved: 5, failed: 0, unknown: 0 });
    let decision = tracker.observe(ProofFrontier { proved: 3, failed: 0, unknown: 2 });
    assert!(matches!(decision, LoopDecision::Regressed { .. }));
}

#[test]
fn test_convergence_regression_more_failures() {
    let mut tracker = ConvergenceTracker::new(10);
    tracker.observe(ProofFrontier { proved: 3, failed: 1, unknown: 0 });
    let decision = tracker.observe(ProofFrontier { proved: 3, failed: 2, unknown: 0 });
    assert!(matches!(decision, LoopDecision::Regressed { .. }));
}

#[test]
fn test_convergence_iteration_limit() {
    let mut tracker = ConvergenceTracker::new(2);
    tracker.observe(ProofFrontier { proved: 1, failed: 1, unknown: 0 });
    let decision = tracker.observe(ProofFrontier { proved: 2, failed: 0, unknown: 0 });
    assert!(matches!(decision, LoopDecision::IterationLimitReached));
}

#[test]
fn test_propose_rewrites_overflow() {
    let results = vec![make_result("overflow:add", VerificationOutcome::Failed)];
    let proposals = propose_rewrites(&results);
    assert_eq!(proposals.len(), 1);
    assert_eq!(proposals[0].kind, "safe_arithmetic");
}

#[test]
fn test_propose_rewrites_div_by_zero() {
    let results = vec![make_result("div_by_zero", VerificationOutcome::Failed)];
    let proposals = propose_rewrites(&results);
    assert_eq!(proposals.len(), 1);
    assert_eq!(proposals[0].kind, "non_zero_check");
}

#[test]
fn test_propose_rewrites_bounds() {
    let results = vec![make_result("bounds", VerificationOutcome::Failed)];
    let proposals = propose_rewrites(&results);
    assert_eq!(proposals.len(), 1);
    assert_eq!(proposals[0].kind, "bounds_check");
}

#[test]
fn test_propose_rewrites_skips_proved() {
    let results = vec![
        make_result("overflow:add", VerificationOutcome::Proved),
        make_result("div_by_zero", VerificationOutcome::Failed),
    ];
    let proposals = propose_rewrites(&results);
    assert_eq!(proposals.len(), 1);
    assert_eq!(proposals[0].kind, "non_zero_check");
}

#[test]
fn test_classify_failure_unknown_kind() {
    let result = make_result("custom_check", VerificationOutcome::Failed);
    let proposals = propose_rewrites(&[result]);
    assert_eq!(proposals.len(), 1);
    assert_eq!(proposals[0].kind, "add_precondition");
}

#[test]
fn test_extract_function_name_from_line() {
    let line = "note: Trust [overflow:add]: arithmetic overflow (Add) -- FAILED (ay, 8ms)";
    assert_eq!(extract_function_name(line), "overflow:add");
}

#[test]
fn test_extract_function_name_fallback() {
    assert_eq!(extract_function_name("random text"), "unknown");
}

// -- Backprop engine tests --

#[test]
fn test_to_strengthen_proposal_overflow() {
    let proposal = RewriteProposal {
        function: "overflow:add".into(),
        kind: "safe_arithmetic".into(),
        description: "Replace raw arithmetic with checked variant".into(),
    };
    let results = vec![make_result("overflow:add", VerificationOutcome::Failed)];
    let sp = to_strengthen_proposal(&proposal, &results, None, None);
    assert!(matches!(sp.kind, ProposalKind::SafeArithmetic { .. }));
    assert_eq!(sp.function_name, "overflow:add");
}

#[test]
fn test_to_strengthen_proposal_precondition_fallback() {
    let proposal = RewriteProposal {
        function: "custom_check".into(),
        kind: "add_precondition".into(),
        description: "Add precondition to constrain inputs".into(),
    };
    let sp = to_strengthen_proposal(&proposal, &[], None, None);
    assert!(matches!(sp.kind, ProposalKind::AddPrecondition { .. }));
}

#[test]
fn test_to_strengthen_proposal_non_zero_check() {
    let proposal = RewriteProposal {
        function: "div_by_zero".into(),
        kind: "non_zero_check".into(),
        description: "Add divisor != 0 assertion".into(),
    };
    let sp = to_strengthen_proposal(&proposal, &[], None, None);
    assert!(matches!(sp.kind, ProposalKind::AddNonZeroCheck { .. }));
}

#[test]
fn test_to_strengthen_proposal_bounds_check() {
    let proposal = RewriteProposal {
        function: "bounds".into(),
        kind: "bounds_check".into(),
        description: "Add bounds check".into(),
    };
    let sp = to_strengthen_proposal(&proposal, &[], None, None);
    assert!(matches!(sp.kind, ProposalKind::AddBoundsCheck { .. }));
}

#[test]
fn test_extract_file_path_with_line() {
    let line = "  --> src/lib.rs:10:5";
    assert_eq!(extract_file_path(line), Some("src/lib.rs".into()));
}

#[test]
fn test_extract_file_path_bare() {
    let line = "error in src/main.rs some context";
    assert_eq!(extract_file_path(line), Some("src/main.rs".into()));
}

#[test]
fn test_extract_file_path_none() {
    assert_eq!(extract_file_path("no file reference here"), None);
}

#[test]
fn test_backprop_engine_governance_blocks_test() {
    let mut engine = BackpropEngine::new();
    let proposal = RewriteProposal {
        function: "test_something".into(),
        kind: "safe_arithmetic".into(),
        description: "test".into(),
    };
    let result = engine.apply(&[proposal], &[]);
    // test_ prefix triggers governance TestFunction violation
    assert_eq!(result.governance_skips, 1);
    assert_eq!(result.rewrites_applied, 0);
}

#[test]
fn test_backprop_engine_with_protected() {
    let mut engine = BackpropEngine::with_protected(&["critical_fn".into()]);
    let proposal = RewriteProposal {
        function: "critical_fn".into(),
        kind: "safe_arithmetic".into(),
        description: "test".into(),
    };
    let result = engine.apply(&[proposal], &[]);
    // Protected function blocks non-spec rewrites
    assert_eq!(result.governance_skips, 1);
    assert_eq!(result.rewrites_applied, 0);
}

#[test]
fn test_backprop_engine_empty_proposals() {
    let mut engine = BackpropEngine::new();
    let result = engine.apply(&[], &[]);
    assert_eq!(result.files_modified, 0);
    assert_eq!(result.rewrites_applied, 0);
    assert_eq!(result.governance_skips, 0);
    assert_eq!(result.limit_skips, 0);
}

#[test]
fn test_to_strengthen_proposal_uses_default_source_file() {
    let proposal = RewriteProposal {
        function: "overflow:add".into(),
        kind: "add_precondition".into(),
        description: "Add precondition".into(),
    };
    // Without default_source_file, falls back to function name
    let sp = to_strengthen_proposal(&proposal, &[], None, None);
    assert_eq!(sp.function_path, "overflow:add");

    // With default_source_file, uses the provided path
    let sp = to_strengthen_proposal(&proposal, &[], Some("/tmp/test.rs"), None);
    assert_eq!(sp.function_path, "/tmp/test.rs");
}

#[test]
fn test_to_strengthen_proposal_rejects_binary_raw_line_without_exact_provenance() {
    let proposal = RewriteProposal {
        function: "overflow:add".into(),
        kind: "add_precondition".into(),
        description: "a <= u32::MAX - b".into(),
    };
    let result = VerificationResult {
        function: "binary::add".into(),
        kind: "overflow:add".into(),
        message: "overflow".into(),
        outcome: VerificationOutcome::Failed,
        backend: "ay-smtlib".into(),
        time_ms: Some(3),
        location: None,
        counterexample: None,
        reason: None,
        raw_line: "  --> /tmp/recovered.rs:1:5".into(),
    };

    let strengthen = to_strengthen_proposal(&proposal, &[result], Some("/tmp/default.rs"), None);

    assert_eq!(
        strengthen.function_path, "overflow:add",
        "binary-derived raw diagnostics must not upgrade to source paths without exact provenance"
    );
}

#[test]
fn test_backprop_engine_queues_spec_rewrite_for_review() {
    // Create a temp file with a function that has an overflow issue
    let dir = std::env::temp_dir().join("trust_rewrite_test");
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("test_rewrite.rs");
    let original_source = "fn add(a: u32, b: u32) -> u32 {\n    a + b\n}\n";
    std::fs::write(&file, original_source).unwrap();

    let file_path_str = file.display().to_string();

    let mut engine = BackpropEngine::new();
    engine.set_default_source_file(file_path_str.clone());

    let proposal = RewriteProposal {
        function: "add".into(),
        kind: "add_precondition".into(),
        description: "a <= u32::MAX - b".into(),
    };

    let result = engine.apply(&[proposal], &[]);

    // A native `requires ...` insertion is an unverified contract claim (Pillar 2):
    // it queues for review instead of auto-writing into user source.
    assert_eq!(result.rewrites_applied, 0);
    assert_eq!(result.files_modified, 0);
    assert_eq!(result.pending_rewrites.len(), 1);
    assert_eq!(result.pending_rewrites[0].policy, ApprovalPolicy::Review);
    match &result.pending_rewrites[0].rewrite.kind {
        trust_backprop::RewriteKind::InsertContractClause { clause, expression } => {
            assert_eq!(*clause, trust_backprop::ContractClauseKind::Requires);
            assert_eq!(expression, "a <= u32::MAX - b");
        }
        other => panic!("expected InsertContractClause pending rewrite, got {other:?}"),
    }

    // The source is untouched until the queued rewrite is approved.
    assert_eq!(std::fs::read_to_string(&file).unwrap(), original_source);

    // Cleanup
    std::fs::remove_file(&file).ok();
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn test_backprop_engine_iterates_queueing_spec_rewrites() {
    // Simulates multiple iterations of the rewrite loop
    let dir = std::env::temp_dir().join("trust_rewrite_iter_test");
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("test_iter.rs");
    let original = "fn compute(x: u32, y: u32) -> u32 {\n    x + y\n}\n";
    std::fs::write(&file, original).unwrap();

    let file_path_str = file.display().to_string();

    let mut engine = BackpropEngine::new();
    engine.set_default_source_file(file_path_str.clone());

    // First iteration: add a precondition — queues for review (Pillar 2),
    // leaving the source untouched.
    let proposal1 = RewriteProposal {
        function: "compute".into(),
        kind: "add_precondition".into(),
        description: "x <= u32::MAX - y".into(),
    };
    let r1 = engine.apply(&[proposal1], &[]);
    assert_eq!(r1.rewrites_applied, 0, "spec insertions queue for review, never auto-apply");
    assert_eq!(r1.files_modified, 0);
    assert_eq!(r1.pending_rewrites.len(), 1, "first iteration should queue its spec rewrite");
    match &r1.pending_rewrites[0].rewrite.kind {
        trust_backprop::RewriteKind::InsertContractClause { clause, expression } => {
            assert_eq!(*clause, trust_backprop::ContractClauseKind::Requires);
            assert_eq!(expression, "x <= u32::MAX - y");
        }
        other => panic!("expected InsertContractClause pending rewrite, got {other:?}"),
    }
    assert_eq!(std::fs::read_to_string(&file).unwrap(), original);

    // Second iteration with a different proposal: queues independently.
    let proposal2 = RewriteProposal {
        function: "compute".into(),
        kind: "add_precondition".into(),
        description: "x > 0".into(),
    };
    let r2 = engine.apply(&[proposal2], &[]);
    assert_eq!(r2.rewrites_applied, 0, "second iteration should also queue, not auto-apply");
    assert_eq!(r2.files_modified, 0);
    assert_eq!(r2.pending_rewrites.len(), 1, "second iteration should queue its spec rewrite");
    match &r2.pending_rewrites[0].rewrite.kind {
        trust_backprop::RewriteKind::InsertContractClause { clause, expression } => {
            assert_eq!(*clause, trust_backprop::ContractClauseKind::Requires);
            assert_eq!(expression, "x > 0");
        }
        other => panic!("expected InsertContractClause pending rewrite, got {other:?}"),
    }
    assert_eq!(std::fs::read_to_string(&file).unwrap(), original);

    // Cleanup
    std::fs::remove_file(&file).ok();
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn test_strengthen_failures_uses_source_context() {
    let dir = std::env::temp_dir().join("trust_strengthen_ctx_test");
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("divide.rs");
    std::fs::write(&file, "fn divide(x: u32, y: u32) -> u32 {\n    x / y\n}\n").unwrap();

    let file_path = file.display().to_string();
    let result = VerificationResult {
        function: "crate::divide".into(),
        kind: "div_by_zero".into(),
        message: "division by zero".into(),
        outcome: VerificationOutcome::Failed,
        backend: "ay-smtlib".into(),
        time_ms: Some(3),
        location: Some(SourceSpan {
            file: file_path.clone(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 10,
        }),
        counterexample: None,
        reason: None,
        raw_line: "note: Trust [div_by_zero] at source divide.rs:1:1".into(),
    };

    let strengthen = strengthen_failures(&[result], None);
    assert!(strengthen.proposals.iter().any(|proposal| {
        matches!(
            &proposal.kind,
            ProposalKind::AddPrecondition { spec_body } if spec_body == "y != 0"
        )
    }));
    assert!(
        strengthen
            .proposals
            .iter()
            .any(|proposal| { matches!(&proposal.kind, ProposalKind::AddNonZeroCheck { .. }) })
    );

    std::fs::remove_file(&file).ok();
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn test_strengthen_failures_rejects_binary_source_without_exact_provenance() {
    let dir = std::env::temp_dir().join("trust_strengthen_binary_source_closed_test");
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("divide.rs");
    std::fs::write(&file, "fn divide(x: u32, y: u32) -> u32 {\n    x / y\n}\n").unwrap();

    let result = VerificationResult {
        function: "binary::divide".into(),
        kind: "div_by_zero".into(),
        message: "division by zero".into(),
        outcome: VerificationOutcome::Failed,
        backend: "ay-smtlib".into(),
        time_ms: Some(3),
        location: Some(SourceSpan {
            file: file.display().to_string(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 10,
        }),
        counterexample: None,
        reason: None,
        raw_line: "note: Trust [div_by_zero] at binary:0x401000".into(),
    };

    let strengthen = strengthen_failures_with_binary_source_provenance(&[result], None);

    assert!(strengthen.proposals.is_empty());
    assert_eq!(strengthen.failures.len(), 1);
    assert!(strengthen.failures[0].source_context.is_none());

    std::fs::remove_file(&file).ok();
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn test_runtime_strengthen_wrapper_keeps_binary_source_closed() {
    let result = VerificationResult {
        function: "binary::divide".into(),
        kind: "div_by_zero".into(),
        message: "division by zero".into(),
        outcome: VerificationOutcome::Failed,
        backend: "ay-smtlib".into(),
        time_ms: Some(3),
        location: Some(SourceSpan {
            file: "/tmp/recovered.rs".into(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 10,
        }),
        counterexample: None,
        reason: None,
        raw_line: "note: Trust [div_by_zero] at binary:0x401000".into(),
    };

    let strengthen = strengthen_failures(&[result], None);

    assert!(strengthen.proposals.is_empty());
    assert_eq!(strengthen.failures.len(), 1);
    assert!(strengthen.failures[0].source_context.is_none());
}

#[test]
fn test_binary_address_raw_diagnostic_requires_checked_provenance() {
    let result = VerificationResult {
        function: "crate::divide".into(),
        kind: "div_by_zero".into(),
        message: "division by zero".into(),
        outcome: VerificationOutcome::Failed,
        backend: "ay-smtlib".into(),
        time_ms: Some(3),
        location: Some(SourceSpan {
            file: "/tmp/recovered.rs".into(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 10,
        }),
        counterexample: None,
        reason: None,
        raw_line: "note: Trust [div_by_zero] at binary:0x401000".into(),
    };

    let strengthen =
        strengthen_failures_with_binary_source_provenance(std::slice::from_ref(&result), None);
    let blockers = binary_source_backpropagation_blockers(&[result], None);

    assert!(strengthen.proposals.is_empty());
    assert_eq!(strengthen.failures.len(), 1);
    assert!(strengthen.failures[0].source_context.is_none());
    assert_eq!(blockers.len(), 1);
    assert!(blockers[0].reason.contains("no exact binary source provenance artifact"));
}

#[test]
fn test_exact_mapping_without_checked_binary_evidence_stays_binary_address_only() {
    let result = VerificationResult {
        function: "binary::divide".into(),
        kind: "div_by_zero".into(),
        message: "division by zero".into(),
        outcome: VerificationOutcome::Failed,
        backend: "ay-smtlib".into(),
        time_ms: Some(3),
        location: Some(SourceSpan {
            file: "/tmp/recovered.rs".into(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 10,
        }),
        counterexample: None,
        reason: None,
        raw_line: "note: Trust [div_by_zero] at binary:0x401000".into(),
    };
    let provenance = RuntimeBinarySourceProvenance::new(
        exact_binary_source_summary(),
        vec![exact_runtime_binary_source_mapping(
            0x401000,
            result.location.clone().expect("test result has source span"),
        )],
    );

    let strengthen = strengthen_failures_with_binary_source_provenance(
        std::slice::from_ref(&result),
        Some(&provenance),
    );
    let blockers = binary_source_backpropagation_blockers(&[result], Some(&provenance));

    assert!(strengthen.proposals.is_empty());
    assert_eq!(strengthen.failures.len(), 1);
    assert!(strengthen.failures[0].source_context.is_none());
    assert_eq!(blockers.len(), 1);
    assert!(blockers[0].reason.contains("source rewrite authority is unchecked"));
    assert!(blockers[0].reason.contains("proof-grade binary verification"));
    assert!(blockers[0].reason.contains("binary-address-only"));
}

#[test]
fn test_checked_handoff_rejects_wrong_binary_digest_before_candidate_generation() {
    let dir = std::env::temp_dir().join("trust_strengthen_binary_source_wrong_digest_test");
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("divide.rs");
    std::fs::write(&file, "fn divide(x: u32, y: u32) -> u32 {\n    x / y\n}\n").unwrap();

    let source = SourceSpan {
        file: file.display().to_string(),
        line_start: 1,
        col_start: 1,
        line_end: 1,
        col_end: 10,
    };
    let valid_mapping = exact_runtime_binary_source_mapping(0x401000, source.clone());
    let mut wrong_binary_mapping = valid_mapping.clone();
    wrong_binary_mapping.binary_artifact_digest_identity = Some(BinaryArtifactDigestIdentity {
        root_artifact_digest: Some(BinaryArtifactDigest::sha256(
            "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee",
        )),
        selected_image: valid_mapping
            .binary_artifact_digest_identity
            .as_ref()
            .and_then(|identity| identity.selected_image.clone()),
    });

    let summary = exact_binary_source_summary();
    let verification = proof_grade_binary_verification_for(&valid_mapping);
    let reconstruction = validated_reconstruction();
    let source_gate = accepted_source_gate(summary.clone());
    let provenance = RuntimeBinarySourceProvenance::new(summary, vec![wrong_binary_mapping])
        .with_checked_binary_backpropagation_evidence(&verification, &reconstruction, &source_gate);

    assert!(!provenance.effective_source_backpropagation_allowed());
    let diagnostics = provenance.source_rewrite_authority_diagnostics().join("; ");
    assert!(diagnostics.contains("exact-provenance-runtime-handoff-rejected"));
    assert!(diagnostics.contains("root/selected-image digest identity"));

    let result = VerificationResult {
        function: "binary::divide".into(),
        kind: "div_by_zero".into(),
        message: "division by zero".into(),
        outcome: VerificationOutcome::Failed,
        backend: "ay-smtlib".into(),
        time_ms: Some(3),
        location: Some(source),
        counterexample: None,
        reason: None,
        raw_line: "note: Trust [div_by_zero] at binary:0x401000".into(),
    };

    let strengthen = strengthen_failures_with_binary_source_provenance(
        std::slice::from_ref(&result),
        Some(&provenance),
    );
    let blockers = binary_source_backpropagation_blockers(&[result], Some(&provenance));

    assert!(
        strengthen.proposals.is_empty(),
        "wrong-binary exact provenance must not generate a source rewrite candidate"
    );
    assert_eq!(blockers.len(), 1);
    assert!(blockers[0].reason.contains("exact-provenance-runtime-handoff-rejected"));

    std::fs::remove_file(&file).ok();
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn test_checked_handoff_rejects_missing_instruction_bytes_before_candidate_generation() {
    let source = SourceSpan {
        file: "/tmp/recovered.rs".into(),
        line_start: 1,
        col_start: 1,
        line_end: 1,
        col_end: 10,
    };
    let valid_mapping = exact_runtime_binary_source_mapping(0x401000, source.clone());
    let mut incomplete_mapping = valid_mapping.clone();
    incomplete_mapping.instruction_bytes.clear();

    let summary = exact_binary_source_summary();
    let verification = proof_grade_binary_verification_for(&valid_mapping);
    let reconstruction = validated_reconstruction();
    let source_gate = accepted_source_gate(summary.clone());
    let provenance = RuntimeBinarySourceProvenance::new(summary, vec![incomplete_mapping])
        .with_checked_binary_backpropagation_evidence(&verification, &reconstruction, &source_gate);

    assert!(!provenance.effective_source_backpropagation_allowed());
    let diagnostics = provenance.source_rewrite_authority_diagnostics().join("; ");
    assert!(diagnostics.contains("exact-provenance-runtime-handoff-rejected"));
    assert!(diagnostics.contains("missing instruction bytes"));

    let result = VerificationResult {
        function: "binary::divide".into(),
        kind: "div_by_zero".into(),
        message: "division by zero".into(),
        outcome: VerificationOutcome::Failed,
        backend: "ay-smtlib".into(),
        time_ms: Some(3),
        location: Some(source),
        counterexample: None,
        reason: None,
        raw_line: "note: Trust [div_by_zero] at binary:0x401000".into(),
    };

    let strengthen =
        strengthen_failures_with_binary_source_provenance(&[result], Some(&provenance));

    assert!(
        strengthen.proposals.is_empty(),
        "missing instruction bytes must not generate a source rewrite candidate"
    );
}

#[test]
fn test_checked_handoff_rejects_ambiguous_source_status_before_candidate_generation() {
    let source = SourceSpan {
        file: "/tmp/recovered.rs".into(),
        line_start: 1,
        col_start: 1,
        line_end: 1,
        col_end: 10,
    };
    let valid_mapping = exact_runtime_binary_source_mapping(0x401000, source.clone());
    let mut ambiguous_mapping = valid_mapping.clone();
    ambiguous_mapping.source_status = Some("ambiguous".into());
    ambiguous_mapping.provenance_status = Some("ambiguous".into());

    let summary = exact_binary_source_summary();
    let verification = proof_grade_binary_verification_for(&valid_mapping);
    let reconstruction = validated_reconstruction();
    let source_gate = accepted_source_gate(summary.clone());
    let provenance = RuntimeBinarySourceProvenance::new(summary, vec![ambiguous_mapping])
        .with_checked_binary_backpropagation_evidence(&verification, &reconstruction, &source_gate);

    assert!(!provenance.effective_source_backpropagation_allowed());
    let diagnostics = provenance.source_rewrite_authority_diagnostics().join("; ");
    assert!(diagnostics.contains("source provenance status `ambiguous`"));
    assert!(diagnostics.contains("binary provenance row status `ambiguous`"));

    let result = VerificationResult {
        function: "binary::divide".into(),
        kind: "div_by_zero".into(),
        message: "division by zero".into(),
        outcome: VerificationOutcome::Failed,
        backend: "ay-smtlib".into(),
        time_ms: Some(3),
        location: Some(source),
        counterexample: None,
        reason: None,
        raw_line: "note: Trust [div_by_zero] at binary:0x401000".into(),
    };

    let strengthen =
        strengthen_failures_with_binary_source_provenance(&[result], Some(&provenance));

    assert!(
        strengthen.proposals.is_empty(),
        "ambiguous imported provenance must not generate a source rewrite candidate"
    );
}

#[test]
fn test_checked_handoff_rejects_binary_address_only_source_mapping() {
    let source = SourceSpan::binary_address(0x401000);
    let valid_mapping = exact_runtime_binary_source_mapping(
        0x401000,
        SourceSpan {
            file: "/tmp/recovered.rs".into(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 10,
        },
    );
    let binary_only_mapping = exact_runtime_binary_source_mapping(0x401000, source.clone());

    let summary = exact_binary_source_summary();
    let verification = proof_grade_binary_verification_for(&valid_mapping);
    let reconstruction = validated_reconstruction();
    let source_gate = accepted_source_gate(summary.clone());
    let provenance = RuntimeBinarySourceProvenance::new(summary, vec![binary_only_mapping])
        .with_checked_binary_backpropagation_evidence(&verification, &reconstruction, &source_gate);

    assert!(!provenance.effective_source_backpropagation_allowed());
    let diagnostics = provenance.source_rewrite_authority_diagnostics().join("; ");
    assert!(diagnostics.contains("source mapping is still binary-address-only"));

    let result = VerificationResult {
        function: "binary::divide".into(),
        kind: "div_by_zero".into(),
        message: "division by zero".into(),
        outcome: VerificationOutcome::Failed,
        backend: "ay-smtlib".into(),
        time_ms: Some(3),
        location: Some(source),
        counterexample: None,
        reason: None,
        raw_line: "note: Trust [div_by_zero] at binary:0x401000".into(),
    };

    let strengthen =
        strengthen_failures_with_binary_source_provenance(&[result], Some(&provenance));

    assert!(
        strengthen.proposals.is_empty(),
        "binary-address-only imported provenance must not generate a source rewrite candidate"
    );
}

#[test]
fn test_checked_handoff_rejects_missing_proof_evidence_identifiers() {
    let source = SourceSpan {
        file: "/tmp/recovered.rs".into(),
        line_start: 1,
        col_start: 1,
        line_end: 1,
        col_end: 10,
    };
    let valid_mapping = exact_runtime_binary_source_mapping(0x401000, source);
    let mut incomplete_mapping = valid_mapping.clone();
    incomplete_mapping.proof_evidence.certificate_sha256 = None;
    incomplete_mapping.proof_evidence.source_backpropagation_gate_sha256 = None;

    let summary = exact_binary_source_summary();
    let verification = proof_grade_binary_verification_for(&valid_mapping);
    let reconstruction = validated_reconstruction();
    let source_gate = accepted_source_gate(summary.clone());
    let provenance = RuntimeBinarySourceProvenance::new(summary, vec![incomplete_mapping])
        .with_checked_binary_backpropagation_evidence(&verification, &reconstruction, &source_gate);

    assert!(!provenance.effective_source_backpropagation_allowed());
    let diagnostics = provenance.source_rewrite_authority_diagnostics().join("; ");
    assert!(diagnostics.contains("missing checked certificate proof evidence id"));
    assert!(
        diagnostics
            .contains("missing checked certificate source-backpropagation gate proof evidence id"),
        "{diagnostics}"
    );
}

#[test]
fn test_checked_handoff_rejects_extra_imported_exact_mapping() {
    let dir = std::env::temp_dir().join("trust_strengthen_binary_source_extra_mapping_test");
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("divide.rs");
    std::fs::write(&file, "fn divide(x: u32, y: u32) -> u32 {\n    x / y\n}\n").unwrap();

    let result = VerificationResult {
        function: "binary::divide".into(),
        kind: "div_by_zero".into(),
        message: "division by zero".into(),
        outcome: VerificationOutcome::Failed,
        backend: "ay-smtlib".into(),
        time_ms: Some(3),
        location: Some(SourceSpan {
            file: file.display().to_string(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 10,
        }),
        counterexample: None,
        reason: None,
        raw_line: "note: Trust [div_by_zero] at binary:0x401008".into(),
    };
    let summary = exact_binary_source_summary();
    let verification = proof_grade_binary_verification();
    let reconstruction = validated_reconstruction();
    let source_gate = accepted_source_gate(summary.clone());
    let provenance = RuntimeBinarySourceProvenance::new(
        summary,
        vec![
            exact_runtime_binary_source_mapping(
                0x401000,
                SourceSpan {
                    file: file.display().to_string(),
                    line_start: 1,
                    col_start: 1,
                    line_end: 1,
                    col_end: 10,
                },
            ),
            exact_runtime_binary_source_mapping(
                0x401008,
                result.location.clone().expect("test result has source span"),
            ),
        ],
    )
    .with_checked_binary_backpropagation_evidence(&verification, &reconstruction, &source_gate);

    let strengthen = strengthen_failures_with_binary_source_provenance(
        std::slice::from_ref(&result),
        Some(&provenance),
    );
    let blockers = binary_source_backpropagation_blockers(&[result], Some(&provenance));

    assert!(strengthen.proposals.is_empty());
    assert_eq!(strengthen.failures.len(), 1);
    assert!(strengthen.failures[0].source_context.is_none());
    assert_eq!(blockers.len(), 1);
    assert!(blockers[0].reason.contains("exact_mapping_count=1"));
    assert!(blockers[0].reason.contains("2 imported exact mapping"));

    std::fs::remove_file(&file).ok();
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn test_binary_source_backpropagation_blockers_require_exact_runtime_provenance() {
    let result = VerificationResult {
        function: "binary::divide".into(),
        kind: "div_by_zero".into(),
        message: "division by zero".into(),
        outcome: VerificationOutcome::Failed,
        backend: "ay-smtlib".into(),
        time_ms: Some(3),
        location: Some(SourceSpan {
            file: "/tmp/recovered.rs".into(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 10,
        }),
        counterexample: None,
        reason: None,
        raw_line: "note: Trust [div_by_zero] at binary:0x401000".into(),
    };

    let blockers = binary_source_backpropagation_blockers(std::slice::from_ref(&result), None);

    assert_eq!(blockers.len(), 1);
    assert_eq!(blockers[0].function, "binary::divide");
    assert_eq!(blockers[0].kind, "div_by_zero");
    assert_eq!(blockers[0].source_file, "/tmp/recovered.rs");
    assert!(blockers[0].reason.contains("no exact binary source provenance artifact"));

    let exact = exact_binary_source_provenance();
    assert!(binary_source_backpropagation_blockers(&[result], Some(&exact)).is_empty());
}

#[test]
fn test_runtime_rewrite_exact_provenance_summary_propagates_ownership_digest() {
    let provenance = exact_binary_source_provenance();
    let summary = RepairRunSummary {
        iterations: 1,
        succeeded: true,
        final_frontier: ProofFrontier { proved: 1, failed: 0, unknown: 0 },
        final_decision: "converged:1".to_string(),
        total_duration_ms: 7,
        exact_source_type_ownership_artifact_digest: provenance
            .exact_source_type_ownership_artifact_digest()
            .map(str::to_string),
    };

    let value = serde_json::to_value(&summary).expect("summary should serialize");

    assert_eq!(
        value["exact_source_type_ownership_artifact_digest"],
        serde_json::json!(EXACT_OWNERSHIP_ARTIFACT_DIGEST)
    );
}

#[test]
fn test_binary_source_backpropagation_blocker_rejects_missing_exact_address_mapping() {
    let result = VerificationResult {
        function: "binary::divide".into(),
        kind: "div_by_zero".into(),
        message: "division by zero".into(),
        outcome: VerificationOutcome::Failed,
        backend: "ay-smtlib".into(),
        time_ms: Some(3),
        location: Some(SourceSpan {
            file: "/tmp/recovered.rs".into(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 10,
        }),
        counterexample: None,
        reason: None,
        raw_line: "note: Trust [div_by_zero] at binary:0x401008".into(),
    };
    let provenance = exact_binary_source_provenance();

    let blockers = binary_source_backpropagation_blockers(&[result], Some(&provenance));

    assert_eq!(blockers.len(), 1);
    assert!(blockers[0].reason.contains("binary:0x401008"));
    assert!(blockers[0].reason.contains("not backed by an exact imported mapping"));
}

#[test]
fn test_binary_source_backpropagation_blocker_rejects_span_mismatch() {
    let result = VerificationResult {
        function: "binary::divide".into(),
        kind: "div_by_zero".into(),
        message: "division by zero".into(),
        outcome: VerificationOutcome::Failed,
        backend: "ay-smtlib".into(),
        time_ms: Some(3),
        location: Some(SourceSpan {
            file: "/tmp/other.rs".into(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 10,
        }),
        counterexample: None,
        reason: None,
        raw_line: "note: Trust [div_by_zero] at binary:0x401000".into(),
    };
    let provenance = exact_binary_source_provenance();

    let blockers = binary_source_backpropagation_blockers(&[result], Some(&provenance));

    assert_eq!(blockers.len(), 1);
    assert!(blockers[0].reason.contains("binary:0x401000"));
}

#[test]
fn test_strengthen_failures_allows_binary_source_with_exact_provenance() {
    let dir = std::env::temp_dir().join("trust_strengthen_binary_source_exact_test");
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("divide.rs");
    std::fs::write(&file, "fn divide(x: u32, y: u32) -> u32 {\n    x / y\n}\n").unwrap();

    let result = VerificationResult {
        function: "binary::divide".into(),
        kind: "div_by_zero".into(),
        message: "division by zero".into(),
        outcome: VerificationOutcome::Failed,
        backend: "ay-smtlib".into(),
        time_ms: Some(3),
        location: Some(SourceSpan {
            file: file.display().to_string(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 10,
        }),
        counterexample: None,
        reason: None,
        raw_line: "note: Trust [div_by_zero] at binary:0x401000".into(),
    };
    let provenance = exact_binary_source_provenance_for(
        0x401000,
        result.location.clone().expect("test result has source span"),
    );

    let strengthen =
        strengthen_failures_with_binary_source_provenance(&[result], Some(&provenance));

    assert!(strengthen.proposals.iter().any(|proposal| {
        matches!(
            &proposal.kind,
            ProposalKind::AddPrecondition { spec_body } if spec_body == "y != 0"
        )
    }));
    assert!(strengthen.failures[0].source_context.is_some());

    std::fs::remove_file(&file).ok();
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn test_strengthen_failures_skips_binary_only_span() {
    let result = VerificationResult {
        function: "binary::add".into(),
        kind: "overflow:add".into(),
        message: "overflow".into(),
        outcome: VerificationOutcome::Failed,
        backend: "ay-smtlib".into(),
        time_ms: Some(3),
        location: Some(SourceSpan {
            file: "binary:0x1000".into(),
            line_start: 0,
            col_start: 0,
            line_end: 0,
            col_end: 0,
        }),
        counterexample: None,
        reason: None,
        raw_line: String::new(),
    };

    let strengthen = strengthen_failures(&[result], Some("/tmp/source.rs"));

    assert!(strengthen.proposals.is_empty());
    assert_eq!(strengthen.failures.len(), 1);
    assert!(strengthen.failures[0].source_context.is_none());
}

#[test]
fn test_backprop_engine_apply_skips_binary_span_even_with_default_source_file() {
    let dir = std::env::temp_dir().join("trust_rewrite_binary_gate_test");
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("source.rs");
    let original = "fn add(a: u32, b: u32) -> u32 {\n    a + b\n}\n";
    std::fs::write(&file, original).unwrap();

    let proposal = RewriteProposal {
        function: "overflow:add".into(),
        kind: "add_precondition".into(),
        description: "a <= u32::MAX - b".into(),
    };
    let verification_result = VerificationResult {
        function: "binary::add".into(),
        kind: "overflow:add".into(),
        message: "overflow".into(),
        outcome: VerificationOutcome::Failed,
        backend: "ay-smtlib".into(),
        time_ms: Some(3),
        location: Some(SourceSpan {
            file: "binary:0x1000".into(),
            line_start: 0,
            col_start: 0,
            line_end: 0,
            col_end: 0,
        }),
        counterexample: None,
        reason: None,
        raw_line: String::new(),
    };

    let mut engine = BackpropEngine::new();
    engine.set_default_source_file(file.display().to_string());
    let result = engine.apply(&[proposal], &[verification_result]);

    assert_eq!(result.governance_skips, 1);
    assert_eq!(result.rewrites_applied, 0);
    assert_eq!(result.files_modified, 0);
    assert_eq!(std::fs::read_to_string(&file).unwrap(), original);

    std::fs::remove_file(&file).ok();
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn test_backprop_engine_apply_rejects_binary_source_without_exact_provenance() {
    let dir = std::env::temp_dir().join("trust_rewrite_binary_source_gate_test");
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("source.rs");
    let original = "fn add(a: u32, b: u32) -> u32 {\n    a + b\n}\n";
    std::fs::write(&file, original).unwrap();

    let proposal = RewriteProposal {
        function: "overflow:add".into(),
        kind: "add_precondition".into(),
        description: "a <= u32::MAX - b".into(),
    };
    let verification_result = VerificationResult {
        function: "binary::add".into(),
        kind: "overflow:add".into(),
        message: "overflow".into(),
        outcome: VerificationOutcome::Failed,
        backend: "ay-smtlib".into(),
        time_ms: Some(3),
        location: Some(SourceSpan {
            file: file.display().to_string(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 10,
        }),
        counterexample: None,
        reason: None,
        raw_line: String::new(),
    };

    let mut engine = BackpropEngine::new();
    engine.set_default_source_file(file.display().to_string());
    let result = engine.apply(&[proposal], &[verification_result]);

    assert_eq!(result.governance_skips, 1);
    assert_eq!(result.rewrites_applied, 0);
    assert_eq!(result.files_modified, 0);
    assert_eq!(std::fs::read_to_string(&file).unwrap(), original);

    std::fs::remove_file(&file).ok();
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn test_backprop_engine_apply_allows_binary_source_with_exact_provenance() {
    let dir = std::env::temp_dir().join("trust_rewrite_binary_source_exact_test");
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("source.rs");
    let original = "fn add(a: u32, b: u32) -> u32 {\n    a + b\n}\n";
    std::fs::write(&file, original).unwrap();

    let proposal = RewriteProposal {
        function: "add".into(),
        kind: "add_precondition".into(),
        description: "a <= u32::MAX - b".into(),
    };
    let verification_result = VerificationResult {
        function: "binary::add".into(),
        kind: "add".into(),
        message: "overflow".into(),
        outcome: VerificationOutcome::Failed,
        backend: "ay-smtlib".into(),
        time_ms: Some(3),
        location: Some(SourceSpan {
            file: file.display().to_string(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 10,
        }),
        counterexample: None,
        reason: None,
        raw_line: "note: Trust [add] at binary:0x401000".into(),
    };

    let mut engine = BackpropEngine::new();
    engine.set_binary_source_provenance(exact_binary_source_provenance_for(
        0x401000,
        verification_result.location.clone().expect("test result has source span"),
    ));
    let result = engine.apply(&[proposal], &[verification_result]);

    // Exact provenance clears the binary-source gate (no governance skip); the
    // spec insertion itself still queues for review rather than auto-applying.
    assert_eq!(result.governance_skips, 0);
    assert_eq!(result.rewrites_applied, 0);
    assert_eq!(result.files_modified, 0);
    assert_eq!(result.pending_rewrites.len(), 1);
    assert_eq!(result.pending_rewrites[0].policy, ApprovalPolicy::Review);
    assert_eq!(std::fs::read_to_string(&file).unwrap(), original);

    std::fs::remove_file(&file).ok();
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn test_backprop_engine_skips_binary_proposal_path() {
    let proposal = Proposal {
        function_path: "binary:0x1000".into(),
        function_name: "add".into(),
        kind: ProposalKind::AddPrecondition { spec_body: "a <= u32::MAX - b".into() },
        confidence: 0.8,
        rationale: "prevent overflow".into(),
    };

    let mut engine = BackpropEngine::new();
    let result = engine.apply_strengthen_proposals(&[proposal], 0, 0);

    assert_eq!(result.governance_skips, 1);
    assert_eq!(result.rewrites_applied, 0);
    assert_eq!(result.files_modified, 0);
    assert!(result.pending_rewrites.is_empty());
}

#[test]
fn test_backprop_engine_queues_expression_rewrites_for_review() {
    let dir = std::env::temp_dir().join("trust_rewrite_review_test");
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("review.rs");
    let original = "fn add(a: u32, b: u32) -> u32 {\n    a + b\n}\n";
    std::fs::write(&file, original).unwrap();

    let proposal = Proposal {
        function_path: file.display().to_string(),
        function_name: "add".into(),
        kind: ProposalKind::SafeArithmetic {
            original: "a + b".into(),
            replacement: "a.checked_add(b).expect(\"addition overflow\")".into(),
        },
        confidence: 0.95,
        rationale: "replace unchecked add".into(),
    };

    let mut engine = BackpropEngine::new();
    let result = engine.apply_strengthen_proposals(&[proposal], 0, 0);

    assert_eq!(result.rewrites_applied, 0);
    assert_eq!(result.pending_rewrites.len(), 1);
    assert_eq!(result.pending_rewrites[0].policy, ApprovalPolicy::Review);
    assert_eq!(std::fs::read_to_string(&file).unwrap(), original);

    std::fs::remove_file(&file).ok();
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn test_build_rewrite_records_includes_structured_diff() {
    let dir = std::env::temp_dir().join("trust_rewrite_record_test");
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("record.rs");
    let original = "fn add(a: u32, b: u32) -> u32 {\n    a + b\n}\n";
    std::fs::write(&file, original).unwrap();

    let rewrite = SourceRewrite {
        file_path: file.display().to_string(),
        offset: original.find('{').unwrap(),
        kind: trust_backprop::RewriteKind::InsertContractClause {
            clause: trust_backprop::ContractClauseKind::Requires,
            expression: "a <= u32::MAX - b".into(),
        },
        function_name: "add".into(),
        rationale: "prevent overflow".into(),
        expected_source_hash: Some(trust_types::digest::stable_sha256_hex(original.as_bytes())),
        provenance: trust_backprop::ClaimProvenance::Authoritative,
    };
    let modified =
        "fn add(a: u32, b: u32) -> u32 \n    requires a <= u32::MAX - b\n{\n    a + b\n}\n"
            .to_string();
    let file_results = vec![FileRewriteResult {
        path: file.display().to_string(),
        original: original.into(),
        modified,
        rewrite_count: 1,
    }];

    let records = build_rewrite_records(&[rewrite], &[], &file_results);
    assert_eq!(records.len(), 1);
    assert_eq!(records[0].status, "applied");
    let rendered = format_unified(records[0].diff.as_ref().expect("diff should exist"));
    assert!(rendered.contains("+    requires a <= u32::MAX - b"));

    std::fs::remove_file(&file).ok();
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn test_append_audit_entries_captures_native_clause_diff_and_review() {
    let original = "fn add(a: u32, b: u32) -> u32 {\n    a + b\n}\n";
    let diff = generate_diff(
        original,
        "fn add(a: u32, b: u32) -> u32 \n    requires a <= u32::MAX - b\n{\n    a + b\n}\n",
        "src/lib.rs",
    );
    let record = RepairRewriteRecord {
        status: "applied".into(),
        policy: Some("review".into()),
        reviewer_notes: None,
        rewrite: SourceRewrite {
            file_path: "src/lib.rs".into(),
            offset: original.find('{').unwrap(),
            kind: trust_backprop::RewriteKind::InsertContractClause {
                clause: trust_backprop::ContractClauseKind::Requires,
                expression: "a <= u32::MAX - b".into(),
            },
            function_name: "add".into(),
            rationale: "prevent overflow".into(),
            expected_source_hash: Some(trust_types::digest::stable_sha256_hex(original.as_bytes())),
            provenance: trust_backprop::ClaimProvenance::Authoritative,
        },
        diff: Some(diff),
        preview_error: None,
    };

    let mut trail = AuditTrail::new();
    append_audit_entries(&mut trail, 1, &[record]);

    assert_eq!(trail.entries().len(), 1);
    assert_eq!(trail.entries()[0].approval_status, ApprovalStatus::Reviewed);
    assert!(
        trail.entries()[0]
            .before_after_diff
            .as_deref()
            .unwrap_or_default()
            .contains("requires a <= u32::MAX - b")
    );
}

// --- Loop safety: what happens to source between an apply and its verdict ---

use super::safety::{RewriteRejection, UnverifiedRewrites, rewrite_rejection};

/// The fixture the program-index benchmark uses for the div-zero obligation.
const DIV_ZERO_SOURCE: &str = "\
fn divide_unchecked(x: u32, y: u32) -> u32 {
    x / y
}

fn main() {
    let _ = divide_unchecked(10, 2);
}
";

#[test]
fn broken_build_is_rejected_even_though_its_frontier_reads_as_progress() {
    // Source that no longer compiles reports no obligations at all, and a
    // frontier with nothing failing in it is what "improved" looks like to any
    // comparison. This test is the reason the build check exists.
    let looks_like_progress = LoopDecision::Continue { verdict: "improved" };
    assert_eq!(
        rewrite_rejection(1, 0, &looks_like_progress),
        Some(RewriteRejection::BrokenBuild),
    );
    assert_eq!(
        rewrite_rejection(1, 0, &LoopDecision::Converged { stable_rounds: 2 }),
        Some(RewriteRejection::BrokenBuild),
    );
}

#[test]
fn failing_obligations_are_not_a_broken_build() {
    // The compiler exits non-zero on every unproved obligation, which is the
    // ordinary state the loop exists to improve.
    let decision = LoopDecision::Continue { verdict: "improved" };
    assert_eq!(rewrite_rejection(1, 4, &decision), None);
}

#[test]
fn a_crate_with_nothing_to_prove_is_not_a_broken_build() {
    let decision = LoopDecision::Continue { verdict: "stable (no change)" };
    assert_eq!(rewrite_rejection(0, 0, &decision), None);
}

#[test]
fn a_regressed_frontier_rejects_the_generation_that_produced_it() {
    let decision = LoopDecision::Regressed { reason: "more failures than previous iteration" };
    assert_eq!(
        rewrite_rejection(1, 4, &decision),
        Some(RewriteRejection::RegressedFrontier("more failures than previous iteration")),
    );
}

#[test]
fn applied_rewrites_carry_a_checkpoint_that_restores_the_users_source() {
    let dir = tempfile::tempdir().expect("temp dir");
    let file = dir.path().join("div_zero.rs");
    std::fs::write(&file, DIV_ZERO_SOURCE).expect("write fixture");
    let path = file.canonicalize().expect("canonicalize fixture").display().to_string();

    let mut engine = BackpropEngine::new();
    let mut result = engine.apply_strengthen_proposals(
        &[Proposal {
            function_path: path.clone(),
            function_name: "divide_unchecked".into(),
            kind: ProposalKind::AddNonZeroCheck {
                check_expr: "assert!(y != 0, \"division by zero\")".into(),
            },
            confidence: 0.8,
            rationale: "Add runtime non-zero check before division".into(),
        }],
        0,
        0,
    );

    assert_eq!(result.rewrites_applied, 1, "the runtime check is auto-applied");
    let applied = std::fs::read_to_string(&path).expect("read rewritten fixture");
    assert_ne!(applied, DIV_ZERO_SOURCE, "the engine must have edited the file");

    let checkpoint = result.pre_apply_checkpoint.take().expect("an apply must leave an undo path");
    let pending = UnverifiedRewrites::new(1, checkpoint, result.rewrites_applied)
        .expect("a non-empty checkpoint is a pending generation");
    assert_eq!(pending.file_count(), 1);
    assert_eq!(pending.restore().expect("restore"), 1);

    let restored = std::fs::read_to_string(&path).expect("read restored fixture");
    assert_eq!(restored, DIV_ZERO_SOURCE, "an undone generation leaves the user's source exactly");
}

#[test]
fn an_iteration_that_wrote_nothing_leaves_nothing_to_undo() {
    let mut engine = BackpropEngine::new();
    let result = engine.apply_strengthen_proposals(&[], 0, 0);
    assert!(result.pre_apply_checkpoint.is_none());
}
