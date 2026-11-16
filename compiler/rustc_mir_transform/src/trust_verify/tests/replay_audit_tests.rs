use super::*;

struct Scratch(PathBuf);

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

type Audit = trust_certify::proof_artifacts::ReplayAudit;
type Results = Vec<(VerificationCondition, VerificationResult)>;

fn replay_fixture(
    label: &str,
) -> (Scratch, Results, Vec<Option<trust_ir::ProofEvidence>>, Vec<Option<Audit>>) {
    let root = Scratch(private_proof_store_test_root(label));
    let store = trust_certify::proof_artifacts::ProofArtifactStore::open(&root.0).unwrap();
    let first = bridge_replay_test_vc();
    assert!(trust_certify::proof_artifacts::certify_vc_with_artifacts(&first, &root.0).is_some());
    assert_eq!(store.publish_session(&root.0).unwrap(), 1);
    store.prepare_session(&root.0).unwrap();
    let mut second = first.clone();
    second.location.line_start += 1;
    second.location.line_end += 1;
    let results = vec![(first, authority_test_proved()), (second, authority_test_proved())];
    let (evidence, audits, cut) =
        certify_all_until_with_artifacts_and_replay_audits(&results, None, Some(&root.0));
    assert_eq!(cut, None);
    for ((vc, _), (proof, audit)) in results.iter().zip(evidence.iter().zip(&audits)) {
        assert!(
            audit.as_ref().expect("actual replay observation").matches(vc, proof.as_ref().unwrap())
        );
    }
    (root, results, evidence, audits)
}

fn authorities(
    results: &Results,
    evidence: &[Option<trust_ir::ProofEvidence>],
    audits: &[Option<Audit>],
) -> Vec<Option<ResultProofAuthority>> {
    build_result_proof_authorities_with_revalidations_and_replay_audits(
        results,
        &[],
        None,
        evidence,
        &[],
        audits,
    )
}

fn rows(
    results: &Results,
    evidence: &[Option<trust_ir::ProofEvidence>],
    authorities: &[Option<ResultProofAuthority>],
) -> Vec<TransportObligationResult> {
    build_transport_results_with_runtime_checks_bound(
        false,
        Some("aarch64-apple-darwin"),
        results,
        None,
        evidence,
        &[],
        authorities,
    )
}

fn audit_count(row: &TransportObligationResult) -> usize {
    row.proof_evidence
        .iter()
        .flat_map(|proof| &proof.diagnostics)
        .filter(|diagnostic| diagnostic.code == replay_audit::CODE)
        .count()
}

#[test]
fn kernel_replay_audit_follows_the_selected_exact_proof_into_public_rows() {
    let (_root, results, evidence, audits) = replay_fixture("replay-audit-public");
    let authorities = authorities(&results, &evidence, &audits);
    let mut published = rows(&results, &evidence, &authorities);
    replay_audit::retain_published(&mut published);
    for (index, row) in published.iter().enumerate() {
        assert_eq!(row.outcome, Outcome::Proved);
        assert_eq!(audit_count(row), 1);
        let diagnostic = row
            .proof_evidence
            .as_ref()
            .unwrap()
            .diagnostics
            .iter()
            .find(|diagnostic| diagnostic.code == replay_audit::CODE)
            .unwrap();
        let detail: serde_json::Value =
            serde_json::from_str(diagnostic.detail.as_ref().unwrap()).unwrap();
        assert_eq!(detail["subject"], results[index].0.function.as_str());
        assert_eq!(detail["obligation_id"], row.obligation_id.as_deref().unwrap());
        assert_eq!(detail["claim_digest_sha256"], row.claim_digest_sha256.as_deref().unwrap());
        assert_eq!(
            detail["replay"],
            serde_json::to_value(audits[index].as_ref().unwrap()).unwrap()
        );
    }
    assert_ne!(audits[0].as_ref().unwrap(), audits[1].as_ref().unwrap());
}

#[test]
fn kernel_replay_audit_skew_or_swap_erases_only_the_observation() {
    let (_root, results, evidence, audits) = replay_fixture("replay-audit-carrier");
    let carriers = [
        vec![],
        audits[..1].to_vec(),
        vec![audits[1].clone(), audits[0].clone()],
        vec![audits[0].clone(), audits[1].clone(), None],
    ];
    for carrier in carriers {
        let authorities = authorities(&results, &evidence, &carrier);
        assert!(authorities.iter().all(|authority| matches!(
            authority,
            Some(ResultProofAuthority::KernelCertified { replay_audit: None, .. })
        )));
        let published = rows(&results, &evidence, &authorities);
        assert!(
            published.iter().all(|row| row.outcome == Outcome::Proved && audit_count(row) == 0)
        );
    }
    let ordinary = build_result_proof_authorities(&results, &[], None, &evidence);
    assert!(rows(&results, &evidence, &ordinary).iter().all(|row| audit_count(row) == 0));
}

#[test]
fn kernel_replay_audit_respects_sweep_deadline_and_nonproved_selection() {
    let (root, mut results, _, _) = replay_fixture("replay-audit-deadline");
    let expired = std::time::Instant::now() - std::time::Duration::from_secs(1);
    let (evidence, audits, cut) =
        certify_all_until_with_artifacts_and_replay_audits(&results, Some(expired), Some(&root.0));
    assert_eq!(cut, Some(0));
    assert!(evidence.iter().all(Option::is_none));
    assert!(audits.iter().all(Option::is_none));
    results[0].1 = bridge_test_unknown();
    let (evidence, audits, cut) =
        certify_all_until_with_artifacts_and_replay_audits(&results, None, Some(&root.0));
    assert_eq!(cut, None);
    assert!(evidence[0].is_none() && audits[0].is_none());
    assert!(evidence[1].is_some() && audits[1].is_some());
}

#[test]
fn kernel_replay_audit_does_not_publish_an_unsupported_semantic_row() {
    let (root, mut results, _, _) = replay_fixture("replay-audit-unsupported");
    results[0].0.kind = VcKind::UnsupportedMir {
        kind: "OpaqueSemanticGap".to_string(),
        detail: "body lowering is unsupported".to_string(),
    };
    let (evidence, audits, cut) =
        certify_all_until_with_artifacts_and_replay_audits(&results, None, Some(&root.0));
    assert_eq!(cut, None);
    assert!(audits[0].is_some(), "mathematics may replay without proving the unsupported program");
    let authority = authorities(&results, &evidence, &audits);
    assert!(matches!(authority[0], Some(ResultProofAuthority::KernelCertified { .. })));
    let published = rows(&results, &evidence, &authority);
    assert_eq!(published[0].outcome, Outcome::Unknown);
    assert_eq!(audit_count(&published[0]), 0);
    assert_eq!(audit_count(&published[1]), 1);
}

#[test]
fn kernel_replay_audit_is_not_copied_through_premise_demotion_or_foreign_row() {
    let (_root, results, evidence, audits) = replay_fixture("replay-audit-authority");
    let mut authority = authorities(&results, &evidence, &audits);
    let premise_free = argument_premise::PremiseFreeRows::unavailable();
    assert_eq!(
        demote_argument_premise_authorities(
            &mut authority,
            argument_premise::NOALIAS_MUT_ARGS,
            &premise_free,
            &[]
        ),
        (0, 2)
    );
    assert!(rows(&results, &evidence, &authority).iter().all(|row| audit_count(row) == 0));
    let authority = authorities(&results, &evidence, &audits);
    let swapped = vec![authority[1].clone(), authority[0].clone()];
    assert!(rows(&results, &evidence, &swapped).iter().all(|row| audit_count(row) == 0));
}

#[test]
fn kernel_replay_audit_is_erased_by_final_row_and_evidence_rewrites() {
    let (_root, results, evidence, audits) = replay_fixture("replay-audit-withdrawal");
    let authority = authorities(&results, &evidence, &audits);
    let original = rows(&results, &evidence, &authority).remove(0);
    assert_eq!(audit_count(&original), 1);
    let mut changed = Vec::new();
    for outcome in [
        Outcome::Unknown,
        Outcome::Timeout,
        Outcome::Failed,
        Outcome::Skipped,
        Outcome::RuntimeChecked,
    ] {
        let mut row = original.clone();
        row.outcome = outcome;
        changed.push(row);
    }
    let mut row = original.clone();
    row.grade = None;
    changed.push(row);
    let mut row = original.clone();
    row.grade.as_mut().unwrap().discharge =
        trust_types::authority_grade::GradeDischarge::SolverAsserted;
    changed.push(row);
    let mut row = original.clone();
    row.proof_evidence.as_mut().unwrap().artifacts[0].metadata = None;
    changed.push(row);
    let mut row = original.clone();
    row.proof_evidence.as_mut().unwrap().backend = "foreign".into();
    changed.push(row);
    let mut row = original.clone();
    row.proof_evidence.as_mut().unwrap().diagnostics.push(transport_diagnostic(
        "proof_materialization_transport_limit",
        TransportEvidenceDiagnosticSeverity::Error,
        "withheld",
    ));
    changed.push(row);
    let mut row = original.clone();
    row.obligation_id = Some("foreign-row".into());
    changed.push(row);
    let mut row = original.clone();
    row.claim_digest_sha256 = Some("0".repeat(64));
    changed.push(row);
    let mut row = original.clone();
    let proof = row.proof_evidence.as_mut().unwrap();
    proof.diagnostics.push(proof.diagnostics[0].clone());
    changed.push(row);
    replay_audit::retain_published(&mut changed);
    assert!(changed.iter().all(|row| audit_count(row) == 0));
    // Submitted observation-shaped diagnostics never mint a private receipt.
    let mut copied = original.clone();
    replay_audit::attach(&mut copied, 0, &results[0].0, None, None);
    assert_eq!(audit_count(&copied), 0);
    assert_eq!(copied.outcome, original.outcome);
}

fn envelope(rows: Vec<TransportObligationResult>) -> FunctionTransportResult {
    let mut result: FunctionTransportResult = serde_json::from_value(serde_json::json!({
        "function":"bridge-test", "results":[], "proved":0, "failed":0, "unknown":0, "runtime_checked":0, "total":0,
    })).unwrap();
    result.results = rows;
    recount(&mut result);
    result
}

fn recount(result: &mut FunctionTransportResult) {
    let counts = PublishedRowTally::of(&result.results, None).json_counts();
    result.proved = counts.proved;
    result.failed = counts.failed;
    result.unknown = counts.unknown;
    result.timed_out = counts.timed_out;
    result.skipped = counts.skipped;
    result.runtime_checked = counts.runtime_checked;
    result.total = counts.total;
}

#[test]
fn kernel_replay_audit_is_absent_from_actual_budget_withheld_serialized_bytes() {
    use trust_types::transport_budget::{TransportBudgetStep, TransportLineFraming};
    let (_root, results, evidence, audits) = replay_fixture("replay-audit-budget");
    let authority = authorities(&results, &evidence, &audits);
    let mut row = rows(&results, &evidence, &authority).remove(0);
    // Isolate the proof-withholding step; the sidecar is optional diagnostic
    // data and withholding it must not itself claim a lost proof.
    row.original_vc_snapshot = None;
    let mut result = envelope(vec![row]);
    let mut stripped = result.clone();
    assert!(trust_types::transport_budget::strip_row_for_step(
        &mut stripped.results[0],
        TransportBudgetStep::WithheldProofEvidence,
        16384
    ));
    recount(&mut stripped);
    replay_audit::retain_published(&mut stripped.results);
    let stripped_bytes =
        serde_json::to_vec(&trust_types::TransportMessage::FunctionResult(stripped)).unwrap().len();
    let budget = stripped_bytes as u64 + 1200;
    let full_bytes =
        serde_json::to_vec(&trust_types::TransportMessage::FunctionResult(result.clone()))
            .unwrap()
            .len();
    assert!(full_bytes as u64 > budget, "fixture must actually exceed the selected line budget");
    let fitted = replay_audit::fit_function_result(
        &mut result,
        budget,
        TransportLineFraming::RawStderr,
        None,
        &mut recount,
    )
    .unwrap();
    assert_eq!(
        result.transport_budget.as_ref().unwrap().step,
        TransportBudgetStep::WithheldProofEvidence
    );
    assert_eq!(result.results[0].outcome, Outcome::Unknown);
    assert_eq!(audit_count(&result.results[0]), 0);
    assert!(
        !fitted.payload.contains(replay_audit::CODE),
        "returned bytes are the actual emission product"
    );
    assert!(fitted.line_bytes <= budget);
}
