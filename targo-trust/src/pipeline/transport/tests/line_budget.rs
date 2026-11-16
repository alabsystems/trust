//! Trust (TRANSPORT-LINE-BUDGET-1): targo-trust's reading of a function report the
//! compiler fitted under the transport line budget
//! (`trust_types::transport_budget`).
//!
//! * A disclosure that agrees with its rows is read like any report: its rows are
//!   admitted, and the rows the compiler demoted read as what they now say.
//! * A disclosure that disagrees with its rows makes the report malformed: no row of
//!   it is admitted, and the function is one genuine unknown that says why.
//! * Over every row shape the gate distinguishes, withholding a row's payloads the way
//!   the compiler does never moves it to a better gate bucket, read through the REAL
//!   `transport_to_verification_result`, `normalize_authenticated_results_for_publication`
//!   and `partition_outcome_counts`.

use trust_types::transport_budget::{
    TRANSPORT_LINE_BUDGET_BYTES, TransportBudgetDisclosure, TransportBudgetStep,
    TransportLineFraming, TransportWithheldEvidence, TransportWithheldField, fit_function_result,
    strip_row_for_step,
};
use trust_types::{
    Outcome, TransportEvidenceArtifact, TransportObligationResult, TransportProofEvidence,
    TransportProofStatus,
};

use super::*;
use crate::pipeline::hardened::partition_outcome_counts;
use crate::types::transport_to_verification_result;

fn row(kind: &str, solver: &str, outcome: Outcome) -> TransportObligationResult {
    serde_json::from_value(serde_json::json!({
        "kind": kind,
        "description": format!("the {kind} obligation"),
        "outcome": outcome.as_str(),
        "solver": solver,
        "time_ms": 1,
    }))
    .expect("row fixture")
}

fn proof(status: TransportProofStatus, bytes: usize) -> TransportProofEvidence {
    TransportProofEvidence {
        suite: "trust-full-verifier".into(),
        backend: "clean".into(),
        request_id: None,
        proof_id: Some("proof:1".into()),
        native_id: None,
        status,
        strength: None,
        evidence: None,
        artifacts: vec![TransportEvidenceArtifact {
            kind: "certificate".into(),
            format: Some("clean-cic".into()),
            artifact_id: None,
            digest: None,
            uri: None,
            materialization: None,
            metadata: Some(serde_json::Value::Array(
                (0..bytes / 4).map(|i| serde_json::Value::from(100 + (i % 150))).collect(),
            )),
        }],
        diagnostics: Vec::new(),
    }
}

fn snapshot() -> Box<trust_types::OriginalVcSnapshot> {
    Box::new(trust_types::OriginalVcSnapshot {
        schema: "trust-original-vc/v1".into(),
        obligation_id: "vc:budget::big:assert:0".into(),
        claim_digest_sha256: "0".repeat(64),
        typed_input_digest_sha256: None,
        expanded_function_identity: None,
        overflow_checks: true,
        target: "aarch64-apple-darwin".into(),
        payload_sha256: "1".repeat(64),
        original_vc_json: "{}".into(),
    })
}

/// The counts as trustc states them for these rows (no instance-discharge or
/// entry-assumption kinds among them).
fn restate(result: &mut trust_types::FunctionTransportResult) {
    let mut counts = [0usize; 6]; // proved failed unknown timed_out skipped runtime_checked
    for row in &result.results {
        match row.outcome {
            Outcome::Proved => counts[0] += 1,
            Outcome::Failed => counts[1] += 1,
            Outcome::RuntimeChecked => counts[5] += 1,
            Outcome::Timeout => {
                counts[3] += 1;
                counts[2] += 1;
            }
            Outcome::Skipped => {
                counts[4] += 1;
                counts[2] += 1;
            }
            _ => counts[2] += 1,
        }
    }
    [
        result.proved,
        result.failed,
        result.unknown,
        result.timed_out,
        result.skipped,
        result.runtime_checked,
    ] = counts;
    result.total = result.results.len();
}

fn envelope(rows: Vec<TransportObligationResult>) -> trust_types::FunctionTransportResult {
    let mut result: trust_types::FunctionTransportResult =
        serde_json::from_value(serde_json::json!({
            "function": "budget::big",
            "crate_name": "budget",
            "results": [],
            "proved": 0, "failed": 0, "unknown": 0, "runtime_checked": 0, "total": 0,
        }))
        .expect("envelope fixture");
    result.results = rows;
    restate(&mut result);
    result
}

/// A three-row report fitted under 20 000 bytes by step 2: row 0 proved with large
/// evidence (demoted), rows 1 and 2 small and proved.
fn fitted_report() -> trust_types::FunctionTransportResult {
    let mut big = row("divzero", "trust-full-verifier", Outcome::Proved);
    big.proof_evidence = Some(proof(TransportProofStatus::Proved, 40_000));
    let mut result = envelope(vec![
        big,
        row("overflow:add", "ay", Outcome::Proved),
        row("overflow:sub", "ay", Outcome::Proved),
    ]);
    fit_function_result(&mut result, 20_000, TransportLineFraming::RawStderr, None, &mut restate)
        .expect("fit");
    assert_eq!(
        result.transport_budget.as_ref().map(|d| d.step),
        Some(TransportBudgetStep::WithheldProofEvidence)
    );
    result
}

fn parse(result: &trust_types::FunctionTransportResult) -> ParsedCompilerOutput {
    let line = format!(
        "{}{}",
        trust_types::TRANSPORT_PREFIX,
        serde_json::to_string(&trust_types::TransportMessage::FunctionResult(result.clone()))
            .unwrap()
    );
    parse_compiler_stderr(Cursor::new(line), false)
}

#[test]
fn an_agreeing_disclosure_is_read_like_any_report() {
    let result = fitted_report();
    let parsed = parse(&result);
    let rows: Vec<_> =
        parsed.verification_results.iter().filter(|r| r.function == "budget::big").collect();
    assert_eq!(rows.len(), 3, "every row admitted: {rows:#?}");
    assert_eq!(rows[0].outcome, VerificationOutcome::Unknown, "the demoted row stays demoted");
    assert!(
        rows[0].reason.as_deref().is_some_and(|r| r.contains("transport line budget:")),
        "{:?}",
        rows[0].reason
    );
    // The disclosure adds no credit and takes none: every row reads exactly as the same
    // report's row reads without it (outcome, reason, structured evidence).
    let mut undisclosed = result.clone();
    undisclosed.transport_budget = None;
    let reading = |parsed: &ParsedCompilerOutput| -> Vec<serde_json::Value> {
        parsed
            .verification_results
            .iter()
            .filter(|r| r.function == "budget::big")
            .map(|r| serde_json::to_value(r).unwrap())
            .collect()
    };
    assert_eq!(reading(&parsed), reading(&parse(&undisclosed)));
    assert!(
        parsed.verification_results.iter().all(|r| r.kind != "transport:line-budget-disclosure"
            && r.kind != "transport:summary-accounting"),
        "no defect: {:#?}",
        parsed.verification_results
    );
}

#[test]
fn a_disagreeing_disclosure_admits_no_row_of_its_report() {
    // The forgeries a consumer must catch: a row that kept `proved` without its
    // evidence, and a disclosure listing a row past the report.
    let mut relabelled = fitted_report();
    relabelled.results[0].outcome = Outcome::Proved;
    restate(&mut relabelled);
    let mut out_of_range = fitted_report();
    out_of_range.transport_budget.as_mut().unwrap().withheld = vec![TransportWithheldEvidence {
        field: TransportWithheldField::ProofEvidencePayloads,
        rows: vec![0, 9],
    }];
    let mut forged_budget = fitted_report();
    forged_budget.transport_budget.as_mut().unwrap().line_budget_bytes =
        TRANSPORT_LINE_BUDGET_BYTES * 2;
    for forged in [relabelled, out_of_range, forged_budget] {
        let parsed = parse(&forged);
        let rows: Vec<_> =
            parsed.verification_results.iter().filter(|r| r.function == "budget::big").collect();
        assert_eq!(rows.len(), 1, "{rows:#?}");
        assert_eq!(rows[0].kind, "transport:line-budget-disclosure");
        assert_eq!(rows[0].outcome, VerificationOutcome::Unknown);
        assert!(
            rows[0].reason.as_deref().is_some_and(|r| r.contains("transport budget disclosure"))
        );
    }
}

/// The rank `partition_outcome_counts` gives one row, best last.
fn partition_rank(result: &VerificationResult) -> (u8, String) {
    let (counts, _) = partition_outcome_counts(std::slice::from_ref(result));
    let rank = if counts.failed == 1 {
        0
    } else if counts.unknown == 1 || counts.mandated == 1 {
        1
    } else if counts.assumed == 1 || counts.contract_panics == 1 || counts.excluded == 1 {
        2
    } else if counts.runtime_checked == 1 {
        3
    } else {
        assert_eq!(counts.proved, 1, "{counts:?}");
        4
    };
    (rank, format!("{counts:?} as {:?}", result.outcome))
}

/// The gate bucket a single row lands in, best last, read two ways: by the raw gate
/// partition, and after the publication normalization that runs before it in the
/// authenticated lane (which ELIDES exact inventory and exclusion rows: rank 5, the
/// row is no longer counted at all).
fn bucket(row: &TransportObligationResult) -> ((u8, String), (u8, String)) {
    let result = transport_to_verification_result("budget::big", row, None, None);
    let raw = partition_rank(&result);
    let mut published = vec![result];
    let _ = crate::types::normalize_authenticated_results_for_publication(&mut published, None);
    let normalized = match published.first() {
        None => (5, "elided by publication normalization".to_string()),
        Some(result) => partition_rank(result),
    };
    (raw, normalized)
}

#[test]
fn withholding_evidence_never_moves_a_row_to_a_better_gate_bucket() {
    use trust_types::assumption::{
        COROUTINE_RESUME_CONTRACT_ROW_KIND, COROUTINE_RESUME_CONTRACT_ROW_REASON,
        COROUTINE_RESUME_CONTRACT_ROW_SOLVER, GLOBAL_ALLOC_DEALLOC_CONTRACT_DISCHARGED_REASON,
        GLOBAL_ALLOC_DEALLOC_CONTRACT_ROW_KIND, GLOBAL_ALLOC_DEALLOC_CONTRACT_ROW_SOLVER,
        INSTANCE_HYPOTHESIS_DISCHARGE_ROW_KIND,
    };
    let shapes: Vec<(&str, &str, Option<&str>)> = vec![
        ("divzero", "trust-full-verifier", None),
        ("overflow:add", "ay", None),
        ("assumption:memory-safe-panic", "trust-full-verifier", None),
        (
            COROUTINE_RESUME_CONTRACT_ROW_KIND,
            COROUTINE_RESUME_CONTRACT_ROW_SOLVER,
            Some(COROUTINE_RESUME_CONTRACT_ROW_REASON),
        ),
        (
            GLOBAL_ALLOC_DEALLOC_CONTRACT_ROW_KIND,
            GLOBAL_ALLOC_DEALLOC_CONTRACT_ROW_SOLVER,
            Some(GLOBAL_ALLOC_DEALLOC_CONTRACT_DISCHARGED_REASON),
        ),
        (trust_types::assumption::CONTRACT_PANIC_MATCHED_ROW_KIND, "trust-full-verifier", None),
        (INSTANCE_HYPOTHESIS_DISCHARGE_ROW_KIND, "trust-full-verifier", None),
        // The envelope-shape kinds: never stripped (`strip_row_for_step` says no).
        (
            trust_types::transport_budget::ZERO_OBLIGATION_INVENTORY_ROW_KIND,
            "trust-structural",
            Some("verified: zero panic obligations"),
        ),
        (
            trust_types::exclusion::TEST_HARNESS_ROW_KIND,
            trust_types::exclusion::TEST_HARNESS_ROW_SOLVER,
            None,
        ),
    ];
    let outcomes = [
        Outcome::Proved,
        Outcome::Failed,
        Outcome::Unknown,
        Outcome::Timeout,
        Outcome::RuntimeChecked,
        Outcome::Skipped,
        Outcome::Unsupported,
    ];
    let statuses = [
        TransportProofStatus::Proved,
        TransportProofStatus::Failed,
        TransportProofStatus::Unknown,
        TransportProofStatus::Timeout,
        TransportProofStatus::Unsupported,
        TransportProofStatus::Rejected,
    ];
    let mut stripped_any = 0;
    for (kind, solver, reason) in &shapes {
        for outcome in outcomes {
            for status in statuses {
                let mut original = row(kind, solver, outcome);
                original.reason = reason.map(str::to_string);
                if *kind == COROUTINE_RESUME_CONTRACT_ROW_KIND {
                    original.description =
                        trust_types::assumption::coroutine_resume_contract_row_description(&[0, 3]);
                }
                original.proof_evidence = Some(proof(status, 64));
                original.original_vc_snapshot = Some(snapshot());
                let before = bucket(&original);
                for step in [
                    TransportBudgetStep::WithheldDiagnosticPayloads,
                    TransportBudgetStep::WithheldProofEvidence,
                ] {
                    let mut stripped = original.clone();
                    if step == TransportBudgetStep::WithheldProofEvidence {
                        strip_row_for_step(
                            &mut stripped,
                            TransportBudgetStep::WithheldDiagnosticPayloads,
                            TRANSPORT_LINE_BUDGET_BYTES,
                        );
                    }
                    if !strip_row_for_step(&mut stripped, step, TRANSPORT_LINE_BUDGET_BYTES) {
                        assert!(
                            trust_types::transport_budget::is_envelope_shape_row(&original)
                                || step == TransportBudgetStep::WithheldProofEvidence,
                            "`{kind}` {outcome:?}: step 1 strips every ordinary row"
                        );
                        continue;
                    }
                    stripped_any += 1;
                    assert!(stripped.original_vc_snapshot.is_none());
                    if step == TransportBudgetStep::WithheldProofEvidence {
                        // Steps are cumulative: step 2 runs on a row step 1 may have cut.
                        // The record stays (status, suite, diagnostics); its payloads go.
                        let record = stripped.proof_evidence.as_ref().expect("record kept");
                        assert_eq!(record.status, status);
                        assert!(
                            record
                                .artifacts
                                .iter()
                                .all(|a| a.metadata.is_none() && a.materialization.is_none())
                        );
                    }
                    let after = bucket(&stripped);
                    for (which, (b, b_label), (a, a_label)) in
                        [("raw gate", &before.0, &after.0), ("published gate", &before.1, &after.1)]
                    {
                        assert!(
                            a <= b,
                            "`{kind}` {outcome:?} with {status:?} evidence, {step:?}, {which}: \
                             read {b_label} with its payloads and {a_label} without"
                        );
                    }
                }
            }
        }
    }
    assert!(stripped_any > 100, "the sweep strips rows: {stripped_any}");
}

#[test]
fn a_disclosure_survives_the_authenticated_reserialization() {
    // The Cargo lane re-serializes each authenticated message before parsing it; the
    // disclosure must survive that, or a consumer would read shorter evidence unmarked.
    let result = fitted_report();
    let json =
        serde_json::to_string(&trust_types::TransportMessage::FunctionResult(result.clone()))
            .unwrap();
    let reparsed = trust_types::parse_transport_payload(&json).unwrap();
    let trust_types::TransportMessage::FunctionResult(reparsed) = reparsed else {
        panic!("not a function result")
    };
    let disclosure: &TransportBudgetDisclosure = reparsed.transport_budget.as_ref().unwrap();
    assert_eq!(Some(disclosure), result.transport_budget.as_ref());
    assert_eq!(disclosure.defect(&reparsed.results), None);
}

#[test]
fn the_envelope_shape_guard_closes_a_real_elision() {
    // Positive control for the guard in `strip_row_for_step`: a zero-obligation
    // inventory LOOKALIKE that carries a snapshot is not elided (it stays and fails
    // closed); the same row with the snapshot cut WOULD be elided. So the ladder must
    // never cut it, and does not.
    let mut lookalike = row(
        trust_types::transport_budget::ZERO_OBLIGATION_INVENTORY_ROW_KIND,
        "trust-structural",
        Outcome::Proved,
    );
    lookalike.description = "function has no panic obligations (trivially panic-free)".into();
    lookalike.reason = Some("verified: zero panic obligations".into());
    lookalike.time_ms = 0;
    let exact = bucket(&lookalike).1;
    assert_eq!(exact.0, 5, "control: the exact row is elided ({})", exact.1);
    lookalike.original_vc_snapshot = Some(snapshot());
    let kept = bucket(&lookalike).1;
    assert!(kept.0 < 5, "a lookalike is not elided ({})", kept.1);
    let mut cut = lookalike.clone();
    cut.original_vc_snapshot = None;
    assert_eq!(bucket(&cut).1.0, 5, "cutting the snapshot would complete the shape");
    let mut guarded = lookalike.clone();
    assert!(!strip_row_for_step(
        &mut guarded,
        TransportBudgetStep::WithheldDiagnosticPayloads,
        TRANSPORT_LINE_BUDGET_BYTES
    ));
    assert!(guarded.original_vc_snapshot.is_some());
}
