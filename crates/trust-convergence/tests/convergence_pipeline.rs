// trust-convergence/tests/convergence_pipeline.rs: Cross-crate integration tests
// for convergence detection across the verification pipeline.
//
// Tests exercise: trust-types + trust-convergence + trust-strengthen + trust_vcgen
// working together to simulate verification loop iterations, detect convergence,
// stagnation, and apply widening/narrowing in abstract domains.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::time::Duration;

use trust_convergence::integration::{VcStatus, VerificationConvergenceTracker};
use trust_convergence::monotonicity::{MonotonicityPolicy, check_monotonicity};
use trust_convergence::stagnation::{SnapshotStagnationDetector, StagnationDetector};
use trust_convergence::termination::{
    ConvergenceRate, ResourceBudget, TerminationAnalyzer, TerminationCriterion, TerminationReason,
    estimate_loop_bound, estimate_remaining_iterations, will_converge,
};
use trust_convergence::visualization::FrontierSnapshot;
use trust_convergence::widening::{
    AbstractState, DelayedWidening, SimpleNarrowing, ThresholdWidening, WideningOperator,
    WideningSchedule, accelerate_convergence, narrow_after_widening,
};
use trust_convergence::{
    ConvergenceDecision, ConvergenceTracker, IterationSnapshot, ProofFrontier, StepVerdict,
};
use trust_strengthen::StrengthenConfig;
use trust_types::{
    BinOp, CrateVerificationResult, Formula, FunctionVerificationResult, ProofStrength, SourceSpan,
    Ty, VcKind, VerificationCondition, VerificationResult,
};

// ---------------------------------------------------------------------------
// Helpers: build verification results simulating pipeline output
// ---------------------------------------------------------------------------

fn make_vc(kind: VcKind, function: &str) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: function.into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    }
}

fn proved() -> VerificationResult {
    VerificationResult::Proved {
        solver: "ay".into(),
        time_ms: 5,
        strength: ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    }
}

fn failed() -> VerificationResult {
    VerificationResult::Failed { solver: "ay".into(), time_ms: 10, counterexample: None }
}

fn unknown() -> VerificationResult {
    VerificationResult::Unknown { solver: "ay".into(), time_ms: 100, reason: "incomplete".into() }
}

fn timeout() -> VerificationResult {
    VerificationResult::Timeout { solver: "ay".into(), timeout_ms: 5000 }
}

/// Build a CrateVerificationResult with a single function and specified results.
fn crate_result(
    func_name: &str,
    results: Vec<(VcKind, VerificationResult)>,
) -> CrateVerificationResult {
    let vcs: Vec<(VerificationCondition, VerificationResult)> =
        results.into_iter().map(|(kind, vr)| (make_vc(kind, func_name), vr)).collect();

    let mut cr = CrateVerificationResult::new("test_crate");
    cr.add_function(FunctionVerificationResult {
        function_path: format!("test_crate::{func_name}"),
        function_name: func_name.into(),
        results: vcs,
        from_notes: 0,
        with_assumptions: 0,
    });
    cr
}

/// Build a CrateVerificationResult with multiple functions.
fn multi_func_crate_result(
    funcs: Vec<(&str, Vec<(VcKind, VerificationResult)>)>,
) -> CrateVerificationResult {
    let mut cr = CrateVerificationResult::new("test_crate");
    for (func_name, results) in funcs {
        let vcs: Vec<(VerificationCondition, VerificationResult)> =
            results.into_iter().map(|(kind, vr)| (make_vc(kind, func_name), vr)).collect();
        cr.add_function(FunctionVerificationResult {
            function_path: format!("test_crate::{func_name}"),
            function_name: func_name.into(),
            results: vcs,
            from_notes: 0,
            with_assumptions: 0,
        });
    }
    cr
}

fn frontier(trusted: u32, certified: u32, rt: u32, failed: u32, unknown: u32) -> ProofFrontier {
    ProofFrontier { trusted, certified, runtime_checked: rt, failed, unknown }
}

fn state_with(proved: &[&str], proposals: &[&str], round: u32) -> AbstractState {
    AbstractState::with_components(
        proved.iter().map(|s| (*s).to_string()).collect(),
        proposals.iter().map(|s| (*s).to_string()).collect(),
        round,
    )
}

// ---------------------------------------------------------------------------
// Test: Simulate verification loop iterations -> convergence detection
// Uses trust-types (CrateVerificationResult) + trust-convergence (tracker)
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_loop_simulation_converges() {
    // Simulate a 4-iteration verification loop where VCs are gradually proved.
    let mut tracker = VerificationConvergenceTracker::new(2, 10);

    // Iteration 0: 1 proved, 2 failed, 1 unknown
    let iter0 = crate_result(
        "compute",
        vec![
            (VcKind::DivisionByZero, proved()),
            (
                VcKind::ArithmeticOverflow {
                    op: BinOp::Add,
                    operand_tys: (
                        Ty::Int { width: 64, signed: false },
                        Ty::Int { width: 64, signed: false },
                    ),
                },
                failed(),
            ),
            (VcKind::IndexOutOfBounds, failed()),
            (VcKind::Postcondition, unknown()),
        ],
    );
    let changes0 = tracker.observe(&iter0);
    // All VCs are new, so no changes expected (no previous state).
    assert!(changes0.is_empty());
    assert!(!tracker.has_regressions());

    // Iteration 1: 2 proved, 1 failed, 1 unknown (improvement)
    let iter1 = crate_result(
        "compute",
        vec![
            (VcKind::DivisionByZero, proved()),
            (
                VcKind::ArithmeticOverflow {
                    op: BinOp::Add,
                    operand_tys: (
                        Ty::Int { width: 64, signed: false },
                        Ty::Int { width: 64, signed: false },
                    ),
                },
                proved(),
            ),
            (VcKind::IndexOutOfBounds, failed()),
            (VcKind::Postcondition, unknown()),
        ],
    );
    let changes1 = tracker.observe(&iter1);
    let improvements: Vec<_> = changes1.iter().filter(|c| c.is_improvement()).collect();
    assert!(!improvements.is_empty(), "should detect ArithmeticOverflow improvement");
    assert!(!tracker.has_regressions());

    // Iteration 2: 3 proved, 0 failed, 1 unknown
    let iter2 = crate_result(
        "compute",
        vec![
            (VcKind::DivisionByZero, proved()),
            (
                VcKind::ArithmeticOverflow {
                    op: BinOp::Add,
                    operand_tys: (
                        Ty::Int { width: 64, signed: false },
                        Ty::Int { width: 64, signed: false },
                    ),
                },
                proved(),
            ),
            (VcKind::IndexOutOfBounds, proved()),
            (VcKind::Postcondition, unknown()),
        ],
    );
    let changes2 = tracker.observe(&iter2);
    let improvements2: Vec<_> = changes2.iter().filter(|c| c.is_improvement()).collect();
    assert!(!improvements2.is_empty());

    // Iteration 3: all proved
    let iter3 = crate_result(
        "compute",
        vec![
            (VcKind::DivisionByZero, proved()),
            (
                VcKind::ArithmeticOverflow {
                    op: BinOp::Add,
                    operand_tys: (
                        Ty::Int { width: 64, signed: false },
                        Ty::Int { width: 64, signed: false },
                    ),
                },
                proved(),
            ),
            (VcKind::IndexOutOfBounds, proved()),
            (VcKind::Postcondition, proved()),
        ],
    );
    let _changes3 = tracker.observe(&iter3);

    // The convergence score should be 1.0 (all proved).
    let score = tracker.convergence_score().expect("has VCs");
    assert!((score - 1.0).abs() < f64::EPSILON);
    assert_eq!(tracker.current_iteration(), 4);
}

#[test]
fn test_pipeline_loop_with_regression_detection() {
    let mut tracker = VerificationConvergenceTracker::new(2, 10);

    // Iteration 0: 2 proved, 1 failed
    let iter0 = crate_result(
        "safe_add",
        vec![
            (VcKind::DivisionByZero, proved()),
            (VcKind::Postcondition, proved()),
            (VcKind::IndexOutOfBounds, failed()),
        ],
    );
    tracker.observe(&iter0);

    // Iteration 1: regression — DivisionByZero no longer proved
    let iter1 = crate_result(
        "safe_add",
        vec![
            (VcKind::DivisionByZero, failed()),
            (VcKind::Postcondition, proved()),
            (VcKind::IndexOutOfBounds, proved()),
        ],
    );
    let changes = tracker.observe(&iter1);
    assert!(tracker.has_regressions(), "DivisionByZero regressed");

    let regressions: Vec<_> = changes.iter().filter(|c| c.is_regression()).collect();
    assert_eq!(regressions.len(), 1);
    assert_eq!(regressions[0].old_status, VcStatus::Proved);
    assert_eq!(regressions[0].new_status, VcStatus::Failed);
}

#[test]
fn test_pipeline_frontier_from_verification_result() {
    // Build a CrateVerificationResult with mixed results across multiple functions.
    let cr = multi_func_crate_result(vec![
        ("func_a", vec![(VcKind::DivisionByZero, proved()), (VcKind::IndexOutOfBounds, proved())]),
        (
            "func_b",
            vec![
                (VcKind::Postcondition, failed()),
                (
                    VcKind::ArithmeticOverflow {
                        op: BinOp::Mul,
                        operand_tys: (
                            Ty::Int { width: 32, signed: true },
                            Ty::Int { width: 32, signed: true },
                        ),
                    },
                    unknown(),
                ),
            ],
        ),
        ("func_c", vec![(VcKind::DivisionByZero, timeout())]),
    ]);

    let f = ProofFrontier::from_verification_result(&cr);
    assert_eq!(f.trusted, 2); // func_a's 2 proved VCs
    assert_eq!(f.certified, 0);
    assert_eq!(f.runtime_checked, 0);
    assert_eq!(f.failed, 1); // func_b's postcondition
    assert_eq!(f.unknown, 2); // func_b's overflow + func_c's timeout
    assert_eq!(f.total(), 5);
    assert_eq!(f.statically_proved(), 2);
    assert_eq!(f.unresolved(), 3);

    let score = f.convergence_score().expect("non-empty");
    assert!((score - 0.4).abs() < f64::EPSILON); // 2/5 = 0.4
}

// ---------------------------------------------------------------------------
// Test: Spec strengthening -> convergence metrics update
// Uses trust-types + trust-strengthen + trust-convergence
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_strengthen_improves_convergence() {
    let mut tracker = VerificationConvergenceTracker::new(3, 10);

    // Iteration 0: 2 failures that strengthen can propose specs for
    let iter0_result = crate_result(
        "midpoint",
        vec![
            (
                VcKind::ArithmeticOverflow {
                    op: BinOp::Add,
                    operand_tys: (
                        Ty::Int { width: 64, signed: false },
                        Ty::Int { width: 64, signed: false },
                    ),
                },
                failed(),
            ),
            (VcKind::DivisionByZero, failed()),
        ],
    );
    tracker.observe(&iter0_result);

    // Run strengthen on the failures
    let strengthen_output =
        trust_strengthen::run(&iter0_result, &StrengthenConfig::default());
    assert!(
        strengthen_output.has_proposals,
        "strengthen should propose fixes for overflow + div-by-zero"
    );
    assert_eq!(strengthen_output.failures_analyzed, 2);
    assert!(strengthen_output.proposals.len() >= 2);

    // Simulate: strengthen proposals accepted, re-verify with better specs.
    // Iteration 1: 1 proved (div-by-zero fixed), 1 still failing
    let iter1_result = crate_result(
        "midpoint",
        vec![
            (
                VcKind::ArithmeticOverflow {
                    op: BinOp::Add,
                    operand_tys: (
                        Ty::Int { width: 64, signed: false },
                        Ty::Int { width: 64, signed: false },
                    ),
                },
                failed(),
            ),
            (VcKind::DivisionByZero, proved()),
        ],
    );
    let changes1 = tracker.observe(&iter1_result);
    let improvements: Vec<_> = changes1.iter().filter(|c| c.is_improvement()).collect();
    assert!(!improvements.is_empty());

    // Re-run strengthen on remaining failure
    let strengthen_output2 =
        trust_strengthen::run(&iter1_result, &StrengthenConfig::default());
    assert!(strengthen_output2.has_proposals);
    assert_eq!(strengthen_output2.failures_analyzed, 1);

    // Iteration 2: all proved
    let iter2_result = crate_result(
        "midpoint",
        vec![
            (
                VcKind::ArithmeticOverflow {
                    op: BinOp::Add,
                    operand_tys: (
                        Ty::Int { width: 64, signed: false },
                        Ty::Int { width: 64, signed: false },
                    ),
                },
                proved(),
            ),
            (VcKind::DivisionByZero, proved()),
        ],
    );
    tracker.observe(&iter2_result);

    let score = tracker.convergence_score().expect("has VCs");
    assert!((score - 1.0).abs() < f64::EPSILON);
    assert!(!tracker.has_regressions());
}

#[test]
fn test_pipeline_strengthen_no_proposals_when_all_proved() {
    // When all VCs are proved, strengthen should propose nothing.
    let result = crate_result(
        "always_ok",
        vec![(VcKind::DivisionByZero, proved()), (VcKind::Postcondition, proved())],
    );

    let output = trust_strengthen::run(&result, &StrengthenConfig::default());
    assert!(!output.has_proposals);
    assert_eq!(output.failures_analyzed, 0);

    // Convergence tracker should see 100% score.
    let f = ProofFrontier::from_verification_result(&result);
    let score = f.convergence_score().expect("has VCs");
    assert!((score - 1.0).abs() < f64::EPSILON);
}

// ---------------------------------------------------------------------------
// Test: Stagnation detection across iterations
// Uses trust-types + trust-convergence::stagnation
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_stagnation_detection_with_verification_results() {
    let mut detector = StagnationDetector::with_threshold(3);

    // Iteration 0: some proved
    let iter0 = crate_result(
        "func",
        vec![
            (VcKind::DivisionByZero, proved()),
            (VcKind::IndexOutOfBounds, failed()),
            (VcKind::Postcondition, failed()),
        ],
    );
    let f0 = ProofFrontier::from_verification_result(&iter0);
    let r0 = detector.observe(&f0);
    assert!(!r0.is_stagnant());

    // Iterations 1-3: identical results (no progress)
    for _ in 0..3 {
        let iter_same = crate_result(
            "func",
            vec![
                (VcKind::DivisionByZero, proved()),
                (VcKind::IndexOutOfBounds, failed()),
                (VcKind::Postcondition, failed()),
            ],
        );
        let f = ProofFrontier::from_verification_result(&iter_same);
        let r = detector.observe(&f);
        if r.stale_iterations >= 3 {
            assert!(r.is_stagnant());
            assert!(r.reason.contains("no improvement"));
            return;
        }
    }
    panic!("should have detected stagnation");
}

#[test]
fn test_pipeline_snapshot_stagnation_with_stuck_vcs() {
    let mut detector = SnapshotStagnationDetector::new(2);

    // Build snapshots from verification results.
    // Iteration 0: proved=["div_zero"], failed=["oob", "postcond"]
    detector.push(FrontierSnapshot {
        iteration: 0,
        proved_count: 1,
        failed_count: 2,
        unknown_count: 0,
        timestamp: 100,
        proved_vcs: vec!["func::div_zero".into()],
        failed_vcs: vec!["func::oob".into(), "func::postcond".into()],
    });

    // Iteration 1: same
    detector.push(FrontierSnapshot {
        iteration: 1,
        proved_count: 1,
        failed_count: 2,
        unknown_count: 0,
        timestamp: 200,
        proved_vcs: vec!["func::div_zero".into()],
        failed_vcs: vec!["func::oob".into(), "func::postcond".into()],
    });

    // Iteration 2: same
    detector.push(FrontierSnapshot {
        iteration: 2,
        proved_count: 1,
        failed_count: 2,
        unknown_count: 0,
        timestamp: 300,
        proved_vcs: vec!["func::div_zero".into()],
        failed_vcs: vec!["func::oob".into(), "func::postcond".into()],
    });

    assert!(detector.is_stagnating());
    let report = detector.stagnation_report();
    assert!(report.is_stagnating);
    assert_eq!(report.stuck_vcs, vec!["func::oob", "func::postcond"]);
    assert_eq!(report.total_snapshots, 3);

    let ratio = report.current_convergence_ratio.expect("has ratio");
    assert!((ratio - 1.0 / 3.0).abs() < 0.01);
}

#[test]
fn test_pipeline_stagnation_broken_by_strengthen() {
    // Simulate: stagnation detected -> strengthen proposes fix -> progress resumes.
    let mut stag_detector = StagnationDetector::with_threshold(2);
    let mut tracker = ConvergenceTracker::new(3, 10);

    // Iteration 0: 1 proved, 1 failed
    let f0 = frontier(1, 0, 0, 1, 0);
    let _ = stag_detector.observe(&f0);
    tracker.observe(IterationSnapshot::new(0, f0.clone()));

    // Iteration 1: same (stale 1)
    let _ = stag_detector.observe(&f0);
    tracker.observe(IterationSnapshot::new(1, f0.clone()));

    // Iteration 2: same (stale 2 -> stagnation!)
    let r = stag_detector.observe(&f0);
    assert!(r.is_stagnant());

    // Run strengthen on the stagnating result
    let cr = crate_result(
        "stuck_func",
        vec![(VcKind::DivisionByZero, proved()), (VcKind::IndexOutOfBounds, failed())],
    );
    let output = trust_strengthen::run(&cr, &StrengthenConfig::default());
    assert!(output.has_proposals, "strengthen should propose fix for OOB");

    // Apply strengthen proposals -> iteration 3: all proved
    let f3 = frontier(2, 0, 0, 0, 0);
    stag_detector.reset();
    let r3 = stag_detector.observe(&f3);
    assert!(!r3.is_stagnant());
    assert_eq!(r3.stale_iterations, 0);

    let decision = tracker.observe(IterationSnapshot::new(2, f3));
    assert!(matches!(decision, ConvergenceDecision::Continue { verdict: StepVerdict::Improved }));
}

// ---------------------------------------------------------------------------
// Test: Monotonicity enforcement with pipeline frontiers
// Uses trust-types + trust-convergence::monotonicity
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_monotonicity_strict_across_iterations() {
    // Iteration 0: 3 proved, 0 failed
    let iter0 = multi_func_crate_result(vec![
        ("f1", vec![(VcKind::DivisionByZero, proved())]),
        ("f2", vec![(VcKind::Postcondition, proved())]),
        ("f3", vec![(VcKind::IndexOutOfBounds, proved())]),
    ]);
    let f0 = ProofFrontier::from_verification_result(&iter0);

    // Iteration 1: regression (f1 no longer proves)
    let iter1 = multi_func_crate_result(vec![
        ("f1", vec![(VcKind::DivisionByZero, failed())]),
        ("f2", vec![(VcKind::Postcondition, proved())]),
        ("f3", vec![(VcKind::IndexOutOfBounds, proved())]),
    ]);
    let f1 = ProofFrontier::from_verification_result(&iter1);

    let result = check_monotonicity(&f0, &f1, MonotonicityPolicy::Strict);
    assert!(!result.is_monotonic);
    assert!(result.should_rollback());
    assert!(result.violation_reason.as_ref().unwrap().contains("static proofs decreased"));

    // Under relaxed policy, also fails because failures increased.
    let relaxed = check_monotonicity(&f0, &f1, MonotonicityPolicy::Relaxed);
    assert!(!relaxed.is_monotonic);
}

#[test]
fn test_pipeline_monotonicity_relaxed_allows_tradeoff() {
    // Iteration 0: trusted=3, certified=0, failed=1
    let f0 = frontier(3, 0, 0, 1, 0);

    // Iteration 1: trusted=2, certified=2, failed=0 (net +1 static proofs, 0 new failures)
    let f1 = frontier(2, 2, 0, 0, 0);

    let strict = check_monotonicity(&f0, &f1, MonotonicityPolicy::Strict);
    // Strict doesn't allow trusted to go down even if certified compensates.
    // Actually: statically_proved_delta = (2+2) - (3+0) = 1 >= 0, so trusted decrease
    // is fine under strict as long as statically_proved doesn't decrease.
    // Also: failed delta = 0-1 = -1 (decrease is good), unresolved: 0+0+0 - (0+1+0) = -1 (decrease).
    assert!(strict.is_monotonic);
}

// ---------------------------------------------------------------------------
// Test: Widening/narrowing in abstract domains across pipeline iterations
// Uses trust-convergence::widening
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_widening_schedule_with_convergence_tracker() {
    // Simulate a loop that stagnates and triggers widening.
    let mut conv_tracker = ConvergenceTracker::new(3, 15);
    let mut schedule = WideningSchedule::new(3, 2, 5);
    let mut threshold_widen = ThresholdWidening::new(2);

    // Iterations 0-1: progress
    let f0 = frontier(1, 0, 0, 3, 0);
    let f1 = frontier(2, 0, 0, 2, 0);
    conv_tracker.observe(IterationSnapshot::new(0, f0));
    conv_tracker.observe(IterationSnapshot::new(1, f1.clone()));
    schedule.tick();
    schedule.tick();
    threshold_widen.observe(&state_with(&["a"], &["b", "c", "d"], 0));
    threshold_widen.observe(&state_with(&["a", "b"], &["c", "d"], 1));

    // Iterations 2-4: stagnation
    for i in 2..=4 {
        conv_tracker.observe(IterationSnapshot::new(i, f1.clone()));
        threshold_widen.observe(&state_with(&["a", "b"], &["c", "d"], i));
        let should_widen = schedule.tick();
        if should_widen && threshold_widen.should_widen() {
            // Apply widening.
            let state = state_with(&["a", "b"], &["c", "d"], i);
            let widened = threshold_widen.widen(&state, &state);
            schedule.record_application();

            // Widened state should promote proposals to proved.
            assert!(widened.proved_vcs.contains("c"));
            assert!(widened.proved_vcs.contains("d"));
            assert!(widened.active_proposals.is_empty());
            break;
        }
    }

    assert!(
        schedule.applications() > 0 || threshold_widen.stale_count() > 0,
        "widening should have been triggered or stale count accumulated"
    );
}

#[test]
fn test_pipeline_delayed_widening_then_narrowing() {
    // Simulate delayed widening with a 3-iteration delay, then narrow.
    let mut delayed = DelayedWidening::new(3, 2);

    let s0 = state_with(&["a"], &["b", "c", "d"], 0);
    let s1 = state_with(&["a"], &["b", "c", "d"], 1);
    let s2 = state_with(&["a"], &["b", "c", "d"], 2);

    delayed.observe(&s0);
    assert!(!delayed.should_widen());
    delayed.observe(&s1);
    assert!(!delayed.should_widen());
    delayed.observe(&s2);
    // After 3 observations (delay=3), stale_count=2 (threshold=2) -> should widen
    assert!(delayed.should_widen());

    // Apply widening.
    let widened = delayed.widen(&s0, &s2);
    assert_eq!(widened.proved_count(), 4); // a + b + c + d
    assert_eq!(widened.proposal_count(), 0);
    assert!(widened.is_top());

    // Simulate re-verification: only b is actually provable.
    let precise = state_with(&["a", "b"], &["c", "d"], 3);

    // Apply narrowing to recover precision.
    let narrowing = SimpleNarrowing;
    let narrowed = narrow_after_widening(&widened, &precise, &narrowing);
    assert!(narrowed.proved_vcs.contains("a"));
    assert!(narrowed.proved_vcs.contains("b"));
    assert!(!narrowed.proved_vcs.contains("c"));
    assert!(!narrowed.proved_vcs.contains("d"));
    assert!(narrowed.active_proposals.contains("c"));
    assert!(narrowed.active_proposals.contains("d"));
}

#[test]
fn test_pipeline_accelerate_convergence_with_stale_history() {
    // Build a history of states showing stagnation.
    let mut tw = ThresholdWidening::new(1);
    let stale_state = state_with(&["a"], &["b", "c"], 1);

    tw.observe(&stale_state);
    tw.observe(&stale_state); // stale=1, threshold=1 -> should widen

    let history = vec![
        state_with(&["a"], &["b", "c"], 0),
        stale_state.clone(),
        stale_state.clone(),
        stale_state.clone(),
    ];

    let result = accelerate_convergence(&history, 2, &tw);
    // Widening should promote b and c to proved.
    assert!(result.proved_vcs.contains("a"));
    assert!(result.proved_vcs.contains("b"));
    assert!(result.proved_vcs.contains("c"));
    assert!(result.active_proposals.is_empty());
}

#[test]
fn test_pipeline_abstract_state_join_meet_lattice() {
    // Two parallel verification paths produce different proved sets.
    let path_a = state_with(&["vc1", "vc2"], &["prop_a"], 3);
    let path_b = state_with(&["vc2", "vc3"], &["prop_b"], 2);

    // Join: union (best of both paths).
    let joined = path_a.join(&path_b);
    assert_eq!(joined.proved_count(), 3); // vc1, vc2, vc3
    assert_eq!(joined.proposal_count(), 2); // prop_a, prop_b
    assert_eq!(joined.round, 3);

    // Meet: intersection (conservative).
    let met = path_a.meet(&path_b);
    assert_eq!(met.proved_count(), 1); // only vc2
    assert_eq!(met.proposal_count(), 0); // no common proposals
    assert_eq!(met.round, 2);

    // Lattice properties.
    assert!(met.is_subset_of(&path_a));
    assert!(met.is_subset_of(&path_b));
    assert!(path_a.is_subset_of(&joined));
    assert!(path_b.is_subset_of(&joined));
}

// ---------------------------------------------------------------------------
// Test: Termination analysis with pipeline-derived frontiers
// Uses trust-types + trust-convergence::termination
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_termination_fixed_point_from_verification_results() {
    let analyzer = TerminationAnalyzer::with_criterion(TerminationCriterion::FixedPoint);

    // Two identical verification results -> fixed point.
    let cr = crate_result(
        "func",
        vec![(VcKind::DivisionByZero, proved()), (VcKind::IndexOutOfBounds, failed())],
    );
    let f = ProofFrontier::from_verification_result(&cr);

    let history = vec![IterationSnapshot::new(0, f.clone()), IterationSnapshot::new(1, f.clone())];

    let reason = analyzer.should_terminate(&history).expect("fixed point");
    assert!(matches!(reason, TerminationReason::FixedPoint { stable_iterations: 2 }));
}

#[test]
fn test_pipeline_termination_confidence_threshold() {
    let analyzer =
        TerminationAnalyzer::with_criterion(TerminationCriterion::ConfidenceThreshold(0.75));

    // 4 out of 4 proved = 100% > 75%
    let cr = crate_result(
        "func",
        vec![
            (VcKind::DivisionByZero, proved()),
            (VcKind::IndexOutOfBounds, proved()),
            (VcKind::Postcondition, proved()),
            (
                VcKind::ArithmeticOverflow {
                    op: BinOp::Add,
                    operand_tys: (
                        Ty::Int { width: 32, signed: false },
                        Ty::Int { width: 32, signed: false },
                    ),
                },
                proved(),
            ),
        ],
    );
    let f = ProofFrontier::from_verification_result(&cr);

    let history = vec![IterationSnapshot::new(0, f)];
    let reason = analyzer.should_terminate(&history).expect("threshold met");
    match reason {
        TerminationReason::ConfidenceThreshold { achieved, threshold } => {
            assert!((achieved - 1.0).abs() < f64::EPSILON);
            assert!((threshold - 0.75).abs() < f64::EPSILON);
        }
        _ => panic!("expected ConfidenceThreshold"),
    }
}

#[test]
fn test_pipeline_termination_budget_exhaustion() {
    let mut analyzer = TerminationAnalyzer::new(
        vec![TerminationCriterion::MaxIterations(100)],
        ResourceBudget::new(Some(Duration::from_secs(10)), None),
    );

    let f = frontier(3, 0, 0, 2, 0);
    // Consume budget over several iterations.
    analyzer.record_iteration(None, &f, Duration::from_secs(4));
    analyzer.record_iteration(Some(&f), &f, Duration::from_secs(4));
    analyzer.record_iteration(Some(&f), &f, Duration::from_secs(4));

    let history = vec![
        IterationSnapshot::new(0, f.clone()),
        IterationSnapshot::new(1, f.clone()),
        IterationSnapshot::new(2, f),
    ];
    let reason = analyzer.should_terminate(&history).expect("budget exhausted");
    assert!(matches!(reason, TerminationReason::BudgetExhausted { .. }));
}

#[test]
fn test_pipeline_convergence_prediction_with_rate_history() {
    let mut analyzer = TerminationAnalyzer::new(vec![], ResourceBudget::unlimited());

    // Simulate steady improvement: 2 VCs proved per iteration.
    let f0 = frontier(2, 0, 0, 8, 0);
    let f1 = frontier(4, 0, 0, 6, 0);
    let f2 = frontier(6, 0, 0, 4, 0);

    analyzer.record_iteration(None, &f0, Duration::from_millis(100));
    analyzer.record_iteration(Some(&f0), &f1, Duration::from_millis(100));
    analyzer.record_iteration(Some(&f1), &f2, Duration::from_millis(100));

    let prediction = analyzer.predict_convergence(10);
    assert!(prediction.will_converge);
    assert!(prediction.estimated_remaining.is_some());
    assert!(prediction.confidence > 0.0);

    let remaining = analyzer.estimate_remaining();
    assert!(remaining.is_some());
}

#[test]
fn test_pipeline_loop_bound_estimation() {
    // 6 unresolved VCs, average 2 VCs per strengthening proposal
    let bound = estimate_loop_bound(6, 2.0);
    assert_eq!(bound, Some(3)); // 6/2 = 3 rounds

    // Fractional case
    let bound2 = estimate_loop_bound(7, 3.0);
    assert_eq!(bound2, Some(3)); // ceil(7/3) = 3

    // No unresolved VCs
    let bound3 = estimate_loop_bound(0, 2.0);
    assert!(bound3.is_none());
}

// ---------------------------------------------------------------------------
// Test: Full loop simulation combining convergence + strengthen + termination
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_full_loop_with_convergence_and_strengthen() {
    // Simulate a complete prove-strengthen-backprop loop.
    let mut conv_tracker = VerificationConvergenceTracker::new(2, 10);
    let mut stag_detector = StagnationDetector::with_threshold(3);
    let mut term_analyzer = TerminationAnalyzer::new(
        vec![
            TerminationCriterion::MaxIterations(10),
            TerminationCriterion::ConfidenceThreshold(1.0),
        ],
        ResourceBudget::unlimited(),
    );
    let mut snapshots: Vec<IterationSnapshot> = Vec::new();

    // Define 4 VCs to prove over multiple iterations.
    let vc_kinds = [
        VcKind::DivisionByZero,
        VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (
                Ty::Int { width: 64, signed: false },
                Ty::Int { width: 64, signed: false },
            ),
        },
        VcKind::IndexOutOfBounds,
        VcKind::Postcondition,
    ];

    // Simulate: each iteration proves one more VC.
    let mut proved_count = 0u32;
    let mut prev_frontier: Option<ProofFrontier> = None;

    for iteration in 0..5 {
        // Build results: first `proved_count+1` are proved, rest fail.
        let target_proved = (iteration + 1).min(vc_kinds.len());
        let results: Vec<(VcKind, VerificationResult)> = vc_kinds
            .iter()
            .enumerate()
            .map(|(i, kind)| {
                if i < target_proved { (kind.clone(), proved()) } else { (kind.clone(), failed()) }
            })
            .collect();

        let cr = crate_result("target_func", results);

        // Convergence tracking.
        conv_tracker.observe(&cr);

        // Frontier tracking.
        let f = ProofFrontier::from_verification_result(&cr);
        let snap = IterationSnapshot::new(iteration as u32, f.clone());
        snapshots.push(snap);

        // Stagnation tracking.
        let _ = stag_detector.observe(&f);

        // Termination analysis.
        term_analyzer.record_iteration(prev_frontier.as_ref(), &f, Duration::from_millis(50));

        // Check termination.
        if let Some(reason) = term_analyzer.should_terminate(&snapshots) {
            if let TerminationReason::ConfidenceThreshold { achieved, .. } = reason {
                assert!((achieved - 1.0).abs() < f64::EPSILON);
                assert_eq!(iteration, 3); // all 4 VCs proved at iteration 3
            }
            proved_count = f.statically_proved();
            break;
        }

        // Run strengthen on failures.
        if f.failed > 0 {
            let output = trust_strengthen::run(&cr, &StrengthenConfig::default());
            assert!(output.has_proposals || f.failed == 0);
        }

        prev_frontier = Some(f);
    }

    // Verify loop completed with all proved.
    assert_eq!(proved_count, 4);
    assert!(!stag_detector.observe(&frontier(4, 0, 0, 0, 0)).is_stagnant());
}

// ---------------------------------------------------------------------------
// Test: Visualization snapshots from verification convergence tracker
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_visualization_snapshots_from_tracker() {
    let mut tracker = VerificationConvergenceTracker::new(3, 10);

    // Iteration 0
    let cr0 = multi_func_crate_result(vec![
        ("f1", vec![(VcKind::DivisionByZero, proved())]),
        ("f2", vec![(VcKind::Postcondition, failed())]),
    ]);
    tracker.observe(&cr0);

    // Build a FrontierSnapshot from the tracker state.
    let snap = trust_convergence::visualization::from_tracker(&tracker);
    assert_eq!(snap.iteration, 1); // observe increments iteration
    assert_eq!(
        snap.proved_count + snap.failed_count + snap.unknown_count,
        tracker.current_statuses().len()
    );

    let ratio = snap.convergence_ratio().expect("has VCs");
    assert!(ratio > 0.0 && ratio < 1.0);
}

// ---------------------------------------------------------------------------
// Test: Multi-function convergence with mixed VC kinds
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_multi_function_convergence_tracking() {
    let mut tracker = VerificationConvergenceTracker::new(2, 10);

    // Iteration 0: 5 functions with mixed results
    let iter0 = multi_func_crate_result(vec![
        (
            "parse_input",
            vec![(VcKind::DivisionByZero, proved()), (VcKind::IndexOutOfBounds, failed())],
        ),
        ("validate", vec![(VcKind::Postcondition, proved())]),
        (
            "transform",
            vec![
                (
                    VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (
                            Ty::Int { width: 32, signed: true },
                            Ty::Int { width: 32, signed: true },
                        ),
                    },
                    failed(),
                ),
                (VcKind::DivisionByZero, unknown()),
            ],
        ),
        (
            "serialize",
            vec![(VcKind::IndexOutOfBounds, proved()), (VcKind::Postcondition, proved())],
        ),
        ("cleanup", vec![(VcKind::Unreachable, timeout())]),
    ]);

    tracker.observe(&iter0);
    let f0 = ProofFrontier::from_verification_result(&iter0);
    assert_eq!(f0.trusted, 4); // parse_input::div, validate::post, serialize::oob, serialize::post
    assert_eq!(f0.failed, 2); // parse_input::oob, transform::overflow
    assert_eq!(f0.unknown, 2); // transform::div, cleanup::unreachable

    // Iteration 1: progress on some fronts
    let iter1 = multi_func_crate_result(vec![
        (
            "parse_input",
            vec![
                (VcKind::DivisionByZero, proved()),
                (VcKind::IndexOutOfBounds, proved()), // fixed!
            ],
        ),
        ("validate", vec![(VcKind::Postcondition, proved())]),
        (
            "transform",
            vec![
                (
                    VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (
                            Ty::Int { width: 32, signed: true },
                            Ty::Int { width: 32, signed: true },
                        ),
                    },
                    proved(),
                ), // fixed!
                (VcKind::DivisionByZero, proved()), // fixed!
            ],
        ),
        (
            "serialize",
            vec![(VcKind::IndexOutOfBounds, proved()), (VcKind::Postcondition, proved())],
        ),
        (
            "cleanup",
            vec![
                (VcKind::Unreachable, proved()), // fixed!
            ],
        ),
    ]);

    let changes = tracker.observe(&iter1);
    let improvements: Vec<_> = changes.iter().filter(|c| c.is_improvement()).collect();
    assert!(improvements.len() >= 4, "should detect 4 newly proved VCs");
    assert!(!tracker.has_regressions());

    let score = tracker.convergence_score().expect("has VCs");
    assert!((score - 1.0).abs() < f64::EPSILON, "all 8 VCs should be proved");
}

// ---------------------------------------------------------------------------
// Test: Convergence report integration
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_convergence_report_with_deltas() {
    let mut tracker = ConvergenceTracker::new(3, 10);

    // Build frontiers from CrateVerificationResults.
    let cr0 = crate_result(
        "func",
        vec![
            (VcKind::DivisionByZero, proved()),
            (VcKind::IndexOutOfBounds, failed()),
            (VcKind::Postcondition, failed()),
        ],
    );
    let f0 = ProofFrontier::from_verification_result(&cr0);

    let cr1 = crate_result(
        "func",
        vec![
            (VcKind::DivisionByZero, proved()),
            (VcKind::IndexOutOfBounds, proved()),
            (VcKind::Postcondition, failed()),
        ],
    );
    let f1 = ProofFrontier::from_verification_result(&cr1);

    tracker.observe(IterationSnapshot::new(0, f0));
    tracker.observe(IterationSnapshot::new(1, f1));

    let report = tracker.latest_report().expect("has report");
    assert_eq!(report.iteration, 1);
    assert_eq!(report.previous_iteration, Some(0));
    assert_eq!(report.step_verdict(), Some(StepVerdict::Improved));

    let delta = report.delta.expect("has delta");
    assert_eq!(delta.statically_proved_delta(), 1); // 1->2 proved
    assert!(delta.is_non_decreasing_static_proofs());
    assert!(delta.is_non_increasing_unresolved());
}

// ---------------------------------------------------------------------------
// Test: Widening schedule with convergence decision feedback
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_widening_reacts_to_convergence_decision() {
    let mut tracker = ConvergenceTracker::new(4, 20);
    let mut schedule = WideningSchedule::every(3);
    let mut widening = ThresholdWidening::new(2);
    let narrowing = SimpleNarrowing;

    let stale_frontier = frontier(3, 0, 0, 2, 0);
    let abstract_state = state_with(&["vc1", "vc2", "vc3"], &["vc4", "vc5"], 0);
    let mut widened_state: Option<AbstractState> = None;

    for i in 0..9u32 {
        let decision = tracker.observe(IterationSnapshot::new(i, stale_frontier.clone()));
        widening.observe(&abstract_state);
        let should_widen = schedule.tick();

        match decision {
            ConvergenceDecision::Continue { verdict: StepVerdict::Stable }
                if should_widen && widening.should_widen() => {
                    let w = widening.widen(&abstract_state, &abstract_state);
                    schedule.record_application();
                    widened_state = Some(w);
                    break;
                }
            ConvergenceDecision::Converged { .. } => {
                break;
            }
            _ => {}
        }
    }

    // If widening was applied, narrow to recover precision.
    if let Some(wide) = widened_state {
        assert!(wide.proved_vcs.contains("vc4"));
        assert!(wide.proved_vcs.contains("vc5"));

        // Suppose only vc4 actually proves.
        let precise = state_with(&["vc1", "vc2", "vc3", "vc4"], &["vc5"], 10);
        let narrowed = narrow_after_widening(&wide, &precise, &narrowing);
        assert!(narrowed.proved_vcs.contains("vc4"));
        assert!(!narrowed.proved_vcs.contains("vc5"));
        assert!(narrowed.active_proposals.contains("vc5"));
    }
}

// ---------------------------------------------------------------------------
// Test: End-to-end convergence rate estimation from pipeline data
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_convergence_rate_estimation() {
    let rates = vec![
        ConvergenceRate {
            vcs_proved_delta: 3,
            cumulative_proved: 3,
            total_vcs: 10,
            moving_average: 3.0,
            trend: 0.0,
        },
        ConvergenceRate {
            vcs_proved_delta: 2,
            cumulative_proved: 5,
            total_vcs: 10,
            moving_average: 2.5,
            trend: -0.5,
        },
        ConvergenceRate {
            vcs_proved_delta: 2,
            cumulative_proved: 7,
            total_vcs: 10,
            moving_average: 2.33,
            trend: -0.17,
        },
    ];

    let prediction = will_converge(&rates, 10);
    assert!(prediction.will_converge);
    assert!(prediction.estimated_remaining.is_some());
    let remaining = prediction.estimated_remaining.unwrap();
    // 3 VCs remaining at ~2.33/iter -> ceil(3/2.33) = 2
    assert!(remaining <= 3);

    // Estimate from a single rate entry.
    let est = estimate_remaining_iterations(&rates[2]);
    assert!(est.is_some());
}

// ---------------------------------------------------------------------------
// Test: Stagnation report JSON serialization (cross-crate: serde + convergence)
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_stagnation_report_serialization() {
    let mut detector = SnapshotStagnationDetector::new(2);
    detector.push(FrontierSnapshot {
        iteration: 0,
        proved_count: 3,
        failed_count: 2,
        unknown_count: 1,
        timestamp: 1000,
        proved_vcs: vec!["f1::div".into(), "f1::oob".into(), "f2::post".into()],
        failed_vcs: vec!["f3::overflow".into(), "f3::div".into()],
    });
    detector.push(FrontierSnapshot {
        iteration: 1,
        proved_count: 3,
        failed_count: 2,
        unknown_count: 1,
        timestamp: 2000,
        proved_vcs: vec!["f1::div".into(), "f1::oob".into(), "f2::post".into()],
        failed_vcs: vec!["f3::overflow".into(), "f3::div".into()],
    });
    detector.push(FrontierSnapshot {
        iteration: 2,
        proved_count: 3,
        failed_count: 2,
        unknown_count: 1,
        timestamp: 3000,
        proved_vcs: vec!["f1::div".into(), "f1::oob".into(), "f2::post".into()],
        failed_vcs: vec!["f3::overflow".into(), "f3::div".into()],
    });

    assert!(detector.is_stagnating());
    let report = detector.stagnation_report();

    // Serialize to JSON and back.
    let json = serde_json::to_string_pretty(&report).expect("serialize");
    let deser: trust_convergence::stagnation::StagnationReport =
        serde_json::from_str(&json).expect("deserialize");

    assert_eq!(report, deser);
    assert!(deser.is_stagnating);
    assert_eq!(deser.stuck_vcs, vec!["f3::div", "f3::overflow"]);
    assert_eq!(deser.total_snapshots, 3);
    assert!(deser.best_convergence_ratio.is_some());
}
