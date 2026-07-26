// trust-convergence/tests/loop_integration.rs: Verification loop integration tests
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::time::Duration;

use trust_convergence::integration::{VcStatus, VerificationConvergenceTracker};
use trust_convergence::monotonicity::{MonotonicityPolicy, check_monotonicity};
use trust_convergence::stagnation::StagnationDetector;
use trust_convergence::termination::{
    ResourceBudget, TerminationAnalyzer, TerminationCriterion, TerminationReason,
};
use trust_convergence::widening::{
    AbstractState, SimpleNarrowing, ThresholdWidening, WideningOperator, narrow_after_widening,
};
use trust_convergence::*;
use trust_strengthen::StrengthenConfig;
use trust_types::*;

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

#[test]
fn test_loop_single_iteration_no_convergence() {
    let mut tracker = VerificationConvergenceTracker::new(2, 8);
    let iteration = crate_result(
        "compute",
        vec![
            (VcKind::DivisionByZero, proved()),
            (
                VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::u32(), Ty::u32()) },
                failed(),
            ),
            (VcKind::Postcondition, unknown()),
        ],
    );

    let changes = tracker.observe(&iteration);
    let decision =
        tracker.tracker().latest_report().expect("tracker should have a report").decision;

    assert!(changes.is_empty());
    assert!(matches!(decision, ConvergenceDecision::Continue { verdict: StepVerdict::Improved }));
    assert_eq!(tracker.current_iteration(), 1);
    assert!(tracker.current_statuses().values().any(|status| *status == VcStatus::Failed));
}

#[test]
fn test_loop_three_iterations_gradual_improvement() {
    let mut tracker = VerificationConvergenceTracker::new(2, 8);
    let mut analyzer =
        TerminationAnalyzer::with_criterion(TerminationCriterion::ConfidenceThreshold(1.0));
    let iterations = [
        crate_result(
            "compute",
            vec![
                (VcKind::DivisionByZero, proved()),
                (VcKind::IndexOutOfBounds, failed()),
                (VcKind::Postcondition, failed()),
                (
                    VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (Ty::u32(), Ty::u32()),
                    },
                    failed(),
                ),
            ],
        ),
        crate_result(
            "compute",
            vec![
                (VcKind::DivisionByZero, proved()),
                (VcKind::IndexOutOfBounds, proved()),
                (VcKind::Postcondition, proved()),
                (
                    VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (Ty::u32(), Ty::u32()),
                    },
                    failed(),
                ),
            ],
        ),
        crate_result(
            "compute",
            vec![
                (VcKind::DivisionByZero, proved()),
                (VcKind::IndexOutOfBounds, proved()),
                (VcKind::Postcondition, proved()),
                (
                    VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (Ty::u32(), Ty::u32()),
                    },
                    proved(),
                ),
            ],
        ),
    ];

    let mut history = Vec::new();
    let mut previous_frontier = None;
    let mut reason = None;

    for (iteration, result) in iterations.iter().enumerate() {
        tracker.observe(result);
        let current = ProofFrontier::from_verification_result(result);
        analyzer.record_iteration(previous_frontier.as_ref(), &current, Duration::from_millis(20));
        history.push(IterationSnapshot::new(iteration as u32, current.clone()));
        reason = analyzer.should_terminate(&history);
        previous_frontier = Some(current);
    }

    let reason = reason.expect("the third iteration should finish the loop");
    assert!(matches!(
        reason,
        TerminationReason::ConfidenceThreshold {
            achieved,
            threshold
        } if (achieved - 1.0).abs() < f64::EPSILON && (threshold - 1.0).abs() < f64::EPSILON
    ));
    assert_eq!(tracker.convergence_score(), Some(1.0));
}

#[test]
fn test_loop_stagnation_triggers_widening() {
    let mut detector = StagnationDetector::with_threshold(2);
    let mut widening = ThresholdWidening::new(2);
    let stable_frontier = frontier(1, 0, 0, 2, 0);
    let stable_state = state_with(&["vc1"], &["proposal_a", "proposal_b"], 0);

    assert!(!detector.observe(&stable_frontier).is_stagnant());
    widening.observe(&stable_state);

    assert!(!detector.observe(&stable_frontier).is_stagnant());
    widening.observe(&stable_state);

    let stagnation = detector.observe(&stable_frontier);
    widening.observe(&stable_state);
    let widened = widening.widen(&stable_state, &stable_state);

    assert!(stagnation.is_stagnant());
    assert!(widening.should_widen());
    assert!(widened.proved_vcs.contains("proposal_a"));
    assert!(widened.proved_vcs.contains("proposal_b"));
    assert!(widened.active_proposals.is_empty());
}

#[test]
fn test_loop_regression_detected_and_rolled_back() {
    let previous = frontier(2, 0, 0, 0, 0);
    let current = frontier(1, 0, 0, 1, 0);
    let monotonicity = check_monotonicity(&previous, &current, MonotonicityPolicy::Strict);
    let rollback_target =
        if monotonicity.should_rollback() { previous.clone() } else { current.clone() };

    assert!(monotonicity.should_rollback());
    assert!(
        monotonicity
            .violation_reason
            .expect("strict policy should explain the regression")
            .contains("static proofs decreased")
    );
    assert_eq!(rollback_target, previous);
}

#[test]
fn test_loop_termination_by_budget_exhaustion() {
    let mut analyzer = TerminationAnalyzer::new(
        vec![],
        ResourceBudget::new(Some(Duration::from_millis(100)), Some(10)),
    );
    let f0 = frontier(1, 0, 0, 1, 0);
    let f1 = frontier(2, 0, 0, 0, 0);
    let history =
        vec![IterationSnapshot::new(0, f0.clone()), IterationSnapshot::new(1, f1.clone())];

    analyzer.record_iteration(None, &f0, Duration::from_millis(60));
    analyzer.record_iteration(Some(&f0), &f1, Duration::from_millis(60));

    let reason =
        analyzer.should_terminate(&history).expect("solver-time budget should be exhausted");
    assert!(matches!(reason, TerminationReason::BudgetExhausted { .. }));
}

#[test]
fn test_loop_termination_by_max_iterations() {
    let analyzer = TerminationAnalyzer::with_criterion(TerminationCriterion::MaxIterations(3));
    let history = vec![
        IterationSnapshot::new(0, frontier(1, 0, 0, 2, 0)),
        IterationSnapshot::new(1, frontier(2, 0, 0, 1, 0)),
        IterationSnapshot::new(2, frontier(2, 0, 0, 1, 0)),
    ];

    let reason = analyzer.should_terminate(&history).expect("iteration limit should stop the loop");
    assert!(matches!(reason, TerminationReason::MaxIterations { limit: 3, reached: 3 }));
}

#[test]
fn test_loop_strengthen_breaks_stagnation() {
    let mut tracker = VerificationConvergenceTracker::new(2, 8);
    let mut detector = StagnationDetector::with_threshold(1);
    let stalled = crate_result(
        "safe_divide",
        vec![(VcKind::DivisionByZero, failed()), (VcKind::Postcondition, failed())],
    );

    tracker.observe(&stalled);
    let first_frontier = ProofFrontier::from_verification_result(&stalled);
    assert!(!detector.observe(&first_frontier).is_stagnant());

    tracker.observe(&stalled);
    let second_frontier = ProofFrontier::from_verification_result(&stalled);
    assert!(detector.observe(&second_frontier).is_stagnant());

    let strengthen_output = trust_strengthen::run(&stalled, &StrengthenConfig::default());
    assert!(strengthen_output.has_proposals);
    assert_eq!(strengthen_output.failures_analyzed, 2);

    let improved = crate_result(
        "safe_divide",
        vec![(VcKind::DivisionByZero, proved()), (VcKind::Postcondition, failed())],
    );
    let changes = tracker.observe(&improved);
    let improved_frontier = ProofFrontier::from_verification_result(&improved);

    assert!(changes.iter().any(|change| change.is_improvement()));
    assert!(!detector.observe(&improved_frontier).is_stagnant());
}

#[test]
fn test_loop_widening_then_narrowing_precision_recovery() {
    let baseline: AbstractState = state_with(&["vc1"], &["proposal_a", "proposal_b"], 0);
    let mut widening = ThresholdWidening::new(1);
    widening.observe(&baseline);
    widening.observe(&baseline);

    let widened = widening.widen(&baseline, &baseline);
    let precise = state_with(&["vc1", "proposal_a"], &["proposal_b"], 2);
    let narrowed = narrow_after_widening(&widened, &precise, &SimpleNarrowing);

    assert!(widened.proved_vcs.contains("proposal_a"));
    assert!(widened.proved_vcs.contains("proposal_b"));
    assert!(narrowed.proved_vcs.contains("proposal_a"));
    assert!(!narrowed.proved_vcs.contains("proposal_b"));
    assert!(narrowed.active_proposals.contains("proposal_b"));
}

#[test]
fn test_loop_convergence_prediction_accuracy() {
    let mut analyzer = TerminationAnalyzer::new(vec![], ResourceBudget::unlimited());
    let frontiers = [frontier(1, 0, 0, 3, 0), frontier(2, 0, 0, 2, 0), frontier(3, 0, 0, 1, 0)];
    let mut previous = None;

    for current in &frontiers {
        analyzer.record_iteration(previous.as_ref(), current, Duration::from_millis(10));
        previous = Some(current.clone());
    }

    let prediction = analyzer.predict_convergence(4);
    assert!(prediction.will_converge);
    assert_eq!(prediction.estimated_remaining, Some(1));
    assert!(prediction.confidence > 0.5);
}

#[test]
fn test_loop_full_orchestration_to_completion() {
    let mut tracker = VerificationConvergenceTracker::new(2, 10);
    let mut detector = StagnationDetector::with_threshold(1);
    let mut analyzer = TerminationAnalyzer::new(
        vec![
            TerminationCriterion::MaxIterations(10),
            TerminationCriterion::ConfidenceThreshold(1.0),
        ],
        ResourceBudget::unlimited(),
    );

    let mut history = Vec::new();
    let mut previous_frontier = None;
    let mut current = crate_result(
        "orchestrated",
        vec![
            (VcKind::DivisionByZero, proved()),
            (VcKind::IndexOutOfBounds, failed()),
            (VcKind::Postcondition, failed()),
        ],
    );

    for iteration in 0..6 {
        tracker.observe(&current);
        let current_frontier = ProofFrontier::from_verification_result(&current);
        let stagnation = detector.observe(&current_frontier);
        analyzer.record_iteration(
            previous_frontier.as_ref(),
            &current_frontier,
            Duration::from_millis(25),
        );
        history.push(IterationSnapshot::new(iteration, current_frontier.clone()));

        if let Some(reason) = analyzer.should_terminate(&history) {
            assert!(matches!(
                reason,
                TerminationReason::ConfidenceThreshold { achieved, .. }
                    if (achieved - 1.0).abs() < f64::EPSILON
            ));
            assert_eq!(tracker.convergence_score(), Some(1.0));
            return;
        }

        current = if stagnation.is_stagnant() {
            let strengthen_output =
                trust_strengthen::run(&current, &StrengthenConfig::default());
            assert!(strengthen_output.has_proposals);
            crate_result(
                "orchestrated",
                vec![
                    (VcKind::DivisionByZero, proved()),
                    (VcKind::IndexOutOfBounds, proved()),
                    (VcKind::Postcondition, failed()),
                ],
            )
        } else if current_frontier.failed > 0 {
            crate_result(
                "orchestrated",
                vec![
                    (VcKind::DivisionByZero, proved()),
                    (VcKind::IndexOutOfBounds, proved()),
                    (VcKind::Postcondition, proved()),
                ],
            )
        } else {
            current.clone()
        };

        previous_frontier = Some(current_frontier);
    }

    panic!("loop should have reached a terminating reason");
}
