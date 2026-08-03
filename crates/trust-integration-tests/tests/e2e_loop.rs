// trust-integration-tests/tests/e2e_loop.rs: End-to-end golden test for the
// prove-strengthen-backprop verification loop.
//
// Exercises the full M5 loop using mock phases that simulate the canonical
// binary_search overflow scenario:
//   1. VerifyPhase detects ArithmeticOverflow on `(lo + hi) / 2`
//   2. StrengthenPhase proposes `mid = lo + (hi - lo) / 2`
//   3. BackpropPhase applies the rewrite
//   4. VerifyPhase re-verifies and finds no overflow
//   5. Loop converges in 2 iterations
//
// Uses trust-convergence for fixed-point detection. Stays inside the crates/
// workspace: nothing here reaches for a rustc_private-dependent crate.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use std::cell::Cell;

use trust_convergence::{
    ConvergenceDecision, ConvergenceTracker, IterationSnapshot, ProofFrontier,
};
// Trust: Import trust-loop for integration testing of the iterative verification loop
use trust_loop::{LoopConfig, VerifyContext};
use trust_strengthen::{Proposal, ProposalKind, StrengthenOutput};
use trust_types::{
    Formula, ProofStrength, Sort, SourceSpan, VcKind, VerificationCondition, VerificationResult,
};

// ---------------------------------------------------------------------------
// Mock phase outputs — local stand-ins carrying only what the loop below reads,
// so the golden sequencing can be exercised without a compiler.
// ---------------------------------------------------------------------------

/// Simplified verify output for the loop test.
#[derive(Debug, Clone)]
struct VerifyOutput {
    frontier: ProofFrontier,
    fingerprint: Option<String>,
    vcs_dispatched: usize,
    vcs_failed: usize,
}

/// Simplified backprop output for the loop test.
#[derive(Debug, Clone)]
struct BackpropOutput {
    applied: usize,
    skipped: usize,
}

// ---------------------------------------------------------------------------
// Phase traits (self-contained)
// ---------------------------------------------------------------------------

trait VerifyPhase {
    fn verify(&self) -> VerifyOutput;
}

trait StrengthenPhase {
    fn strengthen(&self, verify_output: &VerifyOutput) -> StrengthenOutput;
}

trait BackpropPhase {
    fn backpropagate(&self, proposals: &[Proposal]) -> BackpropOutput;
}

// ---------------------------------------------------------------------------
// Loop termination
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum LoopOutcome {
    /// All VCs proved.
    Verified { iterations: u32, vcs_proved: usize },
    /// Failures remain after convergence or exhaustion.
    Refuted { iterations: u32, vcs_failed: usize, exhausted_proposals: bool },
    /// Hit the iteration limit.
    Timeout { iterations: u32, max_iterations: u32 },
    /// Proof frontier regressed.
    Diverged { iterations: u32 },
}

// ---------------------------------------------------------------------------
// Minimal verification loop — the golden sequencing this test pins
// ---------------------------------------------------------------------------

fn run_loop(
    max_iterations: u32,
    stable_round_limit: usize,
    verify: &dyn VerifyPhase,
    strengthen: &dyn StrengthenPhase,
    backprop: &dyn BackpropPhase,
) -> (LoopOutcome, Vec<ProofFrontier>) {
    let mut tracker = ConvergenceTracker::new(stable_round_limit, max_iterations);
    let mut history = Vec::new();
    let mut iteration: u32 = 0;

    loop {
        // Phase 1: Verify
        let v_out = verify.verify();
        history.push(v_out.frontier.clone());

        // Phase 2: Check convergence
        let snapshot = match &v_out.fingerprint {
            Some(fp) => {
                IterationSnapshot::new(iteration, v_out.frontier.clone()).with_fingerprint(fp)
            }
            None => IterationSnapshot::new(iteration, v_out.frontier.clone()),
        };
        let decision = tracker.observe(snapshot);

        // Early exit: all proved
        if v_out.vcs_failed == 0 {
            return (
                LoopOutcome::Verified {
                    iterations: iteration + 1,
                    vcs_proved: v_out.vcs_dispatched,
                },
                history,
            );
        }

        match &decision {
            ConvergenceDecision::Converged { .. } => {
                return (
                    LoopOutcome::Refuted {
                        iterations: iteration + 1,
                        vcs_failed: v_out.vcs_failed,
                        exhausted_proposals: false,
                    },
                    history,
                );
            }
            ConvergenceDecision::IterationLimitReached { limit, .. } => {
                return (
                    LoopOutcome::Timeout { iterations: iteration + 1, max_iterations: *limit },
                    history,
                );
            }
            ConvergenceDecision::Regressed { .. } => {
                return (LoopOutcome::Diverged { iterations: iteration + 1 }, history);
            }
            ConvergenceDecision::Continue { .. } => {
                // Continue to strengthen + backprop
            }
        }

        // Phase 3: Strengthen
        let s_out = strengthen.strengthen(&v_out);

        if !s_out.has_proposals {
            return (
                LoopOutcome::Refuted {
                    iterations: iteration + 1,
                    vcs_failed: v_out.vcs_failed,
                    exhausted_proposals: true,
                },
                history,
            );
        }

        // Phase 4: Backprop
        let b_out = backprop.backpropagate(&s_out.proposals);
        debug_assert_eq!(b_out.applied + b_out.skipped, s_out.proposals.len());

        if b_out.applied == 0 {
            return (
                LoopOutcome::Refuted {
                    iterations: iteration + 1,
                    vcs_failed: v_out.vcs_failed,
                    exhausted_proposals: true,
                },
                history,
            );
        }

        iteration += 1;
    }
}

// ---------------------------------------------------------------------------
// Mock phases: binary_search overflow scenario
// ---------------------------------------------------------------------------

/// Mock verify phase that simulates binary_search verification.
///
/// Call 0: detects ArithmeticOverflow on `(lo + hi) / 2` (1 failed, 4 proved)
/// Call 1+: all VCs pass after strengthen proposes safe midpoint (5 proved, 0 failed)
struct BinarySearchVerify {
    call_count: Cell<usize>,
}

impl BinarySearchVerify {
    fn new() -> Self {
        Self { call_count: Cell::new(0) }
    }
}

impl VerifyPhase for BinarySearchVerify {
    fn verify(&self) -> VerifyOutput {
        let idx = self.call_count.get();
        self.call_count.set(idx + 1);
        if idx == 0 {
            // First call: overflow detected
            VerifyOutput {
                frontier: ProofFrontier {
                    trusted: 4,
                    certified: 0,
                    runtime_checked: 0,
                    failed: 1,
                    unknown: 0,
                },
                fingerprint: Some("overflow_detected".into()),
                vcs_dispatched: 5,
                vcs_failed: 1,
            }
        } else {
            // After strengthening: all pass
            VerifyOutput {
                frontier: ProofFrontier {
                    trusted: 5,
                    certified: 0,
                    runtime_checked: 0,
                    failed: 0,
                    unknown: 0,
                },
                fingerprint: Some("all_proved".into()),
                vcs_dispatched: 5,
                vcs_failed: 0,
            }
        }
    }
}

/// Mock strengthen phase that proposes the safe midpoint computation.
struct BinarySearchStrengthen;

impl StrengthenPhase for BinarySearchStrengthen {
    fn strengthen(&self, verify_output: &VerifyOutput) -> StrengthenOutput {
        if verify_output.vcs_failed == 0 {
            return StrengthenOutput {
                has_proposals: false,
                failures_analyzed: 0,
                proposals: vec![],
            };
        }

        // Propose the classic fix: mid = lo + (hi - lo) / 2
        let proposals = vec![
            Proposal {
                function_path: "search::binary_search".into(),
                function_name: "binary_search".into(),
                kind: ProposalKind::SafeArithmetic {
                    original: "(lo + hi) / 2".into(),
                    replacement: "lo + (hi - lo) / 2".into(),
                },
                confidence: 0.95,
                rationale: "Replace `(lo + hi) / 2` with `lo + (hi - lo) / 2` to avoid \
                            arithmetic overflow when lo and hi are large"
                    .into(),
            },
            Proposal {
                function_path: "search::binary_search".into(),
                function_name: "binary_search".into(),
                kind: ProposalKind::AddPrecondition { spec_body: "hi >= lo".into() },
                confidence: 0.90,
                rationale: "Require hi >= lo as a precondition for binary search correctness"
                    .into(),
            },
        ];

        StrengthenOutput {
            has_proposals: true,
            failures_analyzed: verify_output.vcs_failed,
            proposals,
        }
    }
}

/// Mock backprop phase that applies all proposals.
struct ApplyAllBackprop;

impl BackpropPhase for ApplyAllBackprop {
    fn backpropagate(&self, proposals: &[Proposal]) -> BackpropOutput {
        BackpropOutput { applied: proposals.len(), skipped: 0 }
    }
}

// ---------------------------------------------------------------------------
// Mock phases for edge-case tests
// ---------------------------------------------------------------------------

/// Verify phase that returns a pre-programmed sequence of outputs.
struct SequenceVerify {
    outputs: Vec<VerifyOutput>,
    call_count: Cell<usize>,
}

impl SequenceVerify {
    fn new(outputs: Vec<VerifyOutput>) -> Self {
        Self { outputs, call_count: Cell::new(0) }
    }
}

impl VerifyPhase for SequenceVerify {
    fn verify(&self) -> VerifyOutput {
        let idx = self.call_count.get();
        self.call_count.set(idx + 1);
        self.outputs[idx.min(self.outputs.len() - 1)].clone()
    }
}

/// Strengthen phase that returns a fixed number of proposals.
struct FixedStrengthen {
    proposal_count: usize,
}

impl StrengthenPhase for FixedStrengthen {
    fn strengthen(&self, _: &VerifyOutput) -> StrengthenOutput {
        let proposals: Vec<Proposal> = (0..self.proposal_count)
            .map(|i| Proposal {
                function_path: format!("test::fn_{i}"),
                function_name: format!("fn_{i}"),
                kind: ProposalKind::AddPrecondition { spec_body: format!("x > {i}") },
                confidence: 0.9,
                rationale: format!("mock proposal {i}"),
            })
            .collect();
        StrengthenOutput {
            has_proposals: !proposals.is_empty(),
            failures_analyzed: self.proposal_count,
            proposals,
        }
    }
}

/// Strengthen phase that returns no proposals.
struct EmptyStrengthen;

impl StrengthenPhase for EmptyStrengthen {
    fn strengthen(&self, _: &VerifyOutput) -> StrengthenOutput {
        StrengthenOutput { has_proposals: false, failures_analyzed: 0, proposals: vec![] }
    }
}

/// Backprop phase that applies nothing.
struct NoOpBackprop;

impl BackpropPhase for NoOpBackprop {
    fn backpropagate(&self, proposals: &[Proposal]) -> BackpropOutput {
        BackpropOutput { applied: 0, skipped: proposals.len() }
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn make_verify_output(trusted: u32, failed: u32) -> VerifyOutput {
    VerifyOutput {
        frontier: ProofFrontier { trusted, certified: 0, runtime_checked: 0, failed, unknown: 0 },
        fingerprint: None,
        vcs_dispatched: (trusted + failed) as usize,
        vcs_failed: failed as usize,
    }
}

// ===========================================================================
// Test: Golden binary_search loop converges in 2 iterations
// ===========================================================================

#[test]
fn test_e2e_binary_search_loop_converges_in_two_iterations() {
    let verify = BinarySearchVerify::new();
    let strengthen = BinarySearchStrengthen;
    let backprop = ApplyAllBackprop;

    let (outcome, history) = run_loop(8, 2, &verify, &strengthen, &backprop);

    // The loop should verify in exactly 2 iterations:
    //   Iteration 0: overflow detected, strengthen proposes fix, backprop applies
    //   Iteration 1: all VCs pass -> Verified
    assert_eq!(
        outcome,
        LoopOutcome::Verified { iterations: 2, vcs_proved: 5 },
        "binary_search loop should converge to Verified in 2 iterations"
    );
    assert_eq!(history.len(), 2, "should have 2 frontier snapshots");

    // Iteration 0: 4 proved, 1 failed (overflow)
    assert_eq!(history[0].trusted, 4);
    assert_eq!(history[0].failed, 1);

    // Iteration 1: 5 proved, 0 failed
    assert_eq!(history[1].trusted, 5);
    assert_eq!(history[1].failed, 0);

    // Print summary for golden test visibility
    eprintln!("=== E2E Loop Golden Test: binary_search ===");
    eprintln!("  Iteration 0: trusted={}, failed={}", history[0].trusted, history[0].failed);
    eprintln!("  Iteration 1: trusted={}, failed={}", history[1].trusted, history[1].failed);
    eprintln!("  Outcome: {outcome:?}");
    eprintln!("=== PASSED ===");
}

// ===========================================================================
// Test: Strengthen proposals contain the safe midpoint fix
// ===========================================================================

#[test]
fn test_e2e_strengthen_proposes_safe_midpoint() {
    let strengthen = BinarySearchStrengthen;
    let overflow_output = VerifyOutput {
        frontier: ProofFrontier {
            trusted: 4,
            certified: 0,
            runtime_checked: 0,
            failed: 1,
            unknown: 0,
        },
        fingerprint: None,
        vcs_dispatched: 5,
        vcs_failed: 1,
    };

    let s_out = strengthen.strengthen(&overflow_output);

    assert!(s_out.has_proposals, "should produce proposals for failed VCs");
    assert_eq!(s_out.failures_analyzed, 1);

    // Check for the SafeArithmetic proposal
    let safe_arith = s_out
        .proposals
        .iter()
        .find(|p| matches!(&p.kind, ProposalKind::SafeArithmetic { replacement, .. } if replacement.contains("hi - lo")));
    assert!(
        safe_arith.is_some(),
        "should propose lo + (hi - lo) / 2 as safe arithmetic replacement"
    );

    // Check for the precondition proposal
    let precond = s_out
        .proposals
        .iter()
        .find(|p| matches!(&p.kind, ProposalKind::AddPrecondition { spec_body } if spec_body.contains("hi >= lo")));
    assert!(precond.is_some(), "should propose hi >= lo as a precondition");

    // All proposals should target binary_search
    for p in &s_out.proposals {
        assert_eq!(p.function_name, "binary_search");
        assert!(p.confidence > 0.8, "proposals should have high confidence");
    }
}

// ===========================================================================
// Test: Regression detection stops the loop
// ===========================================================================

#[test]
fn test_e2e_loop_detects_regression() {
    // Iteration 0: 4 proved, 1 failed
    // Iteration 1: 3 proved, 2 failed (regression!)
    let verify = SequenceVerify::new(vec![make_verify_output(4, 1), make_verify_output(3, 2)]);
    let strengthen = FixedStrengthen { proposal_count: 1 };
    let backprop = ApplyAllBackprop;

    let (outcome, history) = run_loop(10, 2, &verify, &strengthen, &backprop);

    assert_eq!(
        outcome,
        LoopOutcome::Diverged { iterations: 2 },
        "loop should detect regression and report Diverged"
    );
    assert_eq!(history.len(), 2);
    assert_eq!(history[0].trusted, 4, "first iteration had 4 proved");
    assert_eq!(history[1].trusted, 3, "second iteration regressed to 3 proved");
}

// ===========================================================================
// Test: Max iteration limit stops the loop
// ===========================================================================

#[test]
fn test_e2e_loop_respects_max_iterations() {
    // Each iteration improves but never reaches 0 failures.
    // With max_iterations=3, iteration 3 triggers IterationLimitReached.
    let verify = SequenceVerify::new(vec![
        make_verify_output(1, 4),
        make_verify_output(2, 3),
        make_verify_output(3, 2),
        make_verify_output(4, 1), // iteration index 3 >= limit 3
    ]);
    let strengthen = FixedStrengthen { proposal_count: 1 };
    let backprop = ApplyAllBackprop;

    let (outcome, history) = run_loop(3, 2, &verify, &strengthen, &backprop);

    assert_eq!(
        outcome,
        LoopOutcome::Timeout { iterations: 4, max_iterations: 3 },
        "loop should stop at iteration limit"
    );
    assert_eq!(history.len(), 4, "should have tried 4 iterations before limit");
}

// ===========================================================================
// Test: No proposals terminates with Refuted
// ===========================================================================

#[test]
fn test_e2e_loop_stops_when_no_proposals() {
    let verify = SequenceVerify::new(vec![make_verify_output(3, 2)]);
    let strengthen = EmptyStrengthen;
    let backprop = ApplyAllBackprop;

    let (outcome, history) = run_loop(10, 2, &verify, &strengthen, &backprop);

    assert_eq!(
        outcome,
        LoopOutcome::Refuted { iterations: 1, vcs_failed: 2, exhausted_proposals: true },
        "should report Refuted with exhausted_proposals when strengthen has nothing"
    );
    assert_eq!(history.len(), 1);
}

// ===========================================================================
// Test: Backprop failure (applies nothing) terminates with Refuted
// ===========================================================================

#[test]
fn test_e2e_loop_stops_when_backprop_fails() {
    let verify = SequenceVerify::new(vec![make_verify_output(3, 2)]);
    let strengthen = FixedStrengthen { proposal_count: 2 };
    let backprop = NoOpBackprop;

    let (outcome, _) = run_loop(10, 2, &verify, &strengthen, &backprop);

    assert_eq!(
        outcome,
        LoopOutcome::Refuted { iterations: 1, vcs_failed: 2, exhausted_proposals: true },
        "should report Refuted when backprop applies nothing"
    );
}

// ===========================================================================
// Test: Convergence (stable frontier) with failures -> Refuted
// ===========================================================================

#[test]
fn test_e2e_loop_converges_with_failures_is_refuted() {
    // Frontier stabilizes with 1 failure remaining: converge -> Refuted
    let verify = SequenceVerify::new(vec![
        make_verify_output(3, 2),
        make_verify_output(4, 1),
        make_verify_output(4, 1), // stable (same as iteration 1)
    ]);
    let strengthen = FixedStrengthen { proposal_count: 1 };
    let backprop = ApplyAllBackprop;

    let (outcome, history) = run_loop(10, 2, &verify, &strengthen, &backprop);

    assert_eq!(
        outcome,
        LoopOutcome::Refuted { iterations: 3, vcs_failed: 1, exhausted_proposals: false },
        "stable frontier with failures should be Refuted (not exhausted)"
    );
    assert_eq!(history.len(), 3);
    assert_eq!(history[2].failed, 1, "last frontier still has 1 failure");
}

// ===========================================================================
// Test: All proved on first pass
// ===========================================================================

#[test]
fn test_e2e_loop_all_proved_first_pass() {
    let verify = SequenceVerify::new(vec![make_verify_output(5, 0)]);
    let strengthen = EmptyStrengthen;
    let backprop = ApplyAllBackprop;

    let (outcome, history) = run_loop(10, 2, &verify, &strengthen, &backprop);

    assert_eq!(
        outcome,
        LoopOutcome::Verified { iterations: 1, vcs_proved: 5 },
        "all proved on first pass should return Verified with 1 iteration"
    );
    assert_eq!(history.len(), 1);
    assert_eq!(history[0].failed, 0);
}

// ===========================================================================
// Test: Multi-step convergence to verified
// ===========================================================================

#[test]
fn test_e2e_loop_gradual_improvement_to_verified() {
    // 3 iterations of gradual improvement before all VCs pass
    let verify = SequenceVerify::new(vec![
        make_verify_output(2, 3),
        make_verify_output(3, 2),
        make_verify_output(4, 1),
        make_verify_output(5, 0), // all proved on iteration 3
    ]);
    let strengthen = FixedStrengthen { proposal_count: 1 };
    let backprop = ApplyAllBackprop;

    let (outcome, history) = run_loop(10, 2, &verify, &strengthen, &backprop);

    assert_eq!(
        outcome,
        LoopOutcome::Verified { iterations: 4, vcs_proved: 5 },
        "gradual improvement should eventually reach Verified"
    );
    assert_eq!(history.len(), 4);
    // Verify monotonic improvement
    for i in 1..history.len() {
        assert!(
            history[i].trusted >= history[i - 1].trusted,
            "proof coverage should not decrease: iter {} ({}) < iter {} ({})",
            i,
            history[i].trusted,
            i - 1,
            history[i - 1].trusted,
        );
    }
}

// ===========================================================================
// Test: Convergence tracker integration (fingerprint-based)
// ===========================================================================

#[test]
fn test_e2e_loop_fingerprint_convergence() {
    let mut out1 = make_verify_output(4, 1);
    out1.fingerprint = Some("fp_abc".into());
    let mut out2 = make_verify_output(4, 1);
    out2.fingerprint = Some("fp_abc".into());

    let verify = SequenceVerify::new(vec![out1, out2]);
    let strengthen = FixedStrengthen { proposal_count: 1 };
    let backprop = ApplyAllBackprop;

    let (outcome, _) = run_loop(10, 2, &verify, &strengthen, &backprop);

    assert_eq!(
        outcome,
        LoopOutcome::Refuted { iterations: 2, vcs_failed: 1, exhausted_proposals: false },
        "same fingerprint should trigger convergence -> Refuted"
    );
}

// ===========================================================================
// Test: History tracks all iterations correctly
// ===========================================================================

#[test]
fn test_e2e_loop_history_fidelity() {
    let verify = SequenceVerify::new(vec![
        make_verify_output(1, 4),
        make_verify_output(3, 2),
        make_verify_output(5, 0),
    ]);
    let strengthen = FixedStrengthen { proposal_count: 2 };
    let backprop = ApplyAllBackprop;

    let (_, history) = run_loop(10, 2, &verify, &strengthen, &backprop);

    assert_eq!(history.len(), 3, "should record 3 iterations");
    assert_eq!(history[0].trusted, 1);
    assert_eq!(history[0].failed, 4);
    assert_eq!(history[1].trusted, 3);
    assert_eq!(history[1].failed, 2);
    assert_eq!(history[2].trusted, 5);
    assert_eq!(history[2].failed, 0);
}

// ===========================================================================
// Trust: Integration tests for trust-loop crate
//
// These tests exercise trust_loop::run_iterative_verification directly,
// bridging the crate into the integration test suite.
// ===========================================================================

/// Trust: Helper to build a VerificationCondition for trust-loop integration tests.
fn make_vc(function: &str, kind: VcKind, formula_name: &str) -> VerificationCondition {
    VerificationCondition {
        function: function.into(),
        kind,
        location: SourceSpan::default(),
        formula: Formula::Var(formula_name.to_string(), Sort::Bool),
        contract_metadata: None,
        obligation: None,
    }
}

fn make_proved() -> VerificationResult {
    VerificationResult::Proved {
        solver: "constant-folder".into(),
        strength: ProofStrength::smt_unsat(),
        time_ms: 1,
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    }
}

fn make_failed() -> VerificationResult {
    VerificationResult::Failed { solver: "constant-folder".into(), counterexample: None, time_ms: 1 }
}

// Trust: VerifyContext implementation for trust-loop integration tests.
// Delegates to pre-programmed step sequences, similar to the mock in trust-loop
// unit tests but exercised from an integration test context.
struct IntegrationVerifyContext {
    verify_steps: Vec<Vec<(VerificationCondition, VerificationResult)>>,
    strengthen_steps: Vec<Vec<VerificationCondition>>,
    verify_calls: Cell<usize>,
    strengthen_calls: Cell<usize>,
}

impl IntegrationVerifyContext {
    fn new(
        verify_steps: Vec<Vec<(VerificationCondition, VerificationResult)>>,
        strengthen_steps: Vec<Vec<VerificationCondition>>,
    ) -> Self {
        Self {
            verify_steps,
            strengthen_steps,
            verify_calls: Cell::new(0),
            strengthen_calls: Cell::new(0),
        }
    }
}

impl VerifyContext for IntegrationVerifyContext {
    fn verify_vcs(
        &self,
        _vcs: &[VerificationCondition],
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        let idx = self.verify_calls.get();
        self.verify_calls.set(idx + 1);
        self.verify_steps[idx.min(self.verify_steps.len().saturating_sub(1))].clone()
    }

    fn strengthen_specs(
        &self,
        _failed: &[(VerificationCondition, VerificationResult)],
    ) -> Vec<VerificationCondition> {
        let idx = self.strengthen_calls.get();
        self.strengthen_calls.set(idx + 1);
        if self.strengthen_steps.is_empty() {
            return Vec::new();
        }
        self.strengthen_steps[idx.min(self.strengthen_steps.len() - 1)].clone()
    }
}

// ===========================================================================
// Test: trust-loop all-proved on first pass (integration)
// ===========================================================================

#[test]
fn test_trust_loop_integration_all_proved_first_pass() {
    let vc_a = make_vc("crate::safe_div", VcKind::DivisionByZero, "vc_a");
    let vc_b = make_vc(
        "crate::checked",
        VcKind::Assertion { message: "postcondition".to_string() },
        "vc_b",
    );
    let ctx = IntegrationVerifyContext::new(
        vec![vec![(vc_a.clone(), make_proved()), (vc_b.clone(), make_proved())]],
        vec![],
    );

    let result =
        trust_loop::run_iterative_verification(&LoopConfig::default(), vec![vc_a, vc_b], &ctx);

    assert_eq!(result.iterations, 1);
    assert_eq!(result.reason, trust_loop::TerminationReason::AllProved);
    assert_eq!(result.final_proved, 2);
    assert_eq!(result.final_failed, 0);
    assert_eq!(result.final_unknown, 0);
    assert_eq!(result.final_results.len(), 2, "should carry paired (VC, result) tuples");
}

// ===========================================================================
// Test: trust-loop converges after strengthening (integration)
// ===========================================================================

#[test]
fn test_trust_loop_integration_converges_after_strengthening() {
    let vc_a =
        make_vc("crate::alpha", VcKind::Assertion { message: "bounds".to_string() }, "alpha_0");
    let vc_b = make_vc("crate::beta", VcKind::DivisionByZero, "beta_0");

    // After strengthening, alpha proves but beta remains failed.
    let vc_a_strengthened =
        make_vc("crate::alpha", VcKind::Assertion { message: "bounds".to_string() }, "alpha_1");

    let ctx = IntegrationVerifyContext::new(
        vec![
            vec![(vc_a.clone(), make_failed()), (vc_b.clone(), make_failed())],
            vec![(vc_a_strengthened.clone(), make_proved()), (vc_b.clone(), make_failed())],
            vec![(vc_b.clone(), make_failed())], // stable: converges
        ],
        vec![vec![vc_a_strengthened]],
    );

    let config = LoopConfig {
        max_iterations: 5,
        stable_round_limit: 2,
        enable_strengthen: true,
        futility: None,
        verdict_config: Default::default(),
    };

    let result = trust_loop::run_iterative_verification(&config, vec![vc_a, vc_b], &ctx);

    assert_eq!(result.iterations, 3);
    assert_eq!(result.reason, trust_loop::TerminationReason::Stalled { stable_rounds: 2 });
    assert_eq!(result.final_proved, 1, "alpha should be proved");
    assert_eq!(result.final_failed, 1, "beta should remain failed");
    assert_eq!(result.history.len(), 3, "should record 3 iterations");
}

// ===========================================================================
// Test: trust-loop with analysis module (integration)
// ===========================================================================

#[test]
fn test_trust_loop_analysis_integration() {
    use trust_loop::analysis::{
        FixpointConfig, LoopCharacteristic, MetricSnapshot, classify_loop, convergence_rate,
        detect_fixpoint, detect_regressions,
    };

    // Build a realistic improving sequence matching a verification loop trajectory
    let snapshots = vec![
        MetricSnapshot::new(1, 2, 5, 3),
        MetricSnapshot::new(2, 4, 3, 3),
        MetricSnapshot::new(3, 6, 2, 2),
        MetricSnapshot::new(4, 8, 1, 1),
    ];

    // Verify classification
    let characteristic = classify_loop(&snapshots);
    assert_eq!(characteristic, LoopCharacteristic::Converging);

    // Verify no regressions
    let regressions = detect_regressions(&snapshots);
    assert!(regressions.is_empty(), "improving sequence should have no regressions");

    // Verify convergence rate
    let rate = convergence_rate(&snapshots, 1.0);
    assert!(rate.avg_improvement > 0.0, "improving sequence should have positive rate");
    assert!(rate.estimated_remaining.is_some(), "should estimate remaining iterations");

    // Verify no premature fixpoint
    let fp_config = FixpointConfig::default();
    assert!(
        detect_fixpoint(&snapshots, &fp_config).is_none(),
        "improving sequence should not be detected as fixpoint"
    );
}

// ===========================================================================
// Test: trust-loop scheduling integration
// ===========================================================================

#[test]
fn test_trust_loop_scheduling_integration() {
    use trust_loop::scheduling::{
        IterationBudget, SchedulerState, SchedulingPolicy, VerificationCandidate,
    };

    // Build candidates matching a realistic verification workload
    let candidates = vec![
        VerificationCandidate {
            function: "crate::safe_div".into(),
            difficulty_estimate: 0.3,
            past_failures: 0,
            vc_count: 2,
        },
        VerificationCandidate {
            function: "crate::binary_search".into(),
            difficulty_estimate: 0.8,
            past_failures: 3,
            vc_count: 5,
        },
        VerificationCandidate {
            function: "crate::sort".into(),
            difficulty_estimate: 0.9,
            past_failures: 1,
            vc_count: 10,
        },
    ];

    let budget = IterationBudget::default();
    let mut scheduler = SchedulerState::new(SchedulingPolicy::PriorityBased, budget, candidates);

    // Priority-based should schedule hardest/most-failed first
    let first = scheduler.schedule_next().expect("should have candidates");
    assert_eq!(
        first.function, "crate::binary_search",
        "binary_search has highest priority (3 failures, 0.8 difficulty)"
    );

    // Should not pause yet (no resources consumed)
    assert!(scheduler.should_pause().is_none(), "should not pause at start");

    // Record some work
    scheduler.record_solver_calls(50);
    scheduler.record_iteration();
    assert_eq!(scheduler.iterations_completed(), 1);
    assert_eq!(scheduler.solver_calls_used(), 50);
}

// ===========================================================================
// Test: trust-loop no-progress terminates (integration)
// ===========================================================================

#[test]
fn test_trust_loop_integration_no_progress_terminates() {
    let vc = make_vc("crate::stuck", VcKind::DivisionByZero, "stuck_0");

    let ctx = IntegrationVerifyContext::new(
        vec![vec![(vc.clone(), make_failed())]],
        vec![], // no strengthen steps
    );

    // With strengthening disabled, a single failure should immediately terminate
    let config = LoopConfig {
        max_iterations: 5,
        stable_round_limit: 2,
        enable_strengthen: false,
        futility: None,
        verdict_config: Default::default(),
    };

    let result = trust_loop::run_iterative_verification(&config, vec![vc], &ctx);

    assert_eq!(result.iterations, 1);
    assert_eq!(result.reason, trust_loop::TerminationReason::NoProgress);
    assert_eq!(result.final_failed, 1);
}
