// dead_code audit: crate-level suppression removed
//! trust-loop: Iterative verification over in-memory verification conditions.
//!
//! This crate keeps the orchestration logic separate from the compiler pass:
//! callers feed VCs from `trust_vcgen`, route them however they want, and
//! optionally produce strengthened replacement VCs for another round.

pub mod analysis;
pub(crate) mod futility;
pub(crate) mod iteration_metrics;
pub mod scheduling;
pub(crate) mod vc_tracker;

use std::collections::BTreeMap;

use trust_convergence::{
    ConvergenceDecision, ConvergenceTracker, ConvergenceVerdict, IterationSnapshot, ProofFrontier,
    VerdictConfig,
};
use trust_types::{SourceSpan, VerificationCondition, VerificationResult};

pub use crate::futility::{FutilityConfig, FutilityReason};
pub use crate::iteration_metrics::IterationMetrics;
pub use crate::vc_tracker::{RegressionEvent, VcStatus};

use crate::futility::FutilityDetector;
use crate::iteration_metrics::MetricsBuilder;
use crate::vc_tracker::VcTracker;

/// Configuration for iterative verification.
#[derive(Debug, Clone)]
pub struct LoopConfig {
    /// Maximum number of verification rounds.
    pub max_iterations: u32,
    /// Number of stable rounds before the frontier is considered converged.
    pub stable_round_limit: usize,
    /// Whether failed VCs should be sent through strengthening.
    pub enable_strengthen: bool,
    /// Futility detection configuration. When `None`, futility detection is disabled.
    pub futility: Option<FutilityConfig>,
    /// Convergence verdict configuration (stall threshold).
    pub verdict_config: VerdictConfig,
}

impl Default for LoopConfig {
    fn default() -> Self {
        Self {
            max_iterations: 5,
            stable_round_limit: 2,
            enable_strengthen: true,
            futility: Some(FutilityConfig::default()),
            verdict_config: VerdictConfig::default(),
        }
    }
}

/// Summary of one verification round.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IterationRecord {
    pub iteration: u32,
    pub proved: usize,
    pub failed: usize,
    pub unknown: usize,
    pub strengthened: usize,
}

/// Overall loop result.
#[derive(Debug, Clone)]
pub struct LoopResult {
    pub iterations: u32,
    pub reason: TerminationReason,
    pub final_proved: usize,
    pub final_failed: usize,
    pub final_unknown: usize,
    pub history: Vec<IterationRecord>,
    /// Paired (VC, result) from the final iteration. Consumers use these
    /// directly instead of re-dispatching to the solver.
    pub final_results: Vec<(VerificationCondition, VerificationResult)>,
    /// Enriched per-iteration metrics (parallel to `history`).
    pub metrics_history: Vec<IterationMetrics>,
    /// Per-VC regression events detected during the loop.
    pub regression_events: Vec<RegressionEvent>,
    /// High-level convergence verdict from the convergence tracker.
    pub verdict: ConvergenceVerdict,
}

/// Why the loop stopped.
#[derive(Debug, Clone, PartialEq)]
pub enum TerminationReason {
    AllProved,
    /// the frontier was stable across `stable_rounds`
    /// iterations but is NOT necessarily all-proved — unproved or failed
    /// obligations may remain. The proof verdict comes from `verdict` /
    /// `final_results`, never from this reason. (Deliberately distinct from
    /// `ConvergenceVerdict::Converged`, which *does* mean all-proved; the old
    /// name `Converged` here invited exactly that confusion.)
    Stalled {
        stable_rounds: usize,
    },
    IterationLimit {
        iterations: u32,
    },
    Regressed,
    NoProgress,
    /// The futility detector determined further iterations are unlikely to help.
    Futility {
        reason: FutilityReason,
    },
}

/// Host hooks required by the loop.
pub trait VerifyContext {
    fn verify_vcs(
        &self,
        vcs: &[VerificationCondition],
    ) -> Vec<(VerificationCondition, VerificationResult)>;

    fn strengthen_specs(
        &self,
        failed: &[(VerificationCondition, VerificationResult)],
    ) -> Vec<VerificationCondition>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ObligationStatus {
    Proved,
    Failed,
    Unknown,
}

impl ObligationStatus {
    fn from_result(result: &VerificationResult) -> Self {
        match result {
            VerificationResult::Proved { .. } => Self::Proved,
            VerificationResult::Failed { .. } => Self::Failed,
            VerificationResult::Unknown { .. } | VerificationResult::Timeout { .. } => {
                Self::Unknown
            }
            _ => Self::Unknown,
        }
    }

    fn as_tag(self) -> char {
        match self {
            Self::Proved => 'P',
            Self::Failed => 'F',
            Self::Unknown => 'U',
        }
    }

    fn is_proved(self) -> bool {
        matches!(self, Self::Proved)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct StatusCounts {
    proved: usize,
    failed: usize,
    unknown: usize,
}

impl StatusCounts {
    fn all_proved(self) -> bool {
        self.failed == 0 && self.unknown == 0
    }

    fn frontier(self) -> ProofFrontier {
        ProofFrontier {
            trusted: self.proved as u32,
            certified: 0,
            runtime_checked: 0,
            failed: self.failed as u32,
            unknown: self.unknown as u32,
        }
    }
}

#[derive(Debug, Clone)]
struct MergeOutcome {
    vcs: Vec<VerificationCondition>,
    applied: usize,
}

/// Run the in-memory verification loop until it converges or stops making progress.
///
/// Integrates fixed-point detection from `trust-convergence`, per-VC tracking
/// via `VcTracker`, futility detection, and enriched iteration metrics.
#[must_use]
pub fn run_iterative_verification(
    config: &LoopConfig,
    initial_vcs: Vec<VerificationCondition>,
    ctx: &dyn VerifyContext,
) -> LoopResult {
    let max_iterations = config.max_iterations.max(1);
    let stable_round_limit = config.stable_round_limit.max(1);
    let mut tracker = ConvergenceTracker::new(stable_round_limit, max_iterations)
        .with_verdict_config(config.verdict_config.clone());
    let futility_detector = config.futility.as_ref().map(|c| FutilityDetector::new(c.clone()));
    let mut vc_tracker = VcTracker::new();
    let mut active_vcs = initial_vcs;
    // the full VC set (kept in sync with strengthenings), so
    // an AllProved claim can be confirmed by re-verifying EVERY VC in the current
    // context — not by trusting carried-forward statuses for VCs that were dropped
    // from `active_vcs` after proving and never re-verified post-strengthen.
    let mut all_vcs = active_vcs.clone();
    let mut carried_statuses = BTreeMap::new();
    let mut history = Vec::new();
    let mut metrics_history = Vec::new();
    let mut all_regression_events = Vec::new();
    let mut iteration = 1u32;
    let mut prev_counts: Option<StatusCounts> = None;

    loop {
        let mut results = ctx.verify_vcs(&active_vcs);

        let mut statuses = update_statuses(&carried_statuses, &results);
        let mut counts = count_statuses(&statuses);

        if counts.all_proved() {
            // a sound AllProved requires every counted VC to
            // have been verified in the CURRENT iteration. `counts` can include a
            // status CARRIED FORWARD by `update_statuses` -- a VC proved earlier,
            // dropped from `active_vcs`, and not re-verified after an intervening
            // strengthen. If the AllProved relies on any such carried status, it
            // must be confirmed by re-verifying the FULL VC set (with
            // strengthenings) in the current context; only the full re-verification
            // result is trusted from this point on.
            let relies_on_carried = statuses
                .keys()
                .any(|k| !results.iter().any(|(vc, _)| &vc_slot_key(vc) == k));
            if relies_on_carried {
                let revalidation = ctx.verify_vcs(&all_vcs);
                let revalidation_statuses = update_statuses(&BTreeMap::new(), &revalidation);
                counts = count_statuses(&revalidation_statuses);
                statuses = revalidation_statuses;
                results = revalidation;
            }
        }

        // Track per-VC statuses for regression detection and delta computation.
        vc_tracker.record_results(iteration, &results);
        let vc_delta = vc_tracker.compute_delta(iteration);
        let iter_regressions = vc_tracker.detect_regressions(iteration);
        all_regression_events.extend(iter_regressions);

        let frontier = counts.frontier();
        let snapshot = IterationSnapshot::new(iteration, frontier)
            .with_fingerprint(status_fingerprint(&statuses));
        let decision = tracker.observe(snapshot);
        carried_statuses = statuses;

        let failed = failed_results(&results);
        let mut record = IterationRecord {
            iteration,
            proved: counts.proved,
            failed: counts.failed,
            unknown: counts.unknown,
            strengthened: 0,
        };

        // Build enriched metrics for this iteration.
        let metrics = MetricsBuilder::new(iteration)
            .counts(counts.proved, counts.failed, counts.unknown, 0)
            .deltas(vc_delta.newly_proved, vc_delta.newly_failed, vc_delta.regressions)
            .build();
        metrics_history.push(metrics);

        // Helper: finalize and return a LoopResult.
        macro_rules! finish {
            ($reason:expr) => {{
                history.push(record);
                return LoopResult {
                    iterations: iteration,
                    reason: $reason,
                    final_proved: counts.proved,
                    final_failed: counts.failed,
                    final_unknown: counts.unknown,
                    history,
                    final_results: results,
                    metrics_history,
                    regression_events: all_regression_events,
                    verdict: tracker.verdict(),
                };
            }};
        }

        if counts.all_proved() {
            finish!(TerminationReason::AllProved);
        }

        // Detect non-monotonic regression: proved count decreased or
        // failed/unknown count increased compared to the previous iteration.
        if let Some(prev) = prev_counts
            && (counts.proved < prev.proved
                || counts.failed > prev.failed
                || counts.unknown > prev.unknown)
        {
            finish!(TerminationReason::Regressed);
        }

        match decision {
            ConvergenceDecision::Converged { stable_rounds, .. } => {
                finish!(TerminationReason::Stalled { stable_rounds });
            }
            ConvergenceDecision::IterationLimitReached { .. } => {
                finish!(TerminationReason::IterationLimit { iterations: iteration });
            }
            ConvergenceDecision::Regressed { .. } => {
                finish!(TerminationReason::Regressed);
            }
            ConvergenceDecision::Continue { .. } => {}
        }

        // Futility detection: check if further iterations are unlikely to help.
        if let Some(ref detector) = futility_detector
            && let Some(reason) = detector.should_stop(&metrics_history)
        {
            finish!(TerminationReason::Futility { reason });
        }

        if !config.enable_strengthen || failed.is_empty() {
            finish!(TerminationReason::NoProgress);
        }

        let strengthened = ctx.strengthen_specs(&failed);
        let merge = merge_unproved_vcs(unproved_vcs(&results), strengthened.clone());
        // Keep the full VC set in sync with the strengthenings so the AllProved
        // re-verification above checks the current (strengthened) formulas.
        all_vcs = merge_unproved_vcs(all_vcs, strengthened).vcs;
        record.strengthened = merge.applied;

        // Update the last metrics entry with strengthening info.
        if let Some(last_metrics) = metrics_history.last_mut() {
            last_metrics.strengthened = merge.applied;
            last_metrics.proposals_applied = merge.applied;
        }

        history.push(record);

        if merge.applied == 0 {
            return LoopResult {
                iterations: iteration,
                reason: TerminationReason::NoProgress,
                final_proved: counts.proved,
                final_failed: counts.failed,
                final_unknown: counts.unknown,
                history,
                final_results: results,
                metrics_history,
                regression_events: all_regression_events,
                verdict: tracker.verdict(),
            };
        }

        active_vcs = merge.vcs;
        prev_counts = Some(counts);
        iteration += 1;
    }
}

fn update_statuses(
    previous: &BTreeMap<String, ObligationStatus>,
    results: &[(VerificationCondition, VerificationResult)],
) -> BTreeMap<String, ObligationStatus> {
    let mut statuses = previous
        .iter()
        .filter_map(|(key, status)| status.is_proved().then_some((key.clone(), *status)))
        .collect::<BTreeMap<_, _>>();

    for (vc, result) in results {
        statuses.insert(vc_slot_key(vc), ObligationStatus::from_result(result));
    }

    statuses
}

fn count_statuses(statuses: &BTreeMap<String, ObligationStatus>) -> StatusCounts {
    let mut counts = StatusCounts { proved: 0, failed: 0, unknown: 0 };

    for status in statuses.values().copied() {
        match status {
            ObligationStatus::Proved => counts.proved += 1,
            ObligationStatus::Failed => counts.failed += 1,
            ObligationStatus::Unknown => counts.unknown += 1,
        }
    }

    counts
}

fn failed_results(
    results: &[(VerificationCondition, VerificationResult)],
) -> Vec<(VerificationCondition, VerificationResult)> {
    results
        .iter()
        .filter(|(_, result)| matches!(result, VerificationResult::Failed { .. }))
        .cloned()
        .collect()
}

fn unproved_vcs(
    results: &[(VerificationCondition, VerificationResult)],
) -> Vec<VerificationCondition> {
    results
        .iter()
        .filter(|(_, result)| !matches!(result, VerificationResult::Proved { .. }))
        .map(|(vc, _)| vc.clone())
        .collect()
}

fn merge_unproved_vcs(
    unproved: Vec<VerificationCondition>,
    strengthened: Vec<VerificationCondition>,
) -> MergeOutcome {
    let mut merged = Vec::with_capacity(unproved.len() + strengthened.len());
    let mut positions = BTreeMap::new();

    for vc in unproved {
        let key = vc_slot_key(&vc);
        positions.insert(key, merged.len());
        merged.push(vc);
    }

    let mut applied = 0;
    for vc in strengthened {
        let key = vc_slot_key(&vc);
        let value_fingerprint = vc_value_fingerprint(&vc);

        if let Some(index) = positions.get(&key).copied() {
            if vc_value_fingerprint(&merged[index]) != value_fingerprint {
                merged[index] = vc;
                applied += 1;
            }
        } else {
            positions.insert(key, merged.len());
            merged.push(vc);
            applied += 1;
        }
    }

    MergeOutcome { vcs: merged, applied }
}

fn status_fingerprint(statuses: &BTreeMap<String, ObligationStatus>) -> String {
    let mut fingerprint = String::new();

    for (key, status) in statuses {
        fingerprint.push_str(key);
        fingerprint.push(':');
        fingerprint.push(status.as_tag());
        fingerprint.push('|');
    }

    fingerprint
}

fn vc_slot_key(vc: &VerificationCondition) -> String {
    format!("{}|{}|{}", vc.function, span_key(&vc.location), vc.kind.description())
}

fn vc_value_fingerprint(vc: &VerificationCondition) -> String {
    format!("{}|{:?}", vc_slot_key(vc), vc.formula)
}

fn span_key(span: &SourceSpan) -> String {
    format!(
        "{}:{}:{}:{}:{}",
        span.file, span.line_start, span.col_start, span.line_end, span.col_end
    )
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;

    use super::*;
    use trust_types::{Formula, ProofStrength, Sort, VcKind};

    struct MockVerifyContext {
        verify_steps: Vec<Vec<(VerificationCondition, VerificationResult)>>,
        strengthen_steps: Vec<Vec<VerificationCondition>>,
        verify_calls: Cell<usize>,
        strengthen_calls: Cell<usize>,
    }

    impl MockVerifyContext {
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

        fn verify_call_count(&self) -> usize {
            self.verify_calls.get()
        }

        fn strengthen_call_count(&self) -> usize {
            self.strengthen_calls.get()
        }

        fn verify_step(&self) -> Vec<(VerificationCondition, VerificationResult)> {
            let idx = self.verify_calls.get();
            self.verify_calls.set(idx + 1);
            self.verify_steps[idx.min(self.verify_steps.len().saturating_sub(1))].clone()
        }

        fn strengthen_step(&self) -> Vec<VerificationCondition> {
            let idx = self.strengthen_calls.get();
            self.strengthen_calls.set(idx + 1);
            if self.strengthen_steps.is_empty() {
                return Vec::new();
            }
            self.strengthen_steps[idx.min(self.strengthen_steps.len() - 1)].clone()
        }
    }

    impl VerifyContext for MockVerifyContext {
        fn verify_vcs(
            &self,
            _vcs: &[VerificationCondition],
        ) -> Vec<(VerificationCondition, VerificationResult)> {
            self.verify_step()
        }

        fn strengthen_specs(
            &self,
            _failed: &[(VerificationCondition, VerificationResult)],
        ) -> Vec<VerificationCondition> {
            self.strengthen_step()
        }
    }

    fn vc(function: &str, kind: VcKind, formula_name: &str) -> VerificationCondition {
        VerificationCondition {
            function: function.into(),
            kind,
            location: SourceSpan::default(),
            formula: Formula::Var(formula_name.to_string(), Sort::Bool),
            contract_metadata: None,
        }
    }

    fn div_zero(function: &str, formula_name: &str) -> VerificationCondition {
        vc(function, VcKind::DivisionByZero, formula_name)
    }

    fn assertion(function: &str, message: &str, formula_name: &str) -> VerificationCondition {
        vc(function, VcKind::Assertion { message: message.to_string() }, formula_name)
    }

    fn proved() -> VerificationResult {
        VerificationResult::Proved {
            solver: "ay".into(),
            strength: ProofStrength::smt_unsat(),
            time_ms: 1,
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    fn failed() -> VerificationResult {
        VerificationResult::Failed { solver: "ay".into(), counterexample: None, time_ms: 1 }
    }

    fn unknown(reason: &str) -> VerificationResult {
        VerificationResult::Unknown {
            solver: "ay".into(),
            reason: reason.to_string(),
            time_ms: 1,
        }
    }

    fn final_status(
        result: &LoopResult,
        vc: &VerificationCondition,
    ) -> Option<ObligationStatus> {
        let expected_key = vc_slot_key(vc);
        result
            .final_results
            .iter()
            .find(|(actual, _)| vc_slot_key(actual) == expected_key)
            .map(|(_, verification)| ObligationStatus::from_result(verification))
    }

    #[test]
    fn test_all_proved_first_pass() {
        let vc_a = div_zero("crate::safe_div", "vc_a");
        let vc_b = assertion("crate::checked", "postcondition", "vc_b");
        let ctx = MockVerifyContext::new(
            vec![vec![(vc_a.clone(), proved()), (vc_b.clone(), proved())]],
            vec![],
        );

        let result = run_iterative_verification(&LoopConfig::default(), vec![vc_a, vc_b], &ctx);

        assert_eq!(result.iterations, 1);
        assert_eq!(result.reason, TerminationReason::AllProved);
        assert_eq!(result.final_proved, 2);
        assert_eq!(result.final_failed, 0);
        assert_eq!(result.final_unknown, 0);
        assert_eq!(
            result.history,
            vec![IterationRecord {
                iteration: 1,
                proved: 2,
                failed: 0,
                unknown: 0,
                strengthened: 0,
            }]
        );
        assert_eq!(ctx.verify_call_count(), 1);
        assert_eq!(ctx.strengthen_call_count(), 0);
    }

    #[test]
    fn test_converges_after_iterations() {
        let vc_a = assertion("crate::alpha", "bounds", "alpha_0");
        let vc_b = div_zero("crate::beta", "beta_0");
        let vc_a_strengthened = assertion("crate::alpha", "bounds", "alpha_1");
        let vc_b_strengthened = div_zero("crate::beta", "beta_1");
        let ctx = MockVerifyContext::new(
            vec![
                vec![(vc_a.clone(), failed()), (vc_b.clone(), failed())],
                vec![(vc_a_strengthened.clone(), proved()), (vc_b.clone(), failed())],
                vec![(vc_b_strengthened.clone(), failed())],
            ],
            vec![vec![vc_a_strengthened], vec![vc_b_strengthened]],
        );
        let config = LoopConfig {
            max_iterations: 5,
            stable_round_limit: 2,
            enable_strengthen: true,
            ..LoopConfig::default()
        };

        let result = run_iterative_verification(&config, vec![vc_a, vc_b], &ctx);

        assert_eq!(result.iterations, 3);
        assert_eq!(result.reason, TerminationReason::Stalled { stable_rounds: 2 });
        assert_eq!(result.final_proved, 1);
        assert_eq!(result.final_failed, 1);
        assert_eq!(result.final_unknown, 0);
        assert_eq!(result.history.len(), 3);
        assert_eq!(result.history[0].strengthened, 1);
        assert_eq!(result.history[1].strengthened, 1);
        assert_eq!(result.history[2].strengthened, 0);
        assert_eq!(ctx.verify_call_count(), 3);
        assert_eq!(ctx.strengthen_call_count(), 2);
    }

    #[test]
    fn test_iteration_limit() {
        let vc_a = assertion("crate::gamma", "overflow", "gamma_0");
        let vc_b = div_zero("crate::delta", "delta_0");
        let vc_c = assertion("crate::epsilon", "invariant", "epsilon_0");
        let vc_a_strengthened = assertion("crate::gamma", "overflow", "gamma_1");
        let vc_b_strengthened = div_zero("crate::delta", "delta_1");
        let ctx = MockVerifyContext::new(
            vec![
                vec![(vc_a.clone(), failed()), (vc_b.clone(), failed()), (vc_c.clone(), failed())],
                vec![
                    (vc_a_strengthened.clone(), proved()),
                    (vc_b.clone(), failed()),
                    (vc_c.clone(), failed()),
                ],
                vec![(vc_b_strengthened.clone(), proved()), (vc_c.clone(), failed())],
            ],
            vec![vec![vc_a_strengthened], vec![vc_b_strengthened]],
        );
        let config = LoopConfig {
            max_iterations: 3,
            stable_round_limit: 4,
            enable_strengthen: true,
            ..LoopConfig::default()
        };

        let result = run_iterative_verification(&config, vec![vc_a, vc_b, vc_c], &ctx);

        assert_eq!(result.iterations, 3);
        assert_eq!(result.reason, TerminationReason::IterationLimit { iterations: 3 });
        assert_eq!(result.final_proved, 2);
        assert_eq!(result.final_failed, 1);
        assert_eq!(result.final_unknown, 0);
        assert_eq!(ctx.verify_call_count(), 3);
        assert_eq!(ctx.strengthen_call_count(), 2);
    }

    #[test]
    fn test_regression_detected_when_strengthen_makes_worse() {
        // Iteration 1: 1 proved, 1 failed out of 2 VCs.
        // Strengthen replaces the failed VC.
        // Iteration 2: 0 proved, 2 failed -- the previously proved VC now fails.
        // This is a non-monotonic regression and should terminate immediately.
        let vc_a = div_zero("crate::regress_a", "a_0");
        let vc_b = assertion("crate::regress_b", "postcond", "b_0");
        let vc_b_strengthened = assertion("crate::regress_b", "postcond", "b_1");
        let ctx = MockVerifyContext::new(
            vec![
                // Iteration 1: vc_a proved, vc_b failed
                vec![(vc_a.clone(), proved()), (vc_b.clone(), failed())],
                // Iteration 2: both fail (regression -- vc_a was proved before)
                vec![(vc_a.clone(), failed()), (vc_b_strengthened.clone(), failed())],
            ],
            vec![vec![vc_b_strengthened]],
        );
        let config = LoopConfig {
            max_iterations: 5,
            stable_round_limit: 3,
            enable_strengthen: true,
            ..LoopConfig::default()
        };

        let result = run_iterative_verification(&config, vec![vc_a, vc_b], &ctx);

        assert_eq!(result.iterations, 2);
        assert_eq!(result.reason, TerminationReason::Regressed);
        // After regression: 0 proved (vc_a regressed), 2 failed
        assert_eq!(result.final_proved, 0);
        assert_eq!(result.final_failed, 2);
        assert_eq!(result.history.len(), 2);
        assert_eq!(result.history[0].proved, 1, "iteration 1 should have 1 proved");
        assert_eq!(result.history[1].proved, 0, "iteration 2 should have 0 proved (regression)");
        assert_eq!(ctx.verify_call_count(), 2);
        assert_eq!(ctx.strengthen_call_count(), 1);
    }

    #[test]
    fn test_regression_detected_when_unknown_increases() {
        // Regression: a previously-proved VC becomes unknown after strengthening
        // of a different VC. proved stays the same but unknown increases.
        let vc_a = div_zero("crate::u_inc_a", "a_0");
        let vc_b = assertion("crate::u_inc_b", "post", "b_0");
        let vc_c = assertion("crate::u_inc_c", "inv", "c_0");
        let vc_b_strengthened = assertion("crate::u_inc_b", "post", "b_1");
        let ctx = MockVerifyContext::new(
            vec![
                // Iteration 1: vc_a proved, vc_b failed, vc_c proved
                vec![(vc_a.clone(), proved()), (vc_b.clone(), failed()), (vc_c.clone(), proved())],
                // Iteration 2: vc_b_strengthened now proved, but vc_c becomes unknown
                // proved: 2 (a carried, b_strengthened), failed: 0, unknown: 1 (c)
                // prev:   proved: 2, failed: 1, unknown: 0
                // unknown increased from 0 to 1 -> regression
                vec![
                    (vc_b_strengthened.clone(), proved()),
                    (vc_c.clone(), unknown("timeout")),
                ],
            ],
            vec![vec![vc_b_strengthened]],
        );
        let config = LoopConfig {
            max_iterations: 5,
            stable_round_limit: 3,
            enable_strengthen: true,
            ..LoopConfig::default()
        };

        let result = run_iterative_verification(&config, vec![vc_a, vc_b, vc_c], &ctx);

        assert_eq!(result.iterations, 2);
        assert_eq!(result.reason, TerminationReason::Regressed);
        // vc_a proved (carried), vc_b_strengthened proved, vc_c unknown
        assert_eq!(result.final_proved, 2);
        assert_eq!(result.final_unknown, 1);
        assert_eq!(result.final_failed, 0);
    }

    #[test]
    fn test_all_proved_revalidation_failed_replaces_carried_results() {
        let vc_a = div_zero("crate::carried_fail_a", "a_0");
        let vc_b = assertion("crate::carried_fail_b", "post", "b_0");
        let vc_b_strengthened = assertion("crate::carried_fail_b", "post", "b_1");
        let ctx = MockVerifyContext::new(
            vec![
                vec![(vc_a.clone(), proved()), (vc_b.clone(), failed())],
                vec![(vc_b_strengthened.clone(), proved())],
                vec![(vc_a.clone(), failed()), (vc_b_strengthened.clone(), proved())],
            ],
            vec![vec![vc_b_strengthened.clone()]],
        );

        let result = run_iterative_verification(
            &LoopConfig::default(),
            vec![vc_a.clone(), vc_b],
            &ctx,
        );

        assert_ne!(result.reason, TerminationReason::AllProved);
        assert_ne!(result.verdict, ConvergenceVerdict::Converged);
        assert_eq!(result.final_proved, 1);
        assert_eq!(result.final_failed, 1);
        assert_eq!(result.final_unknown, 0);
        assert_eq!(result.final_results.len(), 2);
        assert_eq!(final_status(&result, &vc_a), Some(ObligationStatus::Failed));
        assert_eq!(
            final_status(&result, &vc_b_strengthened),
            Some(ObligationStatus::Proved)
        );
        assert_eq!(
            result.history[1],
            IterationRecord {
                iteration: 2,
                proved: 1,
                failed: 1,
                unknown: 0,
                strengthened: 0,
            }
        );
        assert_eq!(result.metrics_history[1].proved, 1);
        assert_eq!(result.metrics_history[1].failed, 1);
        assert_eq!(result.metrics_history[1].unknown, 0);
        assert_eq!(ctx.verify_call_count(), 3);
        assert_eq!(ctx.strengthen_call_count(), 1);
    }

    #[test]
    fn test_all_proved_revalidation_unknown_replaces_carried_results() {
        let vc_a = div_zero("crate::carried_unknown_a", "a_0");
        let vc_b = assertion("crate::carried_unknown_b", "post", "b_0");
        let vc_b_strengthened = assertion("crate::carried_unknown_b", "post", "b_1");
        let ctx = MockVerifyContext::new(
            vec![
                vec![(vc_a.clone(), proved()), (vc_b.clone(), failed())],
                vec![(vc_b_strengthened.clone(), proved())],
                vec![
                    (vc_a.clone(), unknown("full revalidation")),
                    (vc_b_strengthened.clone(), proved()),
                ],
            ],
            vec![vec![vc_b_strengthened.clone()]],
        );

        let result = run_iterative_verification(
            &LoopConfig::default(),
            vec![vc_a.clone(), vc_b],
            &ctx,
        );

        assert_ne!(result.reason, TerminationReason::AllProved);
        assert_ne!(result.verdict, ConvergenceVerdict::Converged);
        assert_eq!(result.final_proved, 1);
        assert_eq!(result.final_failed, 0);
        assert_eq!(result.final_unknown, 1);
        assert_eq!(result.final_results.len(), 2);
        assert_eq!(final_status(&result, &vc_a), Some(ObligationStatus::Unknown));
        assert_eq!(
            final_status(&result, &vc_b_strengthened),
            Some(ObligationStatus::Proved)
        );
        assert_eq!(
            result.history[1],
            IterationRecord {
                iteration: 2,
                proved: 1,
                failed: 0,
                unknown: 1,
                strengthened: 0,
            }
        );
        assert_eq!(result.metrics_history[1].proved, 1);
        assert_eq!(result.metrics_history[1].failed, 0);
        assert_eq!(result.metrics_history[1].unknown, 1);
        assert_eq!(ctx.verify_call_count(), 3);
        assert_eq!(ctx.strengthen_call_count(), 1);
    }

    #[test]
    fn test_no_strengthen() {
        let vc_a = div_zero("crate::single_pass", "single_0");
        let ctx = MockVerifyContext::new(vec![vec![(vc_a.clone(), failed())]], vec![]);
        let config = LoopConfig {
            max_iterations: 5,
            stable_round_limit: 2,
            enable_strengthen: false,
            ..LoopConfig::default()
        };

        let result = run_iterative_verification(&config, vec![vc_a], &ctx);

        assert_eq!(result.iterations, 1);
        assert_eq!(result.reason, TerminationReason::NoProgress);
        assert_eq!(result.final_proved, 0);
        assert_eq!(result.final_failed, 1);
        assert_eq!(result.final_unknown, 0);
        assert_eq!(result.history.len(), 1);
        assert_eq!(result.history[0].strengthened, 0);
        assert_eq!(ctx.verify_call_count(), 1);
        assert_eq!(ctx.strengthen_call_count(), 0);
    }
}
