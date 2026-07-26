// dead_code audit: crate-level suppression removed
//! trust-convergence: Fixed-point detection for the Trust rewrite loop.
//!
//! This crate provides a small, self-contained convergence model for the
//! prove-strengthen-backpropagate loop. It answers three questions:
//! - Did this iteration improve the proof frontier?
//! - Did it regress the proof frontier?
//! - Have we reached a fixed point or iteration limit?
//! - What changed between the last two observations?
//!
//! The current slice is intentionally narrow: it tracks monotonicity and
//! stagnation using aggregate proof counts plus an optional proof frontier
//! fingerprint. Later work can plug in richer function-level diffs.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub(crate) mod error;
pub(crate) mod fixpoint;
pub mod integration;
pub(crate) mod loop_convergence;
pub mod monotonicity;
pub(crate) mod oscillation;
pub mod stagnation;
pub mod termination;
pub mod visualization;
pub mod widening;

pub use error::ConvergenceError;
pub use fixpoint::{
    AbstractValue, FixpointComputer, FixpointConfig, FixpointResult, FixpointState,
};
pub use loop_convergence::{
    BudgetResource, ConvergenceDimensions, ConvergencePolicy, LoopConvergence, LoopDecision,
    LoopObservation, TerminationOutcome, compute_fingerprint, damp_spec_for_oscillation,
};
pub use termination::{
    DecreaseMeasure, LexOrder, RankingAnalyzer, RankingFunction, TerminationConfig,
    TerminationProof, TerminationResult,
};

/// Aggregate proof counts for one iteration of the loop.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofFrontier {
    pub trusted: u32,
    pub certified: u32,
    pub runtime_checked: u32,
    pub failed: u32,
    pub unknown: u32,
}

impl ProofFrontier {
    /// Returns the number of obligations proved without runtime fallback.
    #[must_use]
    pub fn statically_proved(&self) -> u32 {
        self.trusted.saturating_add(self.certified)
    }

    /// Returns the number of obligations not discharged statically.
    #[must_use]
    pub fn unresolved(&self) -> u32 {
        self.runtime_checked.saturating_add(self.failed).saturating_add(self.unknown)
    }

    /// Total number of obligations tracked.
    #[must_use]
    pub fn total(&self) -> u32 {
        self.trusted
            .saturating_add(self.certified)
            .saturating_add(self.runtime_checked)
            .saturating_add(self.failed)
            .saturating_add(self.unknown)
    }

    /// Convergence score: ratio of statically proved obligations to total (0.0..=1.0).
    ///
    /// Returns `None` if there are no obligations.
    #[must_use]
    pub fn convergence_score(&self) -> Option<f64> {
        let total = self.total();
        if total == 0 {
            return None;
        }
        Some(self.statically_proved() as f64 / total as f64)
    }

    /// Compute the signed delta from a previous frontier to this one.
    #[must_use]
    pub fn delta_from(&self, previous: &Self) -> FrontierDelta {
        FrontierDelta {
            trusted: self.trusted as i64 - previous.trusted as i64,
            certified: self.certified as i64 - previous.certified as i64,
            runtime_checked: self.runtime_checked as i64 - previous.runtime_checked as i64,
            failed: self.failed as i64 - previous.failed as i64,
            unknown: self.unknown as i64 - previous.unknown as i64,
        }
    }
}

/// Signed delta between two proof frontiers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FrontierDelta {
    pub trusted: i64,
    pub certified: i64,
    pub runtime_checked: i64,
    pub failed: i64,
    pub unknown: i64,
}

impl FrontierDelta {
    /// Net change in obligations proved statically.
    #[must_use]
    pub fn statically_proved_delta(&self) -> i64 {
        // Trust (flywheel backprop): saturating — per-iteration deltas are tiny;
        // i64 overflow is impossible in practice but unprovable at type level.
        self.trusted.saturating_add(self.certified)
    }

    /// Net change in obligations not discharged statically.
    #[must_use]
    pub fn unresolved_delta(&self) -> i64 {
        self.runtime_checked.saturating_add(self.failed).saturating_add(self.unknown)
    }

    /// True when static proof coverage did not decrease.
    #[must_use]
    pub fn is_non_decreasing_static_proofs(&self) -> bool {
        self.statically_proved_delta() >= 0
    }

    /// True when unresolved obligations did not increase.
    #[must_use]
    pub fn is_non_increasing_unresolved(&self) -> bool {
        self.unresolved_delta() <= 0
    }
}

/// Reportable summary for the latest convergence observation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConvergenceReport {
    pub iteration: u32,
    pub previous_iteration: Option<u32>,
    pub frontier: ProofFrontier,
    pub delta: Option<FrontierDelta>,
    pub decision: ConvergenceDecision,
    pub stable_rounds: usize,
    pub fingerprint_matched: bool,
}

impl ConvergenceReport {
    /// Signed change in static proof coverage for this observation.
    #[must_use]
    pub fn proof_delta(&self) -> Option<i64> {
        self.delta.as_ref().map(FrontierDelta::statically_proved_delta)
    }

    /// Signed change in unresolved obligations for this observation.
    #[must_use]
    pub fn unresolved_delta(&self) -> Option<i64> {
        self.delta.as_ref().map(FrontierDelta::unresolved_delta)
    }

    /// True if the latest observation reached a fixed point.
    #[must_use]
    pub fn is_converged(&self) -> bool {
        matches!(self.decision, ConvergenceDecision::Converged { .. })
    }

    /// The step verdict when the observation is still in the continue state.
    #[must_use]
    pub fn step_verdict(&self) -> Option<StepVerdict> {
        match self.decision {
            ConvergenceDecision::Continue { verdict } => Some(verdict),
            _ => None,
        }
    }
}

/// Snapshot of one loop iteration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IterationSnapshot {
    pub iteration: u32,
    pub frontier: ProofFrontier,
    /// Optional stable identity for the proof frontier, such as a report hash.
    pub fingerprint: Option<String>,
}

impl IterationSnapshot {
    #[must_use]
    pub fn new(iteration: u32, frontier: ProofFrontier) -> Self {
        Self { iteration, frontier, fingerprint: None }
    }

    #[must_use]
    pub fn with_fingerprint(mut self, fingerprint: impl Into<String>) -> Self {
        self.fingerprint = Some(fingerprint.into());
        self
    }
}

/// One-step comparison result between two iterations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StepVerdict {
    Improved,
    Stable,
    Regressed,
}

/// High-level decision after observing an iteration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConvergenceDecision {
    Continue { verdict: StepVerdict },
    Converged { stable_rounds: usize, fingerprint_matched: bool },
    Regressed { reason: RegressionReason },
    IterationLimitReached { iteration: u32, limit: u32 },
}

/// Why the proof frontier regressed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegressionReason {
    FewerStaticProofs,
    MoreFailures,
    MoreUnresolvedObligations,
}

/// High-level verdict about loop convergence state.
///
/// Unlike `ConvergenceDecision` (which is per-step), this summarizes the overall
/// convergence trajectory considering stall detection with a configurable threshold.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConvergenceVerdict {
    /// All obligations proved and frontier stable for the required rounds.
    Converged,
    /// Same frontier (with failures remaining) for N consecutive iterations — no progress.
    Stalled {
        /// How many consecutive iterations had an identical frontier.
        stale_iterations: usize,
    },
    /// Fewer proved obligations than a previous iteration.
    Regressed,
    /// The loop is still making progress (improving or not yet stalled).
    InProgress,
}

/// Configuration for `ConvergenceVerdict` computation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerdictConfig {
    /// Number of consecutive stable iterations (with failures remaining) before
    /// declaring `Stalled`. Default: 3.
    pub stall_threshold: usize,
}

impl VerdictConfig {
    /// Create a config with the given stall threshold.
    #[must_use]
    #[trust::requires(stall_threshold > 0)]
    pub fn new(stall_threshold: usize) -> Self {
        assert!(stall_threshold > 0, "stall_threshold must be non-zero");
        Self { stall_threshold }
    }
}

impl Default for VerdictConfig {
    fn default() -> Self {
        Self { stall_threshold: 3 }
    }
}

/// Tracker for loop convergence.
#[derive(Debug, Clone)]
pub struct ConvergenceTracker {
    stable_round_limit: usize,
    iteration_limit: u32,
    verdict_config: VerdictConfig,
    history: Vec<IterationSnapshot>,
}

impl ConvergenceTracker {
    /// Create a tracker with explicit stability and iteration limits.
    #[must_use]
    // Trust (flywheel backprop): the runtime asserts below are the API
    // precondition — lift them to verified contracts so the assert bodies
    // PROVE from the precondition and call sites are enforced by the verifier
    // ("never test, you prove"). The asserts stay as runtime defense for
    // non-Trust consumers.
    #[trust::requires(stable_round_limit > 0)]
    #[trust::requires(iteration_limit > 0)]
    pub fn new(stable_round_limit: usize, iteration_limit: u32) -> Self {
        assert!(stable_round_limit > 0, "stable_round_limit must be non-zero");
        assert!(iteration_limit > 0, "iteration_limit must be non-zero");
        Self {
            stable_round_limit,
            iteration_limit,
            verdict_config: VerdictConfig::default(),
            history: Vec::new(),
        }
    }

    /// Create a tracker with a custom verdict configuration.
    #[must_use]
    pub fn with_verdict_config(mut self, config: VerdictConfig) -> Self {
        self.verdict_config = config;
        self
    }

    /// Observe a new iteration snapshot and compute the next decision.
    pub fn observe(&mut self, snapshot: IterationSnapshot) -> ConvergenceDecision {
        self.history.push(snapshot);
        // SAFETY: We just pushed to history, so latest_report() cannot return None.
        self.latest_report().unwrap_or_else(|| unreachable!("history empty after push")).decision
    }

    /// Compute the high-level convergence verdict from the current history.
    ///
    /// This considers the full trajectory, not just the latest step:
    /// - `Converged`: all obligations proved and frontier stable
    /// - `Stalled`: same frontier for `stall_threshold` consecutive iterations
    ///   with failures remaining
    /// - `Regressed`: latest decision was a regression
    /// - `InProgress`: improving or not yet stalled
    #[must_use]
    pub fn verdict(&self) -> ConvergenceVerdict {
        let report = match self.latest_report() {
            Some(r) => r,
            None => return ConvergenceVerdict::InProgress,
        };

        match &report.decision {
            ConvergenceDecision::Regressed { .. } => ConvergenceVerdict::Regressed,
            ConvergenceDecision::Converged { .. } => {
                // If all obligations are proved, it's truly converged.
                // If failures remain but frontier is stable, check stall.
                if report.frontier.failed == 0 && report.frontier.unknown == 0 {
                    ConvergenceVerdict::Converged
                } else {
                    // Converged with failures => stalled
                    ConvergenceVerdict::Stalled { stale_iterations: report.stable_rounds }
                }
            }
            ConvergenceDecision::IterationLimitReached { .. } => {
                // Check if we were stalled before hitting the limit.
                if self.consecutive_stable_count() >= self.verdict_config.stall_threshold {
                    ConvergenceVerdict::Stalled {
                        stale_iterations: self.consecutive_stable_count(),
                    }
                } else {
                    ConvergenceVerdict::InProgress
                }
            }
            ConvergenceDecision::Continue { verdict } => {
                match verdict {
                    StepVerdict::Regressed => ConvergenceVerdict::Regressed,
                    StepVerdict::Improved => ConvergenceVerdict::InProgress,
                    StepVerdict::Stable => {
                        let stale = self.consecutive_stable_count();
                        if report.frontier.failed == 0 && report.frontier.unknown == 0 {
                            // All proved but not yet at stable_round_limit for
                            // ConvergenceDecision::Converged. Still converged for verdict.
                            ConvergenceVerdict::Converged
                        } else if stale >= self.verdict_config.stall_threshold {
                            ConvergenceVerdict::Stalled { stale_iterations: stale }
                        } else {
                            ConvergenceVerdict::InProgress
                        }
                    }
                }
            }
        }
    }

    /// Access the verdict configuration.
    #[must_use]
    pub fn verdict_config(&self) -> &VerdictConfig {
        &self.verdict_config
    }

    /// Count consecutive iterations at the tail of history with identical frontiers.
    ///
    /// Returns 1 if there is only one snapshot (it is trivially "stable" with itself),
    /// or 0 if the history is empty.
    #[must_use]
    pub fn consecutive_stable_count(&self) -> usize {
        // Trust (flywheel backprop): `last()` is TOTAL by construction — the
        // former `history[history.len() - 1]` was guarded-but-refuted (the
        // verifier does not yet thread a length guard through a STRUCT-FIELD
        // Vec; noted for the verifier lane). One snapshot is trivially stable
        // with itself, so `count = 1` plus the empty-tail loop preserves the
        // exact prior semantics (empty -> 0, single -> 1) with fewer branches.
        let Some(last) = self.history.last() else {
            return 0;
        };
        let mut count = 1usize;
        for snap in self.history.iter().rev().skip(1) {
            if snap.frontier == last.frontier {
                count = count.saturating_add(1);
            } else {
                break;
            }
        }
        count
    }

    #[must_use]
    pub fn history(&self) -> &[IterationSnapshot] {
        &self.history
    }

    /// Report the latest convergence observation, including frontier deltas.
    #[must_use]
    pub fn latest_report(&self) -> Option<ConvergenceReport> {
        let current = self.history.last()?;
        let previous = self.history.iter().rev().nth(1);
        Some(self.build_report(previous, current))
    }

    /// Report the latest signed frontier delta, if any history exists.
    #[must_use]
    pub fn latest_delta(&self) -> Option<FrontierDelta> {
        self.latest_report().and_then(|report| report.delta)
    }

    fn compare(
        &self,
        previous: &IterationSnapshot,
        current: &IterationSnapshot,
    ) -> ConvergenceDecision {
        if current.frontier.statically_proved() < previous.frontier.statically_proved() {
            return ConvergenceDecision::Regressed { reason: RegressionReason::FewerStaticProofs };
        }

        if current.frontier.failed > previous.frontier.failed {
            return ConvergenceDecision::Regressed { reason: RegressionReason::MoreFailures };
        }

        if current.frontier.unresolved() > previous.frontier.unresolved() {
            return ConvergenceDecision::Regressed {
                reason: RegressionReason::MoreUnresolvedObligations,
            };
        }

        let fingerprint_matched = current
            .fingerprint
            .as_ref()
            .zip(previous.fingerprint.as_ref())
            .is_some_and(|(lhs, rhs)| lhs == rhs);

        let verdict = if current.frontier == previous.frontier {
            StepVerdict::Stable
        } else {
            StepVerdict::Improved
        };

        let stable_rounds = self.trailing_stable_rounds(current, fingerprint_matched);
        if stable_rounds >= self.stable_round_limit {
            return ConvergenceDecision::Converged { stable_rounds, fingerprint_matched };
        }

        ConvergenceDecision::Continue { verdict }
    }

    fn build_report(
        &self,
        previous: Option<&IterationSnapshot>,
        current: &IterationSnapshot,
    ) -> ConvergenceReport {
        let delta = previous.map(|prev| current.frontier.delta_from(&prev.frontier));
        let fingerprint_matched = previous
            .map(|prev| {
                current
                    .fingerprint
                    .as_ref()
                    .zip(prev.fingerprint.as_ref())
                    .is_some_and(|(lhs, rhs)| lhs == rhs)
            })
            .unwrap_or(false);
        let stable_rounds = previous
            .map(|_| self.trailing_stable_rounds(current, fingerprint_matched))
            .unwrap_or(1);
        let decision = match previous {
            None => {
                if current.iteration >= self.iteration_limit {
                    ConvergenceDecision::IterationLimitReached {
                        iteration: current.iteration,
                        limit: self.iteration_limit,
                    }
                } else {
                    ConvergenceDecision::Continue { verdict: StepVerdict::Improved }
                }
            }
            Some(_) if current.iteration >= self.iteration_limit => {
                ConvergenceDecision::IterationLimitReached {
                    iteration: current.iteration,
                    limit: self.iteration_limit,
                }
            }
            Some(previous) => self.compare(previous, current),
        };

        ConvergenceReport {
            iteration: current.iteration,
            previous_iteration: previous.map(|snapshot| snapshot.iteration),
            frontier: current.frontier.clone(),
            delta,
            decision,
            stable_rounds,
            fingerprint_matched,
        }
    }

    fn trailing_stable_rounds(
        &self,
        current: &IterationSnapshot,
        fingerprint_matched: bool,
    ) -> usize {
        let mut stable_rounds = 1usize;
        let mut next = current;

        for snapshot in self.history.iter().rev().skip(1) {
            let same_frontier = snapshot.frontier == next.frontier;
            let same_fingerprint = next
                .fingerprint
                .as_ref()
                .zip(snapshot.fingerprint.as_ref())
                .is_some_and(|(lhs, rhs)| lhs == rhs);

            if same_frontier || (fingerprint_matched && same_fingerprint) {
                stable_rounds = stable_rounds.saturating_add(1);
                next = snapshot;
            } else {
                break;
            }
        }

        stable_rounds
    }
}

impl Default for ConvergenceTracker {
    fn default() -> Self {
        Self::new(2, 8)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn frontier(
        trusted: u32,
        certified: u32,
        runtime_checked: u32,
        failed: u32,
        unknown: u32,
    ) -> ProofFrontier {
        ProofFrontier { trusted, certified, runtime_checked, failed, unknown }
    }

    #[test]
    fn first_observation_continues() {
        let mut tracker = ConvergenceTracker::new(2, 8);
        let decision = tracker.observe(IterationSnapshot::new(0, frontier(1, 0, 2, 0, 3)));
        assert_eq!(decision, ConvergenceDecision::Continue { verdict: StepVerdict::Improved });
    }

    #[test]
    fn improvement_continues() {
        let mut tracker = ConvergenceTracker::new(2, 8);
        tracker.observe(IterationSnapshot::new(0, frontier(1, 0, 2, 0, 3)));
        let decision = tracker.observe(IterationSnapshot::new(1, frontier(2, 0, 1, 0, 2)));
        assert_eq!(decision, ConvergenceDecision::Continue { verdict: StepVerdict::Improved });
    }

    #[test]
    fn repeated_frontier_converges() {
        let mut tracker = ConvergenceTracker::new(2, 8);
        tracker.observe(IterationSnapshot::new(0, frontier(3, 0, 1, 0, 0)));
        let decision = tracker.observe(IterationSnapshot::new(1, frontier(3, 0, 1, 0, 0)));
        assert_eq!(
            decision,
            ConvergenceDecision::Converged { stable_rounds: 2, fingerprint_matched: false }
        );
    }

    #[test]
    fn matching_fingerprint_converges() {
        let mut tracker = ConvergenceTracker::new(2, 8);
        tracker.observe(IterationSnapshot::new(0, frontier(3, 1, 0, 0, 0)).with_fingerprint("abc"));
        let decision = tracker
            .observe(IterationSnapshot::new(1, frontier(3, 1, 0, 0, 0)).with_fingerprint("abc"));
        assert_eq!(
            decision,
            ConvergenceDecision::Converged { stable_rounds: 2, fingerprint_matched: true }
        );
    }

    #[test]
    fn fewer_static_proofs_is_regression() {
        let mut tracker = ConvergenceTracker::new(2, 8);
        tracker.observe(IterationSnapshot::new(0, frontier(4, 1, 0, 0, 0)));
        let decision = tracker.observe(IterationSnapshot::new(1, frontier(3, 1, 0, 0, 0)));
        assert_eq!(
            decision,
            ConvergenceDecision::Regressed { reason: RegressionReason::FewerStaticProofs }
        );
    }

    #[test]
    fn more_failures_is_regression() {
        let mut tracker = ConvergenceTracker::new(2, 8);
        tracker.observe(IterationSnapshot::new(0, frontier(2, 0, 1, 0, 1)));
        let decision = tracker.observe(IterationSnapshot::new(1, frontier(2, 0, 1, 1, 0)));
        assert_eq!(
            decision,
            ConvergenceDecision::Regressed { reason: RegressionReason::MoreFailures }
        );
    }

    #[test]
    fn more_unresolved_is_regression() {
        let mut tracker = ConvergenceTracker::new(2, 8);
        tracker.observe(IterationSnapshot::new(0, frontier(2, 0, 0, 0, 1)));
        let decision = tracker.observe(IterationSnapshot::new(1, frontier(2, 0, 1, 0, 1)));
        assert_eq!(
            decision,
            ConvergenceDecision::Regressed { reason: RegressionReason::MoreUnresolvedObligations }
        );
    }

    #[test]
    fn iteration_limit_is_reported() {
        let mut tracker = ConvergenceTracker::new(2, 2);
        tracker.observe(IterationSnapshot::new(0, frontier(1, 0, 0, 0, 0)));
        let decision = tracker.observe(IterationSnapshot::new(2, frontier(1, 0, 0, 0, 0)));
        assert_eq!(decision, ConvergenceDecision::IterationLimitReached { iteration: 2, limit: 2 });
    }

    #[test]
    fn report_tracks_improvement_delta() {
        let mut tracker = ConvergenceTracker::new(3, 8);
        tracker.observe(IterationSnapshot::new(0, frontier(1, 0, 2, 0, 3)));
        tracker.observe(IterationSnapshot::new(1, frontier(2, 0, 1, 0, 2)));

        let report = tracker.latest_report().expect("latest report");
        assert_eq!(report.previous_iteration, Some(0));
        assert_eq!(report.step_verdict(), Some(StepVerdict::Improved));
        assert_eq!(report.proof_delta(), Some(1));
        assert_eq!(report.unresolved_delta(), Some(-2));
        assert_eq!(report.stable_rounds, 1);
        assert!(!report.fingerprint_matched);
        assert!(report.delta.expect("delta").is_non_decreasing_static_proofs());
        assert!(report.delta.expect("delta").is_non_increasing_unresolved());
    }

    #[test]
    fn report_tracks_stable_frontier() {
        let mut tracker = ConvergenceTracker::new(3, 8);
        tracker.observe(IterationSnapshot::new(0, frontier(3, 0, 1, 0, 0)).with_fingerprint("fp"));
        tracker.observe(IterationSnapshot::new(1, frontier(3, 0, 1, 0, 0)).with_fingerprint("fp"));

        let report = tracker.latest_report().expect("latest report");
        assert_eq!(report.decision, ConvergenceDecision::Continue { verdict: StepVerdict::Stable });
        assert_eq!(report.proof_delta(), Some(0));
        assert_eq!(report.unresolved_delta(), Some(0));
        assert_eq!(report.stable_rounds, 2);
        assert!(report.fingerprint_matched);
    }

    #[test]
    fn report_tracks_regression() {
        let mut tracker = ConvergenceTracker::new(3, 8);
        tracker.observe(IterationSnapshot::new(0, frontier(4, 1, 0, 0, 0)));
        tracker.observe(IterationSnapshot::new(1, frontier(3, 1, 0, 0, 0)));

        let report = tracker.latest_report().expect("latest report");
        assert_eq!(
            report.decision,
            ConvergenceDecision::Regressed { reason: RegressionReason::FewerStaticProofs }
        );
        assert!(report.proof_delta().expect("proof delta") < 0);
        assert_eq!(report.unresolved_delta(), Some(0));
        assert!(!report.is_converged());
    }

    #[test]
    fn convergence_score_all_proved() {
        let f = frontier(5, 3, 0, 0, 0);
        assert_eq!(f.convergence_score(), Some(1.0));
    }

    #[test]
    fn convergence_score_half() {
        let f = frontier(2, 0, 0, 1, 1);
        assert!((f.convergence_score().unwrap() - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn convergence_score_none_when_empty() {
        let f = frontier(0, 0, 0, 0, 0);
        assert!(f.convergence_score().is_none());
    }

    #[test]
    fn total_sums_all_fields() {
        let f = frontier(1, 2, 3, 4, 5);
        assert_eq!(f.total(), 15);
    }

    #[test]
    fn report_tracks_convergence() {
        let mut tracker = ConvergenceTracker::new(2, 8);
        tracker.observe(IterationSnapshot::new(0, frontier(3, 1, 0, 0, 0)).with_fingerprint("abc"));
        tracker.observe(IterationSnapshot::new(1, frontier(3, 1, 0, 0, 0)).with_fingerprint("abc"));

        let report = tracker.latest_report().expect("latest report");
        assert!(report.is_converged());
        assert_eq!(
            report.decision,
            ConvergenceDecision::Converged { stable_rounds: 2, fingerprint_matched: true }
        );
        assert_eq!(report.proof_delta(), Some(0));
        assert_eq!(report.unresolved_delta(), Some(0));
        assert_eq!(report.stable_rounds, 2);
        assert!(report.fingerprint_matched);
    }

    // -- ConvergenceVerdict tests --

    #[test]
    fn verdict_converged_all_proved_stable() {
        // All proved, stable for 3 rounds => Converged
        let mut tracker = ConvergenceTracker::new(3, 10).with_verdict_config(VerdictConfig::new(3));
        tracker.observe(IterationSnapshot::new(0, frontier(5, 0, 0, 0, 0)));
        tracker.observe(IterationSnapshot::new(1, frontier(5, 0, 0, 0, 0)));
        tracker.observe(IterationSnapshot::new(2, frontier(5, 0, 0, 0, 0)));
        assert_eq!(tracker.verdict(), ConvergenceVerdict::Converged);
    }

    #[test]
    fn verdict_converged_early_all_proved() {
        // All proved on first pass, even before stable_round_limit => Converged
        let mut tracker = ConvergenceTracker::new(3, 10).with_verdict_config(VerdictConfig::new(3));
        tracker.observe(IterationSnapshot::new(0, frontier(5, 0, 0, 0, 0)));
        // Only 1 observation, but all proved => Converged for verdict
        // (Continue { Improved } from tracker, but verdict sees all proved)
        assert_eq!(tracker.verdict(), ConvergenceVerdict::InProgress);
        // After second identical observation
        tracker.observe(IterationSnapshot::new(1, frontier(5, 0, 0, 0, 0)));
        // stable_round_limit=3 so tracker says Continue { Stable }, but all proved
        assert_eq!(tracker.verdict(), ConvergenceVerdict::Converged);
    }

    #[test]
    fn verdict_stalled_same_counts_for_3_rounds() {
        // Same frontier with failures for 3+ rounds => Stalled
        let mut tracker = ConvergenceTracker::new(5, 20).with_verdict_config(VerdictConfig::new(3));
        tracker.observe(IterationSnapshot::new(0, frontier(3, 0, 0, 2, 0)));
        assert_eq!(tracker.verdict(), ConvergenceVerdict::InProgress);
        tracker.observe(IterationSnapshot::new(1, frontier(3, 0, 0, 2, 0)));
        assert_eq!(tracker.verdict(), ConvergenceVerdict::InProgress);
        tracker.observe(IterationSnapshot::new(2, frontier(3, 0, 0, 2, 0)));
        // 3 consecutive stable with failures => Stalled
        assert_eq!(tracker.verdict(), ConvergenceVerdict::Stalled { stale_iterations: 3 });
    }

    #[test]
    fn verdict_stalled_custom_threshold() {
        // Custom threshold of 2
        let mut tracker = ConvergenceTracker::new(5, 20).with_verdict_config(VerdictConfig::new(2));
        tracker.observe(IterationSnapshot::new(0, frontier(3, 0, 0, 2, 0)));
        tracker.observe(IterationSnapshot::new(1, frontier(3, 0, 0, 2, 0)));
        assert_eq!(tracker.verdict(), ConvergenceVerdict::Stalled { stale_iterations: 2 });
    }

    #[test]
    fn verdict_regressed_fewer_proved() {
        // Proved count decreases => Regressed
        let mut tracker = ConvergenceTracker::new(3, 10).with_verdict_config(VerdictConfig::new(3));
        tracker.observe(IterationSnapshot::new(0, frontier(5, 0, 0, 1, 0)));
        tracker.observe(IterationSnapshot::new(1, frontier(4, 0, 0, 2, 0)));
        assert_eq!(tracker.verdict(), ConvergenceVerdict::Regressed);
    }

    #[test]
    fn verdict_in_progress_improving() {
        // Improving each iteration => InProgress
        let mut tracker = ConvergenceTracker::new(3, 10).with_verdict_config(VerdictConfig::new(3));
        tracker.observe(IterationSnapshot::new(0, frontier(1, 0, 0, 4, 0)));
        assert_eq!(tracker.verdict(), ConvergenceVerdict::InProgress);
        tracker.observe(IterationSnapshot::new(1, frontier(2, 0, 0, 3, 0)));
        assert_eq!(tracker.verdict(), ConvergenceVerdict::InProgress);
        tracker.observe(IterationSnapshot::new(2, frontier(3, 0, 0, 2, 0)));
        assert_eq!(tracker.verdict(), ConvergenceVerdict::InProgress);
    }

    #[test]
    fn verdict_in_progress_not_yet_stalled() {
        // Same frontier twice but threshold is 3 => still InProgress
        let mut tracker = ConvergenceTracker::new(5, 20).with_verdict_config(VerdictConfig::new(3));
        tracker.observe(IterationSnapshot::new(0, frontier(3, 0, 0, 2, 0)));
        tracker.observe(IterationSnapshot::new(1, frontier(3, 0, 0, 2, 0)));
        // Only 2 stable, threshold is 3
        assert_eq!(tracker.verdict(), ConvergenceVerdict::InProgress);
    }

    #[test]
    fn verdict_empty_history_is_in_progress() {
        let tracker = ConvergenceTracker::new(3, 10);
        assert_eq!(tracker.verdict(), ConvergenceVerdict::InProgress);
    }

    #[test]
    fn verdict_converged_via_decision() {
        // ConvergenceDecision::Converged with no failures => Converged verdict
        let mut tracker = ConvergenceTracker::new(2, 10).with_verdict_config(VerdictConfig::new(3));
        tracker.observe(IterationSnapshot::new(0, frontier(5, 0, 0, 0, 0)));
        tracker.observe(IterationSnapshot::new(1, frontier(5, 0, 0, 0, 0)));
        // Decision is Converged { stable_rounds: 2 }, all proved
        assert_eq!(tracker.verdict(), ConvergenceVerdict::Converged);
    }

    #[test]
    fn verdict_stalled_via_converged_decision_with_failures() {
        // ConvergenceDecision::Converged but with failures => Stalled
        let mut tracker = ConvergenceTracker::new(2, 10).with_verdict_config(VerdictConfig::new(3));
        tracker.observe(IterationSnapshot::new(0, frontier(3, 0, 0, 2, 0)));
        tracker.observe(IterationSnapshot::new(1, frontier(3, 0, 0, 2, 0)));
        // Decision is Converged, but failures remain => Stalled
        assert_eq!(tracker.verdict(), ConvergenceVerdict::Stalled { stale_iterations: 2 });
    }

    #[test]
    fn verdict_consecutive_stable_count() {
        let mut tracker = ConvergenceTracker::new(10, 100);
        assert_eq!(tracker.consecutive_stable_count(), 0);

        tracker.observe(IterationSnapshot::new(0, frontier(3, 0, 0, 2, 0)));
        assert_eq!(tracker.consecutive_stable_count(), 1);

        tracker.observe(IterationSnapshot::new(1, frontier(3, 0, 0, 2, 0)));
        assert_eq!(tracker.consecutive_stable_count(), 2);

        tracker.observe(IterationSnapshot::new(2, frontier(4, 0, 0, 1, 0)));
        assert_eq!(tracker.consecutive_stable_count(), 1);

        tracker.observe(IterationSnapshot::new(3, frontier(4, 0, 0, 1, 0)));
        assert_eq!(tracker.consecutive_stable_count(), 2);

        tracker.observe(IterationSnapshot::new(4, frontier(4, 0, 0, 1, 0)));
        assert_eq!(tracker.consecutive_stable_count(), 3);
    }

    #[test]
    fn verdict_default_config_stall_threshold_is_three() {
        let config = VerdictConfig::default();
        assert_eq!(config.stall_threshold, 3);
    }

    #[test]
    #[should_panic(expected = "stall_threshold must be non-zero")]
    fn verdict_config_zero_threshold_panics() {
        let _ = VerdictConfig::new(0);
    }
}
