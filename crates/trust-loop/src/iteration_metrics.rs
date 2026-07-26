// trust-loop/iteration_metrics.rs: Enriched per-iteration metrics
//
// Replaces the basic IterationRecord with comprehensive metrics including
// per-VC deltas, strengthening effectiveness, cost accounting, and
// computed rates for monitoring loop health.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Comprehensive metrics for one verification iteration.
///
/// This is the enriched replacement for the basic `IterationRecord` counts.
/// It includes per-VC deltas, strengthening effectiveness, cost accounting,
/// and computed rates.
#[derive(Debug, Clone, PartialEq)]
pub struct IterationMetrics {
    /// Iteration number (1-based).
    pub iteration: u32,

    // -- Proof counts (existing) --
    /// Total VCs proved at end of this iteration.
    pub proved: usize,
    /// Total VCs failed at end of this iteration.
    pub failed: usize,
    /// Total VCs unknown at end of this iteration.
    pub unknown: usize,
    /// Total VCs that timed out at end of this iteration.
    pub timeout: usize,
    /// Number of VCs that were strengthened (applied proposals).
    pub strengthened: usize,

    // -- Delta from previous iteration --
    /// VCs that went from non-proved to proved this iteration.
    pub newly_proved: usize,
    /// VCs that went from non-failed to failed this iteration.
    pub newly_failed: usize,
    /// VCs that went from proved to non-proved (regression).
    pub regressions: usize,

    // -- Strengthening effectiveness --
    /// Number of proposals generated this iteration.
    pub proposals_generated: usize,
    /// Number of proposals applied (merged into active VCs).
    pub proposals_applied: usize,
    /// Proposals that led to a successful proof.
    pub proposals_effective: usize,

    // -- Cost accounting --
    /// Total solver time in milliseconds for this iteration.
    pub solver_time_ms: u64,
    /// Number of solver calls in this iteration.
    pub solver_calls: usize,
    /// Wall-clock time for this iteration in milliseconds.
    pub wall_time_ms: u64,

    // -- Computed rates --
    /// Proof rate: proved / total (0.0..=1.0).
    pub proof_rate: f64,
    /// Efficiency: newly_proved / solver_calls (0.0 if no calls).
    pub efficiency: f64,
}

impl IterationMetrics {
    /// Total number of VCs tracked.
    #[must_use]
    pub fn total_vcs(&self) -> usize {
        self.proved + self.failed + self.unknown + self.timeout
    }

    /// Whether this iteration made any forward progress.
    #[must_use]
    pub fn made_progress(&self) -> bool {
        self.newly_proved > 0
    }

    /// Whether this iteration had any regressions.
    #[must_use]
    pub fn had_regressions(&self) -> bool {
        self.regressions > 0
    }

    /// Net progress: newly proved minus regressions.
    #[must_use]
    pub fn net_progress(&self) -> i64 {
        self.newly_proved as i64 - self.regressions as i64
    }

    /// Whether the strengthening was effective (at least one proposal worked).
    #[must_use]
    pub fn strengthening_effective(&self) -> bool {
        self.proposals_effective > 0
    }

    /// Strengthening effectiveness rate: effective / applied.
    #[must_use]
    pub fn strengthening_rate(&self) -> f64 {
        if self.proposals_applied == 0 {
            return 0.0;
        }
        self.proposals_effective as f64 / self.proposals_applied as f64
    }
}

/// Builder for constructing `IterationMetrics` incrementally.
#[derive(Debug, Clone)]
#[must_use]
pub(crate) struct MetricsBuilder {
    iteration: u32,
    proved: usize,
    failed: usize,
    unknown: usize,
    timeout: usize,
    strengthened: usize,
    newly_proved: usize,
    newly_failed: usize,
    regressions: usize,
    proposals_generated: usize,
    proposals_applied: usize,
    proposals_effective: usize,
    solver_time_ms: u64,
    solver_calls: usize,
    wall_time_ms: u64,
}

impl MetricsBuilder {
    /// Start building metrics for the given iteration.
    pub(crate) fn new(iteration: u32) -> Self {
        Self {
            iteration,
            proved: 0,
            failed: 0,
            unknown: 0,
            timeout: 0,
            strengthened: 0,
            newly_proved: 0,
            newly_failed: 0,
            regressions: 0,
            proposals_generated: 0,
            proposals_applied: 0,
            proposals_effective: 0,
            solver_time_ms: 0,
            solver_calls: 0,
            wall_time_ms: 0,
        }
    }

    /// Set the proof counts.
    pub(crate) fn counts(
        mut self,
        proved: usize,
        failed: usize,
        unknown: usize,
        timeout: usize,
    ) -> Self {
        self.proved = proved;
        self.failed = failed;
        self.unknown = unknown;
        self.timeout = timeout;
        self
    }

    /// Set the per-VC deltas.
    pub(crate) fn deltas(
        mut self,
        newly_proved: usize,
        newly_failed: usize,
        regressions: usize,
    ) -> Self {
        self.newly_proved = newly_proved;
        self.newly_failed = newly_failed;
        self.regressions = regressions;
        self
    }

    /// Build the final metrics, computing derived rates.
    pub(crate) fn build(self) -> IterationMetrics {
        let total = self.proved + self.failed + self.unknown + self.timeout;
        let proof_rate = if total == 0 { 0.0 } else { self.proved as f64 / total as f64 };
        let efficiency = if self.solver_calls == 0 {
            0.0
        } else {
            self.newly_proved as f64 / self.solver_calls as f64
        };

        IterationMetrics {
            iteration: self.iteration,
            proved: self.proved,
            failed: self.failed,
            unknown: self.unknown,
            timeout: self.timeout,
            strengthened: self.strengthened,
            newly_proved: self.newly_proved,
            newly_failed: self.newly_failed,
            regressions: self.regressions,
            proposals_generated: self.proposals_generated,
            proposals_applied: self.proposals_applied,
            proposals_effective: self.proposals_effective,
            solver_time_ms: self.solver_time_ms,
            solver_calls: self.solver_calls,
            wall_time_ms: self.wall_time_ms,
            proof_rate,
            efficiency,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_metrics() -> IterationMetrics {
        MetricsBuilder {
            iteration: 1,
            proved: 5,
            failed: 3,
            unknown: 1,
            timeout: 1,
            strengthened: 2,
            newly_proved: 2,
            newly_failed: 1,
            regressions: 0,
            proposals_generated: 4,
            proposals_applied: 3,
            proposals_effective: 2,
            solver_time_ms: 500,
            solver_calls: 10,
            wall_time_ms: 1000,
        }
        .build()
    }

    #[test]
    fn test_total_vcs() {
        let m = sample_metrics();
        assert_eq!(m.total_vcs(), 10);
    }

    #[test]
    fn test_made_progress() {
        let m = sample_metrics();
        assert!(m.made_progress());

        let no_progress = MetricsBuilder::new(1).counts(5, 3, 1, 1).deltas(0, 0, 0).build();
        assert!(!no_progress.made_progress());
    }

    #[test]
    fn test_had_regressions() {
        let m = sample_metrics();
        assert!(!m.had_regressions());

        let with_regression = MetricsBuilder::new(1).counts(5, 3, 1, 1).deltas(0, 0, 1).build();
        assert!(with_regression.had_regressions());
    }

    #[test]
    fn test_net_progress() {
        let m = MetricsBuilder::new(1).counts(5, 3, 1, 1).deltas(3, 0, 1).build();
        assert_eq!(m.net_progress(), 2);
    }

    #[test]
    fn test_net_progress_negative() {
        let m = MetricsBuilder::new(1).counts(5, 3, 1, 1).deltas(0, 2, 3).build();
        assert_eq!(m.net_progress(), -3);
    }

    #[test]
    fn test_strengthening_effective() {
        let m = sample_metrics();
        assert!(m.strengthening_effective());
    }

    #[test]
    fn test_strengthening_rate() {
        let m = sample_metrics();
        assert!((m.strengthening_rate() - 2.0 / 3.0).abs() < 1e-10);
    }

    #[test]
    fn test_strengthening_rate_no_proposals() {
        let m = MetricsBuilder::new(1).build();
        assert!(m.strengthening_rate().abs() < 1e-10);
    }

    #[test]
    fn test_proof_rate() {
        let m = sample_metrics();
        assert!((m.proof_rate - 0.5).abs() < 1e-10); // 5/10
    }

    #[test]
    fn test_proof_rate_no_vcs() {
        let m = MetricsBuilder::new(1).build();
        assert!(m.proof_rate.abs() < 1e-10);
    }

    #[test]
    fn test_efficiency() {
        let m = sample_metrics();
        assert!((m.efficiency - 0.2).abs() < 1e-10); // 2/10
    }

    #[test]
    fn test_efficiency_no_calls() {
        let m = MetricsBuilder::new(1).deltas(2, 0, 0).build();
        assert!(m.efficiency.abs() < 1e-10);
    }

    #[test]
    fn test_builder_defaults() {
        let m = MetricsBuilder::new(1).build();
        assert_eq!(m.iteration, 1);
        assert_eq!(m.proved, 0);
        assert_eq!(m.failed, 0);
        assert_eq!(m.unknown, 0);
        assert_eq!(m.timeout, 0);
        assert_eq!(m.strengthened, 0);
        assert_eq!(m.newly_proved, 0);
        assert_eq!(m.newly_failed, 0);
        assert_eq!(m.regressions, 0);
        assert_eq!(m.proposals_generated, 0);
        assert_eq!(m.proposals_applied, 0);
        assert_eq!(m.proposals_effective, 0);
        assert_eq!(m.solver_time_ms, 0);
        assert_eq!(m.solver_calls, 0);
        assert_eq!(m.wall_time_ms, 0);
    }
}
