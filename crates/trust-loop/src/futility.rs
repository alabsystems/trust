// trust-loop/futility.rs: Futility detection for early loop termination
//
// Detects when the verification loop is unlikely to make further progress and
// should terminate early. Configurable thresholds for no-progress rounds,
// ineffective strengthening, solver time growth, and cost budgets.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::iteration_metrics::IterationMetrics;

/// Why the futility detector decided to stop.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum FutilityReason {
    /// No new proofs for N consecutive rounds despite active strengthening.
    NoProgress {
        /// How many rounds had zero newly proved VCs.
        rounds: usize,
    },
    /// Strengthening produces proposals but none lead to proofs.
    IneffectiveStrengthening {
        /// How many rounds had proposals applied but zero effective.
        rounds: usize,
    },
    /// Solver time is growing too fast (approaching timeout cliff).
    SolverTimeGrowth {
        /// The observed growth rate (ratio of current to previous solver time).
        growth_rate: f64,
    },
    /// Total solver time budget exceeded.
    SolverTimeBudget {
        /// Total solver time consumed in milliseconds.
        total_ms: u64,
        /// The configured limit.
        limit_ms: u64,
    },
    /// Total wall-clock time budget exceeded.
    WallTimeBudget {
        /// Total wall-clock time consumed in milliseconds.
        total_ms: u64,
        /// The configured limit.
        limit_ms: u64,
    },
}

impl std::fmt::Display for FutilityReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoProgress { rounds } => {
                write!(f, "no new proofs for {rounds} consecutive rounds")
            }
            Self::IneffectiveStrengthening { rounds } => {
                write!(f, "strengthening ineffective for {rounds} consecutive rounds")
            }
            Self::SolverTimeGrowth { growth_rate } => {
                write!(f, "solver time growth rate {growth_rate:.2}x exceeds limit")
            }
            Self::SolverTimeBudget { total_ms, limit_ms } => {
                write!(f, "solver time {total_ms}ms exceeds budget {limit_ms}ms")
            }
            Self::WallTimeBudget { total_ms, limit_ms } => {
                write!(f, "wall time {total_ms}ms exceeds budget {limit_ms}ms")
            }
        }
    }
}

/// Configuration for futility detection thresholds.
#[derive(Debug, Clone)]
pub struct FutilityConfig {
    /// Stop after this many consecutive rounds with zero newly proved VCs.
    pub no_progress_rounds: usize,
    /// Stop after this many consecutive rounds where proposals were applied
    /// but none led to proofs.
    pub ineffective_strengthen_rounds: usize,
    /// Stop if solver time grows by more than this factor between rounds.
    pub solver_time_growth_limit: f64,
    /// Maximum total solver time across all iterations (milliseconds).
    pub max_total_solver_time_ms: u64,
    /// Maximum total wall-clock time across all iterations (milliseconds).
    pub max_total_wall_time_ms: u64,
}

impl Default for FutilityConfig {
    fn default() -> Self {
        Self {
            no_progress_rounds: 2,
            ineffective_strengthen_rounds: 3,
            solver_time_growth_limit: 2.0,
            max_total_solver_time_ms: 60_000,
            max_total_wall_time_ms: 120_000,
        }
    }
}

/// Detector that analyzes iteration metrics to decide if continuing is futile.
#[derive(Debug, Clone)]
pub(crate) struct FutilityDetector {
    config: FutilityConfig,
}

impl FutilityDetector {
    /// Create a detector with the given configuration.
    #[must_use]
    pub(crate) fn new(config: FutilityConfig) -> Self {
        Self { config }
    }

    /// Create a detector with default configuration.
    #[must_use]
    pub(crate) fn with_defaults() -> Self {
        Self::new(FutilityConfig::default())
    }

    /// Check if the loop should stop based on accumulated metrics history.
    ///
    /// Returns `Some(reason)` if the loop should stop, `None` to continue.
    #[must_use]
    pub(crate) fn should_stop(&self, metrics: &[IterationMetrics]) -> Option<FutilityReason> {
        if metrics.is_empty() {
            return None;
        }

        // Check 1: No progress for N rounds.
        if let Some(reason) = self.check_no_progress(metrics) {
            return Some(reason);
        }

        // Check 2: Ineffective strengthening.
        if let Some(reason) = self.check_ineffective_strengthening(metrics) {
            return Some(reason);
        }

        // Check 3: Solver time growth rate.
        if let Some(reason) = self.check_solver_time_growth(metrics) {
            return Some(reason);
        }

        // Check 4: Total solver time budget.
        if let Some(reason) = self.check_solver_time_budget(metrics) {
            return Some(reason);
        }

        // Check 5: Total wall-clock time budget.
        if let Some(reason) = self.check_wall_time_budget(metrics) {
            return Some(reason);
        }

        None
    }

    fn check_no_progress(&self, metrics: &[IterationMetrics]) -> Option<FutilityReason> {
        if metrics.len() < self.config.no_progress_rounds {
            return None;
        }

        let tail = &metrics[metrics.len().saturating_sub(self.config.no_progress_rounds)..];
        let all_no_progress = tail.iter().all(|m| m.newly_proved == 0);

        if all_no_progress {
            Some(FutilityReason::NoProgress { rounds: self.config.no_progress_rounds })
        } else {
            None
        }
    }

    fn check_ineffective_strengthening(
        &self,
        metrics: &[IterationMetrics],
    ) -> Option<FutilityReason> {
        if metrics.len() < self.config.ineffective_strengthen_rounds {
            return None;
        }

        let tail =
            &metrics[metrics.len().saturating_sub(self.config.ineffective_strengthen_rounds)..];
        let all_ineffective =
            tail.iter().all(|m| m.proposals_applied > 0 && m.proposals_effective == 0);

        if all_ineffective {
            Some(FutilityReason::IneffectiveStrengthening {
                rounds: self.config.ineffective_strengthen_rounds,
            })
        } else {
            None
        }
    }

    fn check_solver_time_growth(&self, metrics: &[IterationMetrics]) -> Option<FutilityReason> {
        if metrics.len() < 2 {
            return None;
        }

        let prev = &metrics[metrics.len() - 2];
        let curr = &metrics[metrics.len() - 1];

        if prev.solver_time_ms > 0 && curr.solver_time_ms > 0 {
            let growth_rate = curr.solver_time_ms as f64 / prev.solver_time_ms as f64;
            if growth_rate > self.config.solver_time_growth_limit {
                return Some(FutilityReason::SolverTimeGrowth { growth_rate });
            }
        }

        None
    }

    fn check_solver_time_budget(&self, metrics: &[IterationMetrics]) -> Option<FutilityReason> {
        let total: u64 = metrics.iter().map(|m| m.solver_time_ms).sum();
        if total > self.config.max_total_solver_time_ms {
            Some(FutilityReason::SolverTimeBudget {
                total_ms: total,
                limit_ms: self.config.max_total_solver_time_ms,
            })
        } else {
            None
        }
    }

    fn check_wall_time_budget(&self, metrics: &[IterationMetrics]) -> Option<FutilityReason> {
        let total: u64 = metrics.iter().map(|m| m.wall_time_ms).sum();
        if total > self.config.max_total_wall_time_ms {
            Some(FutilityReason::WallTimeBudget {
                total_ms: total,
                limit_ms: self.config.max_total_wall_time_ms,
            })
        } else {
            None
        }
    }
}

impl Default for FutilityDetector {
    fn default() -> Self {
        Self::with_defaults()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn metrics(
        iteration: u32,
        newly_proved: usize,
        proposals_applied: usize,
        proposals_effective: usize,
        solver_time_ms: u64,
        wall_time_ms: u64,
    ) -> IterationMetrics {
        IterationMetrics {
            iteration,
            proved: 0,
            failed: 0,
            unknown: 0,
            timeout: 0,
            strengthened: 0,
            newly_proved,
            newly_failed: 0,
            regressions: 0,
            proposals_generated: 0,
            proposals_applied,
            proposals_effective,
            solver_time_ms,
            solver_calls: 0,
            wall_time_ms,
            proof_rate: 0.0,
            efficiency: 0.0,
        }
    }

    // --- No progress ---

    #[test]
    fn test_no_progress_detected() {
        let detector = FutilityDetector::new(FutilityConfig {
            no_progress_rounds: 2,
            ..FutilityConfig::default()
        });

        let history = vec![metrics(1, 0, 1, 0, 100, 200), metrics(2, 0, 1, 0, 100, 200)];

        let reason = detector.should_stop(&history);
        assert_eq!(reason, Some(FutilityReason::NoProgress { rounds: 2 }));
    }

    #[test]
    fn test_no_progress_not_triggered_with_progress() {
        let detector = FutilityDetector::new(FutilityConfig {
            no_progress_rounds: 2,
            ..FutilityConfig::default()
        });

        let history = vec![
            metrics(1, 0, 1, 0, 100, 200),
            metrics(2, 1, 1, 1, 100, 200), // made progress
        ];

        assert!(detector.should_stop(&history).is_none());
    }

    #[test]
    fn test_no_progress_insufficient_rounds() {
        let detector = FutilityDetector::new(FutilityConfig {
            no_progress_rounds: 3,
            ..FutilityConfig::default()
        });

        let history = vec![metrics(1, 0, 1, 0, 100, 200), metrics(2, 0, 1, 0, 100, 200)];

        assert!(detector.should_stop(&history).is_none());
    }

    // --- Ineffective strengthening ---

    #[test]
    fn test_ineffective_strengthening_detected() {
        let detector = FutilityDetector::new(FutilityConfig {
            ineffective_strengthen_rounds: 2,
            // Disable other checks
            no_progress_rounds: 100,
            solver_time_growth_limit: 100.0,
            max_total_solver_time_ms: u64::MAX,
            max_total_wall_time_ms: u64::MAX,
        });

        let history = vec![
            metrics(1, 0, 3, 0, 100, 200), // applied 3, effective 0
            metrics(2, 0, 2, 0, 100, 200), // applied 2, effective 0
        ];

        let reason = detector.should_stop(&history);
        assert_eq!(reason, Some(FutilityReason::IneffectiveStrengthening { rounds: 2 }));
    }

    #[test]
    fn test_ineffective_not_triggered_when_no_proposals() {
        let detector = FutilityDetector::new(FutilityConfig {
            ineffective_strengthen_rounds: 2,
            no_progress_rounds: 100,
            solver_time_growth_limit: 100.0,
            max_total_solver_time_ms: u64::MAX,
            max_total_wall_time_ms: u64::MAX,
        });

        let history = vec![
            metrics(1, 0, 0, 0, 100, 200), // no proposals applied
            metrics(2, 0, 0, 0, 100, 200),
        ];

        assert!(detector.should_stop(&history).is_none());
    }

    // --- Solver time growth ---

    #[test]
    fn test_solver_time_growth_detected() {
        let detector = FutilityDetector::new(FutilityConfig {
            solver_time_growth_limit: 2.0,
            no_progress_rounds: 100,
            ineffective_strengthen_rounds: 100,
            max_total_solver_time_ms: u64::MAX,
            max_total_wall_time_ms: u64::MAX,
        });

        let history = vec![
            metrics(1, 1, 0, 0, 100, 200),
            metrics(2, 1, 0, 0, 300, 200), // 3x growth
        ];

        let reason = detector.should_stop(&history);
        match reason {
            Some(FutilityReason::SolverTimeGrowth { growth_rate }) => {
                assert!(growth_rate > 2.0);
            }
            other => panic!("expected SolverTimeGrowth, got {other:?}"),
        }
    }

    #[test]
    fn test_solver_time_growth_not_triggered() {
        let detector = FutilityDetector::new(FutilityConfig {
            solver_time_growth_limit: 2.0,
            no_progress_rounds: 100,
            ineffective_strengthen_rounds: 100,
            max_total_solver_time_ms: u64::MAX,
            max_total_wall_time_ms: u64::MAX,
        });

        let history = vec![
            metrics(1, 1, 0, 0, 100, 200),
            metrics(2, 1, 0, 0, 150, 200), // 1.5x growth, under limit
        ];

        assert!(detector.should_stop(&history).is_none());
    }

    // --- Solver time budget ---

    #[test]
    fn test_solver_time_budget_exceeded() {
        let detector = FutilityDetector::new(FutilityConfig {
            max_total_solver_time_ms: 500,
            no_progress_rounds: 100,
            ineffective_strengthen_rounds: 100,
            solver_time_growth_limit: 100.0,
            max_total_wall_time_ms: u64::MAX,
        });

        let history = vec![
            metrics(1, 1, 0, 0, 300, 200),
            metrics(2, 1, 0, 0, 300, 200), // total 600 > 500
        ];

        let reason = detector.should_stop(&history);
        assert_eq!(reason, Some(FutilityReason::SolverTimeBudget { total_ms: 600, limit_ms: 500 }));
    }

    // --- Wall time budget ---

    #[test]
    fn test_wall_time_budget_exceeded() {
        let detector = FutilityDetector::new(FutilityConfig {
            max_total_wall_time_ms: 300,
            no_progress_rounds: 100,
            ineffective_strengthen_rounds: 100,
            solver_time_growth_limit: 100.0,
            max_total_solver_time_ms: u64::MAX,
        });

        let history = vec![
            metrics(1, 1, 0, 0, 100, 200),
            metrics(2, 1, 0, 0, 100, 200), // total wall 400 > 300
        ];

        let reason = detector.should_stop(&history);
        assert_eq!(reason, Some(FutilityReason::WallTimeBudget { total_ms: 400, limit_ms: 300 }));
    }

    // --- Empty metrics ---

    #[test]
    fn test_empty_metrics_continues() {
        let detector = FutilityDetector::with_defaults();
        assert!(detector.should_stop(&[]).is_none());
    }

    // --- Default config ---

    #[test]
    fn test_default_config_values() {
        let config = FutilityConfig::default();
        assert_eq!(config.no_progress_rounds, 2);
        assert_eq!(config.ineffective_strengthen_rounds, 3);
        assert!((config.solver_time_growth_limit - 2.0).abs() < f64::EPSILON);
        assert_eq!(config.max_total_solver_time_ms, 60_000);
        assert_eq!(config.max_total_wall_time_ms, 120_000);
    }

    // --- Display ---

    #[test]
    fn test_futility_reason_display() {
        let r = FutilityReason::NoProgress { rounds: 3 };
        assert!(r.to_string().contains("no new proofs"));

        let r = FutilityReason::IneffectiveStrengthening { rounds: 2 };
        assert!(r.to_string().contains("ineffective"));

        let r = FutilityReason::SolverTimeGrowth { growth_rate: 3.5 };
        assert!(r.to_string().contains("3.50x"));

        let r = FutilityReason::SolverTimeBudget { total_ms: 100, limit_ms: 50 };
        assert!(r.to_string().contains("100ms"));
    }
}
