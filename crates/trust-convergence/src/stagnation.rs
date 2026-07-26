// trust-convergence/stagnation.rs: Stagnation detection for the rewrite loop.
//
// Detects when the prove-strengthen-backprop loop has stopped making progress
// and should be halted to avoid wasting compute.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::ProofFrontier;
use crate::visualization::FrontierSnapshot;

/// Configuration for stagnation detection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StagnationConfig {
    /// Number of consecutive iterations with no improvement before declaring stagnation.
    /// Default: 3.
    pub threshold: usize,
}

impl StagnationConfig {
    /// Create a config with the given threshold.
    #[must_use]
    #[trust::requires(threshold > 0)]
    pub fn new(threshold: usize) -> Self {
        assert!(threshold > 0, "stagnation threshold must be non-zero");
        Self { threshold }
    }
}

impl Default for StagnationConfig {
    fn default() -> Self {
        Self { threshold: 3 }
    }
}

/// Result of a stagnation check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StagnationResult {
    /// Whether the loop should stop.
    pub should_stop: bool,
    /// Number of consecutive iterations with no improvement.
    pub stale_iterations: usize,
    /// The configured threshold.
    pub threshold: usize,
    /// Human-readable reason.
    pub reason: String,
}

impl StagnationResult {
    /// True if the loop is stagnant and should stop.
    #[must_use]
    pub fn is_stagnant(&self) -> bool {
        self.should_stop
    }
}

/// Detects stagnation in the proof frontier across iterations.
#[derive(Debug, Clone)]
pub struct StagnationDetector {
    config: StagnationConfig,
    /// Best static proof count seen so far.
    best_proved: u32,
    /// Lowest failure count seen so far.
    best_failed: u32,
    /// Number of consecutive observations with no improvement over the best.
    stale_count: usize,
    /// Total observations made.
    observation_count: usize,
}

impl StagnationDetector {
    /// Create a new detector with the given config.
    #[must_use]
    pub fn new(config: StagnationConfig) -> Self {
        Self { config, best_proved: 0, best_failed: u32::MAX, stale_count: 0, observation_count: 0 }
    }

    /// Create a detector with the default threshold of 3.
    #[must_use]
    pub fn with_threshold(threshold: usize) -> Self {
        Self::new(StagnationConfig::new(threshold))
    }

    /// Observe a new proof frontier and check for stagnation.
    #[must_use]
    pub fn observe(&mut self, frontier: &ProofFrontier) -> StagnationResult {
        self.observation_count = self.observation_count.saturating_add(1);
        let proved = frontier.statically_proved();
        let failed = frontier.failed;

        let improved = proved > self.best_proved || failed < self.best_failed;

        if improved {
            if proved > self.best_proved {
                self.best_proved = proved;
            }
            if failed < self.best_failed {
                self.best_failed = failed;
            }
            self.stale_count = 0;
        } else {
            self.stale_count = self.stale_count.saturating_add(1);
        }

        let should_stop = self.stale_count >= self.config.threshold;

        let reason = if should_stop {
            format!(
                "no improvement in {} consecutive iterations (threshold: {}), best proved: {}, best failed: {}",
                self.stale_count, self.config.threshold, self.best_proved, self.best_failed
            )
        } else if self.stale_count > 0 {
            format!(
                "{} of {} stale iterations before stop",
                self.stale_count, self.config.threshold
            )
        } else {
            "improving".to_string()
        };

        StagnationResult {
            should_stop,
            stale_iterations: self.stale_count,
            threshold: self.config.threshold,
            reason,
        }
    }

    /// Reset the detector, clearing all history.
    pub fn reset(&mut self) {
        self.best_proved = 0;
        self.best_failed = u32::MAX;
        self.stale_count = 0;
        self.observation_count = 0;
    }

    /// Number of observations made so far.
    #[must_use]
    pub fn observation_count(&self) -> usize {
        self.observation_count
    }

    /// Current number of consecutive stale iterations.
    #[must_use]
    pub fn stale_count(&self) -> usize {
        self.stale_count
    }

    /// The configured stagnation threshold.
    #[must_use]
    pub fn threshold(&self) -> usize {
        self.config.threshold
    }
}

impl Default for StagnationDetector {
    fn default() -> Self {
        Self::new(StagnationConfig::default())
    }
}

/// Count trailing consecutive equal values in a slice.
///
/// Returns the number of trailing elements that equal the last element,
/// or 0 if fewer than 2 elements match.
///
/// Consolidated stagnation primitive shared with `dashboard_data`.
#[must_use]
pub fn count_trailing_equal(values: &[u32]) -> u32 {
    if values.len() < 2 {
        return 0;
    }
    let last = values[values.len() - 1];
    let mut count = 1u32;
    for &v in values.iter().rev().skip(1) {
        if v == last {
            count = count.saturating_add(1);
        } else {
            break;
        }
    }
    if count < 2 { 0 } else { count }
}

/// Detailed stagnation report for human review.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct StagnationReport {
    /// Whether the loop is stagnating.
    pub is_stagnating: bool,
    /// Number of consecutive stale snapshots at the tail.
    pub stale_tail_length: usize,
    /// The configured threshold.
    pub threshold: u32,
    /// Total snapshots analyzed.
    pub total_snapshots: usize,
    /// Best convergence ratio seen across all snapshots (0.0..=1.0).
    pub best_convergence_ratio: Option<f64>,
    /// Current convergence ratio (from the latest snapshot).
    pub current_convergence_ratio: Option<f64>,
    /// Human-readable summary.
    pub summary: String,
    /// List of VCs that have never been proved across all observed snapshots.
    pub stuck_vcs: Vec<String>,
}

/// Snapshot-history-based stagnation detector.
///
/// Operates on `FrontierSnapshot` sequences (from `visualization`) rather than
/// raw `ProofFrontier` values. This allows richer analysis including VC-level
/// stagnation tracking.
#[derive(Debug, Clone)]
pub struct SnapshotStagnationDetector {
    threshold: u32,
    history: Vec<FrontierSnapshot>,
}

impl SnapshotStagnationDetector {
    /// Create a new detector with the given stagnation threshold.
    ///
    /// The detector declares stagnation when the last `threshold` snapshots
    /// show no improvement in the proved VC count.
    #[must_use]
    #[trust::requires(threshold > 0)]
    pub fn new(threshold: u32) -> Self {
        assert!(threshold > 0, "stagnation threshold must be non-zero");
        Self { threshold, history: Vec::new() }
    }

    /// Record a new frontier snapshot.
    pub fn push(&mut self, snapshot: FrontierSnapshot) {
        self.history.push(snapshot);
    }

    /// Number of snapshots recorded.
    #[must_use]
    pub fn snapshot_count(&self) -> usize {
        self.history.len()
    }

    /// Access the full snapshot history.
    #[must_use]
    pub fn history(&self) -> &[FrontierSnapshot] {
        &self.history
    }

    /// True if the last `threshold` snapshots show no improvement.
    #[must_use]
    pub fn is_stagnating(&self) -> bool {
        let len = self.history.len();
        let window = self.threshold as usize;

        if len <= window {
            // Need at least threshold+1 snapshots to judge
            // (one baseline + threshold stale ones).
            return false;
        }

        let tail = &self.history[len - window..];
        let baseline = &self.history[len - window - 1];

        tail.iter().all(|snap| snap.proved_count <= baseline.proved_count)
    }

    /// Generate a detailed stagnation report for human review.
    #[must_use]
    pub fn stagnation_report(&self) -> StagnationReport {
        let is_stagnating = self.is_stagnating();
        let stale_tail = self.trailing_stale_count();
        let total = self.history.len();

        let best_ratio = self
            .history
            .iter()
            .filter_map(|s| s.convergence_ratio())
            .max_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));

        let current_ratio = self.history.last().and_then(|s| s.convergence_ratio());

        let stuck_vcs = self.compute_stuck_vcs();

        let summary = if is_stagnating {
            format!(
                "Stagnating: last {} snapshots show no improvement (threshold: {}). \
                 {} VCs have never been proved.",
                stale_tail,
                self.threshold,
                stuck_vcs.len()
            )
        } else if stale_tail > 0 {
            format!(
                "{} of {} stale snapshots before stagnation declared.",
                stale_tail, self.threshold
            )
        } else if total == 0 {
            "No snapshots recorded.".to_string()
        } else {
            "Making progress.".to_string()
        };

        StagnationReport {
            is_stagnating,
            stale_tail_length: stale_tail,
            threshold: self.threshold,
            total_snapshots: total,
            best_convergence_ratio: best_ratio,
            current_convergence_ratio: current_ratio,
            summary,
            stuck_vcs,
        }
    }

    /// Count consecutive stale snapshots at the tail of history.
    fn trailing_stale_count(&self) -> usize {
        if self.history.len() < 2 {
            return 0;
        }

        let mut count = 0usize;
        let snapshots = &self.history;
        for i in (1..snapshots.len()).rev() {
            if snapshots[i].proved_count <= snapshots[i - 1].proved_count {
                count = count.saturating_add(1);
            } else {
                break;
            }
        }
        count
    }

    /// Identify VCs that appear in failed_vcs across all snapshots and never in proved_vcs.
    fn compute_stuck_vcs(&self) -> Vec<String> {
        use std::collections::BTreeSet;

        let mut ever_proved: BTreeSet<&str> = BTreeSet::new();
        let mut ever_failed: BTreeSet<&str> = BTreeSet::new();

        for snap in &self.history {
            for vc in &snap.proved_vcs {
                ever_proved.insert(vc.as_str());
            }
            for vc in &snap.failed_vcs {
                ever_failed.insert(vc.as_str());
            }
        }

        ever_failed.difference(&ever_proved).map(|s| (*s).to_string()).collect()
    }
}

impl Default for SnapshotStagnationDetector {
    fn default() -> Self {
        Self::new(3)
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
    fn test_first_observation_is_improvement() {
        let mut detector = StagnationDetector::with_threshold(3);
        let result = detector.observe(&frontier(2, 0, 0, 1, 0));
        assert!(!result.should_stop);
        assert!(!result.is_stagnant());
        assert_eq!(result.stale_iterations, 0);
        assert_eq!(result.reason, "improving");
    }

    #[test]
    fn test_continuous_improvement_no_stagnation() {
        let mut detector = StagnationDetector::with_threshold(3);
        for i in 1..=5 {
            let result = detector.observe(&frontier(i, 0, 0, 5 - i, 0));
            assert!(!result.should_stop);
            assert_eq!(result.stale_iterations, 0);
        }
    }

    #[test]
    fn test_stagnation_at_threshold() {
        let mut detector = StagnationDetector::with_threshold(3);

        // First observation: improvement (from initial best of 0).
        let r0 = detector.observe(&frontier(3, 0, 0, 1, 0));
        assert!(!r0.should_stop);
        assert_eq!(r0.stale_iterations, 0);

        // Same frontier repeated: stale_count increments.
        let r1 = detector.observe(&frontier(3, 0, 0, 1, 0));
        assert!(!r1.should_stop);
        assert_eq!(r1.stale_iterations, 1);

        let r2 = detector.observe(&frontier(3, 0, 0, 1, 0));
        assert!(!r2.should_stop);
        assert_eq!(r2.stale_iterations, 2);

        // Third stale iteration hits the threshold.
        let r3 = detector.observe(&frontier(3, 0, 0, 1, 0));
        assert!(r3.should_stop);
        assert!(r3.is_stagnant());
        assert_eq!(r3.stale_iterations, 3);
        assert_eq!(r3.threshold, 3);
        assert!(r3.reason.contains("no improvement"));
    }

    #[test]
    fn test_improvement_resets_stale_count() {
        let mut detector = StagnationDetector::with_threshold(3);

        let _ = detector.observe(&frontier(3, 0, 0, 1, 0)); // improve
        let _ = detector.observe(&frontier(3, 0, 0, 1, 0)); // stale 1
        let _ = detector.observe(&frontier(3, 0, 0, 1, 0)); // stale 2

        // Now an improvement resets the count.
        let r = detector.observe(&frontier(4, 0, 0, 0, 0));
        assert!(!r.should_stop);
        assert_eq!(r.stale_iterations, 0);
    }

    #[test]
    fn test_failure_decrease_counts_as_improvement() {
        let mut detector = StagnationDetector::with_threshold(3);

        let _ = detector.observe(&frontier(3, 0, 0, 5, 0)); // improve
        let _ = detector.observe(&frontier(3, 0, 0, 5, 0)); // stale 1
        let _ = detector.observe(&frontier(3, 0, 0, 5, 0)); // stale 2

        // Fewer failures = improvement, even if proofs didn't increase.
        let r = detector.observe(&frontier(3, 0, 0, 4, 0));
        assert!(!r.should_stop);
        assert_eq!(r.stale_iterations, 0);
    }

    #[test]
    fn test_threshold_of_one_stops_immediately() {
        let mut detector = StagnationDetector::with_threshold(1);

        let _ = detector.observe(&frontier(3, 0, 0, 1, 0)); // improve
        let r = detector.observe(&frontier(3, 0, 0, 1, 0)); // stale 1 = threshold
        assert!(r.should_stop);
        assert_eq!(r.stale_iterations, 1);
    }

    #[test]
    fn test_reset_clears_state() {
        let mut detector = StagnationDetector::with_threshold(3);
        let _ = detector.observe(&frontier(5, 0, 0, 0, 0));
        let _ = detector.observe(&frontier(5, 0, 0, 0, 0));
        assert_eq!(detector.stale_count(), 1);
        assert_eq!(detector.observation_count(), 2);

        detector.reset();
        assert_eq!(detector.stale_count(), 0);
        assert_eq!(detector.observation_count(), 0);
    }

    #[test]
    fn test_regression_counts_as_stale() {
        let mut detector = StagnationDetector::with_threshold(2);
        let _ = detector.observe(&frontier(5, 0, 0, 0, 0)); // improve

        // Regression: fewer proofs, more failures. Not an improvement over best.
        let r = detector.observe(&frontier(3, 0, 0, 2, 0));
        assert_eq!(r.stale_iterations, 1);
        assert!(!r.should_stop);

        let r2 = detector.observe(&frontier(3, 0, 0, 2, 0));
        assert_eq!(r2.stale_iterations, 2);
        assert!(r2.should_stop);
    }

    #[test]
    fn test_default_config_threshold_is_three() {
        let config = StagnationConfig::default();
        assert_eq!(config.threshold, 3);

        let detector = StagnationDetector::default();
        assert_eq!(detector.threshold(), 3);
    }

    #[test]
    #[should_panic(expected = "stagnation threshold must be non-zero")]
    fn test_zero_threshold_panics() {
        let _ = StagnationConfig::new(0);
    }

    #[test]
    fn test_certified_counts_toward_improvement() {
        let mut detector = StagnationDetector::with_threshold(3);
        let _ = detector.observe(&frontier(3, 0, 0, 1, 0)); // improve: proved=3

        // Certified increases but trusted stays the same. statically_proved() = 3+1 = 4 > 3.
        let r = detector.observe(&frontier(3, 1, 0, 1, 0));
        assert!(!r.should_stop);
        assert_eq!(r.stale_iterations, 0);
    }

    // -- SnapshotStagnationDetector tests --

    fn snap(
        iteration: u32,
        proved: Vec<&str>,
        failed: Vec<&str>,
        unknown: usize,
    ) -> FrontierSnapshot {
        FrontierSnapshot {
            iteration,
            proved_count: proved.len(),
            failed_count: failed.len(),
            unknown_count: unknown,
            timestamp: 0,
            proved_vcs: proved.into_iter().map(String::from).collect(),
            failed_vcs: failed.into_iter().map(String::from).collect(),
        }
    }

    #[test]
    fn test_snapshot_detector_empty() {
        let det = SnapshotStagnationDetector::new(3);
        assert!(!det.is_stagnating());
        assert_eq!(det.snapshot_count(), 0);
        let report = det.stagnation_report();
        assert!(!report.is_stagnating);
        assert_eq!(report.summary, "No snapshots recorded.");
    }

    #[test]
    fn test_snapshot_detector_not_enough_data() {
        let mut det = SnapshotStagnationDetector::new(3);
        det.push(snap(0, vec!["a"], vec![], 0));
        det.push(snap(1, vec!["a"], vec![], 0));
        // Only 2 snapshots, need 4 (threshold=3 + 1 baseline).
        assert!(!det.is_stagnating());
    }

    #[test]
    fn test_snapshot_detector_stagnation() {
        let mut det = SnapshotStagnationDetector::new(2);
        // Baseline: 2 proved.
        det.push(snap(0, vec!["a", "b"], vec!["c"], 0));
        // Same count twice => stagnation.
        det.push(snap(1, vec!["a", "b"], vec!["c"], 0));
        det.push(snap(2, vec!["a", "b"], vec!["c"], 0));

        assert!(det.is_stagnating());
        let report = det.stagnation_report();
        assert!(report.is_stagnating);
        assert_eq!(report.stale_tail_length, 2);
        assert_eq!(report.stuck_vcs, vec!["c"]);
    }

    #[test]
    fn test_snapshot_detector_improvement_clears_stagnation() {
        let mut det = SnapshotStagnationDetector::new(2);
        det.push(snap(0, vec!["a"], vec!["b", "c"], 0));
        det.push(snap(1, vec!["a"], vec!["b", "c"], 0));
        det.push(snap(2, vec!["a"], vec!["b", "c"], 0));
        assert!(det.is_stagnating());

        // Now improve.
        det.push(snap(3, vec!["a", "b"], vec!["c"], 0));
        assert!(!det.is_stagnating());
    }

    #[test]
    fn test_snapshot_detector_stuck_vcs() {
        let mut det = SnapshotStagnationDetector::new(2);
        det.push(snap(0, vec!["a"], vec!["b", "c"], 0));
        det.push(snap(1, vec!["a", "b"], vec!["c"], 0));
        // "b" was eventually proved, "c" was never proved.
        let report = det.stagnation_report();
        assert_eq!(report.stuck_vcs, vec!["c"]);
    }

    #[test]
    fn test_snapshot_detector_convergence_ratios() {
        let mut det = SnapshotStagnationDetector::new(3);
        // 1/3 proved
        det.push(snap(0, vec!["a"], vec!["b", "c"], 0));
        // 2/3 proved
        det.push(snap(1, vec!["a", "b"], vec!["c"], 0));

        let report = det.stagnation_report();
        // Best ratio is 2/3.
        let best = report.best_convergence_ratio.expect("best ratio");
        assert!((best - 2.0 / 3.0).abs() < 0.01);
        // Current is also 2/3.
        let current = report.current_convergence_ratio.expect("current ratio");
        assert!((current - 2.0 / 3.0).abs() < 0.01);
    }

    #[test]
    fn test_stagnation_report_json_roundtrip() {
        let report = StagnationReport {
            is_stagnating: true,
            stale_tail_length: 3,
            threshold: 3,
            total_snapshots: 5,
            best_convergence_ratio: Some(0.8),
            current_convergence_ratio: Some(0.6),
            summary: "stagnating".into(),
            stuck_vcs: vec!["foo::bar".into()],
        };
        let json = serde_json::to_string(&report).expect("serialize");
        let deser: StagnationReport = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(report, deser);
    }

    #[test]
    fn test_snapshot_detector_default() {
        let det = SnapshotStagnationDetector::default();
        assert_eq!(det.threshold, 3);
    }

    #[test]
    #[should_panic(expected = "stagnation threshold must be non-zero")]
    fn test_snapshot_detector_zero_threshold_panics() {
        let _ = SnapshotStagnationDetector::new(0);
    }

    #[test]
    fn test_snapshot_detector_making_progress() {
        let mut det = SnapshotStagnationDetector::new(2);
        det.push(snap(0, vec!["a"], vec!["b"], 0));
        det.push(snap(1, vec!["a", "b"], vec![], 0));
        let report = det.stagnation_report();
        assert!(!report.is_stagnating);
        assert_eq!(report.summary, "Making progress.");
    }
}
