// trust-loop/analysis.rs: Loop analysis for convergence detection
//
// Analyzes verification loop iterations for convergence patterns, monotonicity,
// and fixpoint detection. Provides metrics for the prove-strengthen-backprop loop.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// ---------------------------------------------------------------------------
// Loop characteristics
// ---------------------------------------------------------------------------

/// Characteristic of a verification loop's behavior.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoopCharacteristic {
    /// Loop is converging toward a fixpoint.
    Converging,
    /// Loop is diverging (getting worse).
    Diverging,
    /// Loop is oscillating (alternating improvement/regression).
    Oscillating,
    /// Loop has reached a fixpoint (stable).
    Stable,
    /// Not enough data to determine.
    Unknown,
}

impl std::fmt::Display for LoopCharacteristic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Converging => write!(f, "converging"),
            Self::Diverging => write!(f, "diverging"),
            Self::Oscillating => write!(f, "oscillating"),
            Self::Stable => write!(f, "stable"),
            Self::Unknown => write!(f, "unknown"),
        }
    }
}

// ---------------------------------------------------------------------------
// Metric snapshot
// ---------------------------------------------------------------------------

/// A snapshot of verification metrics at one iteration.
#[derive(Debug, Clone)]
pub struct MetricSnapshot {
    /// Iteration number.
    pub iteration: u32,
    /// Number of VCs proved.
    pub proved: usize,
    /// Number of VCs failed.
    pub failed: usize,
    /// Number of VCs unknown/timeout.
    pub unknown: usize,
    /// Custom metric value (e.g., proof coverage percentage).
    pub metric: f64,
}

impl MetricSnapshot {
    pub fn new(iteration: u32, proved: usize, failed: usize, unknown: usize) -> Self {
        let total = proved + failed + unknown;
        let metric = if total == 0 { 0.0 } else { proved as f64 / total as f64 };
        Self { iteration, proved, failed, unknown, metric }
    }

    /// Total VCs.
    #[must_use]
    pub fn total(&self) -> usize {
        self.proved + self.failed + self.unknown
    }
}

// ---------------------------------------------------------------------------
// Monotonicity analysis
// ---------------------------------------------------------------------------

/// Direction of monotonic change.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Monotonicity {
    /// Strictly increasing.
    Increasing,
    /// Strictly decreasing.
    Decreasing,
    /// Non-decreasing (increasing or constant).
    NonDecreasing,
    /// Non-increasing (decreasing or constant).
    NonIncreasing,
    /// Not monotonic.
    None,
}

/// Analyze the monotonicity of a metric sequence.
pub fn analyze_monotonicity(snapshots: &[MetricSnapshot]) -> Monotonicity {
    if snapshots.len() < 2 {
        return Monotonicity::None;
    }

    let mut strictly_increasing = true;
    let mut strictly_decreasing = true;
    let mut non_decreasing = true;
    let mut non_increasing = true;

    for window in snapshots.windows(2) {
        let prev = window[0].metric;
        let curr = window[1].metric;

        if curr <= prev {
            strictly_increasing = false;
        }
        if curr >= prev {
            strictly_decreasing = false;
        }
        if curr < prev {
            non_decreasing = false;
        }
        if curr > prev {
            non_increasing = false;
        }
    }

    if strictly_increasing {
        Monotonicity::Increasing
    } else if strictly_decreasing {
        Monotonicity::Decreasing
    } else if non_decreasing {
        Monotonicity::NonDecreasing
    } else if non_increasing {
        Monotonicity::NonIncreasing
    } else {
        Monotonicity::None
    }
}

// ---------------------------------------------------------------------------
// Fixpoint detection
// ---------------------------------------------------------------------------

/// Configuration for fixpoint detection.
#[derive(Debug, Clone)]
pub struct FixpointConfig {
    /// How many stable iterations before declaring fixpoint.
    pub stable_threshold: usize,
    /// Tolerance for metric changes (values within this are "same").
    pub epsilon: f64,
}

impl Default for FixpointConfig {
    fn default() -> Self {
        Self { stable_threshold: 2, epsilon: 1e-9 }
    }
}

/// Detect fixpoint in a sequence of metric snapshots.
pub fn detect_fixpoint(snapshots: &[MetricSnapshot], config: &FixpointConfig) -> Option<u32> {
    if snapshots.len() < config.stable_threshold + 1 {
        return None;
    }

    let mut stable_count = 0;
    for window in snapshots.windows(2) {
        if (window[1].metric - window[0].metric).abs() < config.epsilon {
            stable_count += 1;
            if stable_count >= config.stable_threshold {
                return Some(window[1].iteration);
            }
        } else {
            stable_count = 0;
        }
    }

    None
}

// ---------------------------------------------------------------------------
// Convergence rate
// ---------------------------------------------------------------------------

/// Convergence rate analysis.
#[derive(Debug, Clone)]
pub struct ConvergenceRate {
    /// Average improvement per iteration.
    pub avg_improvement: f64,
    /// Rate of improvement change (acceleration/deceleration).
    pub acceleration: f64,
    /// Estimated iterations to reach target (None if diverging).
    pub estimated_remaining: Option<u32>,
}

/// Analyze the convergence rate toward a target metric.
pub fn convergence_rate(snapshots: &[MetricSnapshot], target: f64) -> ConvergenceRate {
    if snapshots.len() < 2 {
        return ConvergenceRate {
            avg_improvement: 0.0,
            acceleration: 0.0,
            estimated_remaining: None,
        };
    }

    let improvements: Vec<f64> = snapshots.windows(2).map(|w| w[1].metric - w[0].metric).collect();

    let avg = improvements.iter().sum::<f64>() / improvements.len() as f64;

    let acceleration = if improvements.len() >= 2 {
        let accels: Vec<f64> = improvements.windows(2).map(|w| w[1] - w[0]).collect();
        accels.iter().sum::<f64>() / accels.len() as f64
    } else {
        0.0
    };

    let current = snapshots.last().expect("invariant: len >= 2 guarantees last()").metric;
    let estimated = if current >= target {
        Some(0)
    } else if avg > 0.0 {
        let remaining = target - current;
        Some((remaining / avg).ceil() as u32)
    } else {
        None
    };

    ConvergenceRate { avg_improvement: avg, acceleration, estimated_remaining: estimated }
}

// ---------------------------------------------------------------------------
// Regression detection
// ---------------------------------------------------------------------------

/// A detected regression: the verification result got worse between two iterations.
#[derive(Debug, Clone, PartialEq)]
pub struct Regression {
    /// Iteration where the regression was detected.
    pub iteration: u32,
    /// The proved count dropped or failed/unknown count increased.
    pub proved_before: usize,
    pub proved_after: usize,
    pub failed_before: usize,
    pub failed_after: usize,
    pub unknown_before: usize,
    pub unknown_after: usize,
}

/// Detect non-monotonic regressions within a sequence of snapshots.
///
/// A regression occurs when the verification result gets WORSE between
/// consecutive iterations: proved count decreases, or failed/unknown count
/// increases. Returns all detected regressions.
pub fn detect_regressions(snapshots: &[MetricSnapshot]) -> Vec<Regression> {
    let mut regressions = Vec::new();

    for window in snapshots.windows(2) {
        let prev = &window[0];
        let curr = &window[1];

        // Regression: proved decreased OR failed increased OR unknown increased
        let proved_decreased = curr.proved < prev.proved;
        let failed_increased = curr.failed > prev.failed;
        let unknown_increased = curr.unknown > prev.unknown;

        if proved_decreased || failed_increased || unknown_increased {
            regressions.push(Regression {
                iteration: curr.iteration,
                proved_before: prev.proved,
                proved_after: curr.proved,
                failed_before: prev.failed,
                failed_after: curr.failed,
                unknown_before: prev.unknown,
                unknown_after: curr.unknown,
            });
        }
    }

    regressions
}

// ---------------------------------------------------------------------------
// Loop characteristic analysis
// ---------------------------------------------------------------------------

/// Classify the overall characteristic of a verification loop.
pub fn classify_loop(snapshots: &[MetricSnapshot]) -> LoopCharacteristic {
    if snapshots.len() < 2 {
        return LoopCharacteristic::Unknown;
    }

    let config = FixpointConfig::default();
    if detect_fixpoint(snapshots, &config).is_some() {
        return LoopCharacteristic::Stable;
    }

    let monotonicity = analyze_monotonicity(snapshots);
    match monotonicity {
        Monotonicity::Increasing | Monotonicity::NonDecreasing => LoopCharacteristic::Converging,
        Monotonicity::Decreasing | Monotonicity::NonIncreasing => LoopCharacteristic::Diverging,
        Monotonicity::None => {
            // Check for oscillation: alternating signs of change
            let changes: Vec<f64> =
                snapshots.windows(2).map(|w| w[1].metric - w[0].metric).collect();
            let sign_changes = changes
                .windows(2)
                .filter(|w| (w[0] > 0.0 && w[1] < 0.0) || (w[0] < 0.0 && w[1] > 0.0))
                .count();
            if sign_changes > changes.len() / 2 {
                LoopCharacteristic::Oscillating
            } else {
                LoopCharacteristic::Unknown
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn improving_snapshots() -> Vec<MetricSnapshot> {
        vec![
            MetricSnapshot::new(0, 2, 5, 3),
            MetricSnapshot::new(1, 4, 3, 3),
            MetricSnapshot::new(2, 6, 2, 2),
            MetricSnapshot::new(3, 8, 1, 1),
        ]
    }

    fn stable_snapshots() -> Vec<MetricSnapshot> {
        vec![
            MetricSnapshot::new(0, 5, 5, 0),
            MetricSnapshot::new(1, 5, 5, 0),
            MetricSnapshot::new(2, 5, 5, 0),
            MetricSnapshot::new(3, 5, 5, 0),
        ]
    }

    #[test]
    fn test_metric_snapshot_total() {
        let s = MetricSnapshot::new(0, 3, 2, 1);
        assert_eq!(s.total(), 6);
        assert!((s.metric - 0.5).abs() < 0.01); // 3/6 = 0.5
    }

    #[test]
    fn test_monotonicity_increasing() {
        let snaps = improving_snapshots();
        assert_eq!(analyze_monotonicity(&snaps), Monotonicity::Increasing);
    }

    #[test]
    fn test_monotonicity_decreasing() {
        let snaps = vec![
            MetricSnapshot::new(0, 8, 1, 1),
            MetricSnapshot::new(1, 6, 2, 2),
            MetricSnapshot::new(2, 4, 3, 3),
        ];
        assert_eq!(analyze_monotonicity(&snaps), Monotonicity::Decreasing);
    }

    #[test]
    fn test_monotonicity_non_decreasing() {
        let snaps = stable_snapshots();
        assert_eq!(analyze_monotonicity(&snaps), Monotonicity::NonDecreasing);
    }

    #[test]
    fn test_monotonicity_single_point() {
        let snaps = vec![MetricSnapshot::new(0, 5, 5, 0)];
        assert_eq!(analyze_monotonicity(&snaps), Monotonicity::None);
    }

    #[test]
    fn test_fixpoint_detection() {
        let snaps = stable_snapshots();
        let config = FixpointConfig::default();
        let fp = detect_fixpoint(&snaps, &config);
        assert!(fp.is_some());
    }

    #[test]
    fn test_no_fixpoint() {
        let snaps = improving_snapshots();
        let config = FixpointConfig::default();
        assert!(detect_fixpoint(&snaps, &config).is_none());
    }

    #[test]
    fn test_convergence_rate_improving() {
        let snaps = improving_snapshots();
        let rate = convergence_rate(&snaps, 1.0);
        assert!(rate.avg_improvement > 0.0);
        assert!(rate.estimated_remaining.is_some());
    }

    #[test]
    fn test_convergence_rate_at_target() {
        let snaps = vec![
            MetricSnapshot { iteration: 0, proved: 10, failed: 0, unknown: 0, metric: 1.0 },
            MetricSnapshot { iteration: 1, proved: 10, failed: 0, unknown: 0, metric: 1.0 },
        ];
        let rate = convergence_rate(&snaps, 1.0);
        assert_eq!(rate.estimated_remaining, Some(0));
    }

    #[test]
    fn test_classify_converging() {
        let snaps = improving_snapshots();
        assert_eq!(classify_loop(&snaps), LoopCharacteristic::Converging);
    }

    #[test]
    fn test_classify_stable() {
        let snaps = stable_snapshots();
        assert_eq!(classify_loop(&snaps), LoopCharacteristic::Stable);
    }

    #[test]
    fn test_classify_unknown_single() {
        let snaps = vec![MetricSnapshot::new(0, 5, 5, 0)];
        assert_eq!(classify_loop(&snaps), LoopCharacteristic::Unknown);
    }

    #[test]
    fn test_loop_characteristic_display() {
        assert_eq!(LoopCharacteristic::Converging.to_string(), "converging");
        assert_eq!(LoopCharacteristic::Stable.to_string(), "stable");
        assert_eq!(LoopCharacteristic::Oscillating.to_string(), "oscillating");
    }

    #[test]
    fn test_fixpoint_config_default() {
        let config = FixpointConfig::default();
        assert_eq!(config.stable_threshold, 2);
    }

    #[test]
    fn test_convergence_rate_empty() {
        let rate = convergence_rate(&[], 1.0);
        assert_eq!(rate.avg_improvement, 0.0);
        assert!(rate.estimated_remaining.is_none());
    }

    // -----------------------------------------------------------------------
    // Regression detection
    // -----------------------------------------------------------------------

    #[test]
    fn test_detect_regressions_none_when_improving() {
        let snaps = improving_snapshots();
        let regressions = detect_regressions(&snaps);
        assert!(regressions.is_empty(), "improving sequence should have no regressions");
    }

    #[test]
    fn test_detect_regressions_none_when_stable() {
        let snaps = stable_snapshots();
        let regressions = detect_regressions(&snaps);
        assert!(regressions.is_empty(), "stable sequence should have no regressions");
    }

    #[test]
    fn test_detect_regressions_proved_decreased() {
        let snaps = vec![
            MetricSnapshot::new(1, 5, 3, 2),
            MetricSnapshot::new(2, 3, 3, 4), // proved went from 5 to 3
        ];
        let regressions = detect_regressions(&snaps);
        assert_eq!(regressions.len(), 1);
        assert_eq!(regressions[0].iteration, 2);
        assert_eq!(regressions[0].proved_before, 5);
        assert_eq!(regressions[0].proved_after, 3);
    }

    #[test]
    fn test_detect_regressions_failed_increased() {
        let snaps = vec![
            MetricSnapshot::new(1, 5, 2, 3),
            MetricSnapshot::new(2, 5, 4, 1), // failed went from 2 to 4
        ];
        let regressions = detect_regressions(&snaps);
        assert_eq!(regressions.len(), 1);
        assert_eq!(regressions[0].failed_before, 2);
        assert_eq!(regressions[0].failed_after, 4);
    }

    #[test]
    fn test_detect_regressions_unknown_increased() {
        let snaps = vec![
            MetricSnapshot::new(1, 5, 3, 2),
            MetricSnapshot::new(2, 5, 3, 5), // unknown went from 2 to 5
        ];
        let regressions = detect_regressions(&snaps);
        assert_eq!(regressions.len(), 1);
        assert_eq!(regressions[0].unknown_before, 2);
        assert_eq!(regressions[0].unknown_after, 5);
    }

    #[test]
    fn test_detect_regressions_mid_sequence() {
        // Improving, then regressing, then improving again
        let snaps = vec![
            MetricSnapshot::new(1, 3, 5, 2),
            MetricSnapshot::new(2, 5, 3, 2),
            MetricSnapshot::new(3, 2, 6, 2), // regression: proved 5->2, failed 3->6
            MetricSnapshot::new(4, 6, 2, 2),
        ];
        let regressions = detect_regressions(&snaps);
        assert_eq!(regressions.len(), 1);
        assert_eq!(regressions[0].iteration, 3);
    }

    #[test]
    fn test_detect_regressions_empty_and_single() {
        assert!(detect_regressions(&[]).is_empty());
        assert!(detect_regressions(&[MetricSnapshot::new(1, 5, 3, 2)]).is_empty());
    }
}
