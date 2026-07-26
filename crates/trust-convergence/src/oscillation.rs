// trust-convergence/src/oscillation.rs — Oscillation detection and damping
//
// Part of #295: Add oscillation detection and damping to trust-convergence
//
// Detects cyclic patterns in the prove-strengthen-backpropagate loop and
// applies damping strategies to break them. Operates on f64 metric histories.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Detected oscillation pattern in a metric history.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum OscillationPattern {
    /// Binary flip-flop between two values (period 2).
    Binary,
    /// Periodic oscillation with the given cycle length (period >= 3).
    Periodic(usize),
    /// Values are diverging — amplitude increasing over time.
    Divergent,
}

/// Strategy for damping oscillations in proposed values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum DampingStrategy {
    /// Average current proposal with previous value.
    Averaging,
    /// Momentum-based: blend current with exponentially weighted moving average.
    Momentum,
    /// Exponential decay: scale proposal toward a stable anchor over time.
    ExponentialDecay,
    /// Low-pass filter: suppress high-frequency oscillation components.
    FrequencyCutoff,
}

/// Configuration for oscillation detection.
#[derive(Debug, Clone, PartialEq)]
pub struct OscillationConfig {
    /// Minimum history length before detection kicks in.
    pub min_history: usize,
    /// Tolerance for considering two values "equal" in pattern matching.
    pub tolerance: f64,
    /// Maximum cycle length to search for periodic patterns.
    pub max_period: usize,
    /// Momentum factor for `DampingStrategy::Momentum` in (0.0, 1.0).
    pub momentum_factor: f64,
    /// Decay rate for `DampingStrategy::ExponentialDecay` in (0.0, 1.0).
    pub decay_rate: f64,
}

impl Default for OscillationConfig {
    fn default() -> Self {
        Self {
            min_history: 4,
            tolerance: 1e-9,
            max_period: 8,
            momentum_factor: 0.7,
            decay_rate: 0.5,
        }
    }
}

/// Detect oscillation patterns in a metric history.
///
/// Checks for binary flip-flop, periodic cycles, and divergence.
/// Returns `None` if no pattern is detected or the history is too short.
#[must_use]
pub(crate) fn detect_oscillation(
    history: &[f64],
    config: &OscillationConfig,
) -> Option<OscillationPattern> {
    if history.len() < config.min_history {
        return None;
    }

    // Check for divergence first (amplitude increasing).
    if is_divergent(history, config) {
        return Some(OscillationPattern::Divergent);
    }

    // Check for binary flip-flop (period 2).
    if is_binary_oscillation(history, config) {
        return Some(OscillationPattern::Binary);
    }

    // Check for periodic patterns (period 3..=max_period).
    for period in 3..=config.max_period.min(history.len() / 2) {
        if is_periodic(history, period, config) {
            return Some(OscillationPattern::Periodic(period));
        }
    }

    None
}

/// Apply damping to a proposed value to break oscillation.
///
/// Uses the history and chosen strategy to modify the proposal toward stability.
#[must_use]
pub(crate) fn apply_damping(
    proposed: f64,
    history: &[f64],
    strategy: DampingStrategy,
    config: &OscillationConfig,
) -> f64 {
    if history.is_empty() {
        return proposed;
    }

    match strategy {
        DampingStrategy::Averaging => {
            let prev = history[history.len() - 1];
            (proposed + prev) / 2.0
        }
        DampingStrategy::Momentum => {
            // Exponentially weighted moving average of history, then blend with proposed.
            let alpha = config.momentum_factor;
            let ewma = compute_ewma(history, alpha);
            alpha * ewma + (1.0 - alpha) * proposed
        }
        DampingStrategy::ExponentialDecay => {
            // Pull proposed toward the mean of recent history.
            let anchor = mean(history);
            let rate = config.decay_rate;
            anchor + rate * (proposed - anchor)
        }
        DampingStrategy::FrequencyCutoff => {
            // Simple low-pass: weighted average of last 3 values + proposed.
            let n = history.len().min(3);
            let tail = &history[history.len() - n..];
            let weights: &[f64] = match n {
                1 => &[0.3],
                2 => &[0.15, 0.25],
                _ => &[0.1, 0.15, 0.25],
            };
            let proposed_weight = 1.0 - weights.iter().sum::<f64>();
            let weighted_sum: f64 = tail.iter().zip(weights.iter()).map(|(v, w)| v * w).sum();
            weighted_sum + proposed_weight * proposed
        }
    }
}

/// Check if oscillation amplitude is increasing over time.
fn is_divergent(history: &[f64], config: &OscillationConfig) -> bool {
    if history.len() < 4 {
        return false;
    }

    // Compute successive absolute differences and check if they are increasing.
    let diffs: Vec<f64> = history.windows(2).map(|w| (w[1] - w[0]).abs()).collect();
    if diffs.len() < 3 {
        return false;
    }

    // Check the last 3 diffs for a monotonically increasing trend.
    let n = diffs.len();
    let tail = &diffs[n.saturating_sub(3)..n];
    tail.windows(2).all(|w| w[1] > w[0] + config.tolerance)
}

/// Check for binary (period-2) oscillation in the tail of history.
fn is_binary_oscillation(history: &[f64], config: &OscillationConfig) -> bool {
    let n = history.len();
    if n < 4 {
        return false;
    }

    // Check that at least the last 4 values alternate: a, b, a, b
    let tail = &history[n - 4..];
    approx_eq(tail[0], tail[2], config.tolerance)
        && approx_eq(tail[1], tail[3], config.tolerance)
        && !approx_eq(tail[0], tail[1], config.tolerance)
}

/// Check for periodic oscillation with the given period.
fn is_periodic(history: &[f64], period: usize, config: &OscillationConfig) -> bool {
    let n = history.len();
    // Need at least 2 full cycles to confirm.
    let required = period * 2;
    if n < required {
        return false;
    }

    let tail = &history[n - required..];
    // Check that each position in the second cycle matches the first.
    (0..period).all(|i| approx_eq(tail[i], tail[i + period], config.tolerance))
}

fn approx_eq(a: f64, b: f64, tolerance: f64) -> bool {
    (a - b).abs() <= tolerance
}

fn mean(values: &[f64]) -> f64 {
    if values.is_empty() {
        return 0.0;
    }
    values.iter().sum::<f64>() / values.len() as f64
}

/// Exponentially weighted moving average.
fn compute_ewma(history: &[f64], alpha: f64) -> f64 {
    let mut ewma = history[0];
    for &val in &history[1..] {
        ewma = alpha * val + (1.0 - alpha) * ewma;
    }
    ewma
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::f64::consts::PI;

    fn default_config() -> OscillationConfig {
        OscillationConfig::default()
    }

    #[test]
    fn test_detect_binary_oscillation() {
        let history = vec![1.0, 2.0, 1.0, 2.0, 1.0, 2.0];
        let pattern = detect_oscillation(&history, &default_config());
        assert_eq!(pattern, Some(OscillationPattern::Binary));
    }

    #[test]
    fn test_detect_periodic_oscillation_period_3() {
        let history = vec![1.0, 2.0, 3.0, 1.0, 2.0, 3.0];
        let config = OscillationConfig { min_history: 4, ..default_config() };
        let pattern = detect_oscillation(&history, &config);
        assert_eq!(pattern, Some(OscillationPattern::Periodic(3)));
    }

    #[test]
    fn test_detect_divergent_oscillation() {
        // Amplitude increasing: diffs are 1, 2, 3, 4
        let history = vec![0.0, 1.0, -1.0, 2.0, -2.0, 5.0];
        let pattern = detect_oscillation(&history, &default_config());
        assert_eq!(pattern, Some(OscillationPattern::Divergent));
    }

    #[test]
    fn test_no_oscillation_stable_values() {
        let history = vec![5.0, 5.0, 5.0, 5.0, 5.0];
        let pattern = detect_oscillation(&history, &default_config());
        assert_eq!(pattern, None);
    }

    #[test]
    fn test_insufficient_history_returns_none() {
        let history = vec![1.0, 2.0];
        let pattern = detect_oscillation(&history, &default_config());
        assert_eq!(pattern, None);
    }

    #[test]
    fn test_damping_averaging() {
        let history = vec![10.0, 20.0];
        let damped = apply_damping(30.0, &history, DampingStrategy::Averaging, &default_config());
        // (30 + 20) / 2 = 25
        assert!((damped - 25.0).abs() < 1e-9);
    }

    #[test]
    fn test_damping_momentum() {
        let history = vec![10.0, 12.0, 14.0];
        let config = OscillationConfig { momentum_factor: 0.5, ..default_config() };
        let damped = apply_damping(20.0, &history, DampingStrategy::Momentum, &config);
        // EWMA with alpha=0.5: 10, 11, 12.5 => ewma=12.5
        // result = 0.5 * 12.5 + 0.5 * 20 = 6.25 + 10 = 16.25
        assert!((damped - 16.25).abs() < 1e-9);
    }

    #[test]
    fn test_damping_exponential_decay() {
        let history = vec![10.0, 20.0, 30.0];
        let config = OscillationConfig { decay_rate: 0.5, ..default_config() };
        let damped = apply_damping(50.0, &history, DampingStrategy::ExponentialDecay, &config);
        // mean = 20, result = 20 + 0.5*(50-20) = 35
        assert!((damped - 35.0).abs() < 1e-9);
    }

    #[test]
    fn test_damping_frequency_cutoff() {
        let history = vec![10.0, 20.0, 30.0];
        let damped =
            apply_damping(40.0, &history, DampingStrategy::FrequencyCutoff, &default_config());
        // weights: [0.1, 0.15, 0.25], proposed_weight = 0.5
        // 10*0.1 + 20*0.15 + 30*0.25 + 40*0.5 = 1 + 3 + 7.5 + 20 = 31.5
        assert!((damped - 31.5).abs() < 1e-9);
    }

    #[test]
    fn test_damping_empty_history_returns_proposed() {
        let damped = apply_damping(42.0, &[], DampingStrategy::Averaging, &default_config());
        assert!((damped - 42.0).abs() < 1e-9);
    }

    #[test]
    fn test_periodic_sinusoidal_signal() {
        // Generate a sinusoidal signal with period 4.
        let period = 4;
        let history: Vec<f64> =
            (0..8).map(|i| (2.0 * PI * i as f64 / period as f64).sin()).collect();
        let config = OscillationConfig { tolerance: 1e-6, ..default_config() };
        let pattern = detect_oscillation(&history, &config);
        assert_eq!(pattern, Some(OscillationPattern::Periodic(4)));
    }

    #[test]
    fn test_config_custom_min_history() {
        let config = OscillationConfig { min_history: 10, ..default_config() };
        // 6 points < min_history of 10 => None
        let history = vec![1.0, 2.0, 1.0, 2.0, 1.0, 2.0];
        assert_eq!(detect_oscillation(&history, &config), None);
    }
}
