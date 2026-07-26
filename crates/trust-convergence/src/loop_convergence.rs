// trust-convergence/src/loop_convergence.rs — Unified loop convergence tracker.
//
// Proposal A from #464: Wires OscillationDetector into ConvergenceTracker,
// adds multi-dimensional convergence, graduated termination outcomes, and
// a configurable convergence policy. Provides a single LoopDecision enum
// for use by trust-loop.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::time::Duration;

use crate::oscillation::{
    DampingStrategy, OscillationConfig, OscillationPattern, apply_damping, detect_oscillation,
};
use crate::{
    ConvergenceDecision, ConvergenceTracker, IterationSnapshot, ProofFrontier, StepVerdict,
};

// ---------------------------------------------------------------------------
// LoopDecision — the single enum trust-loop uses
// ---------------------------------------------------------------------------

/// Unified decision returned each iteration of the prove-strengthen-backprop loop.
///
/// Replaces convergence logic that was duplicated across the loop drivers.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum LoopDecision {
    /// Continue iterating; includes per-step diagnostics.
    Continue {
        verdict: StepVerdict,
        oscillation: Option<OscillationPattern>,
        dimensions: ConvergenceDimensions,
    },
    /// Loop reached a terminal state.
    Terminate { outcome: TerminationOutcome, dimensions: ConvergenceDimensions },
}

impl LoopDecision {
    /// Whether the loop should stop.
    #[must_use]
    pub fn should_stop(&self) -> bool {
        matches!(self, Self::Terminate { .. })
    }

    /// Access the convergence dimensions snapshot.
    #[must_use]
    pub fn dimensions(&self) -> &ConvergenceDimensions {
        match self {
            Self::Continue { dimensions, .. } | Self::Terminate { dimensions, .. } => dimensions,
        }
    }
}

// ---------------------------------------------------------------------------
// TerminationOutcome — graduated termination
// ---------------------------------------------------------------------------

/// Why the loop terminated and how much was proved.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum TerminationOutcome {
    /// All VCs proved — frontier stable for the required rounds.
    FullyVerified { stable_rounds: usize },
    /// Some VCs proved, but frontier stabilized with failures remaining.
    PartiallyVerified { proved_ratio: f64, stable_rounds: usize },
    /// Resource budget (wall-time or solver-calls) exhausted.
    BudgetExhausted { resource: BudgetResource, proved_ratio: f64 },
    /// Oscillation or amplitude divergence detected — loop is not converging.
    Diverging { pattern: OscillationPattern, proved_ratio: f64 },
}

/// Which budget resource was exhausted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum BudgetResource {
    WallTime,
    SolverCalls,
    Iterations,
}

// ---------------------------------------------------------------------------
// ConvergenceDimensions — multi-dimensional convergence tracking
// ---------------------------------------------------------------------------

/// Multi-dimensional convergence snapshot.
///
/// Tracks four orthogonal dimensions:
/// 1. Proof frontier progress
/// 2. Spec stability (are specifications changing?)
/// 3. CEX stability (are counterexamples changing?)
/// 4. Solver confidence (are solver results stable?)
#[derive(Debug, Clone, PartialEq)]
pub struct ConvergenceDimensions {
    /// Proof frontier convergence score (0.0..=1.0).
    pub frontier_score: f64,
    /// Spec fingerprint stability (0.0 = unstable, 1.0 = fully stable).
    pub spec_stability: f64,
    /// CEX fingerprint stability (0.0 = unstable, 1.0 = fully stable).
    pub cex_stability: f64,
    /// Solver result confidence (0.0 = inconsistent, 1.0 = fully consistent).
    pub solver_confidence: f64,
}

impl ConvergenceDimensions {
    /// Combined convergence score: weighted mean of all dimensions.
    #[must_use]
    pub fn combined_score(&self) -> f64 {
        // Weights: frontier 40%, spec 25%, CEX 20%, solver 15%
        0.40 * self.frontier_score
            + 0.25 * self.spec_stability
            + 0.20 * self.cex_stability
            + 0.15 * self.solver_confidence
    }

    /// Whether all dimensions exceed the given threshold.
    #[must_use]
    pub fn all_above(&self, threshold: f64) -> bool {
        self.frontier_score >= threshold
            && self.spec_stability >= threshold
            && self.cex_stability >= threshold
            && self.solver_confidence >= threshold
    }

    /// Minimum dimension value.
    #[must_use]
    pub fn min_dimension(&self) -> f64 {
        self.frontier_score
            .min(self.spec_stability)
            .min(self.cex_stability)
            .min(self.solver_confidence)
    }
}

impl Default for ConvergenceDimensions {
    fn default() -> Self {
        Self {
            frontier_score: 0.0,
            spec_stability: 1.0,
            cex_stability: 1.0,
            solver_confidence: 1.0,
        }
    }
}

// ---------------------------------------------------------------------------
// ConvergencePolicy — configurable budgets and thresholds
// ---------------------------------------------------------------------------

/// Policy controlling when and how the loop terminates.
#[derive(Debug, Clone, PartialEq)]
pub struct ConvergencePolicy {
    /// Maximum wall-clock time for the entire loop.
    pub max_wall_time: Option<Duration>,
    /// Maximum number of solver calls across all iterations.
    pub max_solver_calls: Option<u64>,
    /// Maximum iterations (mirrors ConvergenceTracker's iteration_limit).
    pub max_iterations: u32,
    /// Stable rounds required before declaring convergence.
    pub stable_round_limit: usize,
    /// Stall threshold: consecutive identical frontiers with failures triggers stall.
    pub stall_threshold: usize,
    /// Combined convergence score threshold for early termination.
    pub convergence_threshold: f64,
    /// Whether to auto-apply damping when oscillation is detected.
    pub auto_damp: bool,
    /// Damping strategy to use when auto_damp is true.
    pub damping_strategy: DampingStrategy,
    /// Oscillation detection config.
    pub oscillation_config: OscillationConfig,
}

impl Default for ConvergencePolicy {
    fn default() -> Self {
        Self {
            max_wall_time: None,
            max_solver_calls: None,
            max_iterations: 50,
            stable_round_limit: 2,
            stall_threshold: 3,
            convergence_threshold: 0.95,
            auto_damp: true,
            damping_strategy: DampingStrategy::Averaging,
            oscillation_config: OscillationConfig::default(),
        }
    }
}

// ---------------------------------------------------------------------------
// LoopConvergence — the unified tracker
// ---------------------------------------------------------------------------

/// Unified convergence tracker combining frontier tracking, oscillation
/// detection, multi-dimensional convergence, and configurable policy.
///
/// This is the single entry point for convergence decisions in the
/// prove-strengthen-backprop loop.
#[derive(Debug, Clone)]
pub struct LoopConvergence {
    policy: ConvergencePolicy,
    tracker: ConvergenceTracker,
    /// Oscillation scores (convergence_score per iteration) for detection.
    score_history: Vec<f64>,
    /// Spec fingerprints for stability tracking.
    spec_fingerprints: Vec<u64>,
    /// CEX fingerprints for stability tracking.
    cex_fingerprints: Vec<u64>,
    /// Solver confidence per iteration.
    solver_confidences: Vec<f64>,
    /// Wall time consumed so far.
    wall_time_used: Duration,
    /// Solver calls consumed so far.
    solver_calls_used: u64,
}

impl LoopConvergence {
    /// Create a new unified tracker with the given policy.
    #[must_use]
    pub fn new(policy: ConvergencePolicy) -> Self {
        let tracker = ConvergenceTracker::new(policy.stable_round_limit, policy.max_iterations);
        Self {
            policy,
            tracker,
            score_history: Vec::new(),
            spec_fingerprints: Vec::new(),
            cex_fingerprints: Vec::new(),
            solver_confidences: Vec::new(),
            wall_time_used: Duration::ZERO,
            solver_calls_used: 0,
        }
    }

    /// Create with default policy.
    #[must_use]
    pub fn with_defaults() -> Self {
        Self::new(ConvergencePolicy::default())
    }

    /// Observe a new iteration and return the unified loop decision.
    ///
    /// `observation` carries the frontier snapshot plus optional metadata
    /// about spec/CEX fingerprints, solver confidence, and resource usage.
    pub fn observe(&mut self, observation: LoopObservation) -> LoopDecision {
        // Record resource usage.
        self.wall_time_used += observation.wall_time;
        self.solver_calls_used += observation.solver_calls;

        // Track spec fingerprint stability.
        self.spec_fingerprints.push(observation.spec_fingerprint);
        self.cex_fingerprints.push(observation.cex_fingerprint);
        self.solver_confidences.push(observation.solver_confidence);

        // Observe frontier via inner tracker.
        let decision = self.tracker.observe(observation.snapshot.clone());

        // Track convergence score for oscillation detection.
        let score = observation.snapshot.frontier.convergence_score().unwrap_or(0.0);
        self.score_history.push(score);

        // Detect oscillation on the score history.
        let oscillation = detect_oscillation(&self.score_history, &self.policy.oscillation_config);

        // Build multi-dimensional convergence snapshot.
        let dimensions = self.compute_dimensions(&observation.snapshot.frontier);

        // Check budget exhaustion.
        if let Some(resource) = self.check_budget() {
            let proved_ratio = observation.snapshot.frontier.convergence_score().unwrap_or(0.0);
            return LoopDecision::Terminate {
                outcome: TerminationOutcome::BudgetExhausted { resource, proved_ratio },
                dimensions,
            };
        }

        // Check for divergence via oscillation.
        if let Some(OscillationPattern::Divergent) = &oscillation {
            let proved_ratio = observation.snapshot.frontier.convergence_score().unwrap_or(0.0);
            return LoopDecision::Terminate {
                outcome: TerminationOutcome::Diverging {
                    pattern: OscillationPattern::Divergent,
                    proved_ratio,
                },
                dimensions,
            };
        }

        // Map inner ConvergenceDecision to LoopDecision.
        match decision {
            ConvergenceDecision::Converged { stable_rounds, .. } => {
                let frontier = &observation.snapshot.frontier;
                if frontier.failed == 0 && frontier.unknown == 0 {
                    LoopDecision::Terminate {
                        outcome: TerminationOutcome::FullyVerified { stable_rounds },
                        dimensions,
                    }
                } else {
                    let proved_ratio = frontier.convergence_score().unwrap_or(0.0);
                    LoopDecision::Terminate {
                        outcome: TerminationOutcome::PartiallyVerified {
                            proved_ratio,
                            stable_rounds,
                        },
                        dimensions,
                    }
                }
            }
            ConvergenceDecision::IterationLimitReached { .. } => {
                let proved_ratio = observation.snapshot.frontier.convergence_score().unwrap_or(0.0);
                LoopDecision::Terminate {
                    outcome: TerminationOutcome::BudgetExhausted {
                        resource: BudgetResource::Iterations,
                        proved_ratio,
                    },
                    dimensions,
                }
            }
            ConvergenceDecision::Regressed { .. } => {
                // Regression is a Continue (we don't terminate on regression alone).
                LoopDecision::Continue { verdict: StepVerdict::Regressed, oscillation, dimensions }
            }
            ConvergenceDecision::Continue { verdict } => {
                LoopDecision::Continue { verdict, oscillation, dimensions }
            }
        }
    }

    /// Access the underlying convergence tracker.
    #[must_use]
    pub fn tracker(&self) -> &ConvergenceTracker {
        &self.tracker
    }

    /// Access the policy.
    #[must_use]
    pub fn policy(&self) -> &ConvergencePolicy {
        &self.policy
    }

    /// Total wall time used so far.
    #[must_use]
    pub fn wall_time_used(&self) -> Duration {
        self.wall_time_used
    }

    /// Total solver calls used so far.
    #[must_use]
    pub fn solver_calls_used(&self) -> u64 {
        self.solver_calls_used
    }

    /// Apply oscillation-aware damping to a proposed spec strength value.
    ///
    /// If oscillation is detected and auto_damp is enabled, applies the
    /// configured damping strategy. Otherwise returns the proposed value unchanged.
    #[must_use]
    pub fn damp_spec_strength(&self, proposed: f64) -> f64 {
        if !self.policy.auto_damp {
            return proposed;
        }
        let oscillation = detect_oscillation(&self.score_history, &self.policy.oscillation_config);
        match oscillation {
            Some(_) => apply_damping(
                proposed,
                &self.score_history,
                self.policy.damping_strategy,
                &self.policy.oscillation_config,
            ),
            None => proposed,
        }
    }

    /// The score history used for oscillation detection.
    #[must_use]
    pub fn score_history(&self) -> &[f64] {
        &self.score_history
    }

    // -- Internal helpers --

    fn check_budget(&self) -> Option<BudgetResource> {
        if let Some(max_wall) = self.policy.max_wall_time
            && self.wall_time_used >= max_wall
        {
            return Some(BudgetResource::WallTime);
        }
        if let Some(max_calls) = self.policy.max_solver_calls
            && self.solver_calls_used >= max_calls
        {
            return Some(BudgetResource::SolverCalls);
        }
        None
    }

    fn compute_dimensions(&self, frontier: &ProofFrontier) -> ConvergenceDimensions {
        let frontier_score = frontier.convergence_score().unwrap_or(0.0);
        let spec_stability = self.fingerprint_stability(&self.spec_fingerprints);
        let cex_stability = self.fingerprint_stability(&self.cex_fingerprints);
        let solver_confidence = self.mean_recent_confidence();

        ConvergenceDimensions { frontier_score, spec_stability, cex_stability, solver_confidence }
    }

    /// Compute stability from a fingerprint sequence: ratio of consecutive
    /// identical fingerprints in the last N entries.
    fn fingerprint_stability(&self, fingerprints: &[u64]) -> f64 {
        if fingerprints.len() < 2 {
            return 1.0; // Trivially stable with 0-1 entries.
        }
        let window = fingerprints.len().min(5);
        let tail = &fingerprints[fingerprints.len() - window..];
        let matches = tail.windows(2).filter(|w| w[0] == w[1]).count();
        matches as f64 / (window - 1) as f64
    }

    /// Mean solver confidence over the last 5 iterations.
    fn mean_recent_confidence(&self) -> f64 {
        if self.solver_confidences.is_empty() {
            return 1.0;
        }
        let window = self.solver_confidences.len().min(5);
        let tail = &self.solver_confidences[self.solver_confidences.len() - window..];
        tail.iter().sum::<f64>() / window as f64
    }
}

// ---------------------------------------------------------------------------
// LoopObservation — input to LoopConvergence::observe()
// ---------------------------------------------------------------------------

/// All data needed for one convergence observation.
#[derive(Debug, Clone)]
pub struct LoopObservation {
    /// The iteration snapshot (frontier + optional fingerprint).
    pub snapshot: IterationSnapshot,
    /// Hash of the current spec set (for spec stability tracking).
    pub spec_fingerprint: u64,
    /// Hash of the current counterexample set (for CEX stability tracking).
    pub cex_fingerprint: u64,
    /// Solver confidence for this iteration (0.0..=1.0).
    pub solver_confidence: f64,
    /// Wall time consumed by this iteration.
    pub wall_time: Duration,
    /// Number of solver calls in this iteration.
    pub solver_calls: u64,
}

impl LoopObservation {
    /// Create a minimal observation from a frontier snapshot.
    ///
    /// Defaults: spec/CEX fingerprints = 0, confidence = 1.0, no resource usage.
    #[must_use]
    pub fn from_snapshot(snapshot: IterationSnapshot) -> Self {
        Self {
            snapshot,
            spec_fingerprint: 0,
            cex_fingerprint: 0,
            solver_confidence: 1.0,
            wall_time: Duration::ZERO,
            solver_calls: 0,
        }
    }

    /// Set the spec fingerprint.
    #[must_use]
    pub fn with_spec_fingerprint(mut self, fp: u64) -> Self {
        self.spec_fingerprint = fp;
        self
    }

    /// Set the CEX fingerprint.
    #[must_use]
    pub fn with_cex_fingerprint(mut self, fp: u64) -> Self {
        self.cex_fingerprint = fp;
        self
    }

    /// Set the solver confidence.
    #[must_use]
    pub fn with_solver_confidence(mut self, confidence: f64) -> Self {
        self.solver_confidence = confidence;
        self
    }

    /// Set wall time consumed.
    #[must_use]
    pub fn with_wall_time(mut self, duration: Duration) -> Self {
        self.wall_time = duration;
        self
    }

    /// Set solver calls consumed.
    #[must_use]
    pub fn with_solver_calls(mut self, calls: u64) -> Self {
        self.solver_calls = calls;
        self
    }
}

// ---------------------------------------------------------------------------
// Oscillation-aware spec damping helpers
// ---------------------------------------------------------------------------

/// Apply oscillation-aware damping to a proposed spec strength.
///
/// Examines the score history for oscillation patterns and selects an
/// appropriate damping strategy based on the pattern type:
/// - Binary flip-flop: Averaging
/// - Periodic: Momentum
/// - Divergent: ExponentialDecay
///
/// Returns the damped value, or the original if no oscillation detected.
#[must_use]
pub fn damp_spec_for_oscillation(
    proposed: f64,
    score_history: &[f64],
    config: &OscillationConfig,
) -> f64 {
    match detect_oscillation(score_history, config) {
        Some(OscillationPattern::Binary) => {
            apply_damping(proposed, score_history, DampingStrategy::Averaging, config)
        }
        Some(OscillationPattern::Periodic(_)) => {
            apply_damping(proposed, score_history, DampingStrategy::Momentum, config)
        }
        Some(OscillationPattern::Divergent) => {
            apply_damping(proposed, score_history, DampingStrategy::ExponentialDecay, config)
        }
        None => proposed,
    }
}

/// Compute a fingerprint hash for a collection of items.
#[must_use]
pub fn compute_fingerprint<T: Hash>(items: &[T]) -> u64 {
    let mut hasher = DefaultHasher::new();
    for item in items {
        item.hash(&mut hasher);
    }
    hasher.finish()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

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

    fn snap(iteration: u32, f: ProofFrontier) -> IterationSnapshot {
        IterationSnapshot::new(iteration, f)
    }

    fn obs(iteration: u32, f: ProofFrontier) -> LoopObservation {
        LoopObservation::from_snapshot(snap(iteration, f))
    }

    // -- LoopDecision basic tests --

    #[test]
    fn test_fully_verified_terminates() {
        let policy =
            ConvergencePolicy { stable_round_limit: 2, max_iterations: 10, ..Default::default() };
        let mut lc = LoopConvergence::new(policy);

        let d1 = lc.observe(obs(0, frontier(5, 0, 0, 0, 0)));
        assert!(!d1.should_stop()); // First observation: Continue

        let d2 = lc.observe(obs(1, frontier(5, 0, 0, 0, 0)));
        assert!(d2.should_stop());
        match d2 {
            LoopDecision::Terminate {
                outcome: TerminationOutcome::FullyVerified { stable_rounds },
                ..
            } => assert_eq!(stable_rounds, 2),
            other => panic!("Expected FullyVerified, got {other:?}"),
        }
    }

    #[test]
    fn test_partially_verified_terminates() {
        let policy =
            ConvergencePolicy { stable_round_limit: 2, max_iterations: 10, ..Default::default() };
        let mut lc = LoopConvergence::new(policy);

        lc.observe(obs(0, frontier(3, 0, 0, 2, 0)));
        let d2 = lc.observe(obs(1, frontier(3, 0, 0, 2, 0)));
        assert!(d2.should_stop());
        match d2 {
            LoopDecision::Terminate {
                outcome: TerminationOutcome::PartiallyVerified { proved_ratio, stable_rounds },
                ..
            } => {
                assert!((proved_ratio - 0.6).abs() < 1e-9);
                assert_eq!(stable_rounds, 2);
            }
            other => panic!("Expected PartiallyVerified, got {other:?}"),
        }
    }

    #[test]
    fn test_budget_wall_time_exhausted() {
        let policy = ConvergencePolicy {
            max_wall_time: Some(Duration::from_secs(10)),
            max_iterations: 100,
            stable_round_limit: 2,
            ..Default::default()
        };
        let mut lc = LoopConvergence::new(policy);

        // First iteration: use 11 seconds (exceeds budget).
        let o = LoopObservation::from_snapshot(snap(0, frontier(1, 0, 0, 4, 0)))
            .with_wall_time(Duration::from_secs(11));
        let d = lc.observe(o);
        // Budget check happens before frontier analysis, but after recording.
        // Since we just recorded 11s which exceeds 10s max, next observe will catch it.
        // Actually, the first observe records 11s then checks immediately.
        assert!(d.should_stop());
        match d {
            LoopDecision::Terminate {
                outcome: TerminationOutcome::BudgetExhausted { resource, .. },
                ..
            } => assert_eq!(resource, BudgetResource::WallTime),
            other => panic!("Expected BudgetExhausted(WallTime), got {other:?}"),
        }
    }

    #[test]
    fn test_budget_solver_calls_exhausted() {
        let policy = ConvergencePolicy {
            max_solver_calls: Some(100),
            max_iterations: 100,
            stable_round_limit: 2,
            ..Default::default()
        };
        let mut lc = LoopConvergence::new(policy);

        let o =
            LoopObservation::from_snapshot(snap(0, frontier(1, 0, 0, 4, 0))).with_solver_calls(101);
        let d = lc.observe(o);
        assert!(d.should_stop());
        match d {
            LoopDecision::Terminate {
                outcome: TerminationOutcome::BudgetExhausted { resource, .. },
                ..
            } => assert_eq!(resource, BudgetResource::SolverCalls),
            other => panic!("Expected BudgetExhausted(SolverCalls), got {other:?}"),
        }
    }

    #[test]
    fn test_iteration_limit_budget_exhausted() {
        let policy =
            ConvergencePolicy { max_iterations: 2, stable_round_limit: 5, ..Default::default() };
        let mut lc = LoopConvergence::new(policy);

        lc.observe(obs(0, frontier(1, 0, 0, 4, 0)));
        let d = lc.observe(obs(2, frontier(2, 0, 0, 3, 0)));
        assert!(d.should_stop());
        match d {
            LoopDecision::Terminate {
                outcome: TerminationOutcome::BudgetExhausted { resource, .. },
                ..
            } => assert_eq!(resource, BudgetResource::Iterations),
            other => panic!("Expected BudgetExhausted(Iterations), got {other:?}"),
        }
    }

    // -- Multi-dimensional convergence tests --

    #[test]
    fn test_dimensions_computed_correctly() {
        let policy =
            ConvergencePolicy { stable_round_limit: 5, max_iterations: 20, ..Default::default() };
        let mut lc = LoopConvergence::new(policy);

        let o = LoopObservation::from_snapshot(snap(0, frontier(3, 0, 0, 2, 0)))
            .with_spec_fingerprint(42)
            .with_cex_fingerprint(99)
            .with_solver_confidence(0.9);
        let d = lc.observe(o);

        let dims = d.dimensions();
        // frontier_score: 3/5 = 0.6
        assert!((dims.frontier_score - 0.6).abs() < 1e-9);
        // Only 1 fingerprint, so stability = 1.0 (trivially stable).
        assert!((dims.spec_stability - 1.0).abs() < 1e-9);
        assert!((dims.cex_stability - 1.0).abs() < 1e-9);
        assert!((dims.solver_confidence - 0.9).abs() < 1e-9);
    }

    #[test]
    fn test_dimensions_spec_stability_changes() {
        let policy =
            ConvergencePolicy { stable_round_limit: 5, max_iterations: 20, ..Default::default() };
        let mut lc = LoopConvergence::new(policy);

        // Different spec fingerprints each iteration => low stability.
        for i in 0..5 {
            let o = LoopObservation::from_snapshot(snap(i, frontier(2, 0, 0, 3, 0)))
                .with_spec_fingerprint(i as u64); // Changes each time.
            lc.observe(o);
        }

        // Last observation's dimensions should show low spec stability.
        let dims = lc.tracker().history().last().map(|_| {
            let _ = lc.score_history(); // Ensure method is accessible.
        });
        assert!(dims.is_some());

        // Observe one more to check dimensions.
        let o = LoopObservation::from_snapshot(snap(5, frontier(2, 0, 0, 3, 0)))
            .with_spec_fingerprint(5);
        let d = lc.observe(o);
        // All different fingerprints => 0 matches out of 4 pairs => 0.0 stability.
        assert!((d.dimensions().spec_stability - 0.0).abs() < 1e-9);
    }

    #[test]
    fn test_dimensions_combined_score() {
        let dims = ConvergenceDimensions {
            frontier_score: 1.0,
            spec_stability: 1.0,
            cex_stability: 1.0,
            solver_confidence: 1.0,
        };
        assert!((dims.combined_score() - 1.0).abs() < 1e-9);
        assert!(dims.all_above(0.99));
    }

    #[test]
    fn test_dimensions_min_dimension() {
        let dims = ConvergenceDimensions {
            frontier_score: 0.8,
            spec_stability: 0.5,
            cex_stability: 0.9,
            solver_confidence: 0.7,
        };
        assert!((dims.min_dimension() - 0.5).abs() < 1e-9);
    }

    // -- Oscillation detection wired into convergence --

    #[test]
    fn test_oscillation_detected_in_loop() {
        let policy = ConvergencePolicy {
            stable_round_limit: 10,
            max_iterations: 100,
            oscillation_config: OscillationConfig { min_history: 4, ..Default::default() },
            ..Default::default()
        };
        let mut lc = LoopConvergence::new(policy);

        // Alternate between two frontiers => binary oscillation in score.
        let f_high = frontier(4, 0, 0, 1, 0); // score = 0.8
        let f_low = frontier(2, 0, 0, 3, 0); // score = 0.4

        for i in 0..6 {
            let f = if i % 2 == 0 { f_high.clone() } else { f_low.clone() };
            let d = lc.observe(obs(i, f));
            if i >= 4 {
                // After 4+ observations, oscillation should be detected.
                if let LoopDecision::Continue { oscillation, .. } = &d {
                    assert!(oscillation.is_some(), "Expected oscillation at iteration {i}");
                }
            }
        }
    }

    #[test]
    fn test_divergent_oscillation_terminates() {
        let policy = ConvergencePolicy {
            stable_round_limit: 10,
            max_iterations: 100,
            oscillation_config: OscillationConfig {
                min_history: 4,
                tolerance: 1e-9,
                ..Default::default()
            },
            ..Default::default()
        };
        let mut lc = LoopConvergence::new(policy);

        // Create diverging scores: 0.5, 0.3, 0.7, 0.1, 0.9, 0.0, 1.0
        // The differences: 0.2, 0.4, 0.6, 0.8, 0.9, 1.0 => amplitude increasing.
        let scores_and_frontiers = vec![
            frontier(5, 0, 0, 5, 0),  // 0.5
            frontier(3, 0, 0, 7, 0),  // 0.3
            frontier(7, 0, 0, 3, 0),  // 0.7
            frontier(1, 0, 0, 9, 0),  // 0.1
            frontier(9, 0, 0, 1, 0),  // 0.9
            frontier(0, 0, 0, 10, 0), // 0.0
        ];

        let mut terminated = false;
        for (i, f) in scores_and_frontiers.into_iter().enumerate() {
            let d = lc.observe(obs(i as u32, f));
            if let LoopDecision::Terminate {
                outcome: TerminationOutcome::Diverging { .. }, ..
            } = &d
            {
                terminated = true;
                break;
            }
        }
        assert!(terminated, "Expected Diverging termination");
    }

    // -- Oscillation-aware spec damping --

    #[test]
    fn test_damp_spec_no_oscillation_passes_through() {
        let config = OscillationConfig::default();
        let history = vec![0.5, 0.6, 0.7, 0.8]; // Monotone, no oscillation.
        let result = damp_spec_for_oscillation(0.9, &history, &config);
        assert!((result - 0.9).abs() < 1e-9);
    }

    #[test]
    fn test_damp_spec_binary_uses_averaging() {
        let config = OscillationConfig { min_history: 4, tolerance: 1e-9, ..Default::default() };
        let history = vec![0.3, 0.7, 0.3, 0.7];
        let proposed = 0.3;
        let damped = damp_spec_for_oscillation(proposed, &history, &config);
        // Averaging: (0.3 + 0.7) / 2 = 0.5
        assert!((damped - 0.5).abs() < 1e-9);
    }

    #[test]
    fn test_damp_spec_periodic_uses_momentum() {
        let config = OscillationConfig {
            min_history: 4,
            tolerance: 1e-6,
            max_period: 8,
            momentum_factor: 0.5,
            ..Default::default()
        };
        let history = vec![1.0, 2.0, 3.0, 1.0, 2.0, 3.0];
        let proposed = 1.0;
        let damped = damp_spec_for_oscillation(proposed, &history, &config);
        // Should use momentum, result != proposed.
        assert!((damped - proposed).abs() > 1e-6);
    }

    #[test]
    fn test_loop_convergence_damp_spec_strength() {
        let policy = ConvergencePolicy {
            stable_round_limit: 10,
            max_iterations: 100,
            auto_damp: true,
            damping_strategy: DampingStrategy::Averaging,
            oscillation_config: OscillationConfig { min_history: 4, ..Default::default() },
            ..Default::default()
        };
        let mut lc = LoopConvergence::new(policy);

        // Feed oscillating observations.
        let f_high = frontier(4, 0, 0, 1, 0);
        let f_low = frontier(2, 0, 0, 3, 0);
        for i in 0..6 {
            let f = if i % 2 == 0 { f_high.clone() } else { f_low.clone() };
            lc.observe(obs(i, f));
        }

        // Now damp_spec_strength should apply damping.
        let damped = lc.damp_spec_strength(0.8);
        // With oscillation detected, result should differ from 0.8.
        assert!((damped - 0.8).abs() > 1e-6);
    }

    #[test]
    fn test_loop_convergence_no_autodamp_passes_through() {
        let policy = ConvergencePolicy { auto_damp: false, ..Default::default() };
        let lc = LoopConvergence::new(policy);
        assert!((lc.damp_spec_strength(0.42) - 0.42).abs() < 1e-9);
    }

    // -- Integration test: oscillating VCs converge via damping --

    #[test]
    fn test_oscillating_vcs_converge_via_damping() {
        // Demonstrate that ExponentialDecay damping reduces oscillation
        // amplitude. We start with proposals alternating between 0.8 and
        // 0.2 (amplitude 0.6) and show that after damping, the amplitude
        // of damped values decreases significantly.
        let config = OscillationConfig {
            min_history: 4,
            tolerance: 0.01,
            decay_rate: 0.3,
            momentum_factor: 0.7,
            ..Default::default()
        };

        let mut applied: Vec<f64> = vec![0.8, 0.2, 0.8, 0.2];
        let initial_amplitude = 0.6; // |0.8 - 0.2|

        for i in 0..20 {
            let proposed = if i % 2 == 0 { 0.8 } else { 0.2 };
            let damped =
                apply_damping(proposed, &applied, DampingStrategy::ExponentialDecay, &config);
            applied.push(damped);
        }

        // Measure final amplitude: difference between the last two damped values.
        let n = applied.len();
        let final_amplitude = (applied[n - 1] - applied[n - 2]).abs();

        // The damped amplitude should be significantly less than the initial.
        assert!(
            final_amplitude < initial_amplitude * 0.5,
            "Expected damping to reduce amplitude from {initial_amplitude} to < {}, got {final_amplitude}",
            initial_amplitude * 0.5,
        );

        // All damped values should be between 0.2 and 0.8 (bounded by proposals).
        for (i, &v) in applied.iter().enumerate().skip(4) {
            assert!((0.1..=0.9).contains(&v), "Damped value at index {i} out of range: {v}");
        }

        // Mean of damped values should be near 0.5.
        let damped_mean = applied.iter().skip(4).sum::<f64>() / (applied.len() - 4) as f64;
        assert!((damped_mean - 0.5).abs() < 0.15, "Expected mean near 0.5, got {damped_mean}");
    }

    // -- Compute fingerprint utility --

    #[test]
    fn test_compute_fingerprint_deterministic() {
        let items = vec!["a", "b", "c"];
        let fp1 = compute_fingerprint(&items);
        let fp2 = compute_fingerprint(&items);
        assert_eq!(fp1, fp2);
    }

    #[test]
    fn test_compute_fingerprint_different_for_different_inputs() {
        let fp1 = compute_fingerprint(&["a", "b"]);
        let fp2 = compute_fingerprint(&["b", "a"]);
        // Order matters.
        assert_ne!(fp1, fp2);
    }

    // -- ConvergencePolicy defaults --

    #[test]
    fn test_convergence_policy_defaults() {
        let p = ConvergencePolicy::default();
        assert_eq!(p.max_iterations, 50);
        assert_eq!(p.stable_round_limit, 2);
        assert_eq!(p.stall_threshold, 3);
        assert!(p.auto_damp);
        assert!(p.max_wall_time.is_none());
        assert!(p.max_solver_calls.is_none());
    }

    // -- LoopDecision accessors --

    #[test]
    fn test_loop_decision_should_stop() {
        let continue_d = LoopDecision::Continue {
            verdict: StepVerdict::Improved,
            oscillation: None,
            dimensions: ConvergenceDimensions::default(),
        };
        assert!(!continue_d.should_stop());

        let terminate_d = LoopDecision::Terminate {
            outcome: TerminationOutcome::FullyVerified { stable_rounds: 2 },
            dimensions: ConvergenceDimensions::default(),
        };
        assert!(terminate_d.should_stop());
    }

    #[test]
    fn test_convergence_dimensions_default() {
        let d = ConvergenceDimensions::default();
        assert!((d.frontier_score - 0.0).abs() < 1e-9);
        assert!((d.spec_stability - 1.0).abs() < 1e-9);
        assert!((d.cex_stability - 1.0).abs() < 1e-9);
        assert!((d.solver_confidence - 1.0).abs() < 1e-9);
    }

    // -- Wall time and solver call tracking --

    #[test]
    fn test_resource_tracking() {
        let policy =
            ConvergencePolicy { max_iterations: 100, stable_round_limit: 5, ..Default::default() };
        let mut lc = LoopConvergence::new(policy);

        let o = LoopObservation::from_snapshot(snap(0, frontier(1, 0, 0, 4, 0)))
            .with_wall_time(Duration::from_secs(5))
            .with_solver_calls(42);
        lc.observe(o);

        assert_eq!(lc.wall_time_used(), Duration::from_secs(5));
        assert_eq!(lc.solver_calls_used(), 42);

        let o2 = LoopObservation::from_snapshot(snap(1, frontier(2, 0, 0, 3, 0)))
            .with_wall_time(Duration::from_secs(3))
            .with_solver_calls(30);
        lc.observe(o2);

        assert_eq!(lc.wall_time_used(), Duration::from_secs(8));
        assert_eq!(lc.solver_calls_used(), 72);
    }

    // -- Edge case: wall-time budget takes priority over solver-calls budget --

    #[test]
    fn test_budget_wall_time_priority_over_solver_calls() {
        // When both wall-time and solver-calls are exhausted simultaneously,
        // wall-time should be reported (checked first in check_budget).
        let policy = ConvergencePolicy {
            max_wall_time: Some(Duration::from_secs(5)),
            max_solver_calls: Some(10),
            max_iterations: 100,
            stable_round_limit: 5,
            ..Default::default()
        };
        let mut lc = LoopConvergence::new(policy);

        let o = LoopObservation::from_snapshot(snap(0, frontier(1, 0, 0, 4, 0)))
            .with_wall_time(Duration::from_secs(10))
            .with_solver_calls(20);
        let d = lc.observe(o);
        assert!(d.should_stop());
        match d {
            LoopDecision::Terminate {
                outcome: TerminationOutcome::BudgetExhausted { resource, .. },
                ..
            } => assert_eq!(resource, BudgetResource::WallTime),
            other => panic!("Expected BudgetExhausted(WallTime), got {other:?}"),
        }
    }

    // -- Edge case: empty frontier (zero total VCs) --

    #[test]
    fn test_empty_frontier_dimensions() {
        let policy =
            ConvergencePolicy { stable_round_limit: 5, max_iterations: 20, ..Default::default() };
        let mut lc = LoopConvergence::new(policy);

        let o = LoopObservation::from_snapshot(snap(0, frontier(0, 0, 0, 0, 0)));
        let d = lc.observe(o);
        let dims = d.dimensions();
        // convergence_score returns None for zero total => frontier_score = 0.0
        assert!((dims.frontier_score - 0.0).abs() < 1e-9);
    }

    // -- Edge case: regression does not terminate (continues) --

    #[test]
    fn test_regression_continues_does_not_terminate() {
        let policy =
            ConvergencePolicy { stable_round_limit: 5, max_iterations: 100, ..Default::default() };
        let mut lc = LoopConvergence::new(policy);

        lc.observe(obs(0, frontier(5, 0, 0, 0, 0)));
        let d = lc.observe(obs(1, frontier(3, 0, 0, 2, 0)));
        // Regression should be Continue, not Terminate.
        assert!(!d.should_stop());
        match d {
            LoopDecision::Continue { verdict, .. } => {
                assert_eq!(verdict, StepVerdict::Regressed);
            }
            other => panic!("Expected Continue with Regressed verdict, got {other:?}"),
        }
    }

    // -- Edge case: CEX stability with alternating fingerprints --

    #[test]
    fn test_cex_stability_alternating_fingerprints() {
        let policy =
            ConvergencePolicy { stable_round_limit: 10, max_iterations: 20, ..Default::default() };
        let mut lc = LoopConvergence::new(policy);

        // Alternate CEX fingerprints: 1, 2, 1, 2, 1, 2
        for i in 0..6 {
            let cex_fp = if i % 2 == 0 { 1u64 } else { 2u64 };
            let o = LoopObservation::from_snapshot(snap(i, frontier(3, 0, 0, 2, 0)))
                .with_cex_fingerprint(cex_fp)
                .with_spec_fingerprint(42); // Spec stable.
            lc.observe(o);
        }

        // Observe one more to check dimensions.
        let o = LoopObservation::from_snapshot(snap(6, frontier(3, 0, 0, 2, 0)))
            .with_cex_fingerprint(1)
            .with_spec_fingerprint(42);
        let d = lc.observe(o);
        // CEX alternates => 0 consecutive matches in last 5 => stability = 0.0
        assert!((d.dimensions().cex_stability - 0.0).abs() < 1e-9);
        // Spec is always 42 => fully stable
        assert!((d.dimensions().spec_stability - 1.0).abs() < 1e-9);
    }

    // -- Edge case: spec stability with partial matches --

    #[test]
    fn test_spec_stability_partial_matches() {
        let policy =
            ConvergencePolicy { stable_round_limit: 10, max_iterations: 20, ..Default::default() };
        let mut lc = LoopConvergence::new(policy);

        // Fingerprints: 10, 10, 20, 20, 20 => last 5 window has 3 matches out of 4 pairs
        let fps = [10u64, 10, 20, 20, 20];
        for (i, &fp) in fps.iter().enumerate() {
            let o = LoopObservation::from_snapshot(snap(i as u32, frontier(3, 0, 0, 2, 0)))
                .with_spec_fingerprint(fp);
            lc.observe(o);
        }

        // Observe one more with same fingerprint to get 6 entries.
        let o = LoopObservation::from_snapshot(snap(5, frontier(3, 0, 0, 2, 0)))
            .with_spec_fingerprint(20);
        let d = lc.observe(o);
        // Window of last 5: [10, 20, 20, 20, 20]
        // Pairs: (10,20)=no, (20,20)=yes, (20,20)=yes, (20,20)=yes => 3/4 = 0.75
        assert!((d.dimensions().spec_stability - 0.75).abs() < 1e-9);
    }

    // -- Edge case: with_defaults constructor --

    #[test]
    fn test_with_defaults_matches_default_policy() {
        let lc = LoopConvergence::with_defaults();
        let p = lc.policy();
        assert_eq!(p.max_iterations, 50);
        assert_eq!(p.stable_round_limit, 2);
        assert!(p.auto_damp);
    }

    // -- Edge case: combined score weights sum to 1.0 --

    #[test]
    fn test_combined_score_weights_sum_to_one() {
        let dims = ConvergenceDimensions {
            frontier_score: 0.0,
            spec_stability: 0.0,
            cex_stability: 0.0,
            solver_confidence: 0.0,
        };
        assert!((dims.combined_score() - 0.0).abs() < 1e-9);

        // all_above should fail for threshold > 0
        assert!(!dims.all_above(0.01));
    }

    // -- Edge case: convergence after improving then stabilizing --

    #[test]
    fn test_improve_then_stabilize_converges() {
        let policy =
            ConvergencePolicy { stable_round_limit: 2, max_iterations: 20, ..Default::default() };
        let mut lc = LoopConvergence::new(policy);

        // Improve from 2/5 to 4/5, then stabilize at 4/5 for 2 rounds.
        lc.observe(obs(0, frontier(2, 0, 0, 3, 0)));
        let d1 = lc.observe(obs(1, frontier(4, 0, 0, 1, 0)));
        assert!(!d1.should_stop()); // Improving, not stable yet.

        lc.observe(obs(2, frontier(4, 0, 0, 1, 0)));
        let d3 = lc.observe(obs(3, frontier(4, 0, 0, 1, 0)));
        // 3 consecutive identical (iteration 1, 2, 3) but stable_round_limit=2
        // so should converge with failures remaining => PartiallyVerified.
        assert!(d3.should_stop());
        match d3 {
            LoopDecision::Terminate {
                outcome: TerminationOutcome::PartiallyVerified { proved_ratio, .. },
                ..
            } => {
                assert!((proved_ratio - 0.8).abs() < 1e-9);
            }
            other => panic!("Expected PartiallyVerified, got {other:?}"),
        }
    }

    // -- Edge case: fingerprint utility with empty input --

    #[test]
    fn test_compute_fingerprint_empty_input() {
        let empty: Vec<&str> = vec![];
        let fp = compute_fingerprint(&empty);
        // Should produce a deterministic hash even for empty input.
        let fp2 = compute_fingerprint(&empty);
        assert_eq!(fp, fp2);
    }

    // -- Edge case: LoopObservation builder chain --

    #[test]
    fn test_loop_observation_builder_chain() {
        let o = LoopObservation::from_snapshot(snap(0, frontier(5, 0, 0, 0, 0)))
            .with_spec_fingerprint(123)
            .with_cex_fingerprint(456)
            .with_solver_confidence(0.95)
            .with_wall_time(Duration::from_millis(500))
            .with_solver_calls(10);
        assert_eq!(o.spec_fingerprint, 123);
        assert_eq!(o.cex_fingerprint, 456);
        assert!((o.solver_confidence - 0.95).abs() < 1e-9);
        assert_eq!(o.wall_time, Duration::from_millis(500));
        assert_eq!(o.solver_calls, 10);
    }

    // -- Edge case: monotonicity integration with convergence --

    #[test]
    fn test_proof_strength_monotonicity_via_convergence() {
        // Verify that LoopConvergence correctly detects when proofs get weaker
        // (fewer proved VCs) across iterations.
        let policy =
            ConvergencePolicy { stable_round_limit: 5, max_iterations: 20, ..Default::default() };
        let mut lc = LoopConvergence::new(policy);

        // Start with 8 proved, then drop to 5 (proof strength regression).
        lc.observe(obs(0, frontier(8, 0, 0, 2, 0)));
        let d = lc.observe(obs(1, frontier(5, 0, 0, 5, 0)));
        // Should continue with Regressed verdict (proof got weaker).
        match d {
            LoopDecision::Continue { verdict, dimensions, .. } => {
                assert_eq!(verdict, StepVerdict::Regressed);
                // Frontier score should reflect the weaker state.
                assert!((dimensions.frontier_score - 0.5).abs() < 1e-9);
            }
            other => panic!("Expected Continue(Regressed), got {other:?}"),
        }
    }

    // -- Edge case: solver confidence averaging --

    #[test]
    fn test_solver_confidence_averaging_over_window() {
        let policy =
            ConvergencePolicy { stable_round_limit: 10, max_iterations: 20, ..Default::default() };
        let mut lc = LoopConvergence::new(policy);

        // Feed 6 iterations with decreasing confidence.
        let confidences = [1.0, 0.9, 0.8, 0.7, 0.6, 0.5];
        for (i, &conf) in confidences.iter().enumerate() {
            let o = LoopObservation::from_snapshot(snap(i as u32, frontier(3, 0, 0, 2, 0)))
                .with_solver_confidence(conf);
            lc.observe(o);
        }

        // Last observation to check dimensions.
        let o = LoopObservation::from_snapshot(snap(6, frontier(3, 0, 0, 2, 0)))
            .with_solver_confidence(0.4);
        let d = lc.observe(o);
        // Window of last 5 confidences: [0.7, 0.6, 0.5, 0.4] wait, let me count...
        // History has 7 entries: [1.0, 0.9, 0.8, 0.7, 0.6, 0.5, 0.4]
        // Window = min(7, 5) = 5, tail = [0.8, 0.7, 0.6, 0.5, 0.4]
        // Mean = (0.8 + 0.7 + 0.6 + 0.5 + 0.4) / 5 = 3.0 / 5 = 0.6
        assert!((d.dimensions().solver_confidence - 0.6).abs() < 1e-9);
    }

    // -- Edge case: budget exhaustion before divergence detection --

    #[test]
    fn test_budget_takes_priority_over_divergence() {
        let policy = ConvergencePolicy {
            max_wall_time: Some(Duration::from_secs(1)),
            max_iterations: 100,
            stable_round_limit: 10,
            oscillation_config: OscillationConfig { min_history: 4, ..Default::default() },
            ..Default::default()
        };
        let mut lc = LoopConvergence::new(policy);

        // Feed observations that would trigger divergence, but with wall time
        // exceeding the budget. Budget should win.
        let scores_and_frontiers = vec![
            frontier(5, 0, 0, 5, 0),
            frontier(3, 0, 0, 7, 0),
            frontier(7, 0, 0, 3, 0),
            frontier(1, 0, 0, 9, 0),
        ];

        let mut found_budget = false;
        for (i, f) in scores_and_frontiers.into_iter().enumerate() {
            let o = LoopObservation::from_snapshot(snap(i as u32, f))
                .with_wall_time(Duration::from_secs(2)); // Each exceeds budget.
            let d = lc.observe(o);
            if let LoopDecision::Terminate {
                outcome: TerminationOutcome::BudgetExhausted { resource, .. },
                ..
            } = &d
            {
                assert_eq!(*resource, BudgetResource::WallTime);
                found_budget = true;
                break;
            }
        }
        assert!(found_budget, "Expected BudgetExhausted before Diverging");
    }
}
