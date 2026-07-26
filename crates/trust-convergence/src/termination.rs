// trust-convergence/termination.rs: Loop termination analysis and guarantees.
//
// Evaluates termination criteria each iteration, estimates convergence rates,
// predicts remaining iterations, and tracks resource budgets. Ensures the
// prove-strengthen-backprop loop terminates with a clear reason.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::time::Duration;

use crate::{IterationSnapshot, ProofFrontier};

/// Why the loop terminated.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum TerminationReason {
    /// Maximum iteration count reached.
    MaxIterations { limit: usize, reached: usize },
    /// No VCs changed status between iterations (fixed point).
    FixedPoint { stable_iterations: usize },
    /// Stagnation timeout elapsed with no progress.
    StagnationTimeout { elapsed: Duration, limit: Duration },
    /// Confidence threshold met — enough VCs proved.
    ConfidenceThreshold { achieved: f64, threshold: f64 },
    /// A combined criterion fired; the inner reason is the first trigger.
    Combined { trigger: Box<TerminationReason> },
    /// Resource budget exhausted.
    BudgetExhausted { resource: ResourceKind },
}

/// Which resource ran out.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ResourceKind {
    /// Total solver wall-clock time.
    SolverTime,
    /// Total loop iterations.
    Iterations,
}

/// A single termination criterion.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum TerminationCriterion {
    /// Stop after N iterations.
    MaxIterations(usize),
    /// Stop when no VCs change status (frontier identical two iterations in a row).
    FixedPoint,
    /// Stop when no progress for the given duration.
    StagnationTimeout(Duration),
    /// Stop when convergence score >= threshold (0.0..=1.0).
    ConfidenceThreshold(f64),
    /// Any inner criterion triggers termination.
    Combined(Vec<TerminationCriterion>),
}

/// Prediction of whether the loop will converge.
#[derive(Debug, Clone, PartialEq)]
pub struct ConvergencePrediction {
    /// Whether convergence is predicted.
    pub will_converge: bool,
    /// Estimated iterations remaining (None if unknown).
    pub estimated_remaining: Option<usize>,
    /// Confidence in the prediction (0.0..=1.0).
    pub confidence: f64,
    /// Human-readable explanation.
    pub explanation: String,
}

/// Per-iteration convergence rate measurement.
#[derive(Debug, Clone, PartialEq)]
pub struct ConvergenceRate {
    /// VCs proved in this iteration (delta from previous).
    pub vcs_proved_delta: i64,
    /// Cumulative VCs proved so far.
    pub cumulative_proved: u32,
    /// Total VCs tracked.
    pub total_vcs: u32,
    /// Moving average of VCs proved per iteration over the last N iterations.
    pub moving_average: f64,
    /// Trend: positive means accelerating, negative means decelerating.
    pub trend: f64,
}

/// Resource budget tracking for the verification loop.
#[derive(Debug, Clone, PartialEq)]
pub struct ResourceBudget {
    /// Maximum solver time allowed.
    pub max_solver_time: Option<Duration>,
    /// Solver time consumed so far.
    pub solver_time_used: Duration,
    /// Maximum iterations allowed.
    pub max_iterations: Option<usize>,
    /// Iterations consumed so far.
    pub iterations_used: usize,
}

impl ResourceBudget {
    /// Create a new budget with optional limits.
    #[must_use]
    pub fn new(max_solver_time: Option<Duration>, max_iterations: Option<usize>) -> Self {
        Self {
            max_solver_time,
            solver_time_used: Duration::ZERO,
            max_iterations,
            iterations_used: 0,
        }
    }

    /// Create an unlimited budget.
    #[must_use]
    pub fn unlimited() -> Self {
        Self::new(None, None)
    }

    /// Record solver time consumed.
    pub fn record_solver_time(&mut self, elapsed: Duration) {
        self.solver_time_used += elapsed;
    }

    /// Record one iteration.
    pub fn record_iteration(&mut self) {
        self.iterations_used = self.iterations_used.saturating_add(1);
    }

    /// Whether the solver time budget is exhausted.
    #[must_use]
    pub fn solver_time_exhausted(&self) -> bool {
        self.max_solver_time.is_some_and(|max| self.solver_time_used >= max)
    }

    /// Whether the iteration budget is exhausted.
    #[must_use]
    pub fn iterations_exhausted(&self) -> bool {
        self.max_iterations.is_some_and(|max| self.iterations_used >= max)
    }

    /// Whether any budget is exhausted.
    #[must_use]
    pub fn any_exhausted(&self) -> bool {
        self.solver_time_exhausted() || self.iterations_exhausted()
    }

    /// Which resource is exhausted, if any. Returns the first exhausted resource.
    #[must_use]
    pub fn exhausted_resource(&self) -> Option<ResourceKind> {
        if self.solver_time_exhausted() {
            Some(ResourceKind::SolverTime)
        } else if self.iterations_exhausted() {
            Some(ResourceKind::Iterations)
        } else {
            None
        }
    }

    /// Remaining solver time, or None if unlimited.
    #[must_use]
    pub fn remaining_solver_time(&self) -> Option<Duration> {
        self.max_solver_time.map(|max| max.saturating_sub(self.solver_time_used))
    }

    /// Remaining iterations, or None if unlimited.
    #[must_use]
    pub fn remaining_iterations(&self) -> Option<usize> {
        self.max_iterations.map(|max| max.saturating_sub(self.iterations_used))
    }
}

impl Default for ResourceBudget {
    fn default() -> Self {
        // Default: 10 minutes solver time, 50 iterations.
        Self::new(Some(Duration::from_secs(600)), Some(50))
    }
}

/// Evaluates termination criteria each iteration.
#[derive(Debug, Clone)]
pub struct TerminationAnalyzer {
    /// The criteria to evaluate.
    criteria: Vec<TerminationCriterion>,
    /// Resource budget.
    budget: ResourceBudget,
    /// History of convergence rates.
    rate_history: Vec<ConvergenceRate>,
    /// Duration with no progress (for stagnation timeout).
    stagnation_elapsed: Duration,
    /// Whether progress was made in the last iteration.
    last_was_progress: bool,
}

impl TerminationAnalyzer {
    /// Create a new analyzer with the given criteria and budget.
    #[must_use]
    pub fn new(criteria: Vec<TerminationCriterion>, budget: ResourceBudget) -> Self {
        Self {
            criteria,
            budget,
            rate_history: Vec::new(),
            stagnation_elapsed: Duration::ZERO,
            last_was_progress: true,
        }
    }

    /// Create an analyzer with a single criterion and default budget.
    #[must_use]
    pub fn with_criterion(criterion: TerminationCriterion) -> Self {
        Self::new(vec![criterion], ResourceBudget::default())
    }

    /// Evaluate all criteria against the current state. Returns `Some(reason)` if
    /// the loop should terminate, `None` if it should continue.
    #[must_use]
    pub fn should_terminate(&self, history: &[IterationSnapshot]) -> Option<TerminationReason> {
        // Check resource budget first.
        if let Some(resource) = self.budget.exhausted_resource() {
            return Some(TerminationReason::BudgetExhausted { resource });
        }

        for criterion in &self.criteria {
            if let Some(reason) = self.evaluate_criterion(criterion, history) {
                return Some(reason);
            }
        }
        None
    }

    /// Record that an iteration completed, updating internal state.
    pub fn record_iteration(
        &mut self,
        previous: Option<&ProofFrontier>,
        current: &ProofFrontier,
        solver_time: Duration,
    ) {
        self.budget.record_iteration();
        self.budget.record_solver_time(solver_time);

        let vcs_proved_delta = match previous {
            Some(prev) => current.statically_proved() as i64 - prev.statically_proved() as i64,
            None => current.statically_proved() as i64,
        };

        let made_progress = vcs_proved_delta > 0;
        if made_progress {
            self.stagnation_elapsed = Duration::ZERO;
        } else {
            self.stagnation_elapsed += solver_time;
        }
        self.last_was_progress = made_progress;

        let cumulative_proved = current.statically_proved();
        let total_vcs = current.total();

        // Compute moving average over last 5 rates.
        let window: usize = 5;
        let recent_deltas: Vec<i64> = self
            .rate_history
            .iter()
            .rev()
            .take(window.saturating_sub(1))
            .map(|r| r.vcs_proved_delta)
            .collect();

        let sum: i64 = recent_deltas.iter().sum::<i64>() + vcs_proved_delta;
        let count = recent_deltas.len().saturating_add(1);
        let moving_average = sum as f64 / count as f64;

        // Trend: compare current average to previous average.
        let prev_avg = if recent_deltas.is_empty() {
            0.0
        } else {
            recent_deltas.iter().sum::<i64>() as f64 / recent_deltas.len() as f64
        };
        let trend = moving_average - prev_avg;

        self.rate_history.push(ConvergenceRate {
            vcs_proved_delta,
            cumulative_proved,
            total_vcs,
            moving_average,
            trend,
        });
    }

    /// Get the latest convergence rate, if any iterations have been recorded.
    #[must_use]
    pub fn latest_rate(&self) -> Option<&ConvergenceRate> {
        self.rate_history.last()
    }

    /// Get the full rate history.
    #[must_use]
    pub fn rate_history(&self) -> &[ConvergenceRate] {
        &self.rate_history
    }

    /// Access the resource budget.
    #[must_use]
    pub fn budget(&self) -> &ResourceBudget {
        &self.budget
    }

    /// Mutable access to the resource budget.
    pub fn budget_mut(&mut self) -> &mut ResourceBudget {
        &mut self.budget
    }

    /// Predict whether the loop will converge based on rate history.
    #[must_use]
    pub fn predict_convergence(&self, total_vcs: u32) -> ConvergencePrediction {
        will_converge(&self.rate_history, total_vcs)
    }

    /// Estimate remaining iterations based on current rate.
    #[must_use]
    pub fn estimate_remaining(&self) -> Option<usize> {
        let rate = self.latest_rate()?;
        estimate_remaining_iterations(rate)
    }

    fn evaluate_criterion(
        &self,
        criterion: &TerminationCriterion,
        history: &[IterationSnapshot],
    ) -> Option<TerminationReason> {
        match criterion {
            TerminationCriterion::MaxIterations(limit) => {
                if history.len() >= *limit {
                    Some(TerminationReason::MaxIterations { limit: *limit, reached: history.len() })
                } else {
                    None
                }
            }
            TerminationCriterion::FixedPoint => check_fixed_point(history),
            TerminationCriterion::StagnationTimeout(limit) => {
                if self.stagnation_elapsed >= *limit {
                    Some(TerminationReason::StagnationTimeout {
                        elapsed: self.stagnation_elapsed,
                        limit: *limit,
                    })
                } else {
                    None
                }
            }
            TerminationCriterion::ConfidenceThreshold(threshold) => {
                check_confidence_threshold(history, *threshold)
            }
            TerminationCriterion::Combined(inner) => {
                for sub in inner {
                    if let Some(reason) = self.evaluate_criterion(sub, history) {
                        return Some(TerminationReason::Combined { trigger: Box::new(reason) });
                    }
                }
                None
            }
        }
    }
}

impl Default for TerminationAnalyzer {
    fn default() -> Self {
        Self::new(
            vec![
                TerminationCriterion::MaxIterations(50),
                TerminationCriterion::FixedPoint,
                TerminationCriterion::ConfidenceThreshold(1.0),
            ],
            ResourceBudget::default(),
        )
    }
}

/// Check if the history shows a fixed point (last two frontiers identical).
fn check_fixed_point(history: &[IterationSnapshot]) -> Option<TerminationReason> {
    if history.len() < 2 {
        return None;
    }
    let last = &history[history.len() - 1];
    let prev = &history[history.len() - 2];
    if last.frontier == prev.frontier {
        // Count how many consecutive identical frontiers.
        let mut stable = 1usize;
        for i in (0..history.len().saturating_sub(1)).rev() {
            if history[i].frontier == last.frontier {
                stable = stable.saturating_add(1);
            } else {
                break;
            }
        }
        Some(TerminationReason::FixedPoint { stable_iterations: stable })
    } else {
        None
    }
}

/// Check if the confidence threshold is met.
fn check_confidence_threshold(
    history: &[IterationSnapshot],
    threshold: f64,
) -> Option<TerminationReason> {
    let last = history.last()?;
    let score = last.frontier.convergence_score()?;
    if score >= threshold {
        Some(TerminationReason::ConfidenceThreshold { achieved: score, threshold })
    } else {
        None
    }
}

/// Estimate remaining iterations from a convergence rate.
///
/// Returns `None` if the rate is zero or negative (cannot estimate).
#[must_use]
pub fn estimate_remaining_iterations(rate: &ConvergenceRate) -> Option<usize> {
    if rate.moving_average <= 0.0 || rate.total_vcs == 0 {
        return None;
    }
    let remaining_vcs = rate.total_vcs.saturating_sub(rate.cumulative_proved);
    if remaining_vcs == 0 {
        return Some(0);
    }
    let estimate = (remaining_vcs as f64 / rate.moving_average).ceil() as usize;
    Some(estimate)
}

/// Estimate loop bound from strengthening proposals.
///
/// Given the number of unresolved VCs and an average VCs-per-proposal rate,
/// returns the estimated number of strengthening rounds needed.
#[must_use]
pub fn estimate_loop_bound(unresolved_vcs: u32, avg_vcs_per_proposal: f64) -> Option<usize> {
    if avg_vcs_per_proposal <= 0.0 || unresolved_vcs == 0 {
        return None;
    }
    Some((unresolved_vcs as f64 / avg_vcs_per_proposal).ceil() as usize)
}

/// Predict convergence from a history of convergence rates.
#[must_use]
pub fn will_converge(rate_history: &[ConvergenceRate], total_vcs: u32) -> ConvergencePrediction {
    if rate_history.is_empty() || total_vcs == 0 {
        return ConvergencePrediction {
            will_converge: false,
            estimated_remaining: None,
            confidence: 0.0,
            explanation: "insufficient data for prediction".to_string(),
        };
    }

    let latest = &rate_history[rate_history.len() - 1];

    // If already fully proved, we've converged.
    if latest.cumulative_proved >= total_vcs {
        return ConvergencePrediction {
            will_converge: true,
            estimated_remaining: Some(0),
            confidence: 1.0,
            explanation: "all VCs proved".to_string(),
        };
    }

    // If moving average is non-positive, convergence is unlikely.
    if latest.moving_average <= 0.0 {
        return ConvergencePrediction {
            will_converge: false,
            estimated_remaining: None,
            confidence: 0.7,
            explanation: format!(
                "non-positive moving average ({:.2}): no progress trend",
                latest.moving_average
            ),
        };
    }

    // Estimate remaining iterations.
    let remaining_vcs = total_vcs.saturating_sub(latest.cumulative_proved);
    let estimated = (remaining_vcs as f64 / latest.moving_average).ceil() as usize;

    // Confidence based on trend stability and data quantity.
    let data_confidence = (rate_history.len() as f64 / 10.0).min(1.0);
    let trend_confidence = if latest.trend >= 0.0 {
        0.8
    } else {
        // Decelerating — less confident.
        0.4
    };
    let confidence = (data_confidence * 0.4 + trend_confidence * 0.6).min(1.0);

    let explanation = format!(
        "avg {:.2} VCs/iter, trend {:.2}, ~{} iterations remaining",
        latest.moving_average, latest.trend, estimated
    );

    ConvergencePrediction {
        will_converge: true,
        estimated_remaining: Some(estimated),
        confidence,
        explanation,
    }
}

// ---------------------------------------------------------------------------
// Ranking-function-based termination analysis
// ---------------------------------------------------------------------------

/// A ranking function maps loop states to a well-ordered domain.
/// If the function strictly decreases on every iteration, the loop terminates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RankingFunction {
    /// Human-readable name for this ranking function.
    pub name: String,
    /// Symbolic expression for the ranking (e.g. "n - i").
    pub expression: String,
    /// Domain of the ranking (e.g. "non-negative integers").
    pub domain: String,
}

/// Evidence that a ranking function decreases for a particular variable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecreaseMeasure {
    /// The variable being measured.
    pub variable: String,
    /// Value before the loop body.
    pub before: String,
    /// Value after the loop body.
    pub after: String,
    /// Whether the decrease is strict (true) or non-strict (false).
    pub strict: bool,
}

/// A lexicographic ordering of ranking functions.
///
/// Termination is proved if, at each iteration, the tuple of ranking function
/// values decreases in lexicographic order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexOrder {
    /// Ranking functions in decreasing priority order.
    pub components: Vec<RankingFunction>,
}

/// Configuration for ranking-function-based termination analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TerminationConfig {
    /// Maximum attempts to synthesize a ranking function.
    pub max_ranking_attempts: usize,
    /// Whether to attempt lexicographic orderings.
    pub use_lexicographic: bool,
    /// Whether to attempt iteration bound synthesis.
    pub bound_synthesis: bool,
}

impl Default for TerminationConfig {
    fn default() -> Self {
        Self { max_ranking_attempts: 10, use_lexicographic: true, bound_synthesis: true }
    }
}

/// Result of a ranking-function-based termination proof attempt.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum TerminationResult {
    /// Termination was proved.
    Terminates(TerminationProof),
    /// The analysis found a potential non-termination reason.
    MayNotTerminate(String),
    /// The analysis could not determine termination.
    Unknown,
}

/// A complete termination proof via ranking functions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TerminationProof {
    /// The ranking function that proves termination.
    pub ranking_function: RankingFunction,
    /// Evidence that the ranking decreases on each iteration.
    pub decrease_evidence: Vec<DecreaseMeasure>,
    /// Optional upper bound on the number of iterations.
    pub bound: Option<u64>,
}

/// Analyzes loop termination using ranking functions and lexicographic orderings.
#[derive(Debug, Clone)]
pub struct RankingAnalyzer {
    config: TerminationConfig,
}

impl RankingAnalyzer {
    /// Create a new ranking analyzer with the given configuration.
    #[must_use]
    pub fn new(config: TerminationConfig) -> Self {
        Self { config }
    }

    /// Attempt to prove termination of a loop body over the given variables.
    ///
    /// Examines the loop body and variables to find a ranking function that
    /// strictly decreases on each iteration.
    #[must_use]
    pub fn prove_termination(&self, loop_body: &str, variables: &[&str]) -> TerminationResult {
        // Try to find decreasing variables by scanning the loop body.
        let mut decreasing_vars: Vec<(&str, &str)> = Vec::new();

        for var in variables {
            // Look for patterns like "var = var - 1" or "var -= 1".
            let dec_pattern = format!("{var} = {var} - ");
            let dec_assign = format!("{var} -= ");
            if loop_body.contains(&dec_pattern) || loop_body.contains(&dec_assign) {
                decreasing_vars.push((var, "1"));
            }
        }

        if decreasing_vars.is_empty() {
            // Try lexicographic if configured.
            if self.config.use_lexicographic && variables.len() > 1 {
                // Try each variable individually.
                for var in variables {
                    let dec_pattern = format!("{var} = {var} - ");
                    let dec_assign = format!("{var} -= ");
                    if loop_body.contains(&dec_pattern) || loop_body.contains(&dec_assign) {
                        decreasing_vars.push((var, "1"));
                    }
                }
            }
            if decreasing_vars.is_empty() {
                return TerminationResult::MayNotTerminate(
                    "no decreasing variable found".to_string(),
                );
            }
        }

        // Attempt to find a ranking function.
        if let Some(ranking) = self.find_ranking_function(&decreasing_vars) {
            let mut evidence = Vec::new();
            for (var, delta) in &decreasing_vars {
                evidence.push(DecreaseMeasure {
                    variable: (*var).to_string(),
                    before: (*var).to_string(),
                    after: format!("{var} - {delta}"),
                    strict: true,
                });
            }

            let bound = if self.config.bound_synthesis {
                self.bounded_iteration_count(&ranking, "n")
            } else {
                None
            };

            TerminationResult::Terminates(TerminationProof {
                ranking_function: ranking,
                decrease_evidence: evidence,
                bound,
            })
        } else {
            TerminationResult::Unknown
        }
    }

    /// Find a ranking function from a set of decreasing variable pairs.
    ///
    /// Each pair is (variable_name, decrease_amount).
    /// Tries multiple ranking function strategies in order:
    ///   - Simple decrement (single variable)
    ///   - Lexicographic ordering (pairs of variables)
    ///   - Polynomial (quadratic combinations)
    ///   - Structural recursion depth
    #[must_use]
    pub fn find_ranking_function(
        &self,
        decreasing_vars: &[(&str, &str)],
    ) -> Option<RankingFunction> {
        if decreasing_vars.is_empty() {
            return None;
        }

        for attempt in 0..self.config.max_ranking_attempts {
            let candidate = self.generate_ranking_candidate(decreasing_vars, attempt);

            if let Some(rf) = candidate
                && self.validate_ranking_candidate(&rf, decreasing_vars)
            {
                return Some(rf);
            }
        }

        None
    }

    /// Generate a ranking function candidate for the given attempt number.
    ///
    /// Different attempts use different strategies:
    ///   - Attempts 0..n: simple decrement on each variable
    ///   - Attempts n..2n: lexicographic pairs (if enabled)
    ///   - Attempts 2n..3n: polynomial (quadratic) combinations
    ///   - Attempts 3n..: structural recursion depth
    fn generate_ranking_candidate(
        &self,
        decreasing_vars: &[(&str, &str)],
        attempt: usize,
    ) -> Option<RankingFunction> {
        let n = decreasing_vars.len();
        // Trust (flywheel backprop): totalize — with `n == 0` every branch guard
        // below fails and the structural-recursion arm computes `attempt % 0`, a
        // REACHABLE modulo-zero panic Trust's own verifier flagged when verifying
        // this crate. No variables -> no candidate is the correct semantics, and
        // the early return gives `n >= 1` to every `n - 1`, `% n`, and index
        // below, so they PROVE.
        if n == 0 {
            return None;
        }

        if attempt < n {
            // Strategy 1: Simple decrement — use each variable in turn.
            let (var, _delta) = decreasing_vars[attempt];
            Some(RankingFunction {
                name: format!("rank_{var}"),
                expression: var.to_string(),
                domain: "non-negative integers".to_string(),
            })
        } else if self.config.use_lexicographic && attempt < n.saturating_mul(2) && n > 1 {
            // Strategy 2: Lexicographic ordering — pair primary + secondary variable.
            let primary_idx = (attempt.saturating_sub(n)) % n;
            let secondary_idx = (primary_idx + 1) % n;
            let (primary, _) = decreasing_vars[primary_idx];
            let (secondary, _) = decreasing_vars[secondary_idx];
            Some(RankingFunction {
                name: format!("rank_lex_{primary}_{secondary}"),
                expression: format!("({primary}, {secondary})"),
                domain: "lexicographic non-negative integers".to_string(),
            })
        } else if attempt < n.saturating_mul(3) {
            // Strategy 3: Polynomial (quadratic) combination.
            let idx =
                (attempt.saturating_sub(if self.config.use_lexicographic && n > 1 { n.saturating_mul(2) } else { n })) % n;
            let (var, _delta) = decreasing_vars[idx.min(n - 1)];
            Some(RankingFunction {
                name: format!("rank_poly_{var}"),
                expression: format!("{var} * {var}"),
                domain: "non-negative integers".to_string(),
            })
        } else {
            // Strategy 4: Structural recursion depth.
            let idx = (attempt.saturating_sub(n.saturating_mul(3))) % n;
            let (var, _delta) = decreasing_vars[idx.min(n - 1)];
            Some(RankingFunction {
                name: format!("rank_depth_{var}"),
                expression: format!("depth({var})"),
                domain: "non-negative integers".to_string(),
            })
        }
    }

    /// Validate that a ranking function candidate actually decreases for the
    /// given set of decreasing variables.
    ///
    /// A candidate is valid when, for at least one decreasing variable, the
    /// ranking expression strictly decreases after the variable is decremented.
    /// Different expression shapes require different checks:
    ///   - Simple variable: symbolic/numeric via `check_decrease`.
    ///   - Lexicographic tuple: at least one component must decrease.
    ///   - Polynomial / structural: base variable must appear and decrease.
    fn validate_ranking_candidate(
        &self,
        candidate: &RankingFunction,
        decreasing_vars: &[(&str, &str)],
    ) -> bool {
        for (var, delta) in decreasing_vars {
            if !candidate.expression.contains(var) {
                continue;
            }

            // All strategies require a strictly positive delta.
            if let Ok(d) = delta.parse::<f64>()
                && d <= 0.0
            {
                continue;
            }

            // Simple variable expression (Strategy 1): direct decrease check.
            if candidate.expression == *var {
                let after = format!("{var} - {delta}");
                if self.check_decrease(candidate, &candidate.expression, &after) {
                    return true;
                }
                continue;
            }

            // Lexicographic tuple expression (Strategy 2): a component decreases.
            if candidate.expression.starts_with('(') && candidate.expression.ends_with(')') {
                // The expression contains the variable, so the tuple decreases
                // lexicographically when that component decreases.
                let after_expr = candidate.expression.replace(var, &format!("{var} - {delta}"));
                if after_expr != candidate.expression {
                    return true;
                }
                continue;
            }

            // Polynomial expression (Strategy 3): e.g. "var * var".
            // If the base variable strictly decreases by a positive amount,
            // the polynomial also decreases for positive values.
            if candidate.expression.contains(" * ") {
                let after_expr = candidate.expression.replace(var, &format!("({var} - {delta})"));
                if after_expr != candidate.expression {
                    return true;
                }
                continue;
            }

            // Structural recursion depth (Strategy 4): e.g. "depth(var)".
            if candidate.expression.starts_with("depth(") {
                let after_expr = candidate.expression.replace(var, &format!("{var} - {delta}"));
                if after_expr != candidate.expression {
                    return true;
                }
                continue;
            }
        }
        false
    }

    /// Check whether a ranking function decreases between a before and after state.
    #[must_use]
    pub fn check_decrease(&self, ranking: &RankingFunction, before: &str, after: &str) -> bool {
        // Symbolic check: if the ranking expression matches "before" and
        // "after" looks like "before - k" for some positive k, it decreases.
        if after.starts_with(before) && after.contains(" - ") {
            return true;
        }

        // Parse numeric values if possible.
        if let (Ok(b), Ok(a)) = (before.parse::<i64>(), after.parse::<i64>()) {
            return a < b;
        }

        // If after is a simple subtraction from the ranking expression.
        let minus_pattern = format!("{} - ", ranking.expression);
        if after.starts_with(&minus_pattern) {
            return true;
        }

        false
    }

    /// Construct a lexicographic ordering from multiple ranking functions.
    #[must_use]
    pub fn lexicographic_order(&self, rankings: Vec<RankingFunction>) -> LexOrder {
        LexOrder { components: rankings }
    }

    /// Attempt to compute a bounded iteration count from a ranking function.
    ///
    /// If the initial value can be parsed or estimated, returns the bound.
    #[must_use]
    pub fn bounded_iteration_count(
        &self,
        _ranking: &RankingFunction,
        initial: &str,
    ) -> Option<u64> {
        if !self.config.bound_synthesis {
            return None;
        }

        // If initial is a numeric value, use it directly.
        if let Ok(n) = initial.parse::<u64>() {
            return Some(n);
        }

        // Cannot determine numeric bound from symbolic initial value.
        None
    }

    /// Synthesize a ranking function from a loop condition and body effect.
    ///
    /// Examines the condition to determine what variable is being tested,
    /// and the body effect to determine how it changes.
    #[must_use]
    pub fn synthesize_ranking(
        &self,
        loop_condition: &str,
        body_effect: &str,
    ) -> Option<RankingFunction> {
        // Look for patterns like "i < n" or "i > 0" in the condition.
        // And "i += 1" or "i -= 1" in the body.

        // Pattern: "VAR > 0" with "VAR -= STEP" => ranking = VAR
        for part in loop_condition.split(" && ") {
            let trimmed = part.trim();
            if let Some(var) = trimmed.strip_suffix(" > 0") {
                let var = var.trim();
                let dec_pattern = format!("{var} -= ");
                if body_effect.contains(&dec_pattern) {
                    return Some(RankingFunction {
                        name: format!("rank_{var}"),
                        expression: var.to_string(),
                        domain: "non-negative integers".to_string(),
                    });
                }
            }

            // Pattern: "VAR < BOUND" with "VAR += STEP" => ranking = BOUND - VAR
            if trimmed.contains(" < ") {
                let parts: Vec<&str> = trimmed.splitn(2, " < ").collect();
                if parts.len() == 2 {
                    let var = parts[0].trim();
                    let bound = parts[1].trim();
                    let inc_pattern = format!("{var} += ");
                    if body_effect.contains(&inc_pattern) {
                        return Some(RankingFunction {
                            name: format!("rank_{bound}_minus_{var}"),
                            expression: format!("{bound} - {var}"),
                            domain: "non-negative integers".to_string(),
                        });
                    }
                }
            }
        }

        None
    }

    /// Access the configuration.
    #[must_use]
    pub fn config(&self) -> &TerminationConfig {
        &self.config
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{IterationSnapshot, ProofFrontier};

    fn frontier(trusted: u32, certified: u32, rt: u32, failed: u32, unknown: u32) -> ProofFrontier {
        ProofFrontier { trusted, certified, runtime_checked: rt, failed, unknown }
    }

    fn snap(iteration: u32, f: ProofFrontier) -> IterationSnapshot {
        IterationSnapshot::new(iteration, f)
    }

    // --- TerminationCriterion: MaxIterations ---

    #[test]
    fn test_max_iterations_not_reached() {
        let analyzer = TerminationAnalyzer::with_criterion(TerminationCriterion::MaxIterations(5));
        let history = vec![snap(0, frontier(1, 0, 0, 2, 0))];
        assert!(analyzer.should_terminate(&history).is_none());
    }

    #[test]
    fn test_max_iterations_reached() {
        let analyzer = TerminationAnalyzer::with_criterion(TerminationCriterion::MaxIterations(3));
        let history = vec![
            snap(0, frontier(1, 0, 0, 2, 0)),
            snap(1, frontier(2, 0, 0, 1, 0)),
            snap(2, frontier(3, 0, 0, 0, 0)),
        ];
        let reason = analyzer.should_terminate(&history).expect("should terminate");
        assert!(matches!(reason, TerminationReason::MaxIterations { limit: 3, reached: 3 }));
    }

    // --- TerminationCriterion: FixedPoint ---

    #[test]
    fn test_fixed_point_not_reached() {
        let analyzer = TerminationAnalyzer::with_criterion(TerminationCriterion::FixedPoint);
        let history = vec![snap(0, frontier(1, 0, 0, 2, 0)), snap(1, frontier(2, 0, 0, 1, 0))];
        assert!(analyzer.should_terminate(&history).is_none());
    }

    #[test]
    fn test_fixed_point_reached() {
        let analyzer = TerminationAnalyzer::with_criterion(TerminationCriterion::FixedPoint);
        let history = vec![snap(0, frontier(3, 0, 0, 1, 0)), snap(1, frontier(3, 0, 0, 1, 0))];
        let reason = analyzer.should_terminate(&history).expect("should terminate");
        assert!(matches!(reason, TerminationReason::FixedPoint { stable_iterations: 2 }));
    }

    #[test]
    fn test_fixed_point_single_iteration() {
        let analyzer = TerminationAnalyzer::with_criterion(TerminationCriterion::FixedPoint);
        let history = vec![snap(0, frontier(3, 0, 0, 1, 0))];
        assert!(analyzer.should_terminate(&history).is_none());
    }

    // --- TerminationCriterion: StagnationTimeout ---

    #[test]
    fn test_stagnation_timeout_not_reached() {
        let analyzer = TerminationAnalyzer::with_criterion(
            TerminationCriterion::StagnationTimeout(Duration::from_secs(60)),
        );
        let history = vec![snap(0, frontier(1, 0, 0, 2, 0))];
        assert!(analyzer.should_terminate(&history).is_none());
    }

    #[test]
    fn test_stagnation_timeout_reached() {
        let mut analyzer = TerminationAnalyzer::new(
            vec![TerminationCriterion::StagnationTimeout(Duration::from_secs(10))],
            ResourceBudget::unlimited(),
        );
        let f = frontier(3, 0, 0, 1, 0);
        // First iteration: has progress (from nothing to 3 proved).
        analyzer.record_iteration(None, &f, Duration::from_secs(2));
        // Subsequent iterations: no progress, stagnation accumulates.
        analyzer.record_iteration(Some(&f), &f, Duration::from_secs(4));
        analyzer.record_iteration(Some(&f), &f, Duration::from_secs(4));
        analyzer.record_iteration(Some(&f), &f, Duration::from_secs(4));

        let history =
            vec![snap(0, f.clone()), snap(1, f.clone()), snap(2, f.clone()), snap(3, f.clone())];
        let reason = analyzer.should_terminate(&history).expect("should terminate");
        assert!(matches!(reason, TerminationReason::StagnationTimeout { .. }));
    }

    // --- TerminationCriterion: ConfidenceThreshold ---

    #[test]
    fn test_confidence_threshold_not_met() {
        let analyzer =
            TerminationAnalyzer::with_criterion(TerminationCriterion::ConfidenceThreshold(0.9));
        let history = vec![snap(0, frontier(1, 0, 0, 9, 0))]; // 10% proved
        assert!(analyzer.should_terminate(&history).is_none());
    }

    #[test]
    fn test_confidence_threshold_met() {
        let analyzer =
            TerminationAnalyzer::with_criterion(TerminationCriterion::ConfidenceThreshold(0.8));
        let history = vec![snap(0, frontier(8, 1, 0, 1, 0))]; // 90% proved
        let reason = analyzer.should_terminate(&history).expect("should terminate");
        match reason {
            TerminationReason::ConfidenceThreshold { achieved, threshold } => {
                assert!(achieved >= 0.8);
                assert!((threshold - 0.8).abs() < f64::EPSILON);
            }
            _ => panic!("expected ConfidenceThreshold"),
        }
    }

    #[test]
    fn test_confidence_threshold_empty_frontier() {
        let analyzer =
            TerminationAnalyzer::with_criterion(TerminationCriterion::ConfidenceThreshold(0.5));
        let history = vec![snap(0, frontier(0, 0, 0, 0, 0))];
        // convergence_score() returns None for empty frontier.
        assert!(analyzer.should_terminate(&history).is_none());
    }

    // --- TerminationCriterion: Combined ---

    #[test]
    fn test_combined_first_triggers() {
        let analyzer = TerminationAnalyzer::with_criterion(TerminationCriterion::Combined(vec![
            TerminationCriterion::MaxIterations(2),
            TerminationCriterion::FixedPoint,
        ]));
        let history = vec![snap(0, frontier(1, 0, 0, 2, 0)), snap(1, frontier(2, 0, 0, 1, 0))];
        let reason = analyzer.should_terminate(&history).expect("should terminate");
        match reason {
            TerminationReason::Combined { trigger } => {
                assert!(matches!(*trigger, TerminationReason::MaxIterations { .. }));
            }
            _ => panic!("expected Combined"),
        }
    }

    #[test]
    fn test_combined_second_triggers() {
        let analyzer = TerminationAnalyzer::with_criterion(TerminationCriterion::Combined(vec![
            TerminationCriterion::MaxIterations(10),
            TerminationCriterion::FixedPoint,
        ]));
        let history = vec![snap(0, frontier(3, 0, 0, 1, 0)), snap(1, frontier(3, 0, 0, 1, 0))];
        let reason = analyzer.should_terminate(&history).expect("should terminate");
        match reason {
            TerminationReason::Combined { trigger } => {
                assert!(matches!(*trigger, TerminationReason::FixedPoint { .. }));
            }
            _ => panic!("expected Combined"),
        }
    }

    #[test]
    fn test_combined_none_triggers() {
        let analyzer = TerminationAnalyzer::with_criterion(TerminationCriterion::Combined(vec![
            TerminationCriterion::MaxIterations(10),
            TerminationCriterion::FixedPoint,
        ]));
        let history = vec![snap(0, frontier(1, 0, 0, 2, 0)), snap(1, frontier(2, 0, 0, 1, 0))];
        assert!(analyzer.should_terminate(&history).is_none());
    }

    // --- ResourceBudget ---

    #[test]
    fn test_resource_budget_unlimited() {
        let budget = ResourceBudget::unlimited();
        assert!(!budget.any_exhausted());
        assert!(budget.remaining_solver_time().is_none());
        assert!(budget.remaining_iterations().is_none());
    }

    #[test]
    fn test_resource_budget_solver_time() {
        let mut budget = ResourceBudget::new(Some(Duration::from_secs(10)), None);
        assert!(!budget.solver_time_exhausted());
        budget.record_solver_time(Duration::from_secs(5));
        assert!(!budget.solver_time_exhausted());
        assert_eq!(budget.remaining_solver_time(), Some(Duration::from_secs(5)));
        budget.record_solver_time(Duration::from_secs(6));
        assert!(budget.solver_time_exhausted());
        assert_eq!(budget.remaining_solver_time(), Some(Duration::ZERO));
    }

    #[test]
    fn test_resource_budget_iterations() {
        let mut budget = ResourceBudget::new(None, Some(3));
        assert!(!budget.iterations_exhausted());
        budget.record_iteration();
        budget.record_iteration();
        assert!(!budget.iterations_exhausted());
        assert_eq!(budget.remaining_iterations(), Some(1));
        budget.record_iteration();
        assert!(budget.iterations_exhausted());
        assert_eq!(budget.remaining_iterations(), Some(0));
    }

    #[test]
    fn test_resource_budget_exhausted_resource() {
        let mut budget = ResourceBudget::new(Some(Duration::from_secs(1)), Some(100));
        assert!(budget.exhausted_resource().is_none());
        budget.record_solver_time(Duration::from_secs(2));
        assert_eq!(budget.exhausted_resource(), Some(ResourceKind::SolverTime));
    }

    #[test]
    fn test_resource_budget_default() {
        let budget = ResourceBudget::default();
        assert_eq!(budget.max_solver_time, Some(Duration::from_secs(600)));
        assert_eq!(budget.max_iterations, Some(50));
        assert!(!budget.any_exhausted());
    }

    #[test]
    fn test_budget_exhaustion_terminates() {
        let mut analyzer = TerminationAnalyzer::new(
            vec![TerminationCriterion::MaxIterations(100)],
            ResourceBudget::new(None, Some(2)),
        );
        analyzer.budget_mut().record_iteration();
        analyzer.budget_mut().record_iteration();

        let history = vec![snap(0, frontier(1, 0, 0, 2, 0))];
        let reason = analyzer.should_terminate(&history).expect("should terminate");
        assert!(matches!(
            reason,
            TerminationReason::BudgetExhausted { resource: ResourceKind::Iterations }
        ));
    }

    // --- ConvergenceRate + record_iteration ---

    #[test]
    fn test_record_iteration_tracks_rate() {
        let mut analyzer = TerminationAnalyzer::new(vec![], ResourceBudget::unlimited());
        let f0 = frontier(1, 0, 0, 4, 0);
        let f1 = frontier(3, 0, 0, 2, 0);

        analyzer.record_iteration(None, &f0, Duration::from_millis(100));
        let rate = analyzer.latest_rate().expect("rate exists");
        assert_eq!(rate.vcs_proved_delta, 1);
        assert_eq!(rate.cumulative_proved, 1);
        assert_eq!(rate.total_vcs, 5);

        analyzer.record_iteration(Some(&f0), &f1, Duration::from_millis(200));
        let rate = analyzer.latest_rate().expect("rate exists");
        assert_eq!(rate.vcs_proved_delta, 2);
        assert_eq!(rate.cumulative_proved, 3);
        assert_eq!(rate.total_vcs, 5);
        assert!(rate.moving_average > 0.0);
    }

    #[test]
    fn test_record_iteration_no_progress_tracks_stagnation() {
        let mut analyzer = TerminationAnalyzer::new(
            vec![TerminationCriterion::StagnationTimeout(Duration::from_secs(5))],
            ResourceBudget::unlimited(),
        );
        let f = frontier(3, 0, 0, 2, 0);
        // First iteration establishes baseline (counts as progress since it's first).
        analyzer.record_iteration(None, &f, Duration::from_secs(2));
        // Second iteration: no delta, so stagnation accumulates.
        analyzer.record_iteration(Some(&f), &f, Duration::from_secs(3));
        analyzer.record_iteration(Some(&f), &f, Duration::from_secs(3));

        let history = vec![snap(0, f.clone()), snap(1, f.clone()), snap(2, f.clone())];
        let reason = analyzer.should_terminate(&history).expect("should terminate");
        assert!(matches!(reason, TerminationReason::StagnationTimeout { .. }));
    }

    #[test]
    fn test_record_iteration_progress_resets_stagnation() {
        let mut analyzer = TerminationAnalyzer::new(
            vec![TerminationCriterion::StagnationTimeout(Duration::from_secs(10))],
            ResourceBudget::unlimited(),
        );
        let f0 = frontier(3, 0, 0, 2, 0);
        let f1 = frontier(3, 0, 0, 2, 0);
        let f2 = frontier(4, 0, 0, 1, 0);

        analyzer.record_iteration(None, &f0, Duration::from_secs(4));
        analyzer.record_iteration(Some(&f0), &f1, Duration::from_secs(4));
        // Progress! Stagnation resets.
        analyzer.record_iteration(Some(&f1), &f2, Duration::from_secs(4));

        let history = vec![snap(0, f0), snap(1, f1), snap(2, f2)];
        assert!(analyzer.should_terminate(&history).is_none());
    }

    // --- estimate_remaining_iterations ---

    #[test]
    fn test_estimate_remaining_positive_rate() {
        let rate = ConvergenceRate {
            vcs_proved_delta: 2,
            cumulative_proved: 6,
            total_vcs: 10,
            moving_average: 2.0,
            trend: 0.0,
        };
        assert_eq!(estimate_remaining_iterations(&rate), Some(2));
    }

    #[test]
    fn test_estimate_remaining_fractional() {
        let rate = ConvergenceRate {
            vcs_proved_delta: 1,
            cumulative_proved: 5,
            total_vcs: 10,
            moving_average: 1.5,
            trend: 0.0,
        };
        // (10-5)/1.5 = 3.33, ceil = 4
        assert_eq!(estimate_remaining_iterations(&rate), Some(4));
    }

    #[test]
    fn test_estimate_remaining_zero_rate() {
        let rate = ConvergenceRate {
            vcs_proved_delta: 0,
            cumulative_proved: 5,
            total_vcs: 10,
            moving_average: 0.0,
            trend: 0.0,
        };
        assert!(estimate_remaining_iterations(&rate).is_none());
    }

    #[test]
    fn test_estimate_remaining_negative_rate() {
        let rate = ConvergenceRate {
            vcs_proved_delta: -1,
            cumulative_proved: 3,
            total_vcs: 10,
            moving_average: -0.5,
            trend: -0.5,
        };
        assert!(estimate_remaining_iterations(&rate).is_none());
    }

    #[test]
    fn test_estimate_remaining_all_proved() {
        let rate = ConvergenceRate {
            vcs_proved_delta: 2,
            cumulative_proved: 10,
            total_vcs: 10,
            moving_average: 2.0,
            trend: 0.0,
        };
        assert_eq!(estimate_remaining_iterations(&rate), Some(0));
    }

    // --- estimate_loop_bound ---

    #[test]
    fn test_loop_bound_normal() {
        assert_eq!(estimate_loop_bound(10, 2.0), Some(5));
    }

    #[test]
    fn test_loop_bound_fractional() {
        assert_eq!(estimate_loop_bound(10, 3.0), Some(4)); // ceil(10/3) = 4
    }

    #[test]
    fn test_loop_bound_zero_rate() {
        assert!(estimate_loop_bound(10, 0.0).is_none());
    }

    #[test]
    fn test_loop_bound_zero_vcs() {
        assert!(estimate_loop_bound(0, 2.0).is_none());
    }

    #[test]
    fn test_loop_bound_negative_rate() {
        assert!(estimate_loop_bound(10, -1.0).is_none());
    }

    // --- will_converge / predict_convergence ---

    #[test]
    fn test_predict_convergence_empty_history() {
        let pred = will_converge(&[], 10);
        assert!(!pred.will_converge);
        assert!(pred.estimated_remaining.is_none());
        assert!((pred.confidence - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_predict_convergence_all_proved() {
        let rates = vec![ConvergenceRate {
            vcs_proved_delta: 2,
            cumulative_proved: 10,
            total_vcs: 10,
            moving_average: 2.0,
            trend: 0.0,
        }];
        let pred = will_converge(&rates, 10);
        assert!(pred.will_converge);
        assert_eq!(pred.estimated_remaining, Some(0));
        assert!((pred.confidence - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_predict_convergence_positive_rate() {
        let rates = vec![ConvergenceRate {
            vcs_proved_delta: 2,
            cumulative_proved: 6,
            total_vcs: 10,
            moving_average: 2.0,
            trend: 0.1,
        }];
        let pred = will_converge(&rates, 10);
        assert!(pred.will_converge);
        assert_eq!(pred.estimated_remaining, Some(2));
        assert!(pred.confidence > 0.0);
    }

    #[test]
    fn test_predict_convergence_no_progress() {
        let rates = vec![ConvergenceRate {
            vcs_proved_delta: 0,
            cumulative_proved: 3,
            total_vcs: 10,
            moving_average: 0.0,
            trend: -0.5,
        }];
        let pred = will_converge(&rates, 10);
        assert!(!pred.will_converge);
        assert!(pred.estimated_remaining.is_none());
    }

    #[test]
    fn test_predict_convergence_decelerating() {
        let rates = vec![ConvergenceRate {
            vcs_proved_delta: 1,
            cumulative_proved: 5,
            total_vcs: 10,
            moving_average: 0.5,
            trend: -0.3,
        }];
        let pred = will_converge(&rates, 10);
        assert!(pred.will_converge);
        // Decelerating: lower confidence.
        assert!(pred.confidence < 0.6);
    }

    #[test]
    fn test_predict_convergence_zero_total() {
        let pred = will_converge(&[], 0);
        assert!(!pred.will_converge);
    }

    // --- TerminationAnalyzer: predict_convergence + estimate_remaining ---

    #[test]
    fn test_analyzer_predict_convergence() {
        let mut analyzer = TerminationAnalyzer::new(vec![], ResourceBudget::unlimited());
        let f0 = frontier(2, 0, 0, 8, 0);
        let f1 = frontier(4, 0, 0, 6, 0);
        analyzer.record_iteration(None, &f0, Duration::from_millis(50));
        analyzer.record_iteration(Some(&f0), &f1, Duration::from_millis(50));

        let pred = analyzer.predict_convergence(10);
        assert!(pred.will_converge);
        assert!(pred.estimated_remaining.is_some());
    }

    #[test]
    fn test_analyzer_estimate_remaining() {
        let mut analyzer = TerminationAnalyzer::new(vec![], ResourceBudget::unlimited());
        let f0 = frontier(2, 0, 0, 8, 0);
        let f1 = frontier(4, 0, 0, 6, 0);
        analyzer.record_iteration(None, &f0, Duration::from_millis(50));
        analyzer.record_iteration(Some(&f0), &f1, Duration::from_millis(50));

        let remaining = analyzer.estimate_remaining();
        assert!(remaining.is_some());
    }

    #[test]
    fn test_analyzer_default_has_criteria() {
        let analyzer = TerminationAnalyzer::default();
        assert_eq!(analyzer.criteria.len(), 3);
    }

    // --- Fixed point counting ---

    #[test]
    fn test_fixed_point_counts_consecutive() {
        let f = frontier(3, 0, 0, 1, 0);
        let history = vec![
            snap(0, frontier(1, 0, 0, 3, 0)),
            snap(1, f.clone()),
            snap(2, f.clone()),
            snap(3, f.clone()),
        ];
        let reason = check_fixed_point(&history).expect("fixed point");
        match reason {
            TerminationReason::FixedPoint { stable_iterations } => {
                assert_eq!(stable_iterations, 3);
            }
            _ => panic!("expected FixedPoint"),
        }
    }

    #[test]
    fn test_rate_history_growth() {
        let mut analyzer = TerminationAnalyzer::new(vec![], ResourceBudget::unlimited());
        let f = frontier(5, 0, 0, 0, 0);
        for _ in 0..10 {
            analyzer.record_iteration(Some(&f), &f, Duration::from_millis(10));
        }
        assert_eq!(analyzer.rate_history().len(), 10);
    }

    // =========================================================================
    // Ranking-function-based termination tests
    // =========================================================================

    #[test]
    fn test_ranking_function_creation() {
        let rf = RankingFunction {
            name: "rank_n".to_string(),
            expression: "n".to_string(),
            domain: "non-negative integers".to_string(),
        };
        assert_eq!(rf.name, "rank_n");
        assert_eq!(rf.expression, "n");
        assert_eq!(rf.domain, "non-negative integers");
    }

    #[test]
    fn test_decrease_measure_strict() {
        let dm = DecreaseMeasure {
            variable: "i".to_string(),
            before: "i".to_string(),
            after: "i - 1".to_string(),
            strict: true,
        };
        assert!(dm.strict);
        assert_eq!(dm.variable, "i");
    }

    #[test]
    fn test_decrease_measure_non_strict() {
        let dm = DecreaseMeasure {
            variable: "x".to_string(),
            before: "10".to_string(),
            after: "10".to_string(),
            strict: false,
        };
        assert!(!dm.strict);
    }

    #[test]
    fn test_lex_order_creation() {
        let analyzer = RankingAnalyzer::new(TerminationConfig::default());
        let r1 = RankingFunction {
            name: "rank_i".to_string(),
            expression: "i".to_string(),
            domain: "non-negative integers".to_string(),
        };
        let r2 = RankingFunction {
            name: "rank_j".to_string(),
            expression: "j".to_string(),
            domain: "non-negative integers".to_string(),
        };
        let order = analyzer.lexicographic_order(vec![r1.clone(), r2.clone()]);
        assert_eq!(order.components.len(), 2);
        assert_eq!(order.components[0], r1);
        assert_eq!(order.components[1], r2);
    }

    #[test]
    fn test_termination_config_default() {
        let config = TerminationConfig::default();
        assert_eq!(config.max_ranking_attempts, 10);
        assert!(config.use_lexicographic);
        assert!(config.bound_synthesis);
    }

    #[test]
    fn test_ranking_analyzer_prove_simple_decrement() {
        let analyzer = RankingAnalyzer::new(TerminationConfig::default());
        let result = analyzer.prove_termination("n = n - 1", &["n"]);
        match result {
            TerminationResult::Terminates(proof) => {
                assert_eq!(proof.ranking_function.expression, "n");
                assert!(!proof.decrease_evidence.is_empty());
                assert!(proof.decrease_evidence[0].strict);
            }
            other => panic!("expected Terminates, got {other:?}"),
        }
    }

    #[test]
    fn test_ranking_analyzer_prove_dec_assign() {
        let analyzer = RankingAnalyzer::new(TerminationConfig::default());
        let result = analyzer.prove_termination("i -= 1", &["i"]);
        match result {
            TerminationResult::Terminates(proof) => {
                assert_eq!(proof.ranking_function.expression, "i");
            }
            other => panic!("expected Terminates, got {other:?}"),
        }
    }

    #[test]
    fn test_ranking_analyzer_no_decrease_found() {
        let analyzer = RankingAnalyzer::new(TerminationConfig::default());
        let result = analyzer.prove_termination("x = x + 1", &["x"]);
        assert!(matches!(result, TerminationResult::MayNotTerminate(_)));
    }

    #[test]
    fn test_ranking_analyzer_empty_variables() {
        let analyzer = RankingAnalyzer::new(TerminationConfig::default());
        let result = analyzer.prove_termination("n = n - 1", &[]);
        assert!(matches!(result, TerminationResult::MayNotTerminate(_)));
    }

    #[test]
    fn test_find_ranking_function_basic() {
        let analyzer = RankingAnalyzer::new(TerminationConfig::default());
        let rf = analyzer.find_ranking_function(&[("n", "1")]);
        assert!(rf.is_some());
        let rf = rf.unwrap();
        assert_eq!(rf.expression, "n");
    }

    #[test]
    fn test_find_ranking_function_empty() {
        let analyzer = RankingAnalyzer::new(TerminationConfig::default());
        assert!(analyzer.find_ranking_function(&[]).is_none());
    }

    #[test]
    fn test_find_ranking_function_skips_non_decreasing() {
        // First variable has delta "0" (not strictly decreasing), so the ranking
        // function search must skip it and find the second variable instead.
        // This exercises the multi-attempt loop (bug #672).
        let analyzer = RankingAnalyzer::new(TerminationConfig::default());
        let rf = analyzer.find_ranking_function(&[("flag", "0"), ("n", "1")]);
        assert!(rf.is_some(), "should find a ranking function on attempt > 0");
        let rf = rf.unwrap();
        assert_eq!(rf.expression, "n", "should skip 'flag' (delta 0) and select 'n' (delta 1)");
    }

    #[test]
    fn test_find_ranking_function_all_non_decreasing_returns_none() {
        // When no variable has a strictly positive delta, no ranking function
        // should be found — the loop must exhaust all attempts and return None.
        let config = TerminationConfig {
            max_ranking_attempts: 5,
            use_lexicographic: false,
            bound_synthesis: false,
        };
        let analyzer = RankingAnalyzer::new(config);
        assert!(
            analyzer.find_ranking_function(&[("x", "0"), ("y", "0")]).is_none(),
            "no ranking function when all deltas are zero"
        );
    }

    #[test]
    fn test_check_decrease_symbolic() {
        let analyzer = RankingAnalyzer::new(TerminationConfig::default());
        let rf = RankingFunction {
            name: "rank_n".to_string(),
            expression: "n".to_string(),
            domain: "non-negative integers".to_string(),
        };
        assert!(analyzer.check_decrease(&rf, "n", "n - 1"));
    }

    #[test]
    fn test_check_decrease_numeric() {
        let analyzer = RankingAnalyzer::new(TerminationConfig::default());
        let rf = RankingFunction {
            name: "rank".to_string(),
            expression: "x".to_string(),
            domain: "integers".to_string(),
        };
        assert!(analyzer.check_decrease(&rf, "10", "9"));
        assert!(!analyzer.check_decrease(&rf, "5", "5"));
        assert!(!analyzer.check_decrease(&rf, "3", "7"));
    }

    #[test]
    fn test_bounded_iteration_count_numeric() {
        let analyzer = RankingAnalyzer::new(TerminationConfig::default());
        let rf = RankingFunction {
            name: "rank_n".to_string(),
            expression: "n".to_string(),
            domain: "non-negative integers".to_string(),
        };
        assert_eq!(analyzer.bounded_iteration_count(&rf, "42"), Some(42));
    }

    #[test]
    fn test_bounded_iteration_count_symbolic() {
        let analyzer = RankingAnalyzer::new(TerminationConfig::default());
        let rf = RankingFunction {
            name: "rank_n".to_string(),
            expression: "n".to_string(),
            domain: "non-negative integers".to_string(),
        };
        assert!(analyzer.bounded_iteration_count(&rf, "n").is_none());
    }

    #[test]
    fn test_bounded_iteration_count_disabled() {
        let config = TerminationConfig { bound_synthesis: false, ..TerminationConfig::default() };
        let analyzer = RankingAnalyzer::new(config);
        let rf = RankingFunction {
            name: "rank_n".to_string(),
            expression: "n".to_string(),
            domain: "non-negative integers".to_string(),
        };
        assert!(analyzer.bounded_iteration_count(&rf, "100").is_none());
    }

    #[test]
    fn test_synthesize_ranking_decreasing_var() {
        let analyzer = RankingAnalyzer::new(TerminationConfig::default());
        let rf = analyzer.synthesize_ranking("n > 0", "n -= 1");
        assert!(rf.is_some());
        let rf = rf.unwrap();
        assert_eq!(rf.expression, "n");
    }

    #[test]
    fn test_synthesize_ranking_increasing_towards_bound() {
        let analyzer = RankingAnalyzer::new(TerminationConfig::default());
        let rf = analyzer.synthesize_ranking("i < n", "i += 1");
        assert!(rf.is_some());
        let rf = rf.unwrap();
        assert_eq!(rf.expression, "n - i");
    }

    #[test]
    fn test_synthesize_ranking_no_match() {
        let analyzer = RankingAnalyzer::new(TerminationConfig::default());
        let rf = analyzer.synthesize_ranking("flag == true", "toggle(flag)");
        assert!(rf.is_none());
    }

    #[test]
    fn test_ranking_analyzer_config_access() {
        let config = TerminationConfig {
            max_ranking_attempts: 5,
            use_lexicographic: false,
            bound_synthesis: true,
        };
        let analyzer = RankingAnalyzer::new(config);
        assert_eq!(analyzer.config().max_ranking_attempts, 5);
        assert!(!analyzer.config().use_lexicographic);
    }
}
