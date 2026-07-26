// trust-convergence/fixpoint.rs: Abstract fixpoint computation with widening/narrowing.
//
// Implements fixpoint iteration over a concrete AbstractValue lattice for computing
// loop invariants and program properties. Supports configurable widening delay,
// narrowing passes, and multi-variable state tracking via FixpointState.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

/// Abstract value in a lattice for fixpoint computation.
///
/// Represents elements of an abstract domain ordered by inclusion:
/// `Bottom <= Constant/Set/Interval <= Top`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum AbstractValue {
    /// No information (least element).
    Bottom,
    /// All values (greatest element).
    Top,
    /// Closed interval `[lo, hi]`.
    Interval(i64, i64),
    /// Finite set of concrete values.
    Set(Vec<i64>),
    /// Single constant value.
    Constant(i64),
}

/// Configuration for fixpoint iteration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FixpointConfig {
    /// Maximum number of iterations before giving up.
    pub max_iterations: usize,
    /// Number of iterations to delay before applying widening.
    pub widening_delay: usize,
    /// Whether to apply narrowing after the widened fixpoint is reached.
    pub use_narrowing: bool,
}

impl Default for FixpointConfig {
    fn default() -> Self {
        Self { max_iterations: 100, widening_delay: 3, use_narrowing: true }
    }
}

/// Result of a fixpoint computation on a single abstract value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FixpointResult {
    /// The computed fixpoint value.
    pub value: AbstractValue,
    /// Number of iterations performed.
    pub iterations: usize,
    /// Whether the computation converged within the iteration limit.
    pub converged: bool,
    /// Number of times widening was applied.
    pub widening_applied: usize,
}

/// Multi-variable abstract state for fixpoint computation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FixpointState {
    /// Map from variable names to abstract values.
    pub values: BTreeMap<String, AbstractValue>,
    /// Current iteration number.
    pub iteration: usize,
}

impl FixpointState {
    /// Create a new empty state at iteration 0.
    #[must_use]
    pub fn new() -> Self {
        Self { values: BTreeMap::new(), iteration: 0 }
    }

    /// Create a state with the given values at iteration 0.
    #[must_use]
    pub fn with_values(values: impl IntoIterator<Item = (String, AbstractValue)>) -> Self {
        Self { values: values.into_iter().collect(), iteration: 0 }
    }

    /// Get the abstract value for a variable, defaulting to Bottom.
    #[must_use]
    pub fn get(&self, var: &str) -> &AbstractValue {
        self.values.get(var).unwrap_or(&AbstractValue::Bottom)
    }

    /// Set the abstract value for a variable.
    pub fn set(&mut self, var: impl Into<String>, value: AbstractValue) {
        self.values.insert(var.into(), value);
    }
}

impl Default for FixpointState {
    fn default() -> Self {
        Self::new()
    }
}

/// Fixpoint computation engine with widening and narrowing.
#[derive(Debug, Clone)]
pub struct FixpointComputer {
    config: FixpointConfig,
}

impl FixpointComputer {
    /// Create a new computer with the given configuration.
    #[must_use]
    pub fn new(config: FixpointConfig) -> Self {
        Self { config }
    }

    /// Compute the fixpoint of `transfer` starting from `init`.
    ///
    /// Runs ascending iteration with join until stable, applying widening
    /// after `widening_delay` iterations. If `use_narrowing` is set, applies
    /// descending narrowing passes to recover precision.
    #[must_use]
    pub fn compute<F>(&self, init: AbstractValue, transfer: F) -> FixpointResult
    where
        F: Fn(&AbstractValue) -> AbstractValue,
    {
        let mut current = init;
        let mut iterations = 0;
        let mut widening_applied = 0;

        // Ascending phase: iterate until fixpoint or limit.
        loop {
            if iterations >= self.config.max_iterations {
                return FixpointResult {
                    value: current,
                    iterations,
                    converged: false,
                    widening_applied,
                };
            }

            let next = transfer(&current);
            let joined = join(&current, &next);

            // Check if we have reached a fixpoint.
            if includes(&current, &joined) {
                // If narrowing is enabled, refine.
                if self.config.use_narrowing && widening_applied > 0 {
                    let narrowed = self.narrow_phase(&current, &transfer, &mut iterations);
                    return FixpointResult {
                        value: narrowed,
                        iterations,
                        converged: true,
                        widening_applied,
                    };
                }
                return FixpointResult {
                    value: current,
                    iterations,
                    converged: true,
                    widening_applied,
                };
            }

            // Apply widening after delay.
            if iterations >= self.config.widening_delay {
                current = widen(&current, &joined);
                widening_applied = widening_applied.saturating_add(1);
            } else {
                current = joined;
            }

            iterations = iterations.saturating_add(1);
        }
    }

    /// Compute fixpoint over a multi-variable state.
    ///
    /// Iterates the transfer function on the full state until no variable changes
    /// (or the iteration limit is reached). Applies per-variable widening after
    /// `widening_delay` iterations to ensure convergence on infinite domains.
    ///
    /// Added widening support to prevent divergence.
    #[must_use]
    pub fn compute_state<F>(&self, init: FixpointState, transfer: F) -> FixpointState
    where
        F: Fn(&FixpointState) -> FixpointState,
    {
        let mut current = init;
        for i in 0..self.config.max_iterations {
            current.iteration = i;
            let next = transfer(&current);
            if next.values == current.values {
                current.iteration = i.saturating_add(1);
                return current;
            }

            // Apply per-variable widening after the delay threshold
            // to guarantee convergence on infinite ascending chains.
            if i >= self.config.widening_delay {
                let mut widened_values = BTreeMap::new();
                // Collect all variable names from both states
                let all_keys: BTreeSet<String> =
                    current.values.keys().chain(next.values.keys()).cloned().collect();
                for key in all_keys {
                    let cur_val = current.values.get(&key).unwrap_or(&AbstractValue::Bottom);
                    let next_val = next.values.get(&key).unwrap_or(&AbstractValue::Bottom);
                    widened_values.insert(key, widen(cur_val, next_val));
                }
                current = FixpointState { values: widened_values, iteration: i.saturating_add(1) };
            } else {
                current = FixpointState { values: next.values, iteration: i.saturating_add(1) };
            }
        }
        current
    }

    /// Check whether `a` and `b` represent the same abstract value.
    #[must_use]
    pub fn is_fixpoint(&self, a: &AbstractValue, b: &AbstractValue) -> bool {
        includes(a, b) && includes(b, a)
    }

    /// Narrowing phase: refine the widened fixpoint.
    fn narrow_phase<F>(
        &self,
        widened: &AbstractValue,
        transfer: &F,
        iterations: &mut usize,
    ) -> AbstractValue
    where
        F: Fn(&AbstractValue) -> AbstractValue,
    {
        let max_narrow = self.config.max_iterations.saturating_sub(*iterations).min(10);
        let mut current = widened.clone();

        for _ in 0..max_narrow {
            let next = transfer(&current);
            let narrowed = narrow(&current, &next);
            if narrowed == current {
                break;
            }
            current = narrowed;
            *iterations = iterations.saturating_add(1);
        }
        current
    }
}

// ---------------------------------------------------------------------------
// Lattice operations
// ---------------------------------------------------------------------------

/// Least upper bound (join) of two abstract values.
///
/// Returns the smallest value that contains both `a` and `b`.
#[must_use]
pub(crate) fn join(a: &AbstractValue, b: &AbstractValue) -> AbstractValue {
    match (a, b) {
        (AbstractValue::Bottom, other) | (other, AbstractValue::Bottom) => other.clone(),
        (AbstractValue::Top, _) | (_, AbstractValue::Top) => AbstractValue::Top,
        (AbstractValue::Constant(x), AbstractValue::Constant(y)) => {
            if x == y {
                AbstractValue::Constant(*x)
            } else {
                AbstractValue::Interval((*x).min(*y), (*x).max(*y))
            }
        }
        (AbstractValue::Constant(c), AbstractValue::Interval(lo, hi))
        | (AbstractValue::Interval(lo, hi), AbstractValue::Constant(c)) => {
            AbstractValue::Interval((*lo).min(*c), (*hi).max(*c))
        }
        (AbstractValue::Interval(lo1, hi1), AbstractValue::Interval(lo2, hi2)) => {
            AbstractValue::Interval((*lo1).min(*lo2), (*hi1).max(*hi2))
        }
        (AbstractValue::Set(s1), AbstractValue::Set(s2)) => {
            let mut merged = s1.clone();
            for v in s2 {
                if !merged.contains(v) {
                    merged.push(*v);
                }
            }
            merged.sort_unstable();
            AbstractValue::Set(merged)
        }
        (AbstractValue::Set(s), AbstractValue::Constant(c))
        | (AbstractValue::Constant(c), AbstractValue::Set(s)) => {
            let mut merged = s.clone();
            if !merged.contains(c) {
                merged.push(*c);
            }
            merged.sort_unstable();
            AbstractValue::Set(merged)
        }
        (AbstractValue::Set(s), AbstractValue::Interval(lo, hi))
        | (AbstractValue::Interval(lo, hi), AbstractValue::Set(s)) => {
            let set_min = s.iter().copied().min().unwrap_or(*lo);
            let set_max = s.iter().copied().max().unwrap_or(*hi);
            AbstractValue::Interval((*lo).min(set_min), (*hi).max(set_max))
        }
    }
}

/// Greatest lower bound (meet) of two abstract values.
///
/// Returns the largest value contained in both `a` and `b`.
#[must_use]
#[cfg(test)]
fn meet(a: &AbstractValue, b: &AbstractValue) -> AbstractValue {
    match (a, b) {
        (AbstractValue::Bottom, _) | (_, AbstractValue::Bottom) => AbstractValue::Bottom,
        (AbstractValue::Top, other) | (other, AbstractValue::Top) => other.clone(),
        (AbstractValue::Constant(x), AbstractValue::Constant(y)) => {
            if x == y {
                AbstractValue::Constant(*x)
            } else {
                AbstractValue::Bottom
            }
        }
        (AbstractValue::Constant(c), AbstractValue::Interval(lo, hi))
        | (AbstractValue::Interval(lo, hi), AbstractValue::Constant(c)) => {
            if c >= lo && c <= hi {
                AbstractValue::Constant(*c)
            } else {
                AbstractValue::Bottom
            }
        }
        (AbstractValue::Interval(lo1, hi1), AbstractValue::Interval(lo2, hi2)) => {
            let lo = (*lo1).max(*lo2);
            let hi = (*hi1).min(*hi2);
            if lo > hi { AbstractValue::Bottom } else { AbstractValue::Interval(lo, hi) }
        }
        (AbstractValue::Set(s1), AbstractValue::Set(s2)) => {
            let intersection: Vec<i64> = s1.iter().filter(|v| s2.contains(v)).copied().collect();
            if intersection.is_empty() {
                AbstractValue::Bottom
            } else {
                AbstractValue::Set(intersection)
            }
        }
        (AbstractValue::Set(s), AbstractValue::Constant(c))
        | (AbstractValue::Constant(c), AbstractValue::Set(s)) => {
            if s.contains(c) {
                AbstractValue::Constant(*c)
            } else {
                AbstractValue::Bottom
            }
        }
        (AbstractValue::Set(s), AbstractValue::Interval(lo, hi))
        | (AbstractValue::Interval(lo, hi), AbstractValue::Set(s)) => {
            let filtered: Vec<i64> =
                s.iter().filter(|v| **v >= *lo && **v <= *hi).copied().collect();
            if filtered.is_empty() { AbstractValue::Bottom } else { AbstractValue::Set(filtered) }
        }
    }
}

/// Widening operator for abstract values.
///
/// Over-approximates to ensure ascending chains stabilize. Unstable bounds
/// are pushed to infinity (i64::MIN / i64::MAX).
#[must_use]
pub(crate) fn widen(a: &AbstractValue, b: &AbstractValue) -> AbstractValue {
    match (a, b) {
        (AbstractValue::Bottom, other) => other.clone(),
        (_, AbstractValue::Bottom) => a.clone(),
        (AbstractValue::Top, _) | (_, AbstractValue::Top) => AbstractValue::Top,
        (AbstractValue::Interval(lo1, hi1), AbstractValue::Interval(lo2, hi2)) => {
            let lo = if lo2 < lo1 { i64::MIN } else { *lo1 };
            let hi = if hi2 > hi1 { i64::MAX } else { *hi1 };
            AbstractValue::Interval(lo, hi)
        }
        (AbstractValue::Constant(c1), AbstractValue::Constant(c2)) => {
            if c1 == c2 {
                AbstractValue::Constant(*c1)
            } else {
                let lo = if c2 < c1 { i64::MIN } else { *c1 };
                let hi = if c2 > c1 { i64::MAX } else { *c1 };
                AbstractValue::Interval(lo, hi)
            }
        }
        (AbstractValue::Constant(c), AbstractValue::Interval(lo, hi)) => {
            let new_lo = if lo < c { i64::MIN } else { *c };
            let new_hi = if hi > c { i64::MAX } else { *c };
            AbstractValue::Interval(new_lo, new_hi)
        }
        (AbstractValue::Interval(lo, hi), AbstractValue::Constant(c)) => {
            let new_lo = if c < lo { i64::MIN } else { *lo };
            let new_hi = if c > hi { i64::MAX } else { *hi };
            AbstractValue::Interval(new_lo, new_hi)
        }
        // Sets widen to intervals covering the union range.
        _ => {
            let (lo_a, hi_a) = bounds_of(a);
            let (lo_b, hi_b) = bounds_of(b);
            let lo = if lo_b < lo_a { i64::MIN } else { lo_a };
            let hi = if hi_b > hi_a { i64::MAX } else { hi_a };
            AbstractValue::Interval(lo, hi)
        }
    }
}

/// Narrowing operator for abstract values.
///
/// Recovers precision from a widened over-approximation by tightening
/// infinite bounds to finite ones from the more precise value.
#[must_use]
pub(crate) fn narrow(a: &AbstractValue, b: &AbstractValue) -> AbstractValue {
    match (a, b) {
        (AbstractValue::Bottom, _) | (_, AbstractValue::Bottom) => AbstractValue::Bottom,
        (_, AbstractValue::Top) => a.clone(),
        (AbstractValue::Top, other) => other.clone(),
        (AbstractValue::Interval(lo1, hi1), AbstractValue::Interval(lo2, hi2)) => {
            let lo = if *lo1 == i64::MIN { *lo2 } else { *lo1 };
            let hi = if *hi1 == i64::MAX { *hi2 } else { *hi1 };
            AbstractValue::Interval(lo, hi)
        }
        (AbstractValue::Interval(lo, hi), AbstractValue::Constant(c)) => {
            let new_lo = if *lo == i64::MIN { *c } else { *lo };
            let new_hi = if *hi == i64::MAX { *c } else { *hi };
            AbstractValue::Interval(new_lo, new_hi)
        }
        _ => b.clone(),
    }
}

/// Check whether `a` includes (is a superset of) `b`: `a >= b`.
#[must_use]
pub(crate) fn includes(a: &AbstractValue, b: &AbstractValue) -> bool {
    match (a, b) {
        (_, AbstractValue::Bottom) => true,
        (AbstractValue::Bottom, _) => false,
        (AbstractValue::Top, _) => true,
        (_, AbstractValue::Top) => false,
        (AbstractValue::Interval(lo1, hi1), AbstractValue::Interval(lo2, hi2)) => {
            lo1 <= lo2 && hi1 >= hi2
        }
        (AbstractValue::Interval(lo, hi), AbstractValue::Constant(c)) => c >= lo && c <= hi,
        (AbstractValue::Constant(c1), AbstractValue::Constant(c2)) => c1 == c2,
        (AbstractValue::Constant(_), AbstractValue::Interval(..)) => false,
        (AbstractValue::Set(s1), AbstractValue::Set(s2)) => s2.iter().all(|v| s1.contains(v)),
        (AbstractValue::Set(s), AbstractValue::Constant(c)) => s.contains(c),
        (AbstractValue::Constant(c), AbstractValue::Set(s)) => s.len() == 1 && s.contains(c),
        (AbstractValue::Interval(lo, hi), AbstractValue::Set(s)) => {
            s.iter().all(|v| v >= lo && v <= hi)
        }
        (AbstractValue::Set(_), AbstractValue::Interval(..)) => false,
    }
}

/// Extract the bounds of an abstract value as (lo, hi).
fn bounds_of(v: &AbstractValue) -> (i64, i64) {
    match v {
        AbstractValue::Bottom => (1, 0), // empty
        AbstractValue::Top => (i64::MIN, i64::MAX),
        AbstractValue::Constant(c) => (*c, *c),
        AbstractValue::Interval(lo, hi) => (*lo, *hi),
        AbstractValue::Set(s) => {
            if s.is_empty() {
                (1, 0)
            } else {
                // SAFETY: The else-branch only runs when s is non-empty.
                let lo =
                    s.iter().copied().min().unwrap_or_else(|| unreachable!("min on non-empty set"));
                let hi =
                    s.iter().copied().max().unwrap_or_else(|| unreachable!("max on non-empty set"));
                (lo, hi)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- join ---

    #[test]
    fn test_join_bottom_identity() {
        let a = AbstractValue::Interval(1, 10);
        assert_eq!(join(&AbstractValue::Bottom, &a), a);
        assert_eq!(join(&a, &AbstractValue::Bottom), a);
    }

    #[test]
    fn test_join_top_absorbing() {
        let a = AbstractValue::Interval(1, 10);
        assert_eq!(join(&AbstractValue::Top, &a), AbstractValue::Top);
        assert_eq!(join(&a, &AbstractValue::Top), AbstractValue::Top);
    }

    #[test]
    fn test_join_constants_equal() {
        assert_eq!(
            join(&AbstractValue::Constant(5), &AbstractValue::Constant(5)),
            AbstractValue::Constant(5)
        );
    }

    #[test]
    fn test_join_constants_different() {
        assert_eq!(
            join(&AbstractValue::Constant(3), &AbstractValue::Constant(7)),
            AbstractValue::Interval(3, 7)
        );
    }

    #[test]
    fn test_join_intervals() {
        assert_eq!(
            join(&AbstractValue::Interval(1, 5), &AbstractValue::Interval(3, 10)),
            AbstractValue::Interval(1, 10)
        );
    }

    #[test]
    fn test_join_sets() {
        assert_eq!(
            join(&AbstractValue::Set(vec![1, 3]), &AbstractValue::Set(vec![2, 3])),
            AbstractValue::Set(vec![1, 2, 3])
        );
    }

    #[test]
    fn test_join_constant_and_interval() {
        assert_eq!(
            join(&AbstractValue::Constant(0), &AbstractValue::Interval(5, 10)),
            AbstractValue::Interval(0, 10)
        );
    }

    // --- meet ---

    #[test]
    fn test_meet_bottom_absorbing() {
        let a = AbstractValue::Interval(1, 10);
        assert_eq!(meet(&AbstractValue::Bottom, &a), AbstractValue::Bottom);
        assert_eq!(meet(&a, &AbstractValue::Bottom), AbstractValue::Bottom);
    }

    #[test]
    fn test_meet_top_identity() {
        let a = AbstractValue::Interval(1, 10);
        assert_eq!(meet(&AbstractValue::Top, &a), a);
        assert_eq!(meet(&a, &AbstractValue::Top), a);
    }

    #[test]
    fn test_meet_disjoint_intervals() {
        assert_eq!(
            meet(&AbstractValue::Interval(1, 3), &AbstractValue::Interval(5, 10)),
            AbstractValue::Bottom
        );
    }

    #[test]
    fn test_meet_overlapping_intervals() {
        assert_eq!(
            meet(&AbstractValue::Interval(1, 7), &AbstractValue::Interval(5, 10)),
            AbstractValue::Interval(5, 7)
        );
    }

    #[test]
    fn test_meet_constant_in_interval() {
        assert_eq!(
            meet(&AbstractValue::Constant(5), &AbstractValue::Interval(1, 10)),
            AbstractValue::Constant(5)
        );
    }

    #[test]
    fn test_meet_constant_outside_interval() {
        assert_eq!(
            meet(&AbstractValue::Constant(15), &AbstractValue::Interval(1, 10)),
            AbstractValue::Bottom
        );
    }

    #[test]
    fn test_meet_sets() {
        assert_eq!(
            meet(&AbstractValue::Set(vec![1, 2, 3]), &AbstractValue::Set(vec![2, 3, 4])),
            AbstractValue::Set(vec![2, 3])
        );
    }

    // --- widen ---

    #[test]
    fn test_widen_from_bottom() {
        let b = AbstractValue::Interval(1, 5);
        assert_eq!(widen(&AbstractValue::Bottom, &b), b);
    }

    #[test]
    fn test_widen_intervals_upper_grows() {
        assert_eq!(
            widen(&AbstractValue::Interval(0, 10), &AbstractValue::Interval(0, 15)),
            AbstractValue::Interval(0, i64::MAX)
        );
    }

    #[test]
    fn test_widen_intervals_lower_shrinks() {
        assert_eq!(
            widen(&AbstractValue::Interval(0, 10), &AbstractValue::Interval(-5, 10)),
            AbstractValue::Interval(i64::MIN, 10)
        );
    }

    #[test]
    fn test_widen_intervals_stable() {
        assert_eq!(
            widen(&AbstractValue::Interval(0, 10), &AbstractValue::Interval(2, 8)),
            AbstractValue::Interval(0, 10)
        );
    }

    // --- narrow ---

    #[test]
    fn test_narrow_from_widened() {
        assert_eq!(
            narrow(&AbstractValue::Interval(i64::MIN, i64::MAX), &AbstractValue::Interval(3, 7)),
            AbstractValue::Interval(3, 7)
        );
    }

    #[test]
    fn test_narrow_partial_infinite() {
        assert_eq!(
            narrow(&AbstractValue::Interval(i64::MIN, 10), &AbstractValue::Interval(2, 10)),
            AbstractValue::Interval(2, 10)
        );
    }

    #[test]
    fn test_narrow_finite_unchanged() {
        assert_eq!(
            narrow(&AbstractValue::Interval(0, 10), &AbstractValue::Interval(2, 8)),
            AbstractValue::Interval(0, 10)
        );
    }

    // --- includes ---

    #[test]
    fn test_includes_bottom_included_in_everything() {
        assert!(includes(&AbstractValue::Interval(0, 10), &AbstractValue::Bottom));
        assert!(includes(&AbstractValue::Bottom, &AbstractValue::Bottom));
    }

    #[test]
    fn test_includes_top_includes_everything() {
        assert!(includes(&AbstractValue::Top, &AbstractValue::Interval(0, 10)));
        assert!(includes(&AbstractValue::Top, &AbstractValue::Constant(5)));
    }

    #[test]
    fn test_includes_interval_contains_subinterval() {
        assert!(includes(&AbstractValue::Interval(0, 10), &AbstractValue::Interval(2, 8)));
        assert!(!includes(&AbstractValue::Interval(2, 8), &AbstractValue::Interval(0, 10)));
    }

    #[test]
    fn test_includes_interval_contains_constant() {
        assert!(includes(&AbstractValue::Interval(0, 10), &AbstractValue::Constant(5)));
        assert!(!includes(&AbstractValue::Interval(0, 10), &AbstractValue::Constant(15)));
    }

    #[test]
    fn test_includes_set_contains_subset() {
        assert!(includes(&AbstractValue::Set(vec![1, 2, 3]), &AbstractValue::Set(vec![1, 3])));
        assert!(!includes(&AbstractValue::Set(vec![1, 3]), &AbstractValue::Set(vec![1, 2, 3])));
    }

    // --- FixpointComputer ---

    #[test]
    fn test_compute_constant_transfer() {
        let computer = FixpointComputer::new(FixpointConfig {
            max_iterations: 100,
            widening_delay: 3,
            use_narrowing: false,
        });
        let result = computer.compute(AbstractValue::Constant(0), |_| AbstractValue::Constant(0));
        assert!(result.converged);
        assert_eq!(result.value, AbstractValue::Constant(0));
        assert_eq!(result.widening_applied, 0);
    }

    #[test]
    fn test_compute_bounded_growth() {
        let computer = FixpointComputer::new(FixpointConfig {
            max_iterations: 100,
            widening_delay: 100, // no widening
            use_narrowing: false,
        });
        let result = computer.compute(AbstractValue::Interval(0, 0), |v| {
            if let AbstractValue::Interval(lo, hi) = v {
                AbstractValue::Interval(*lo, (*hi + 1).min(5))
            } else {
                v.clone()
            }
        });
        assert!(result.converged);
        assert_eq!(result.value, AbstractValue::Interval(0, 5));
    }

    #[test]
    fn test_compute_unbounded_needs_widening() {
        let computer = FixpointComputer::new(FixpointConfig {
            max_iterations: 100,
            widening_delay: 2,
            use_narrowing: false,
        });
        let result = computer.compute(AbstractValue::Interval(0, 0), |v| {
            if let AbstractValue::Interval(lo, hi) = v {
                AbstractValue::Interval(*lo, hi.saturating_add(1))
            } else {
                v.clone()
            }
        });
        assert!(result.converged);
        assert_eq!(result.value, AbstractValue::Interval(0, i64::MAX));
        assert!(result.widening_applied > 0);
    }

    #[test]
    fn test_compute_with_narrowing() {
        let computer = FixpointComputer::new(FixpointConfig {
            max_iterations: 100,
            widening_delay: 0,
            use_narrowing: true,
        });
        // Transfer always produces [0, 10]. Widening overshoots, narrowing recovers.
        let result =
            computer.compute(AbstractValue::Interval(0, 0), |_| AbstractValue::Interval(0, 10));
        assert!(result.converged);
        assert_eq!(result.value, AbstractValue::Interval(0, 10));
    }

    #[test]
    fn test_compute_max_iterations_exceeded() {
        let computer = FixpointComputer::new(FixpointConfig {
            max_iterations: 5,
            widening_delay: 100, // no widening
            use_narrowing: false,
        });
        let result = computer.compute(AbstractValue::Interval(0, 0), |v| {
            if let AbstractValue::Interval(lo, hi) = v {
                AbstractValue::Interval(*lo, hi + 1)
            } else {
                v.clone()
            }
        });
        assert!(!result.converged);
        assert_eq!(result.iterations, 5);
    }

    #[test]
    fn test_is_fixpoint() {
        let computer = FixpointComputer::new(FixpointConfig::default());
        assert!(
            computer.is_fixpoint(&AbstractValue::Interval(0, 10), &AbstractValue::Interval(0, 10))
        );
        assert!(
            !computer.is_fixpoint(&AbstractValue::Interval(0, 10), &AbstractValue::Interval(0, 5))
        );
    }

    // --- FixpointState ---

    #[test]
    fn test_fixpoint_state_new() {
        let state = FixpointState::new();
        assert_eq!(state.iteration, 0);
        assert!(state.values.is_empty());
        assert_eq!(*state.get("x"), AbstractValue::Bottom);
    }

    #[test]
    fn test_fixpoint_state_get_set() {
        let mut state = FixpointState::new();
        state.set("x", AbstractValue::Constant(42));
        assert_eq!(*state.get("x"), AbstractValue::Constant(42));
        assert_eq!(*state.get("y"), AbstractValue::Bottom);
    }

    #[test]
    fn test_compute_state_converges() {
        let computer = FixpointComputer::new(FixpointConfig {
            max_iterations: 100,
            widening_delay: 100, // high delay: finite domain converges without widening
            use_narrowing: false,
        });

        let mut init = FixpointState::new();
        init.set("x", AbstractValue::Constant(0));

        let result = computer.compute_state(init, |state| {
            let mut next = state.clone();
            // x converges to Interval(0, 5)
            if let AbstractValue::Constant(c) = state.get("x") {
                if *c < 5 {
                    next.set("x", AbstractValue::Constant(c + 1));
                }
            } else if let AbstractValue::Interval(_, hi) = state.get("x")
                && *hi < 5
            {
                next.set("x", AbstractValue::Interval(0, hi + 1));
            }
            next
        });

        assert_eq!(*result.get("x"), AbstractValue::Constant(5));
    }

    // --- compute_state widening tests ---

    #[test]
    fn test_compute_state_widening_converges_on_infinite_domain() {
        // Without widening, an unbounded increment would hit max_iterations.
        // With widening_delay=2, widening kicks in and stabilizes.
        let computer = FixpointComputer::new(FixpointConfig {
            max_iterations: 50,
            widening_delay: 2,
            use_narrowing: false,
        });

        let mut init = FixpointState::new();
        init.set("x", AbstractValue::Interval(0, 0));

        let result = computer.compute_state(init, |state| {
            let mut next = state.clone();
            // Unbounded growth: x upper bound increases each iteration
            if let AbstractValue::Interval(lo, hi) = state.get("x") {
                next.set("x", AbstractValue::Interval(*lo, hi.saturating_add(1)));
            }
            next
        });

        // After widening, the upper bound should have been pushed to i64::MAX
        // and the iteration should converge (widened value includes the next).
        match result.get("x") {
            AbstractValue::Interval(lo, hi) => {
                assert_eq!(*lo, 0);
                assert_eq!(*hi, i64::MAX);
            }
            other => panic!("expected Interval, got {other:?}"),
        }
        // Should converge well before max_iterations
        assert!(result.iteration < 50);
    }

    #[test]
    fn test_compute_state_no_widening_before_delay() {
        // With a high widening delay, the first iterations use plain join.
        let computer = FixpointComputer::new(FixpointConfig {
            max_iterations: 10,
            widening_delay: 100, // effectively no widening
            use_narrowing: false,
        });

        let mut init = FixpointState::new();
        init.set("x", AbstractValue::Constant(0));

        let result = computer.compute_state(init, |state| {
            let mut next = state.clone();
            if let AbstractValue::Constant(c) = state.get("x")
                && *c < 5
            {
                next.set("x", AbstractValue::Constant(c + 1));
            }
            next
        });

        // Should converge without widening since domain is finite
        assert_eq!(*result.get("x"), AbstractValue::Constant(5));
    }

    #[test]
    fn test_compute_state_widening_multiple_variables() {
        let computer = FixpointComputer::new(FixpointConfig {
            max_iterations: 50,
            widening_delay: 2,
            use_narrowing: false,
        });

        let mut init = FixpointState::new();
        init.set("x", AbstractValue::Interval(0, 0));
        init.set("y", AbstractValue::Interval(0, 0));

        let result = computer.compute_state(init, |state| {
            let mut next = state.clone();
            // x grows unbounded upward, y grows unbounded downward
            if let AbstractValue::Interval(lo, hi) = state.get("x") {
                next.set("x", AbstractValue::Interval(*lo, hi.saturating_add(1)));
            }
            if let AbstractValue::Interval(lo, hi) = state.get("y") {
                next.set("y", AbstractValue::Interval(lo.saturating_sub(1), *hi));
            }
            next
        });

        // Both should have been widened
        match result.get("x") {
            AbstractValue::Interval(lo, hi) => {
                assert_eq!(*lo, 0);
                assert_eq!(*hi, i64::MAX);
            }
            other => panic!("expected Interval for x, got {other:?}"),
        }
        match result.get("y") {
            AbstractValue::Interval(lo, hi) => {
                assert_eq!(*lo, i64::MIN);
                assert_eq!(*hi, 0);
            }
            other => panic!("expected Interval for y, got {other:?}"),
        }
        assert!(result.iteration < 50);
    }

    #[test]
    fn test_fixpoint_config_default() {
        let config = FixpointConfig::default();
        assert_eq!(config.max_iterations, 100);
        assert_eq!(config.widening_delay, 3);
        assert!(config.use_narrowing);
    }

    #[test]
    fn test_fixpoint_result_fields() {
        let result = FixpointResult {
            value: AbstractValue::Interval(0, 10),
            iterations: 7,
            converged: true,
            widening_applied: 2,
        };
        assert_eq!(result.iterations, 7);
        assert!(result.converged);
        assert_eq!(result.widening_applied, 2);
    }

    #[test]
    fn test_join_set_and_constant() {
        assert_eq!(
            join(&AbstractValue::Set(vec![1, 3]), &AbstractValue::Constant(2)),
            AbstractValue::Set(vec![1, 2, 3])
        );
    }

    #[test]
    fn test_meet_set_and_interval() {
        assert_eq!(
            meet(&AbstractValue::Set(vec![1, 5, 10, 15]), &AbstractValue::Interval(3, 12)),
            AbstractValue::Set(vec![5, 10])
        );
    }

    #[test]
    fn test_includes_interval_contains_set() {
        assert!(includes(&AbstractValue::Interval(0, 10), &AbstractValue::Set(vec![1, 5, 10])));
        assert!(!includes(&AbstractValue::Interval(0, 10), &AbstractValue::Set(vec![1, 5, 15])));
    }

    #[test]
    fn test_widen_constants_different() {
        // c1=5, c2=10 => c2 > c1, so hi -> MAX; lo stays 5
        assert_eq!(
            widen(&AbstractValue::Constant(5), &AbstractValue::Constant(10)),
            AbstractValue::Interval(5, i64::MAX)
        );
    }

    #[test]
    fn test_narrow_top_returns_other() {
        assert_eq!(
            narrow(&AbstractValue::Top, &AbstractValue::Interval(1, 5)),
            AbstractValue::Interval(1, 5)
        );
    }

    #[test]
    fn test_narrow_bottom_returns_bottom() {
        assert_eq!(
            narrow(&AbstractValue::Bottom, &AbstractValue::Interval(1, 5)),
            AbstractValue::Bottom
        );
        assert_eq!(
            narrow(&AbstractValue::Interval(1, 5), &AbstractValue::Bottom),
            AbstractValue::Bottom
        );
    }
}
