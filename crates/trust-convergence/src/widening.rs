// trust-convergence/widening.rs: Abstract interpretation widening for loop convergence.
//
// Applies widening and narrowing operators to accelerate convergence of the
// prove-strengthen-backprop loop. When stagnation is detected, widening jumps
// past oscillation; narrowing recovers precision afterward.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;

/// Abstract state representing the verification loop's progress.
///
/// Models the loop state as an abstract domain with three components:
/// - Set of proven VCs (monotonically increasing in a healthy run)
/// - Set of active spec proposals being evaluated
/// - Current strengthening round number
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbstractState {
    /// Set of VC identifiers that have been proven.
    pub proved_vcs: BTreeSet<String>,
    /// Set of active specification proposal identifiers.
    pub active_proposals: BTreeSet<String>,
    /// Current strengthening round number.
    pub round: u32,
}

impl AbstractState {
    /// Create a new empty abstract state at round 0.
    #[must_use]
    pub fn new() -> Self {
        Self { proved_vcs: BTreeSet::new(), active_proposals: BTreeSet::new(), round: 0 }
    }

    /// Create a state with given proved VCs, proposals, and round.
    #[must_use]
    pub fn with_components(
        proved_vcs: BTreeSet<String>,
        active_proposals: BTreeSet<String>,
        round: u32,
    ) -> Self {
        Self { proved_vcs, active_proposals, round }
    }

    /// Number of proven VCs.
    #[must_use]
    pub fn proved_count(&self) -> usize {
        self.proved_vcs.len()
    }

    /// Number of active proposals.
    #[must_use]
    pub fn proposal_count(&self) -> usize {
        self.active_proposals.len()
    }

    /// Whether this state is "top" — all VCs proved or proposals exhausted.
    #[must_use]
    pub fn is_top(&self) -> bool {
        self.active_proposals.is_empty() && !self.proved_vcs.is_empty()
    }

    /// Whether this state is "bottom" — nothing proved, no proposals.
    #[must_use]
    pub fn is_bottom(&self) -> bool {
        self.proved_vcs.is_empty() && self.active_proposals.is_empty()
    }

    /// Join two states: union of proved VCs and proposals.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        Self {
            proved_vcs: self.proved_vcs.union(&other.proved_vcs).cloned().collect(),
            active_proposals: self
                .active_proposals
                .union(&other.active_proposals)
                .cloned()
                .collect(),
            round: self.round.max(other.round),
        }
    }

    /// Meet two states: intersection of proved VCs and proposals.
    #[must_use]
    pub fn meet(&self, other: &Self) -> Self {
        Self {
            proved_vcs: self.proved_vcs.intersection(&other.proved_vcs).cloned().collect(),
            active_proposals: self
                .active_proposals
                .intersection(&other.active_proposals)
                .cloned()
                .collect(),
            round: self.round.min(other.round),
        }
    }

    /// Whether this state is a subset of (less than or equal to) another.
    #[must_use]
    pub fn is_subset_of(&self, other: &Self) -> bool {
        self.proved_vcs.is_subset(&other.proved_vcs)
            && self.active_proposals.is_subset(&other.active_proposals)
    }
}

impl Default for AbstractState {
    fn default() -> Self {
        Self::new()
    }
}

/// Widening operator: over-approximates to ensure convergence.
pub trait WideningOperator: std::fmt::Debug {
    /// Apply widening: given old state and new state, produce a widened state
    /// that is an over-approximation of both, ensuring the ascending chain
    /// eventually stabilizes.
    fn widen(&self, old_state: &AbstractState, new_state: &AbstractState) -> AbstractState;
}

/// Narrowing operator: recovers precision after widening.
pub trait NarrowingOperator: std::fmt::Debug {
    /// Apply narrowing: given the widened state and a more precise state,
    /// produce a state that is between the two (tighter than widened,
    /// but still sound).
    fn narrow(&self, wide_state: &AbstractState, precise_state: &AbstractState) -> AbstractState;
}

/// Threshold widening: after N iterations, jump to "top" for non-converging components.
///
/// If the proved VC set has not grown after `threshold` iterations, assume all
/// remaining proposals will eventually prove their VCs and add them to the proved set.
#[derive(Debug, Clone)]
pub struct ThresholdWidening {
    /// Number of iterations before widening kicks in.
    threshold: usize,
    /// Counter of iterations with no growth in proved VCs.
    stale_count: usize,
    /// Last seen proved count for detecting stagnation.
    last_proved_count: usize,
}

impl ThresholdWidening {
    /// Create a new threshold widening with the given iteration threshold.
    #[must_use]
    #[trust::requires(threshold > 0)]
    pub fn new(threshold: usize) -> Self {
        assert!(threshold > 0, "widening threshold must be non-zero");
        Self { threshold, stale_count: 0, last_proved_count: 0 }
    }

    /// Update the internal counter based on the current state.
    pub fn observe(&mut self, state: &AbstractState) {
        let current = state.proved_count();
        if current > self.last_proved_count {
            self.stale_count = 0;
            self.last_proved_count = current;
        } else {
            self.stale_count = self.stale_count.saturating_add(1);
        }
    }

    /// Whether widening should be applied (stale count >= threshold).
    #[must_use]
    pub fn should_widen(&self) -> bool {
        self.stale_count >= self.threshold
    }

    /// Current stale iteration count.
    #[must_use]
    pub fn stale_count(&self) -> usize {
        self.stale_count
    }

    /// Reset the internal counter.
    pub fn reset(&mut self) {
        self.stale_count = 0;
        self.last_proved_count = 0;
    }
}

impl WideningOperator for ThresholdWidening {
    fn widen(&self, _old_state: &AbstractState, new_state: &AbstractState) -> AbstractState {
        if !self.should_widen() {
            return new_state.clone();
        }

        // Widen: assume all active proposals will succeed.
        let mut widened = new_state.clone();
        for proposal in &new_state.active_proposals {
            widened.proved_vcs.insert(proposal.clone());
        }
        widened.active_proposals.clear();
        widened
    }
}

/// Delayed widening: apply widening only after K iterations of no progress.
///
/// Similar to threshold widening but with a configurable delay before any
/// widening is applied. This allows the natural fixpoint computation to
/// proceed for the first `delay` iterations.
#[derive(Debug, Clone)]
pub struct DelayedWidening {
    /// Number of total iterations before widening can be applied.
    delay: usize,
    /// Inner widening operator applied after the delay.
    threshold: usize,
    /// Total iterations observed.
    total_iterations: usize,
    /// Stale iterations since last progress.
    stale_count: usize,
    /// Last proved count for detecting progress.
    last_proved_count: usize,
}

impl DelayedWidening {
    /// Create a delayed widening that waits `delay` iterations before applying
    /// threshold widening with the given `threshold`.
    #[must_use]
    #[trust::requires(delay > 0)]
    #[trust::requires(threshold > 0)]
    pub fn new(delay: usize, threshold: usize) -> Self {
        assert!(delay > 0, "delay must be non-zero");
        assert!(threshold > 0, "threshold must be non-zero");
        Self { delay, threshold, total_iterations: 0, stale_count: 0, last_proved_count: 0 }
    }

    /// Observe a new state, updating internal counters.
    pub fn observe(&mut self, state: &AbstractState) {
        self.total_iterations = self.total_iterations.saturating_add(1);
        let current = state.proved_count();
        if current > self.last_proved_count {
            self.stale_count = 0;
            self.last_proved_count = current;
        } else {
            self.stale_count = self.stale_count.saturating_add(1);
        }
    }

    /// Whether widening should be applied.
    #[must_use]
    pub fn should_widen(&self) -> bool {
        self.total_iterations >= self.delay && self.stale_count >= self.threshold
    }

    /// Total iterations observed.
    #[must_use]
    pub fn total_iterations(&self) -> usize {
        self.total_iterations
    }

    /// Reset all counters.
    pub fn reset(&mut self) {
        self.total_iterations = 0;
        self.stale_count = 0;
        self.last_proved_count = 0;
    }
}

impl WideningOperator for DelayedWidening {
    fn widen(&self, _old_state: &AbstractState, new_state: &AbstractState) -> AbstractState {
        if !self.should_widen() {
            return new_state.clone();
        }

        // Widen: accept all proposals as proved.
        let mut widened = new_state.clone();
        for proposal in &new_state.active_proposals {
            widened.proved_vcs.insert(proposal.clone());
        }
        widened.active_proposals.clear();
        widened
    }
}

/// Simple narrowing: intersect the widened state with the precise state,
/// keeping anything proven in either.
#[derive(Debug, Clone)]
pub struct SimpleNarrowing;

impl NarrowingOperator for SimpleNarrowing {
    fn narrow(&self, wide_state: &AbstractState, precise_state: &AbstractState) -> AbstractState {
        // Keep only VCs that are in both the wide and precise states,
        // plus any newly proved in the precise state.
        let proved: BTreeSet<String> = wide_state
            .proved_vcs
            .intersection(&precise_state.proved_vcs)
            .chain(precise_state.proved_vcs.difference(&wide_state.proved_vcs))
            .cloned()
            .collect();

        // Proposals come from the precise state.
        AbstractState {
            proved_vcs: proved,
            active_proposals: precise_state.active_proposals.clone(),
            round: precise_state.round,
        }
    }
}

/// Schedule controlling when and where widening is applied.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WideningSchedule {
    /// Apply widening every N iterations (0 = never by schedule alone).
    pub interval: usize,
    /// Apply widening only after this many total iterations.
    pub min_iterations: usize,
    /// Maximum number of widening applications (0 = unlimited).
    pub max_applications: usize,
    /// Counter of widening applications so far.
    applications: usize,
    /// Total iterations observed.
    iterations: usize,
}

impl WideningSchedule {
    /// Create a new schedule.
    #[must_use]
    pub fn new(interval: usize, min_iterations: usize, max_applications: usize) -> Self {
        Self { interval, min_iterations, max_applications, applications: 0, iterations: 0 }
    }

    /// Simple schedule: widen every N iterations, no minimum, unlimited applications.
    #[must_use]
    pub fn every(interval: usize) -> Self {
        Self::new(interval, 0, 0)
    }

    /// Record an iteration and return whether widening should be applied now.
    pub fn tick(&mut self) -> bool {
        self.iterations = self.iterations.saturating_add(1);
        self.should_widen_now()
    }

    /// Whether widening should be applied at the current iteration.
    #[must_use]
    pub fn should_widen_now(&self) -> bool {
        if self.iterations < self.min_iterations {
            return false;
        }
        if self.max_applications > 0 && self.applications >= self.max_applications {
            return false;
        }
        if self.interval == 0 {
            return false;
        }
        self.iterations.is_multiple_of(self.interval)
    }

    /// Record that widening was applied.
    pub fn record_application(&mut self) {
        self.applications = self.applications.saturating_add(1);
    }

    /// Number of widening applications so far.
    #[must_use]
    pub fn applications(&self) -> usize {
        self.applications
    }

    /// Total iterations observed.
    #[must_use]
    pub fn iterations(&self) -> usize {
        self.iterations
    }

    /// Reset the schedule.
    pub fn reset(&mut self) {
        self.applications = 0;
        self.iterations = 0;
    }
}

impl Default for WideningSchedule {
    fn default() -> Self {
        // Default: widen every 5 iterations, after at least 3 iterations, up to 10 times.
        Self::new(5, 3, 10)
    }
}

/// Apply widening to jump past stagnation in the state history.
///
/// Examines the history of abstract states. If the last `stale_window` states
/// show no growth in proved VCs, applies the widening operator to accelerate
/// convergence.
#[must_use]
pub fn accelerate_convergence(
    state_history: &[AbstractState],
    stale_window: usize,
    operator: &dyn WideningOperator,
) -> AbstractState {
    if state_history.is_empty() {
        return AbstractState::new();
    }

    let last = &state_history[state_history.len() - 1];

    if state_history.len() < stale_window + 1 {
        return last.clone();
    }

    // Check if the last `stale_window` states show no growth.
    let baseline = &state_history[state_history.len() - stale_window - 1];
    let is_stale = state_history[state_history.len() - stale_window..]
        .iter()
        .all(|s| s.proved_count() <= baseline.proved_count());

    if is_stale { operator.widen(baseline, last) } else { last.clone() }
}

/// Recover precision after widening by applying the narrowing operator.
///
/// Takes a widened (over-approximate) state and a precise (actual verification)
/// state and produces a tighter approximation.
#[must_use]
pub fn narrow_after_widening(
    wide_state: &AbstractState,
    precise_state: &AbstractState,
    operator: &dyn NarrowingOperator,
) -> AbstractState {
    operator.narrow(wide_state, precise_state)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn state_with(proved: &[&str], proposals: &[&str], round: u32) -> AbstractState {
        AbstractState {
            proved_vcs: proved.iter().map(|s| (*s).to_string()).collect(),
            active_proposals: proposals.iter().map(|s| (*s).to_string()).collect(),
            round,
        }
    }

    // --- AbstractState ---

    #[test]
    fn test_abstract_state_new() {
        let state = AbstractState::new();
        assert_eq!(state.proved_count(), 0);
        assert_eq!(state.proposal_count(), 0);
        assert_eq!(state.round, 0);
        assert!(state.is_bottom());
        assert!(!state.is_top());
    }

    #[test]
    fn test_abstract_state_with_components() {
        let state = state_with(&["a", "b"], &["c"], 3);
        assert_eq!(state.proved_count(), 2);
        assert_eq!(state.proposal_count(), 1);
        assert_eq!(state.round, 3);
        assert!(!state.is_bottom());
        assert!(!state.is_top());
    }

    #[test]
    fn test_abstract_state_is_top() {
        let state = state_with(&["a", "b"], &[], 5);
        assert!(state.is_top());
    }

    #[test]
    fn test_abstract_state_join() {
        let s1 = state_with(&["a", "b"], &["x"], 1);
        let s2 = state_with(&["b", "c"], &["y"], 2);
        let joined = s1.join(&s2);
        assert_eq!(joined.proved_count(), 3); // a, b, c
        assert_eq!(joined.proposal_count(), 2); // x, y
        assert_eq!(joined.round, 2);
    }

    #[test]
    fn test_abstract_state_meet() {
        let s1 = state_with(&["a", "b", "c"], &["x", "y"], 3);
        let s2 = state_with(&["b", "c", "d"], &["y", "z"], 1);
        let met = s1.meet(&s2);
        assert_eq!(met.proved_count(), 2); // b, c
        assert_eq!(met.proposal_count(), 1); // y
        assert_eq!(met.round, 1);
    }

    #[test]
    fn test_abstract_state_is_subset_of() {
        let s1 = state_with(&["a"], &["x"], 1);
        let s2 = state_with(&["a", "b"], &["x", "y"], 2);
        assert!(s1.is_subset_of(&s2));
        assert!(!s2.is_subset_of(&s1));
    }

    #[test]
    fn test_abstract_state_default() {
        let state = AbstractState::default();
        assert!(state.is_bottom());
    }

    // --- ThresholdWidening ---

    #[test]
    fn test_threshold_widening_no_stagnation() {
        let mut tw = ThresholdWidening::new(3);
        let s1 = state_with(&["a"], &["b", "c"], 1);
        let s2 = state_with(&["a", "b"], &["c"], 2);

        tw.observe(&s1);
        tw.observe(&s2);
        assert!(!tw.should_widen());

        let widened = tw.widen(&s1, &s2);
        // No widening applied: should return new_state as-is.
        assert_eq!(widened, s2);
    }

    #[test]
    fn test_threshold_widening_stagnation_triggers() {
        let mut tw = ThresholdWidening::new(2);
        let s = state_with(&["a"], &["b", "c"], 1);

        tw.observe(&s);
        tw.observe(&s); // stale 1
        tw.observe(&s); // stale 2
        assert!(tw.should_widen());

        let old = state_with(&["a"], &["b", "c"], 0);
        let widened = tw.widen(&old, &s);
        // Widening: proposals b, c should be moved to proved.
        assert!(widened.proved_vcs.contains("a"));
        assert!(widened.proved_vcs.contains("b"));
        assert!(widened.proved_vcs.contains("c"));
        assert!(widened.active_proposals.is_empty());
    }

    #[test]
    fn test_threshold_widening_progress_resets() {
        let mut tw = ThresholdWidening::new(2);
        let s1 = state_with(&["a"], &["b"], 1);
        tw.observe(&s1);
        tw.observe(&s1); // stale 1
        assert_eq!(tw.stale_count(), 1);

        let s2 = state_with(&["a", "b"], &[], 2);
        tw.observe(&s2); // progress!
        assert_eq!(tw.stale_count(), 0);
        assert!(!tw.should_widen());
    }

    #[test]
    fn test_threshold_widening_reset() {
        let mut tw = ThresholdWidening::new(1);
        let s = state_with(&["a"], &["b"], 1);
        tw.observe(&s);
        tw.observe(&s);
        assert!(tw.should_widen());
        tw.reset();
        assert!(!tw.should_widen());
    }

    #[test]
    #[should_panic(expected = "widening threshold must be non-zero")]
    fn test_threshold_widening_zero_panics() {
        let _ = ThresholdWidening::new(0);
    }

    // --- DelayedWidening ---

    #[test]
    fn test_delayed_widening_before_delay() {
        let mut dw = DelayedWidening::new(5, 2);
        let s = state_with(&["a"], &["b", "c"], 1);
        // 3 observations (before delay of 5).
        dw.observe(&s);
        dw.observe(&s);
        dw.observe(&s);
        assert!(!dw.should_widen());
        assert_eq!(dw.total_iterations(), 3);
    }

    #[test]
    fn test_delayed_widening_after_delay_stagnating() {
        let mut dw = DelayedWidening::new(3, 2);
        let s = state_with(&["a"], &["b", "c"], 1);

        // 3 observations to pass delay.
        dw.observe(&s);
        dw.observe(&s);
        dw.observe(&s);
        // Now stale_count=2 (first observation establishes baseline, next two are stale).
        // But actually first observe sets last_proved_count=1, second is stale=1, third is stale=2.
        assert!(dw.should_widen());

        let widened = dw.widen(&s, &s);
        assert!(widened.proved_vcs.contains("b"));
        assert!(widened.proved_vcs.contains("c"));
    }

    #[test]
    fn test_delayed_widening_progress_after_delay() {
        let mut dw = DelayedWidening::new(3, 2);
        let s1 = state_with(&["a"], &["b", "c"], 1);
        let s2 = state_with(&["a", "b"], &["c"], 2);
        let s3 = state_with(&["a", "b", "c"], &[], 3);

        dw.observe(&s1);
        dw.observe(&s2);
        dw.observe(&s3);
        // Making progress: stale_count stays 0.
        assert!(!dw.should_widen());
    }

    #[test]
    fn test_delayed_widening_reset() {
        let mut dw = DelayedWidening::new(2, 1);
        let s = state_with(&["a"], &["b"], 1);
        dw.observe(&s);
        dw.observe(&s);
        assert!(dw.should_widen());
        dw.reset();
        assert!(!dw.should_widen());
        assert_eq!(dw.total_iterations(), 0);
    }

    #[test]
    #[should_panic(expected = "delay must be non-zero")]
    fn test_delayed_widening_zero_delay_panics() {
        let _ = DelayedWidening::new(0, 1);
    }

    #[test]
    #[should_panic(expected = "threshold must be non-zero")]
    fn test_delayed_widening_zero_threshold_panics() {
        let _ = DelayedWidening::new(1, 0);
    }

    // --- SimpleNarrowing ---

    #[test]
    fn test_simple_narrowing() {
        let narrowing = SimpleNarrowing;
        // Wide state over-approximated: proved a, b, c.
        let wide = state_with(&["a", "b", "c"], &[], 3);
        // Precise state: only a and b actually proved, c still a proposal.
        let precise = state_with(&["a", "b"], &["c"], 3);

        let narrowed = narrowing.narrow(&wide, &precise);
        // Should keep a, b (intersection) + anything new in precise.
        assert!(narrowed.proved_vcs.contains("a"));
        assert!(narrowed.proved_vcs.contains("b"));
        // c is not in both proved sets' intersection, but IS in precise.proved
        // difference from wide.proved — wait, c is in wide but not precise's proved,
        // and c is in precise.proved difference wide.proved? No.
        // The narrowing keeps intersection(wide.proved, precise.proved) union
        // precise.proved.difference(wide.proved).
        // intersection = {a, b}, difference = {} => result = {a, b}.
        assert!(!narrowed.proved_vcs.contains("c"));
        assert!(narrowed.active_proposals.contains("c"));
    }

    #[test]
    fn test_simple_narrowing_new_proof() {
        let narrowing = SimpleNarrowing;
        let wide = state_with(&["a", "b"], &["c"], 2);
        // Precise state found a new proof for "d" not in wide.
        let precise = state_with(&["a", "d"], &["c"], 3);

        let narrowed = narrowing.narrow(&wide, &precise);
        // a is in intersection, d is in precise.difference(wide).
        assert!(narrowed.proved_vcs.contains("a"));
        assert!(narrowed.proved_vcs.contains("d"));
        // b is in wide but not precise => dropped.
        assert!(!narrowed.proved_vcs.contains("b"));
    }

    // --- WideningSchedule ---

    #[test]
    fn test_schedule_every() {
        let mut sched = WideningSchedule::every(3);
        assert!(!sched.tick()); // iter 1
        assert!(!sched.tick()); // iter 2
        assert!(sched.tick()); // iter 3
        assert!(!sched.tick()); // iter 4
        assert!(!sched.tick()); // iter 5
        assert!(sched.tick()); // iter 6
    }

    #[test]
    fn test_schedule_min_iterations() {
        let mut sched = WideningSchedule::new(2, 4, 0);
        assert!(!sched.tick()); // iter 1: below min
        assert!(!sched.tick()); // iter 2: below min (and would fire)
        assert!(!sched.tick()); // iter 3: below min
        assert!(sched.tick()); // iter 4: at min and interval
    }

    #[test]
    fn test_schedule_max_applications() {
        let mut sched = WideningSchedule::new(1, 0, 2);
        assert!(sched.tick()); // iter 1
        sched.record_application();
        assert!(sched.tick()); // iter 2
        sched.record_application();
        assert!(!sched.tick()); // iter 3: max reached
    }

    #[test]
    fn test_schedule_default() {
        let sched = WideningSchedule::default();
        assert_eq!(sched.interval, 5);
        assert_eq!(sched.min_iterations, 3);
        assert_eq!(sched.max_applications, 10);
    }

    #[test]
    fn test_schedule_zero_interval() {
        let mut sched = WideningSchedule::new(0, 0, 0);
        assert!(!sched.tick());
        assert!(!sched.tick());
        // interval=0 means never widen by schedule.
    }

    #[test]
    fn test_schedule_reset() {
        let mut sched = WideningSchedule::every(2);
        sched.tick();
        sched.tick();
        sched.record_application();
        assert_eq!(sched.applications(), 1);
        assert_eq!(sched.iterations(), 2);
        sched.reset();
        assert_eq!(sched.applications(), 0);
        assert_eq!(sched.iterations(), 0);
    }

    // --- accelerate_convergence ---

    #[test]
    fn test_accelerate_empty_history() {
        let tw = ThresholdWidening::new(2);
        let result = accelerate_convergence(&[], 2, &tw);
        assert!(result.is_bottom());
    }

    #[test]
    fn test_accelerate_not_enough_history() {
        let tw = ThresholdWidening::new(2);
        let history = vec![state_with(&["a"], &["b"], 1)];
        let result = accelerate_convergence(&history, 3, &tw);
        assert_eq!(result, history[0]);
    }

    #[test]
    fn test_accelerate_stale_triggers_widening() {
        let mut tw = ThresholdWidening::new(1);
        let s = state_with(&["a"], &["b", "c"], 1);
        // Manually trigger widening.
        tw.observe(&s);
        tw.observe(&s);

        let history = vec![state_with(&["a"], &["b", "c"], 0), s.clone(), s.clone(), s.clone()];
        let result = accelerate_convergence(&history, 2, &tw);
        // Widening should have promoted proposals to proved.
        assert!(result.proved_vcs.contains("b"));
        assert!(result.proved_vcs.contains("c"));
    }

    #[test]
    fn test_accelerate_progress_no_widening() {
        let tw = ThresholdWidening::new(2);
        let history = vec![
            state_with(&["a"], &["b", "c"], 0),
            state_with(&["a", "b"], &["c"], 1),
            state_with(&["a", "b", "c"], &[], 2),
        ];
        let result = accelerate_convergence(&history, 2, &tw);
        // No stagnation: should return the last state unchanged.
        assert_eq!(result, history[2]);
    }

    // --- narrow_after_widening ---

    #[test]
    fn test_narrow_after_widening() {
        let narrowing = SimpleNarrowing;
        let wide = state_with(&["a", "b", "c"], &[], 3);
        let precise = state_with(&["a", "b"], &["c"], 3);

        let result = narrow_after_widening(&wide, &precise, &narrowing);
        assert_eq!(result.proved_count(), 2); // a, b
        assert!(result.active_proposals.contains("c"));
    }

    // --- Integration: widening then narrowing ---

    #[test]
    fn test_widen_then_narrow_workflow() {
        // Simulate: stagnation -> widen -> verify -> narrow.
        let mut tw = ThresholdWidening::new(1);
        let stale = state_with(&["a"], &["b", "c"], 5);

        tw.observe(&stale);
        tw.observe(&stale);
        assert!(tw.should_widen());

        // Widen: over-approximate.
        let old = state_with(&["a"], &["b", "c"], 4);
        let widened = tw.widen(&old, &stale);
        assert_eq!(widened.proved_count(), 3); // a, b, c
        assert_eq!(widened.proposal_count(), 0);

        // Now "verify" the widened state. Suppose b is actually proved but c isn't.
        let actual = state_with(&["a", "b"], &["c"], 6);

        // Narrow to recover precision.
        let narrowing = SimpleNarrowing;
        let narrowed = narrow_after_widening(&widened, &actual, &narrowing);
        assert!(narrowed.proved_vcs.contains("a"));
        assert!(narrowed.proved_vcs.contains("b"));
        assert!(!narrowed.proved_vcs.contains("c"));
        assert!(narrowed.active_proposals.contains("c"));
    }
}
