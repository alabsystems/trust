// trust-temporal/bmc.rs: Bounded model checking for state machines
//
// Implements bounded model checking (BMC) by unrolling transition relations
// up to a finite depth K and checking whether a safety property can be violated
// within K steps. Supports iterative deepening and completeness estimation.
//
// References:
//   Biere, Cimatti, Clarke, Zhu. "Bounded Model Checking" (Advances in
//     Computers, 2003).
//   Bradley, Manna. "The Calculus of Computation" (Springer, 2007). Ch. 10.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;
use trust_types::fx::FxHashSet;

use crate::{StateId, StateMachine, Trace};
use trust_types::fx::FxHashMap;

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// A safety property to check: a predicate over state labels.
///
/// The property holds at a state if the state's labels satisfy the predicate.
/// For BMC, we check whether any reachable state within K steps violates the
/// property (i.e., reaches a state where the property is false).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafetyProperty {
    /// Human-readable name of the property.
    pub name: String,
    /// The label that must hold in every reachable state.
    /// A state satisfies the property if it carries this label.
    pub required_label: String,
}

impl SafetyProperty {
    /// Create a new safety property.
    #[must_use]
    pub fn new(name: impl Into<String>, required_label: impl Into<String>) -> Self {
        Self { name: name.into(), required_label: required_label.into() }
    }

    /// Check whether a state satisfies this property.
    #[must_use]
    pub(crate) fn holds_at(&self, state: &crate::State) -> bool {
        state.labels.iter().any(|l| l == &self.required_label)
    }
}

impl fmt::Display for SafetyProperty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AG({})", self.required_label)
    }
}

/// Result of a bounded model check.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum BmcResult {
    /// The property holds up to bound K (no violation found within K steps).
    Safe {
        /// The bound up to which the property was verified.
        bound: usize,
    },
    /// The property is violated: a counterexample trace was found.
    Unsafe {
        /// The counterexample trace from the initial state to the violating state.
        trace: Trace,
        /// The depth at which the violation was found.
        depth: usize,
    },
}

impl BmcResult {
    /// Whether the check found the property to be safe (within bounds).
    #[must_use]
    pub fn is_safe(&self) -> bool {
        matches!(self, BmcResult::Safe { .. })
    }

    /// Whether the check found a violation.
    #[must_use]
    pub fn is_unsafe(&self) -> bool {
        matches!(self, BmcResult::Unsafe { .. })
    }

    /// Extract the counterexample trace, if any.
    #[must_use]
    pub fn counterexample(&self) -> Option<&Trace> {
        match self {
            BmcResult::Unsafe { trace, .. } => Some(trace),
            BmcResult::Safe { .. } => None,
        }
    }
}

impl fmt::Display for BmcResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BmcResult::Safe { bound } => write!(f, "SAFE (verified up to bound {bound})"),
            BmcResult::Unsafe { depth, trace } => {
                write!(f, "UNSAFE at depth {depth} (trace length: {})", trace.len())
            }
        }
    }
}

/// Result of a completeness check (test-only; not part of public API).
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
struct CompletenessResult {
    /// Whether the bound K is sufficient to prove the property for all depths.
    pub is_complete: bool,
    /// The bound that was checked.
    pub bound: usize,
    /// Number of reachable states at this bound.
    pub reachable_count: usize,
    /// Total number of states in the model.
    pub total_states: usize,
}

#[cfg(test)]
impl CompletenessResult {
    /// Whether the bounded check proves the property for all depths.
    #[must_use]
    fn proves_unbounded(&self) -> bool {
        self.is_complete
    }
}

/// An unrolled transition formula representing K steps of the transition relation.
///
/// Each step maps (state_at_step_i) -> (set of possible states_at_step_{i+1}).
/// This is the semantic representation; in a real SMT-based BMC you would emit
/// logical formulas. Here we represent it structurally for model checking.
#[derive(Debug, Clone)]
pub(crate) struct UnrolledTransition {
    /// States reachable at each step. `steps[i]` is the set of states
    /// reachable in exactly `i` transitions from the initial state.
    pub steps: Vec<FxHashSet<StateId>>,
    /// For each (step, state), the predecessor at step-1 that led here.
    /// Used for counterexample reconstruction.
    pub(crate) parent: Vec<FxHashMap<StateId, StateId>>,
}

#[cfg(test)]
impl UnrolledTransition {
    /// States reachable at exactly step `k`.
    #[must_use]
    fn states_at_step(&self, k: usize) -> Option<&FxHashSet<StateId>> {
        self.steps.get(k)
    }

    /// Total number of distinct states reached across all steps.
    #[must_use]
    fn total_reachable(&self) -> usize {
        let mut all: FxHashSet<StateId> = FxHashSet::default();
        for step in &self.steps {
            all.extend(step);
        }
        all.len()
    }
}

// ---------------------------------------------------------------------------
// BMC Engine
// ---------------------------------------------------------------------------

/// Bounded model checking engine.
///
/// Explores the state space up to a configurable depth, checking whether a
/// safety property can be violated within that many transitions.
pub struct BmcEngine<'a> {
    machine: &'a StateMachine,
}

impl<'a> BmcEngine<'a> {
    /// Create a BMC engine for the given state machine.
    #[must_use]
    pub fn new(machine: &'a StateMachine) -> Self {
        Self { machine }
    }

    /// Unroll the transition relation for `k` steps from the initial state.
    ///
    /// Returns the set of states reachable at each step, along with the
    /// parent map for counterexample reconstruction.
    #[must_use]
    fn unroll_transition(&self, k: usize) -> UnrolledTransition {
        let mut steps: Vec<FxHashSet<StateId>> = Vec::with_capacity(k + 1);
        let mut parent: Vec<FxHashMap<StateId, StateId>> = Vec::with_capacity(k + 1);

        // Step 0: initial state
        let mut current = FxHashSet::default();
        current.insert(self.machine.initial);
        steps.push(current);
        parent.push(FxHashMap::default());

        // Steps 1..k: successors
        for _step in 1..=k {
            let prev = &steps[steps.len() - 1];
            let mut next = FxHashSet::default();
            let mut next_parent = FxHashMap::default();

            for &state in prev {
                for succ in self.machine.successors(state) {
                    if next.insert(succ) {
                        next_parent.insert(succ, state);
                    }
                }
            }

            steps.push(next);
            parent.push(next_parent);
        }

        UnrolledTransition { steps, parent }
    }

    /// Check whether a safety property holds within K transitions.
    ///
    /// Returns `Safe(k)` if no violation is found within K steps, or
    /// `Unsafe(trace)` with the counterexample path if a violation exists.
    #[must_use]
    pub fn check_bounded(&self, property: &SafetyProperty, k: usize) -> BmcResult {
        let unrolled = self.unroll_transition(k);

        // Check each step for a violating state
        for (step_idx, step_states) in unrolled.steps.iter().enumerate() {
            for &state_id in step_states {
                let satisfies = self.machine.state(state_id).is_some_and(|s| property.holds_at(s));

                if !satisfies {
                    let trace = self.reconstruct_trace(&unrolled, step_idx, state_id);
                    return BmcResult::Unsafe { trace, depth: step_idx };
                }
            }
        }

        BmcResult::Safe { bound: k }
    }

    /// Reconstruct a counterexample trace from the unrolled transition.
    fn reconstruct_trace(
        &self,
        unrolled: &UnrolledTransition,
        step: usize,
        target: StateId,
    ) -> Trace {
        let mut path = vec![target];
        let mut current = target;

        for s in (1..=step).rev() {
            if let Some(&prev) = unrolled.parent[s].get(&current) {
                path.push(prev);
                current = prev;
            } else {
                break;
            }
        }

        path.reverse();
        Trace::new(path)
    }
}

// ---------------------------------------------------------------------------
// Test-only helpers
// ---------------------------------------------------------------------------

#[cfg(test)]
impl BmcResult {
    /// The bound at which the result was determined.
    #[must_use]
    fn bound(&self) -> usize {
        match self {
            BmcResult::Safe { bound } => *bound,
            BmcResult::Unsafe { depth, .. } => *depth,
        }
    }
}

#[cfg(test)]
impl<'a> BmcEngine<'a> {
    /// Iterative deepening: increment the bound from 0 to `max_k`,
    /// stopping at the first violation or when `max_k` is reached.
    #[must_use]
    fn iterative_deepening(&self, property: &SafetyProperty, max_k: usize) -> BmcResult {
        for k in 0..=max_k {
            let result = self.check_bounded(property, k);
            if result.is_unsafe() {
                return result;
            }

            let completeness = self.completeness_check(k);
            if completeness.is_complete {
                return BmcResult::Safe { bound: k };
            }
        }

        BmcResult::Safe { bound: max_k }
    }

    /// Completeness check: determines whether bound K is sufficient to prove
    /// safety for ALL depths (not just up to K).
    #[must_use]
    fn completeness_check(&self, k: usize) -> CompletenessResult {
        let unrolled = self.unroll_transition(k);

        let mut seen_before_k: FxHashSet<StateId> = FxHashSet::default();
        for step in unrolled.steps.iter().take(k) {
            seen_before_k.extend(step);
        }

        let step_k = unrolled.steps.get(k).cloned().unwrap_or_default();
        let is_complete = step_k.is_subset(&seen_before_k);

        let reachable_count = unrolled.total_reachable();
        let total_states = self.machine.states.len();

        CompletenessResult { is_complete, bound: k, reachable_count, total_states }
    }

    /// Estimate the maximum useful bound (diameter) of the model.
    #[must_use]
    fn diameter_bound(&self) -> usize {
        let mut seen = FxHashSet::default();
        let mut frontier: FxHashSet<StateId> = FxHashSet::default();

        seen.insert(self.machine.initial);
        frontier.insert(self.machine.initial);

        let mut depth = 0;

        loop {
            let mut next_frontier = FxHashSet::default();
            for &state in &frontier {
                for succ in self.machine.successors(state) {
                    if seen.insert(succ) {
                        next_frontier.insert(succ);
                    }
                }
            }

            if next_frontier.is_empty() {
                break;
            }

            frontier = next_frontier;
            depth += 1;
        }

        depth
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{State, StateMachineBuilder, Transition};

    // ---- Helper models ----

    /// Safe model: all states have "safe" label.
    fn safe_model() -> StateMachine {
        StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "S0").with_label("safe"))
            .add_state(State::new(StateId(1), "S1").with_label("safe"))
            .add_state(State::new(StateId(2), "S2").with_label("safe"))
            .add_transition(Transition::new(StateId(0), StateId(1), "a"))
            .add_transition(Transition::new(StateId(1), StateId(2), "b"))
            .add_transition(Transition::new(StateId(2), StateId(0), "c"))
            .build()
    }

    /// Unsafe model: bug state reachable at depth 2.
    fn unsafe_model() -> StateMachine {
        StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "S0").with_label("safe"))
            .add_state(State::new(StateId(1), "S1").with_label("safe"))
            .add_state(State::new(StateId(2), "Bug").with_label("error"))
            .add_transition(Transition::new(StateId(0), StateId(1), "step"))
            .add_transition(Transition::new(StateId(1), StateId(2), "crash"))
            .build()
    }

    /// Linear chain: S0->S1->S2->S3->S4, all safe.
    fn chain_model() -> StateMachine {
        StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "S0").with_label("safe"))
            .add_state(State::new(StateId(1), "S1").with_label("safe"))
            .add_state(State::new(StateId(2), "S2").with_label("safe"))
            .add_state(State::new(StateId(3), "S3").with_label("safe"))
            .add_state(State::new(StateId(4), "S4").with_label("safe"))
            .add_transition(Transition::new(StateId(0), StateId(1), "a"))
            .add_transition(Transition::new(StateId(1), StateId(2), "b"))
            .add_transition(Transition::new(StateId(2), StateId(3), "c"))
            .add_transition(Transition::new(StateId(3), StateId(4), "d"))
            .build()
    }

    /// Branching model: S0 -> S1, S0 -> S2, both safe, S1->S3(unsafe)
    fn branching_unsafe_model() -> StateMachine {
        StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "S0").with_label("safe"))
            .add_state(State::new(StateId(1), "S1").with_label("safe"))
            .add_state(State::new(StateId(2), "S2").with_label("safe"))
            .add_state(State::new(StateId(3), "S3").with_label("error"))
            .add_transition(Transition::new(StateId(0), StateId(1), "left"))
            .add_transition(Transition::new(StateId(0), StateId(2), "right"))
            .add_transition(Transition::new(StateId(1), StateId(3), "fail"))
            .build()
    }

    fn safe_prop() -> SafetyProperty {
        SafetyProperty::new("all_safe", "safe")
    }

    // ---- Unrolling tests ----

    #[test]
    fn test_unroll_transition_step_zero() {
        let model = safe_model();
        let engine = BmcEngine::new(&model);
        let unrolled = engine.unroll_transition(0);

        assert_eq!(unrolled.steps.len() - 1, 0);
        assert_eq!(unrolled.steps.len(), 1);
        assert!(unrolled.steps[0].contains(&StateId(0)));
    }

    #[test]
    fn test_unroll_transition_step_one() {
        let model = safe_model();
        let engine = BmcEngine::new(&model);
        let unrolled = engine.unroll_transition(1);

        assert_eq!(unrolled.steps.len(), 2);
        assert!(unrolled.steps[0].contains(&StateId(0)));
        assert!(unrolled.steps[1].contains(&StateId(1)));
    }

    #[test]
    fn test_unroll_transition_full_cycle() {
        let model = safe_model();
        let engine = BmcEngine::new(&model);
        let unrolled = engine.unroll_transition(3);

        assert_eq!(unrolled.total_reachable(), 3); // All 3 states
        // Step 3 should revisit S0
        assert!(unrolled.steps[3].contains(&StateId(0)));
    }

    // ---- Bounded check tests ----

    #[test]
    fn test_check_bounded_safe_model() {
        let model = safe_model();
        let engine = BmcEngine::new(&model);
        let result = engine.check_bounded(&safe_prop(), 5);

        assert!(result.is_safe());
        assert_eq!(result.bound(), 5);
    }

    #[test]
    fn test_check_bounded_unsafe_at_depth_2() {
        let model = unsafe_model();
        let engine = BmcEngine::new(&model);

        // At bound 1, safe (bug is at depth 2)
        let result = engine.check_bounded(&safe_prop(), 1);
        assert!(result.is_safe());

        // At bound 2, unsafe
        let result = engine.check_bounded(&safe_prop(), 2);
        assert!(result.is_unsafe());
        assert_eq!(result.bound(), 2);
    }

    #[test]
    fn test_check_bounded_counterexample_trace() {
        let model = unsafe_model();
        let engine = BmcEngine::new(&model);
        let result = engine.check_bounded(&safe_prop(), 3);

        let trace = result.counterexample().expect("should have counterexample");
        assert!(trace.starts_at(StateId(0)));
        assert!(trace.visits(StateId(2))); // Bug state
        assert_eq!(trace.len(), 3); // S0 -> S1 -> Bug
    }

    #[test]
    fn test_check_bounded_branching_counterexample() {
        let model = branching_unsafe_model();
        let engine = BmcEngine::new(&model);
        let result = engine.check_bounded(&safe_prop(), 3);

        assert!(result.is_unsafe());
        let trace = result.counterexample().unwrap();
        assert!(trace.starts_at(StateId(0)));
        assert!(trace.visits(StateId(3))); // The error state
    }

    // ---- Iterative deepening tests ----

    #[test]
    fn test_iterative_deepening_finds_bug() {
        let model = unsafe_model();
        let engine = BmcEngine::new(&model);
        let result = engine.iterative_deepening(&safe_prop(), 10);

        assert!(result.is_unsafe());
        // Should find bug at depth 2, not 10
        assert_eq!(result.bound(), 2);
    }

    #[test]
    fn test_iterative_deepening_safe_with_early_termination() {
        let model = safe_model();
        let engine = BmcEngine::new(&model);
        let result = engine.iterative_deepening(&safe_prop(), 100);

        assert!(result.is_safe());
        // Should terminate early via completeness check, not at 100
        assert!(result.bound() < 100);
    }

    #[test]
    fn test_iterative_deepening_chain_safe() {
        let model = chain_model();
        let engine = BmcEngine::new(&model);
        let result = engine.iterative_deepening(&safe_prop(), 20);

        assert!(result.is_safe());
    }

    // ---- Completeness check tests ----

    #[test]
    fn test_completeness_cyclic_model() {
        let model = safe_model();
        let engine = BmcEngine::new(&model);

        // At depth 0, not complete (haven't seen all states)
        let c0 = engine.completeness_check(0);
        assert!(!c0.is_complete);

        // At depth 3, step 3 revisits S0 which was already at step 0
        let c3 = engine.completeness_check(3);
        assert!(c3.is_complete);
        assert!(c3.proves_unbounded());
    }

    #[test]
    fn test_completeness_chain_model() {
        let model = chain_model();
        let engine = BmcEngine::new(&model);

        // At depth 3, not complete (S4 not yet reached)
        let c3 = engine.completeness_check(3);
        assert!(!c3.is_complete);

        // At depth 5, step 5 has no new states (S4 is a dead end)
        let c5 = engine.completeness_check(5);
        assert!(c5.is_complete);
    }

    // ---- Diameter tests ----

    #[test]
    fn test_diameter_cyclic_model() {
        let model = safe_model();
        let engine = BmcEngine::new(&model);
        let d = engine.diameter_bound();
        // S0->S1->S2 takes 2 transitions, then cycle. Diameter = 2.
        assert_eq!(d, 2);
    }

    #[test]
    fn test_diameter_chain_model() {
        let model = chain_model();
        let engine = BmcEngine::new(&model);
        let d = engine.diameter_bound();
        // S0->S1->S2->S3->S4: longest shortest path is 4
        assert_eq!(d, 4);
    }

    #[test]
    fn test_diameter_single_state() {
        let model =
            StateMachineBuilder::new(StateId(0)).add_state(State::new(StateId(0), "lone")).build();
        let engine = BmcEngine::new(&model);
        assert_eq!(engine.diameter_bound(), 0);
    }

    // ---- Display tests ----

    #[test]
    fn test_bmc_result_display_safe() {
        let result = BmcResult::Safe { bound: 10 };
        let s = result.to_string();
        assert!(s.contains("SAFE"));
        assert!(s.contains("10"));
    }

    #[test]
    fn test_bmc_result_display_unsafe() {
        let result =
            BmcResult::Unsafe { trace: Trace::new(vec![StateId(0), StateId(1)]), depth: 1 };
        let s = result.to_string();
        assert!(s.contains("UNSAFE"));
        assert!(s.contains("depth 1"));
    }

    #[test]
    fn test_safety_property_display() {
        let prop = SafetyProperty::new("invariant", "safe");
        assert_eq!(prop.to_string(), "AG(safe)");
    }

    // ---- Edge cases ----

    #[test]
    fn test_check_bounded_zero_depth_initial_unsafe() {
        // Initial state violates property
        let model = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Bad").with_label("error"))
            .build();
        let engine = BmcEngine::new(&model);
        let result = engine.check_bounded(&safe_prop(), 0);

        assert!(result.is_unsafe());
        assert_eq!(result.bound(), 0);
        let trace = result.counterexample().unwrap();
        assert_eq!(trace.len(), 1);
        assert_eq!(trace.states[0], StateId(0));
    }

    #[test]
    fn test_check_bounded_empty_frontier() {
        // Dead end: S0 -> S1 (no further transitions)
        let model = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "S0").with_label("safe"))
            .add_state(State::new(StateId(1), "S1").with_label("safe"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .build();
        let engine = BmcEngine::new(&model);
        // At depth 5, steps 2..5 have empty frontiers
        let result = engine.check_bounded(&safe_prop(), 5);
        assert!(result.is_safe());
    }

    #[test]
    fn test_unrolled_states_at_step() {
        let model = safe_model();
        let engine = BmcEngine::new(&model);
        let unrolled = engine.unroll_transition(2);

        assert!(unrolled.states_at_step(0).unwrap().contains(&StateId(0)));
        assert!(unrolled.states_at_step(1).unwrap().contains(&StateId(1)));
        assert!(unrolled.states_at_step(2).unwrap().contains(&StateId(2)));
        assert!(unrolled.states_at_step(3).is_none());
    }
}
