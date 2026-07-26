//! trust-temporal: State-machine and temporal-property scaffolding for Trust.
//!
//! This crate is intentionally small and self-contained. It models:
//! - labeled states and transitions,
//! - path fragments over state machines,
//! - basic temporal properties that a future checker can evaluate.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// Trust: Allow std HashMap/HashSet — FxHash lint only applies to compiler internals
#![allow(rustc::default_hash_types, rustc::potential_query_instability)]
// dead_code audit: crate-level suppression removed

pub mod bmc;
pub mod ctl;
pub mod fairness;
pub mod liveness;
pub mod ltl;
pub mod ty_bridge;
pub mod tla_spec_gen;

pub use bmc::{BmcEngine, BmcResult, SafetyProperty};
pub use ctl::{CtlFormula, CtlModelChecker, CtlResult};
pub use liveness::{LivenessProperty, LivenessResult};
pub use ltl::LtlFormula;

use std::collections::VecDeque;
use trust_types::fx::FxHashSet;

/// Identifier for a state in a state machine.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StateId(pub usize);

/// A labeled state in a state machine.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    pub id: StateId,
    pub name: String,
    pub labels: Vec<String>,
}

impl State {
    #[must_use]
    pub fn new(id: StateId, name: impl Into<String>) -> Self {
        Self { id, name: name.into(), labels: Vec::new() }
    }

    #[must_use]
    pub fn with_label(mut self, label: impl Into<String>) -> Self {
        self.labels.push(label.into());
        self
    }
}

/// A directed transition between states.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Transition {
    pub from: StateId,
    pub to: StateId,
    pub event: String,
    pub guard: Option<String>,
}

impl Transition {
    #[must_use]
    pub fn new(from: StateId, to: StateId, event: impl Into<String>) -> Self {
        Self { from, to, event: event.into(), guard: None }
    }

    #[must_use]
    pub fn with_guard(mut self, guard: impl Into<String>) -> Self {
        self.guard = Some(guard.into());
        self
    }
}

/// A complete state machine model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StateMachine {
    pub initial: StateId,
    pub states: Vec<State>,
    pub transitions: Vec<Transition>,
}

impl StateMachine {
    #[must_use]
    pub fn new(initial: StateId) -> Self {
        Self { initial, states: Vec::new(), transitions: Vec::new() }
    }

    pub fn add_state(&mut self, state: State) {
        self.states.push(state);
    }

    pub fn add_transition(&mut self, transition: Transition) {
        self.transitions.push(transition);
    }

    #[must_use]
    pub fn state(&self, id: StateId) -> Option<&State> {
        self.states.iter().find(|state| state.id == id)
    }

    #[must_use]
    pub fn contains_state(&self, id: StateId) -> bool {
        self.state(id).is_some()
    }

    #[must_use]
    pub fn outgoing(&self, id: StateId) -> Vec<&Transition> {
        self.transitions.iter().filter(|transition| transition.from == id).collect()
    }

    #[must_use]
    pub fn successors(&self, id: StateId) -> Vec<StateId> {
        self.outgoing(id).into_iter().map(|transition| transition.to).collect()
    }

    #[must_use]
    pub fn is_deadlock_state(&self, id: StateId) -> bool {
        !self.transitions.iter().any(|transition| transition.from == id)
    }

    /// Reachable states within `max_depth` transitions from the initial state.
    ///
    /// This is a bounded exploration helper, not a full model checker. It is
    /// intentionally conservative: first discovery wins and cycles are folded
    /// by visited-state tracking.
    #[must_use]
    pub fn reachable_states(&self, max_depth: usize) -> Vec<StateId> {
        if max_depth == 0 {
            return vec![self.initial];
        }

        let mut seen = FxHashSet::default();
        let mut queue = VecDeque::from([(self.initial, 0usize)]);
        let mut reachable = Vec::new();

        while let Some((state, depth)) = queue.pop_front() {
            if !seen.insert(state) {
                continue;
            }

            reachable.push(state);
            if depth == max_depth {
                continue;
            }

            for next in self.successors(state) {
                queue.push_back((next, depth + 1));
            }
        }

        reachable
    }

    /// Enumerate bounded traces from the initial state.
    ///
    /// Each trace is a prefix through the machine with at most `max_depth`
    /// transitions. Cycles are bounded by depth rather than expanded forever.
    #[must_use]
    pub fn bounded_traces(&self, max_depth: usize) -> Vec<Trace> {
        if self.states.is_empty() {
            return vec![];
        }

        let mut traces = Vec::new();
        let mut queue = VecDeque::from([Trace::new(vec![self.initial])]);

        while let Some(trace) = queue.pop_front() {
            let Some(last) = trace.last_state() else {
                continue;
            };

            let depth = trace.len().saturating_sub(1);
            traces.push(trace.clone());

            if depth == max_depth {
                continue;
            }

            let successors = self.successors(last);
            if successors.is_empty() {
                continue;
            }

            for next in successors {
                let mut next_trace = trace.clone();
                next_trace.states.push(next);
                queue.push_back(next_trace);
            }
        }

        traces
    }
}

/// Incremental builder for state machines.
///
/// The builder keeps state insertion and transition wiring local so temporal
/// extraction helpers can build a machine from smaller control-flow fragments.
#[derive(Debug, Clone)]
pub struct StateMachineBuilder {
    initial: StateId,
    states: Vec<State>,
    transitions: Vec<Transition>,
}

impl StateMachineBuilder {
    #[must_use]
    pub fn new(initial: StateId) -> Self {
        Self { initial, states: Vec::new(), transitions: Vec::new() }
    }

    #[must_use]
    pub fn add_state(mut self, state: State) -> Self {
        self.push_state(state);
        self
    }

    #[must_use]
    pub fn add_transition(mut self, transition: Transition) -> Self {
        self.transitions.push(transition);
        self
    }

    pub fn push_state(&mut self, state: State) {
        if let Some(existing) = self.states.iter_mut().find(|existing| existing.id == state.id) {
            *existing = state;
        } else {
            self.states.push(state);
        }
    }

    pub fn push_transition(&mut self, transition: Transition) {
        self.transitions.push(transition);
    }

    #[must_use]
    pub fn build(mut self) -> StateMachine {
        if !self.states.iter().any(|state| state.id == self.initial) {
            self.states.push(State::new(self.initial, format!("state_{}", self.initial.0)));
        }

        StateMachine { initial: self.initial, states: self.states, transitions: self.transitions }
    }
}

/// Temporal property kinds supported by the scaffold.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TemporalProperty {
    Always { condition: String },
    Eventually { condition: String },
    LeadsTo { antecedent: String, consequent: String },
    Until { left: String, right: String },
}

impl TemporalProperty {
    #[must_use]
    pub fn description(&self) -> String {
        match self {
            TemporalProperty::Always { condition } => format!("always {condition}"),
            TemporalProperty::Eventually { condition } => format!("eventually {condition}"),
            TemporalProperty::LeadsTo { antecedent, consequent } => {
                format!("{antecedent} leads_to {consequent}")
            }
            TemporalProperty::Until { left, right } => format!("{left} until {right}"),
        }
    }
}

/// A temporal verification target: a state machine plus property.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TemporalSpec {
    pub machine: StateMachine,
    pub property: TemporalProperty,
}

impl TemporalSpec {
    #[must_use]
    pub fn new(machine: StateMachine, property: TemporalProperty) -> Self {
        Self { machine, property }
    }
}

/// A bounded trace through the state machine.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Trace {
    pub states: Vec<StateId>,
}

impl Trace {
    #[must_use]
    pub fn new(states: Vec<StateId>) -> Self {
        Self { states }
    }

    #[must_use]
    pub fn starts_at(&self, initial: StateId) -> bool {
        self.states.first().copied() == Some(initial)
    }

    #[must_use]
    pub fn visits(&self, state: StateId) -> bool {
        self.states.contains(&state)
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.states.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.states.is_empty()
    }

    #[must_use]
    pub fn last_state(&self) -> Option<StateId> {
        self.states.last().copied()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_machine() -> StateMachine {
        StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Idle").with_label("start"))
            .add_state(State::new(StateId(1), "Busy").with_label("active"))
            .add_state(State::new(StateId(2), "Done").with_label("terminal"))
            .add_transition(Transition::new(StateId(0), StateId(1), "start"))
            .add_transition(Transition::new(StateId(1), StateId(2), "finish").with_guard("ok"))
            .build()
    }

    #[test]
    fn state_machine_tracks_states_and_transitions() {
        let machine = sample_machine();
        assert_eq!(machine.state(StateId(1)).unwrap().name, "Busy");
        assert_eq!(machine.outgoing(StateId(0)).len(), 1);
        assert!(!machine.is_deadlock_state(StateId(1)));
        assert!(machine.is_deadlock_state(StateId(2)));
    }

    #[test]
    fn temporal_properties_render_descriptions() {
        assert_eq!(
            TemporalProperty::Always { condition: "safe".into() }.description(),
            "always safe"
        );
        assert_eq!(
            TemporalProperty::LeadsTo {
                antecedent: "request".into(),
                consequent: "response".into()
            }
            .description(),
            "request leads_to response"
        );
    }

    #[test]
    fn traces_report_membership() {
        let trace = Trace::new(vec![StateId(0), StateId(1), StateId(2)]);
        assert!(trace.starts_at(StateId(0)));
        assert!(trace.visits(StateId(2)));
        assert!(!trace.visits(StateId(3)));
    }

    #[test]
    fn temporal_spec_composes_machine_and_property() {
        let spec = TemporalSpec::new(
            sample_machine(),
            TemporalProperty::Eventually { condition: "Done".into() },
        );
        assert_eq!(spec.machine.states.len(), 3);
        assert_eq!(spec.property.description(), "eventually Done");
    }

    #[test]
    fn builder_inserts_initial_state_when_missing() {
        let machine =
            StateMachineBuilder::new(StateId(7)).add_state(State::new(StateId(1), "Ready")).build();

        assert!(machine.contains_state(StateId(7)));
        assert_eq!(machine.state(StateId(7)).unwrap().name, "state_7");
        assert_eq!(machine.state(StateId(1)).unwrap().name, "Ready");
    }

    #[test]
    fn reachable_states_follow_bounded_transitions() {
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Start"))
            .add_state(State::new(StateId(1), "Middle"))
            .add_state(State::new(StateId(2), "End"))
            .add_transition(Transition::new(StateId(0), StateId(1), "step"))
            .add_transition(Transition::new(StateId(1), StateId(2), "finish"))
            .add_transition(Transition::new(StateId(2), StateId(1), "retry"))
            .build();

        assert_eq!(machine.reachable_states(0), vec![StateId(0)]);
        assert_eq!(machine.reachable_states(1), vec![StateId(0), StateId(1)]);
        assert_eq!(machine.reachable_states(2), vec![StateId(0), StateId(1), StateId(2)]);
    }

    #[test]
    fn bounded_traces_enumerate_prefixes_without_unbounded_growth() {
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Start"))
            .add_state(State::new(StateId(1), "Loop"))
            .add_transition(Transition::new(StateId(0), StateId(1), "enter"))
            .add_transition(Transition::new(StateId(1), StateId(1), "spin"))
            .build();

        let traces = machine.bounded_traces(2);

        assert!(traces.iter().any(|trace| trace.states == vec![StateId(0)]));
        assert!(traces.iter().any(|trace| trace.states == vec![StateId(0), StateId(1)]));
        assert!(
            traces.iter().any(|trace| trace.states == vec![StateId(0), StateId(1), StateId(1)])
        );
        assert!(traces.iter().all(|trace| trace.len() <= 3));
    }
}
