// trust-temporal/ty_bridge.rs: Bridge from native StateMachine to tla_mc_core
//
// Provides a TransitionSystem adapter so trust-temporal's
// StateMachine can be explored by tla_mc_core's BFS/SCC algorithms directly,
// without going through the router.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use tla_mc_core::{BfsError, BfsOutcome, NoopObserver, TransitionSystem, explore_bfs};

use crate::{StateId, StateMachine};

/// Adapter that implements `tla_mc_core::TransitionSystem` over
/// `trust_temporal::StateMachine`.
///
/// State is represented as `usize` (the `StateId` inner value). Actions are
/// transition event strings. Fingerprints are the state index itself (unique
/// by construction in trust_temporal).
#[derive(Clone)]
pub struct StateMachineAdapter {
    machine: StateMachine,
}

impl StateMachineAdapter {
    /// Create a new adapter wrapping the given state machine.
    #[must_use]
    pub fn new(machine: StateMachine) -> Self {
        Self { machine }
    }
}

impl TransitionSystem for StateMachineAdapter {
    type State = usize;
    type Action = String;
    type Fingerprint = usize;

    fn initial_states(&self) -> Vec<Self::State> {
        vec![self.machine.initial.0]
    }

    fn successors(&self, state: &Self::State) -> Vec<(Self::Action, Self::State)> {
        self.machine
            .outgoing(StateId(*state))
            .into_iter()
            .map(|t| (t.event.clone(), t.to.0))
            .collect()
    }

    fn fingerprint(&self, state: &Self::State) -> Self::Fingerprint {
        *state
    }
}

/// Run BFS exploration on a `StateMachine` via `tla_mc_core`.
///
/// Returns the BFS outcome with state count and completion status.
pub fn explore(machine: &StateMachine) -> Result<BfsOutcome, BfsError> {
    let adapter = StateMachineAdapter::new(machine.clone());
    let mut observer = NoopObserver::<StateMachineAdapter>::default();
    explore_bfs(&adapter, &mut observer)
}

/// Check deadlock freedom by BFS exploration.
///
/// Returns `true` if no reachable state is a deadlock (i.e., every reachable
/// state has at least one outgoing transition). Returns `false` if any
/// reachable state has no successors, or if exploration fails.
#[must_use]
pub fn check_deadlock_freedom(machine: &StateMachine) -> bool {
    match explore(machine) {
        Ok(outcome) => {
            let reachable = machine.reachable_states(outcome.states_discovered);
            !reachable.iter().any(|id| machine.is_deadlock_state(*id))
        }
        Err(_) => false,
    }
}

/// Find all deadlock states reachable from the initial state.
///
/// Returns a list of `StateId`s that are reachable and have no outgoing
/// transitions.
#[cfg(test)]
#[must_use]
fn find_deadlock_states(machine: &StateMachine) -> Vec<StateId> {
    match explore(machine) {
        Ok(outcome) => {
            let reachable = machine.reachable_states(outcome.states_discovered);
            reachable.into_iter().filter(|id| machine.is_deadlock_state(*id)).collect()
        }
        Err(_) => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{State, StateMachineBuilder, Transition};

    #[test]
    fn adapter_initial_states() {
        let machine =
            StateMachineBuilder::new(StateId(0)).add_state(State::new(StateId(0), "Start")).build();
        let adapter = StateMachineAdapter::new(machine);
        assert_eq!(adapter.initial_states(), vec![0]);
    }

    #[test]
    fn adapter_successors() {
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .build();
        let adapter = StateMachineAdapter::new(machine);
        assert_eq!(adapter.successors(&0), vec![("go".to_string(), 1)]);
        assert!(adapter.successors(&1).is_empty());
    }

    #[test]
    fn adapter_fingerprint() {
        let machine = StateMachineBuilder::new(StateId(0)).build();
        let adapter = StateMachineAdapter::new(machine);
        assert_eq!(adapter.fingerprint(&42), 42);
    }

    #[test]
    fn explore_linear_chain() {
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_state(State::new(StateId(2), "C"))
            .add_transition(Transition::new(StateId(0), StateId(1), "ab"))
            .add_transition(Transition::new(StateId(1), StateId(2), "bc"))
            .build();

        let outcome = explore(&machine).expect("BFS should succeed");
        assert!(outcome.completed);
        assert_eq!(outcome.states_discovered, 3);
    }

    #[test]
    fn explore_cycle() {
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "forward"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        let outcome = explore(&machine).expect("BFS should succeed");
        assert!(outcome.completed);
        assert_eq!(outcome.states_discovered, 2);
    }

    #[test]
    fn deadlock_freedom_cycle() {
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "forward"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        assert!(check_deadlock_freedom(&machine));
    }

    #[test]
    fn deadlock_freedom_fails_with_terminal() {
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .build();

        assert!(!check_deadlock_freedom(&machine));
    }

    #[test]
    fn find_deadlock_states_empty_on_cycle() {
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "forward"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        assert!(find_deadlock_states(&machine).is_empty());
    }

    #[test]
    fn find_deadlock_states_identifies_terminal() {
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .build();

        let deadlocks = find_deadlock_states(&machine);
        assert_eq!(deadlocks, vec![StateId(1)]);
    }
}
