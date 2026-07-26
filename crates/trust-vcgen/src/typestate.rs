// Type state verification for trust_vcgen.
//
// Verifies that objects transition through valid states according to a
// type state machine. Detects invalid transitions, unreachable states,
// deadlocks, and protocol violations.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;

use trust_types::fx::{FxHashMap, FxHashSet};

/// A single state in the type state machine.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeState {
    /// Name of the state.
    pub name: String,
    /// Properties that hold in this state.
    pub properties: Vec<String>,
}

/// A transition between two states, triggered by a method call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StateTransition {
    /// Source state name.
    pub from: String,
    /// Target state name.
    pub to: String,
    /// Method that triggers this transition.
    pub method: String,
    /// Optional guard condition (must hold for transition to fire).
    pub guard: Option<String>,
}

/// A complete type state machine definition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeStateMachine {
    /// All states in the machine.
    pub states: Vec<TypeState>,
    /// All transitions between states.
    pub transitions: Vec<StateTransition>,
    /// The initial state name.
    pub initial_state: String,
    /// States that represent error conditions.
    pub error_states: Vec<String>,
}

/// Errors that can occur during type state verification.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum TransitionError {
    /// An invalid transition was attempted.
    #[error("invalid transition from `{from}` to `{to}`")]
    InvalidTransition {
        /// Source state.
        from: String,
        /// Target state.
        to: String,
    },
    /// A state is unreachable from the initial state.
    #[error("unreachable state: `{0}`")]
    UnreachableState(String),
    /// A deadlock was detected (states with no outgoing transitions that
    /// are not designated as terminal/error states).
    #[error("deadlock detected in states: {0:?}")]
    DeadlockDetected(Vec<String>),
    /// The initial state has not been defined or does not exist.
    #[error("missing initial state")]
    MissingInitialState,
}

/// A property that must hold in a given state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StateProperty {
    /// The state this property applies to.
    pub state_name: String,
    /// The invariant expression (as a string).
    pub invariant: String,
}

/// Builder and verifier for type state machines.
#[derive(Debug, Clone, Default)]
pub struct TypeStateVerifier {
    states: Vec<TypeState>,
    transitions: Vec<StateTransition>,
    initial_state: Option<String>,
    error_states: Vec<String>,
}

impl TypeStateVerifier {
    /// Create a new, empty verifier.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a state to the machine.
    pub fn add_state(&mut self, state: TypeState) {
        self.states.push(state);
    }

    /// Add a transition to the machine.
    pub fn add_transition(&mut self, transition: StateTransition) {
        self.transitions.push(transition);
    }

    /// Set the initial state. The state must be added separately via
    /// `add_state`.
    pub fn set_initial(&mut self, state: &str) {
        self.initial_state = Some(state.to_string());
    }

    /// Mark a state as an error/terminal state.
    pub fn add_error_state(&mut self, state: &str) {
        self.error_states.push(state.to_string());
    }

    // -- internal helpers --------------------------------------------------

    /// Collect the set of state names.
    fn state_names(&self) -> FxHashSet<&str> {
        self.states.iter().map(|s| s.name.as_str()).collect()
    }

    /// Build an adjacency list (state name -> set of reachable state names).
    fn adjacency(&self) -> FxHashMap<&str, FxHashSet<&str>> {
        let mut adj: FxHashMap<&str, FxHashSet<&str>> = FxHashMap::default();
        for t in &self.transitions {
            adj.entry(t.from.as_str()).or_default().insert(t.to.as_str());
        }
        adj
    }

    /// BFS from `start`, returning the set of reachable state names.
    fn reachable_from<'a>(&'a self, start: &'a str) -> FxHashSet<&'a str> {
        let adj = self.adjacency();
        let mut visited: FxHashSet<&str> = FxHashSet::default();
        let mut queue: VecDeque<&str> = VecDeque::new();
        visited.insert(start);
        queue.push_back(start);
        while let Some(cur) = queue.pop_front() {
            if let Some(neighbours) = adj.get(cur) {
                for &next in neighbours {
                    if visited.insert(next) {
                        queue.push_back(next);
                    }
                }
            }
        }
        visited
    }

    // -- public verification API -------------------------------------------

    /// Verify that every transition references valid states and that the
    /// initial state exists.
    pub fn verify_transitions(&self) -> Result<(), TransitionError> {
        let initial = self.initial_state.as_deref().ok_or(TransitionError::MissingInitialState)?;
        let names = self.state_names();
        if !names.contains(initial) {
            return Err(TransitionError::MissingInitialState);
        }
        for t in &self.transitions {
            if !names.contains(t.from.as_str()) || !names.contains(t.to.as_str()) {
                return Err(TransitionError::InvalidTransition {
                    from: t.from.clone(),
                    to: t.to.clone(),
                });
            }
        }
        Ok(())
    }

    /// Build a `TypeStateMachine` after verification.
    pub fn build_state_machine(&self) -> Result<TypeStateMachine, TransitionError> {
        self.verify_transitions()?;
        Ok(TypeStateMachine {
            states: self.states.clone(),
            transitions: self.transitions.clone(),
            // SAFETY: verify_transitions() above ensures initial_state is Some.
            initial_state: self
                .initial_state
                .clone()
                .unwrap_or_else(|| unreachable!("initial_state None after verify_transitions")),
            error_states: self.error_states.clone(),
        })
    }

    /// Check that a sequence of state names forms a valid protocol trace
    /// starting from the initial state.
    pub fn check_protocol(&self, trace: &[&str]) -> Result<(), TransitionError> {
        let initial = self.initial_state.as_deref().ok_or(TransitionError::MissingInitialState)?;
        if trace.is_empty() {
            return Ok(());
        }
        if trace[0] != initial {
            return Err(TransitionError::InvalidTransition {
                from: initial.to_string(),
                to: trace[0].to_string(),
            });
        }
        let adj = self.adjacency();
        for window in trace.windows(2) {
            let from = window[0];
            let to = window[1];
            let valid = adj.get(from).is_some_and(|set| set.contains(to));
            if !valid {
                return Err(TransitionError::InvalidTransition {
                    from: from.to_string(),
                    to: to.to_string(),
                });
            }
        }
        Ok(())
    }

    /// Return the list of states that are unreachable from the initial state.
    #[must_use]
    pub fn unreachable_states(&self) -> Vec<String> {
        let Some(initial) = self.initial_state.as_deref() else {
            return self.states.iter().map(|s| s.name.clone()).collect();
        };
        let reachable = self.reachable_from(initial);
        self.states
            .iter()
            .filter(|s| !reachable.contains(s.name.as_str()))
            .map(|s| s.name.clone())
            .collect()
    }

    /// Check whether state `to` is reachable from state `from`.
    #[must_use]
    pub fn can_reach(&self, from: &str, to: &str) -> bool {
        self.reachable_from(from).contains(to)
    }

    /// Return states that have no outgoing transitions and are not marked
    /// as error/terminal states. These represent potential deadlocks.
    #[must_use]
    pub fn deadlock_states(&self) -> Vec<String> {
        let names = self.state_names();
        let adj = self.adjacency();
        let error_set: FxHashSet<&str> = self.error_states.iter().map(String::as_str).collect();
        names
            .into_iter()
            .filter(|name| {
                let has_outgoing = adj.get(name).is_some_and(|s| !s.is_empty());
                !has_outgoing && !error_set.contains(name)
            })
            .map(|s| s.to_string())
            .sorted_unstable()
    }

    /// Detect a NON-TRIVIAL cycle (length ≥ 2 — i.e. a cycle through two or more
    /// DISTINCT states, ignoring self-loops). Returns the cycle's states (in
    /// discovery order) if one exists, else `None`.
    ///
    /// A transition machine with NO non-trivial cycle is **convergent**: from any
    /// state, repeatedly applying the transition reaches a fixed point (a
    /// self-loop) or a sink in finitely many steps — it cannot livelock. This is
    /// the property `#[trust::terminating]` asserts on an enum-step function.
    /// Detection is exact on the finite extracted graph (an iterative DFS marking
    /// nodes white/gray/black; a gray→gray edge to a *distinct* node is a
    /// back-edge closing a non-trivial cycle).
    #[must_use]
    pub fn nontrivial_cycle(&self) -> Option<Vec<String>> {
        #[derive(Clone, Copy, PartialEq)]
        enum Mark {
            White,
            Gray,
            Black,
        }
        let adj = self.adjacency();
        // Deterministic node order: every state plus every transition endpoint.
        let mut nodes: Vec<&str> = self.states.iter().map(|s| s.name.as_str()).collect();
        for t in &self.transitions {
            nodes.push(t.from.as_str());
            nodes.push(t.to.as_str());
        }
        nodes.sort_unstable();
        nodes.dedup();

        let mut mark: FxHashMap<&str, Mark> = nodes.iter().map(|&n| (n, Mark::White)).collect();

        for &root in &nodes {
            if mark.get(root) != Some(&Mark::White) {
                continue;
            }
            // Iterative white/gray/black DFS. Each stack entry is either an
            // ENTER (false) or a RETURN (true) marker; the shared `path` holds the
            // current Gray stack so a Gray successor (back-edge) reconstructs the
            // cycle. A self-loop is skipped (it is a fixed point, not a livelock).
            let mut stack: Vec<(&str, bool)> = vec![(root, false)];
            let mut path: Vec<&str> = Vec::new();
            while let Some((node, returning)) = stack.pop() {
                if returning {
                    mark.insert(node, Mark::Black);
                    path.pop();
                    continue;
                }
                // A duplicate ENTER for an already-visited node: skip (its first
                // ENTER already colored it Gray then Black via the return marker).
                if mark.get(node) != Some(&Mark::White) {
                    continue;
                }
                mark.insert(node, Mark::Gray);
                path.push(node);
                stack.push((node, true)); // RETURN marker → colors Black, pops path.
                if let Some(succs) = adj.get(node) {
                    let mut ordered: Vec<&str> = succs.iter().copied().collect();
                    ordered.sort_unstable();
                    for succ in ordered {
                        if succ == node {
                            continue; // self-loop is trivial (a fixed point)
                        }
                        match mark.get(succ) {
                            Some(Mark::Gray) => {
                                // Back-edge to a distinct ancestor → non-trivial cycle.
                                let start = path.iter().position(|&n| n == succ).unwrap_or(0);
                                let mut cycle: Vec<String> =
                                    path[start..].iter().map(|s| s.to_string()).collect();
                                cycle.push(succ.to_string());
                                return Some(cycle);
                            }
                            Some(Mark::Black) => {}
                            _ => stack.push((succ, false)),
                        }
                    }
                }
            }
        }
        None
    }
}

/// Trust: extract an enum-state-machine `TypeStateVerifier` from a transition
/// function shaped like `fn step(s: E) -> E { match s { V0 => .., V1 => .., .. } }`.
///
/// The entry block must read the parameter's discriminant and `SwitchInt` on it;
/// each match arm must assign the return slot (`_0`) a field-less enum
/// `Aggregate` (the output variant). States are variant indices (`"v{n}"`);
/// transitions are `input_variant -> output_variant` (method `"step"`).
///
/// Returns `None` — declining to model, which is always sound (no verdict) — for
/// any function outside this exact shape, OR when the `SwitchInt` discriminant
/// values are not the contiguous `0..n` set (the default-discriminant signature
/// that guarantees `discriminant value == Aggregate variant index`, so the
/// switch's input space and the aggregate's output space coincide). This
/// conservative gate keeps a machine over an explicit-discriminant enum
/// (`enum E { A = 5, .. }`), whose two spaces could otherwise diverge, from being
/// mis-modeled.
#[must_use]
pub fn extract_enum_step_machine(
    func: &trust_types::VerifiableFunction,
) -> Option<TypeStateVerifier> {
    use trust_types::{AggregateKind, BlockId, Operand, Rvalue, Statement, Terminator};

    /// The single non-projected `local` an operand reads, if any.
    fn operand_local(op: &Operand) -> Option<usize> {
        match op {
            Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => Some(p.local),
            _ => None,
        }
    }

    /// Follow at most a few `Goto`s from `block_id`, returning the field-less enum
    /// `Aggregate` variant assigned to the return slot `_0`, if any.
    fn output_variant(body: &trust_types::VerifiableBody, mut block_id: BlockId) -> Option<usize> {
        for _ in 0..8 {
            let block = body.blocks.iter().find(|b| b.id == block_id)?;
            for stmt in &block.stmts {
                if let Statement::Assign {
                    place,
                    rvalue: Rvalue::Aggregate(AggregateKind::Adt { variant, .. }, _),
                    ..
                } = stmt
                    && place.local == 0
                    && place.projections.is_empty()
                {
                    return Some(*variant);
                }
            }
            match &block.terminator {
                Terminator::Goto(next) => block_id = *next,
                _ => return None,
            }
        }
        None
    }

    use trust_types::Projection;

    /// True iff `place` is the `field_idx`-th field of `param_local` downcast to
    /// `variant` (`(_param as variant).field_idx`), with or without an explicit
    /// `Downcast` projection in the lowered IR.
    fn place_is_input_field(
        place: &trust_types::Place,
        param_local: usize,
        variant: usize,
        field_idx: usize,
    ) -> bool {
        place.local == param_local
            && matches!(place.projections.as_slice(),
                [Projection::Downcast(v), Projection::Field(f)] if *v == variant && *f == field_idx)
            || (place.local == param_local
                && matches!(place.projections.as_slice(),
                    [Projection::Field(f)] if *f == field_idx))
    }

    /// True iff `op` is the input param's `field_idx`-th field (downcast to
    /// `variant`), possibly through ONE whole-local `Use` copy
    /// (`_b = (_param as variant).field_idx; … Aggregate(.., [move _b])`). The
    /// intermediate local's definition must be UNIQUE (else, conservatively, NOT
    /// an identity copy). Any computed value (`Not`, `BinaryOp`, …) returns false.
    fn operand_is_input_field(
        body: &trust_types::VerifiableBody,
        op: &Operand,
        param_local: usize,
        variant: usize,
        field_idx: usize,
    ) -> bool {
        let (Operand::Copy(place) | Operand::Move(place)) = op else { return false };
        if place_is_input_field(place, param_local, variant, field_idx) {
            return true;
        }
        if !place.projections.is_empty() {
            return false;
        }
        let mut def: Option<&Operand> = None;
        let mut def_count = 0usize;
        for stmt in body.blocks.iter().flat_map(|b| &b.stmts) {
            if let Statement::Assign { place: d, rvalue, .. } = stmt
                && d.local == place.local
                && d.projections.is_empty()
            {
                def_count += 1;
                if let Rvalue::Use(inner) = rvalue {
                    def = Some(inner);
                }
            }
        }
        if def_count != 1 {
            return false; // not a single-assignment temp — conservatively decline
        }
        match def {
            Some(Operand::Copy(p) | Operand::Move(p)) => {
                place_is_input_field(p, param_local, variant, field_idx)
            }
            _ => false,
        }
    }

    /// SOUNDNESS (hunt-12): a discriminant-keyed SELF-transition `v -> v` is a real
    /// fixed point ONLY when the arm returns the input value UNCHANGED — else the
    /// abstraction collapses distinct payload states (`A(true)`, `A(false)`) into one
    /// and a payload-oscillating self-loop `A(b) => A(!b)` is FALSELY proved to
    /// "converge to a fixed point" while it cycles forever. Identity iff: the whole
    /// input is returned (`_0 = move _param`), OR the SAME variant is reconstructed
    /// with every payload operand a verbatim copy of the input's same-index field
    /// (empty payload — a fieldless variant — is vacuously preserved). Any computed
    /// payload operand ⇒ NOT preserved (the caller then declines the whole machine).
    fn self_edge_preserves_value(
        body: &trust_types::VerifiableBody,
        mut block_id: BlockId,
        param_local: usize,
        variant: usize,
    ) -> bool {
        for _ in 0..8 {
            let Some(block) = body.blocks.iter().find(|b| b.id == block_id) else {
                return false;
            };
            for stmt in &block.stmts {
                if let Statement::Assign { place, rvalue, .. } = stmt
                    && place.local == 0
                    && place.projections.is_empty()
                {
                    return match rvalue {
                        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                            if p.local == param_local && p.projections.is_empty() =>
                        {
                            true
                        }
                        Rvalue::Aggregate(AggregateKind::Adt { variant: v, .. }, ops)
                            if *v == variant =>
                        {
                            ops.iter().enumerate().all(|(i, op)| {
                                operand_is_input_field(body, op, param_local, variant, i)
                            })
                        }
                        _ => false,
                    };
                }
            }
            match &block.terminator {
                Terminator::Goto(next) => block_id = *next,
                _ => return false,
            }
        }
        false
    }

    let body = &func.body;
    let entry = body.blocks.iter().find(|b| b.id == BlockId(0))?;

    // The entry block must compute `_d = Discriminant(param)` on a parameter.
    let mut discr_local: Option<usize> = None;
    let mut param_local: Option<usize> = None;
    for stmt in &entry.stmts {
        if let Statement::Assign { place, rvalue: Rvalue::Discriminant(src), .. } = stmt
            && src.projections.is_empty()
            && src.local >= 1
            && src.local <= body.arg_count
            && place.projections.is_empty()
        {
            discr_local = Some(place.local);
            param_local = Some(src.local);
        }
    }
    let discr_local = discr_local?;
    let param_local = param_local?;

    // ...and switch on that discriminant.
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &entry.terminator else {
        return None;
    };
    if operand_local(discr)? != discr_local {
        return None;
    }

    // Default-discriminant gate: switch values must be exactly {0, 1, .., n-1}.
    let mut values: Vec<u128> = targets.iter().map(|(v, _)| *v).collect();
    values.sort_unstable();
    if values.is_empty() || values.iter().enumerate().any(|(i, &v)| v != i as u128) {
        return None;
    }

    let mut verifier = TypeStateVerifier::new();
    let mut states: std::collections::BTreeSet<usize> = std::collections::BTreeSet::new();
    for (value, target) in targets {
        let from = *value as usize;
        let to = output_variant(body, *target)?;
        // SOUNDNESS (hunt-12): a self-transition `v -> v` is only a sound fixed point
        // if it returns the input value UNCHANGED. A payload-oscillating self-loop
        // (`A(b) => A(!b)`) reads as `v0 -> v0` on the discriminant alone but cycles
        // forever; decline the whole machine rather than falsely prove convergence.
        if from == to && !self_edge_preserves_value(body, *target, param_local, from) {
            return None;
        }
        states.insert(from);
        states.insert(to);
        verifier.add_transition(StateTransition {
            from: format!("v{from}"),
            to: format!("v{to}"),
            method: "step".to_string(),
            guard: None,
        });
    }

    // The `otherwise` arm of an exhaustive enum match is `Unreachable`. If it is
    // instead a reachable arm that produces an output we cannot attribute to a
    // specific input variant, decline to model (sound).
    if let Some(block) = body.blocks.iter().find(|b| b.id == *otherwise)
        && !matches!(block.terminator, Terminator::Unreachable)
        && output_variant(body, *otherwise).is_some()
    {
        return None;
    }

    for v in &states {
        verifier.add_state(TypeState { name: format!("v{v}"), properties: Vec::new() });
    }
    // Initial state is irrelevant to convergence (which quantifies over ALL
    // states); set it to the lowest variant so `verify_transitions` is satisfied.
    if let Some(first) = states.iter().next() {
        verifier.set_initial(&format!("v{first}"));
    }
    Some(verifier)
}

/// Extension trait to sort iterators (avoids pulling in itertools).
trait SortedUnstable: Iterator {
    fn sorted_unstable(self) -> Vec<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        let mut v: Vec<_> = self.collect();
        v.sort_unstable();
        v
    }
}

impl<I: Iterator> SortedUnstable for I {}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: create a simple state with no properties.
    fn state(name: &str) -> TypeState {
        TypeState { name: name.to_string(), properties: vec![] }
    }

    /// Helper: create a transition with no guard.
    fn trans(from: &str, to: &str, method: &str) -> StateTransition {
        StateTransition {
            from: from.to_string(),
            to: to.to_string(),
            method: method.to_string(),
            guard: None,
        }
    }

    /// Helper: build the classic file-handle state machine:
    /// Closed -> Open -> (Read | Write) -> Closed
    fn file_handle_verifier() -> TypeStateVerifier {
        let mut v = TypeStateVerifier::new();
        v.add_state(state("Closed"));
        v.add_state(state("Open"));
        v.add_state(state("Reading"));
        v.add_state(state("Writing"));
        v.add_transition(trans("Closed", "Open", "open"));
        v.add_transition(trans("Open", "Reading", "read"));
        v.add_transition(trans("Open", "Writing", "write"));
        v.add_transition(trans("Reading", "Open", "done_read"));
        v.add_transition(trans("Writing", "Open", "done_write"));
        v.add_transition(trans("Open", "Closed", "close"));
        v.set_initial("Closed");
        v
    }

    #[test]
    fn test_typestate_verifier_new_is_empty() {
        let v = TypeStateVerifier::new();
        assert!(v.states.is_empty());
        assert!(v.transitions.is_empty());
        assert!(v.initial_state.is_none());
    }

    // ---- nontrivial_cycle (convergence) ---------------------------------

    #[test]
    fn test_nontrivial_cycle_converging_chain_is_none() {
        // v0 -> v1 -> v2 -> v2 (sink self-loop): converges, no livelock.
        let mut v = TypeStateVerifier::new();
        for s in ["v0", "v1", "v2"] {
            v.add_state(state(s));
        }
        v.add_transition(trans("v0", "v1", "step"));
        v.add_transition(trans("v1", "v2", "step"));
        v.add_transition(trans("v2", "v2", "step"));
        assert_eq!(v.nontrivial_cycle(), None);
    }

    #[test]
    fn test_nontrivial_cycle_two_cycle_detected() {
        // v0 -> v1 -> v0: a 2-cycle (livelock).
        let mut v = TypeStateVerifier::new();
        v.add_state(state("v0"));
        v.add_state(state("v1"));
        v.add_transition(trans("v0", "v1", "step"));
        v.add_transition(trans("v1", "v0", "step"));
        assert!(v.nontrivial_cycle().is_some());
    }

    #[test]
    fn test_nontrivial_cycle_ignores_self_loop() {
        // v0 -> v0 only: a fixed point, NOT a livelock.
        let mut v = TypeStateVerifier::new();
        v.add_state(state("v0"));
        v.add_transition(trans("v0", "v0", "step"));
        assert_eq!(v.nontrivial_cycle(), None);
    }

    #[test]
    fn test_nontrivial_cycle_file_handle_has_cycle() {
        // The classic Closed<->Open<->Reading machine cycles (no fixed point).
        assert!(file_handle_verifier().nontrivial_cycle().is_some());
    }

    // ---- extract_enum_step_machine --------------------------------------

    /// Build a `fn step(s: E) -> E` body: entry reads `_d = Discriminant(_1)`,
    /// `SwitchInt(_d)` over `arms` (input variant value -> target block), each
    /// target block assigns `_0 = Aggregate(Adt{variant})` for the given output.
    fn enum_step_func(arms: &[(u128, usize)]) -> trust_types::VerifiableFunction {
        use trust_types::*;
        let mut blocks = Vec::new();
        let mut targets = Vec::new();
        // Target blocks start at id 2 (id 1 is the unreachable `otherwise`).
        for (i, (value, out)) in arms.iter().enumerate() {
            let bid = BlockId(2 + i);
            targets.push((*value, bid));
            blocks.push(BasicBlock {
                id: bid,
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: "E".to_string(),
                            variant: *out,
                            active_field: None,
                            args: None,
                        },
                        vec![],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            });
        }
        let entry = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Discriminant(Place::local(1)),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(2)),
                targets,
                otherwise: BlockId(1),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        };
        let unreachable =
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Unreachable };
        let mut all = vec![entry, unreachable];
        all.append(&mut blocks);
        VerifiableFunction {
            name: "step".to_string(),
            def_path: "step".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::Unit, name: Some("s".into()) },
                    LocalDecl { index: 2, ty: Ty::Int { width: 64, signed: true }, name: None },
                ],
                blocks: all,
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_extract_enum_step_converging() {
        // Idle(0)->Running(1), Running(1)->Done(2), Done(2)->Done(2): converges.
        let func = enum_step_func(&[(0, 1), (1, 2), (2, 2)]);
        let v = extract_enum_step_machine(&func).expect("recognizable enum-step");
        assert_eq!(v.transitions.len(), 3);
        assert_eq!(v.nontrivial_cycle(), None, "machine converges to Done");
    }

    #[test]
    fn test_extract_enum_step_cyclic() {
        // A(0)->B(1), B(1)->A(0): a 2-cycle (does NOT terminate).
        let func = enum_step_func(&[(0, 1), (1, 0)]);
        let v = extract_enum_step_machine(&func).expect("recognizable enum-step");
        assert!(v.nontrivial_cycle().is_some(), "machine livelocks A<->B");
    }

    #[test]
    fn test_extract_enum_step_non_default_discriminants_declines() {
        // Switch values {0, 2} are not contiguous from 0 → decline (sound).
        let func = enum_step_func(&[(0, 0), (2, 2)]);
        assert!(extract_enum_step_machine(&func).is_none());
    }

    #[test]
    fn test_typestate_verify_transitions_valid() {
        let v = file_handle_verifier();
        assert!(v.verify_transitions().is_ok());
    }

    #[test]
    fn test_typestate_verify_transitions_missing_initial() {
        let mut v = TypeStateVerifier::new();
        v.add_state(state("A"));
        assert_eq!(v.verify_transitions(), Err(TransitionError::MissingInitialState));
    }

    #[test]
    fn test_typestate_verify_transitions_invalid_state_ref() {
        let mut v = TypeStateVerifier::new();
        v.add_state(state("A"));
        v.set_initial("A");
        v.add_transition(trans("A", "B", "go"));
        let err = v.verify_transitions().unwrap_err();
        assert!(matches!(err, TransitionError::InvalidTransition { from, to }
            if from == "A" && to == "B"));
    }

    #[test]
    fn test_typestate_build_state_machine_success() {
        let v = file_handle_verifier();
        let machine = v.build_state_machine().unwrap();
        assert_eq!(machine.initial_state, "Closed");
        assert_eq!(machine.states.len(), 4);
        assert_eq!(machine.transitions.len(), 6);
    }

    #[test]
    fn test_typestate_build_state_machine_missing_initial() {
        let v = TypeStateVerifier::new();
        assert!(v.build_state_machine().is_err());
    }

    #[test]
    fn test_typestate_check_protocol_valid_trace() {
        let v = file_handle_verifier();
        assert!(v.check_protocol(&["Closed", "Open", "Reading", "Open", "Closed"]).is_ok());
    }

    #[test]
    fn test_typestate_check_protocol_invalid_trace() {
        let v = file_handle_verifier();
        let err = v.check_protocol(&["Closed", "Reading"]).unwrap_err();
        assert!(matches!(err, TransitionError::InvalidTransition { from, to }
            if from == "Closed" && to == "Reading"));
    }

    #[test]
    fn test_typestate_check_protocol_wrong_start() {
        let v = file_handle_verifier();
        let err = v.check_protocol(&["Open", "Closed"]).unwrap_err();
        assert!(
            matches!(&err, TransitionError::InvalidTransition { from, to }
                if from == "Closed" && to == "Open"
            ) || matches!(&err, TransitionError::InvalidTransition { .. })
        );
    }

    #[test]
    fn test_typestate_check_protocol_empty_trace() {
        let v = file_handle_verifier();
        assert!(v.check_protocol(&[]).is_ok());
    }

    #[test]
    fn test_typestate_unreachable_states_none() {
        let v = file_handle_verifier();
        assert!(v.unreachable_states().is_empty());
    }

    #[test]
    fn test_typestate_unreachable_states_detected() {
        let mut v = file_handle_verifier();
        v.add_state(state("Orphan"));
        let unreachable = v.unreachable_states();
        assert_eq!(unreachable, vec!["Orphan".to_string()]);
    }

    #[test]
    fn test_typestate_can_reach_true() {
        let v = file_handle_verifier();
        assert!(v.can_reach("Closed", "Writing"));
    }

    #[test]
    fn test_typestate_can_reach_false() {
        let mut v = TypeStateVerifier::new();
        v.add_state(state("A"));
        v.add_state(state("B"));
        v.set_initial("A");
        // No transitions from A to B.
        assert!(!v.can_reach("A", "B"));
    }

    #[test]
    fn test_typestate_can_reach_self() {
        let v = file_handle_verifier();
        assert!(v.can_reach("Closed", "Closed"));
    }

    #[test]
    fn test_typestate_deadlock_states_detected() {
        let mut v = TypeStateVerifier::new();
        v.add_state(state("Init"));
        v.add_state(state("Running"));
        v.add_state(state("Stuck"));
        v.add_transition(trans("Init", "Running", "start"));
        v.add_transition(trans("Running", "Stuck", "fail"));
        v.set_initial("Init");
        // "Stuck" has no outgoing transitions and is not an error state.
        let deadlocks = v.deadlock_states();
        assert!(deadlocks.contains(&"Stuck".to_string()));
    }

    #[test]
    fn test_typestate_deadlock_states_error_excluded() {
        let mut v = TypeStateVerifier::new();
        v.add_state(state("Init"));
        v.add_state(state("Terminal"));
        v.add_transition(trans("Init", "Terminal", "finish"));
        v.set_initial("Init");
        v.add_error_state("Terminal");
        // "Terminal" has no outgoing transitions but IS an error/terminal state.
        let deadlocks = v.deadlock_states();
        assert!(!deadlocks.contains(&"Terminal".to_string()));
    }

    #[test]
    fn test_typestate_state_property() {
        let prop =
            StateProperty { state_name: "Open".to_string(), invariant: "fd >= 0".to_string() };
        assert_eq!(prop.state_name, "Open");
        assert_eq!(prop.invariant, "fd >= 0");
    }

    #[test]
    fn test_typestate_transition_with_guard() {
        let t = StateTransition {
            from: "Open".to_string(),
            to: "Locked".to_string(),
            method: "lock".to_string(),
            guard: Some("has_permission".to_string()),
        };
        assert_eq!(t.guard, Some("has_permission".to_string()));
    }

    #[test]
    fn test_typestate_deadlock_detected_error_variant() {
        let err = TransitionError::DeadlockDetected(vec!["A".into(), "B".into()]);
        let msg = format!("{err}");
        assert!(msg.contains("deadlock"));
        assert!(msg.contains("A"));
        assert!(msg.contains("B"));
    }

    #[test]
    fn test_typestate_initial_state_not_in_states() {
        let mut v = TypeStateVerifier::new();
        v.add_state(state("A"));
        v.set_initial("B"); // B not added as state
        assert_eq!(v.verify_transitions(), Err(TransitionError::MissingInitialState));
    }
}
