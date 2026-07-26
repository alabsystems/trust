// trust-temporal/liveness.rs: Liveness property checking for state machines
//
// Checks liveness properties ("something good eventually happens") using
// Buchi automata construction over state machine graphs. Produces lasso-shaped
// counterexamples (prefix + cycle) when a liveness property is violated.
//
// Key concepts:
// - LivenessProperty: a named "eventually" formula over state labels
// - ResponseProperty: if P then eventually Q
// - Buchi automata: acceptance = visit accepting states infinitely often
// - Lasso counterexample: finite prefix + repeating cycle that avoids acceptance
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;
use trust_types::fx::{FxHashMap, FxHashSet};

use crate::{StateId, StateMachine};

// ---------------------------------------------------------------------------
// Trust: R5 checker fence (2026-07-18 R5 temporal-lane blueprint, slice S2).
//
// Code-verified defects being fenced (NOT repaired — the repair is the
// post-R5 checker work):
// - `check_liveness` accepts at SCC granularity: an SCC containing at least
//   one accepting state is accepted wholesale, but a sub-cycle inside that
//   SCC can avoid every accepting state forever (sub-cycle blindness), so a
//   `Satisfied` from this algorithm can be a false positive.
// - The per-trigger `check_response` shape is `#[cfg(test)]`-only; no sound
//   response checking is reachable from production.
// - `build_lasso`/`find_cycle_in_scc` can fabricate a `vec![entry, entry]`
//   self-loop that does not exist in the machine, and the BFS prefix can run
//   through an accepting state — either way the published lasso is a
//   non-witness for an `F phi` violation.
//
// The fence is fail-closed and invents no capability: every positive is
// demoted to `Unknown` with a named machine-readable reason, and `Violated`
// publishes only after an in-process step replay of the lasso against the
// machine (validate-before-publish).
// ---------------------------------------------------------------------------

/// Trust: R5 fence — named reason attached to every demoted positive verdict
/// from the in-process liveness checker.
pub const LIVENESS_POSITIVE_FENCE_REASON: &str = "in-process temporal liveness positive fenced: \
     SCC-level acceptance is sub-cycle-blind pending the R5 checker repair";

/// Trust: R5 fence — named reason attached when a claimed violation's lasso
/// fails in-process step replay against the machine (the counterexample is
/// withheld rather than published unvalidated).
pub const LIVENESS_VIOLATION_REPLAY_FENCE_REASON: &str = "in-process temporal liveness violation \
     fenced: lasso counterexample failed step replay against the machine pending the R5 checker \
     repair";

/// A liveness property: something must eventually hold.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LivenessProperty {
    /// Human-readable name for the property.
    pub name: String,
    /// The state label that must eventually be reached.
    /// A state satisfies this if its labels contain `eventually_formula`.
    pub eventually_formula: String,
}

impl LivenessProperty {
    /// Create a new liveness property.
    #[must_use]
    pub fn new(name: impl Into<String>, eventually_formula: impl Into<String>) -> Self {
        Self { name: name.into(), eventually_formula: eventually_formula.into() }
    }
}

/// A response property: if P holds, then Q must eventually hold.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResponseProperty {
    /// Human-readable name.
    pub name: String,
    /// Trigger condition (label that must be present).
    pub trigger: String,
    /// Response condition (label that must eventually be reached).
    pub response: String,
}

#[cfg(test)]
impl ResponseProperty {
    /// Create a new response property.
    #[must_use]
    fn new(
        name: impl Into<String>,
        trigger: impl Into<String>,
        response: impl Into<String>,
    ) -> Self {
        Self { name: name.into(), trigger: trigger.into(), response: response.into() }
    }

    /// Convert to a liveness property by encoding as "from any trigger state,
    /// eventually reach a response state".
    #[must_use]
    fn to_liveness(&self) -> LivenessProperty {
        LivenessProperty { name: self.name.clone(), eventually_formula: self.response.clone() }
    }
}

/// Result of a liveness check.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum LivenessResult {
    /// The property is satisfied: all infinite paths eventually reach an
    /// accepting state.
    Satisfied,
    /// The property is violated: there exists an infinite path (lasso-shaped)
    /// that never reaches an accepting state.
    Violated {
        /// Lasso-shaped counterexample: prefix leads to a cycle.
        /// `lasso_trace[..cycle_start]` is the prefix.
        /// `lasso_trace[cycle_start..]` is the repeating cycle.
        lasso_trace: Vec<StateId>,
        /// Index where the cycle begins in `lasso_trace`.
        cycle_start: usize,
    },
    /// Trust: R5 fence — the checker could not produce a verdict it is
    /// entitled to publish: positives are demoted (SCC-level acceptance is
    /// sub-cycle-blind) and violations whose lasso fails step replay are
    /// withheld. Carries a named machine-readable reason.
    Unknown {
        /// Named reason for the demotion (see the `*_FENCE_REASON` constants).
        reason: String,
    },
}

#[cfg(test)]
impl LivenessResult {
    /// Returns true if the property is satisfied.
    #[must_use]
    pub(crate) fn is_satisfied(&self) -> bool {
        matches!(self, LivenessResult::Satisfied)
    }
}

/// Check a liveness property against a state machine.
///
/// A liveness property `F phi` (eventually phi) is satisfied if every infinite
/// execution path eventually visits a state whose labels contain `phi`.
///
/// The algorithm:
/// 1. Identify "accepting" states: those whose labels contain the formula.
/// 2. Find all reachable strongly connected components (SCCs).
/// 3. If any non-trivial SCC (has a cycle) is reachable and contains no
///    accepting state, then liveness is violated. Produce a lasso counterexample.
///
/// Non-trivial SCC: has at least one internal edge (including self-loops).
///
/// Trust: R5 fence — the acceptance side of this algorithm is UNSOUND
/// (SCC-level acceptance is sub-cycle-blind: a fair SCC containing an unfair
/// sub-cycle is wrongly accepted), so this function never returns
/// `Satisfied`: positives are demoted to `Unknown` with
/// [`LIVENESS_POSITIVE_FENCE_REASON`]. `Violated` publishes only after
/// [`replay_lasso_f_violation`] validates the lasso step-by-step against the
/// machine; an unreplayable lasso is withheld as `Unknown` with
/// [`LIVENESS_VIOLATION_REPLAY_FENCE_REASON`].
#[must_use]
pub fn check_liveness(sm: &StateMachine, prop: &LivenessProperty) -> LivenessResult {
    if sm.states.is_empty() {
        // Trust: R5 fence — the empty-machine "vacuously satisfied" positive
        // is demoted along with every other positive from this algorithm.
        return LivenessResult::Unknown { reason: LIVENESS_POSITIVE_FENCE_REASON.to_string() };
    }

    // Identify accepting states
    let accepting: FxHashSet<StateId> = sm
        .states
        .iter()
        .filter(|s| s.labels.contains(&prop.eventually_formula))
        .map(|s| s.id)
        .collect();

    // Build adjacency map
    let adj = build_adjacency(sm);

    // Find reachable state IDs from initial
    let reachable = reachable_set(sm.initial, &adj);

    // Find SCCs using Tarjan's algorithm
    let sccs = tarjan_scc(&reachable, &adj);

    // Check each SCC for violations
    let mut replay_failure: Option<String> = None;
    for scc in &sccs {
        // Skip trivial SCCs (single node with no self-loop)
        if scc.len() == 1 {
            let state = scc[0];
            let has_self_loop = adj.get(&state).is_some_and(|succs| succs.contains(&state));
            if !has_self_loop {
                continue;
            }
        }

        // Check if this SCC has any accepting state
        let has_accepting = scc.iter().any(|s| accepting.contains(s));
        if !has_accepting {
            // Candidate violation: build a lasso counterexample, then
            // Trust: R5 fence — publish it only if it replays against the
            // machine (validate-before-publish).
            let lasso = build_lasso(sm.initial, scc, &adj);
            match replay_lasso_f_violation(sm, &accepting, &lasso.trace, lasso.cycle_start) {
                Ok(()) => {
                    return LivenessResult::Violated {
                        lasso_trace: lasso.trace,
                        cycle_start: lasso.cycle_start,
                    };
                }
                Err(detail) => {
                    if replay_failure.is_none() {
                        replay_failure = Some(detail);
                    }
                }
            }
        }
    }

    // Trust: R5 fence — no validated counterexample. The pre-fence algorithm
    // returned `Satisfied` here, which is unsound (sub-cycle blindness);
    // demote to Unknown with the named reason. If a candidate violation was
    // found but failed replay, name that instead — the machine may or may not
    // satisfy the property, and this checker cannot tell.
    match replay_failure {
        Some(detail) => LivenessResult::Unknown {
            reason: format!("{LIVENESS_VIOLATION_REPLAY_FENCE_REASON} ({detail})"),
        },
        None => LivenessResult::Unknown { reason: LIVENESS_POSITIVE_FENCE_REASON.to_string() },
    }
}

/// Trust: R5 fence — in-process step replay of a lasso counterexample
/// against the machine (validate-before-publish).
///
/// A lasso genuinely refutes `F phi` (strict semantics: the infinite path
/// never visits an accepting state) only when:
/// 1. it starts at the machine's initial state,
/// 2. every claimed step is a real transition of the machine — the duplicated
///    state `build_lasso` leaves at the prefix/cycle junction is tolerated as
///    a stutter artifact (no step), everywhere else `a == b` requires a real
///    self-loop,
/// 3. the cycle genuinely closes (first == last with a real step in between,
///    an explicit closing edge, or a real self-loop for a single-state
///    cycle — this catches the fabricated `vec![entry, entry]` fallback),
/// 4. no state anywhere in the trace is accepting (visiting an accepting
///    state anywhere on the path satisfies the eventuality, so the trace
///    refutes nothing).
///
/// This is strictly a validator: it can only reject counterexamples the
/// checker proposes, never mint new ones.
pub(crate) fn replay_lasso_f_violation(
    sm: &StateMachine,
    accepting: &FxHashSet<StateId>,
    lasso_trace: &[StateId],
    cycle_start: usize,
) -> Result<(), String> {
    if lasso_trace.is_empty() {
        return Err("empty lasso trace".to_string());
    }
    if cycle_start >= lasso_trace.len() {
        return Err(format!(
            "cycle_start {cycle_start} leaves an empty cycle in a trace of length {}",
            lasso_trace.len()
        ));
    }
    if lasso_trace[0] != sm.initial {
        return Err(format!(
            "lasso starts at state {} instead of the initial state {}",
            lasso_trace[0].0, sm.initial.0
        ));
    }
    for sid in lasso_trace {
        if sm.state(*sid).is_none() {
            return Err(format!("lasso references state {} not present in the machine", sid.0));
        }
    }

    let edges: FxHashSet<(StateId, StateId)> =
        sm.transitions.iter().map(|t| (t.from, t.to)).collect();

    for (i, pair) in lasso_trace.windows(2).enumerate() {
        let (a, b) = (pair[0], pair[1]);
        // `build_lasso` concatenates a BFS prefix ending at the SCC entry
        // with a cycle beginning at the same entry: the duplicated junction
        // state is a stutter artifact, not a claimed step.
        if i + 1 == cycle_start && a == b {
            continue;
        }
        if !edges.contains(&(a, b)) {
            return Err(format!(
                "claimed step {} -> {} is not a transition of the machine",
                a.0, b.0
            ));
        }
    }

    let cycle = &lasso_trace[cycle_start..];
    let first = cycle[0];
    let last = *cycle.last().expect("cycle is non-empty (checked above)");
    if first == last {
        if cycle.len() < 2 && !edges.contains(&(first, first)) {
            // The fabricated single-state "cycle" with no real self-loop.
            return Err(format!(
                "single-state cycle at {} has no self-loop in the machine",
                first.0
            ));
        }
        // len >= 2: every in-cycle step was already validated above and the
        // repetition wraps through those same real steps.
    } else if !edges.contains(&(last, first)) {
        return Err(format!("cycle does not close: no transition {} -> {}", last.0, first.0));
    }

    if let Some(acc) = lasso_trace.iter().find(|sid| accepting.contains(sid)) {
        return Err(format!(
            "lasso visits accepting state {} — the path satisfies the eventuality and refutes \
             nothing",
            acc.0
        ));
    }

    Ok(())
}

/// Check a response property: G(trigger -> F response).
///
/// For every reachable state with the trigger label, check that all infinite
/// paths from it eventually reach a state with the response label.
#[cfg(test)]
#[must_use]
fn check_response(sm: &StateMachine, prop: &ResponseProperty) -> LivenessResult {
    if sm.states.is_empty() {
        return LivenessResult::Satisfied;
    }

    let adj = build_adjacency(sm);
    let reachable = reachable_set(sm.initial, &adj);

    // Find trigger states
    let trigger_states: Vec<StateId> = sm
        .states
        .iter()
        .filter(|s| reachable.contains(&s.id))
        .filter(|s| s.labels.contains(&prop.trigger))
        .map(|s| s.id)
        .collect();

    // Response states
    let response_states: FxHashSet<StateId> =
        sm.states.iter().filter(|s| s.labels.contains(&prop.response)).map(|s| s.id).collect();

    // For each trigger state, check liveness of reaching a response state
    for trigger_id in &trigger_states {
        // Find SCCs reachable from trigger_id
        let reachable_from_trigger = reachable_set(*trigger_id, &adj);
        let sccs = tarjan_scc(&reachable_from_trigger, &adj);

        for scc in &sccs {
            if scc.len() == 1 {
                let state = scc[0];
                let has_self_loop = adj.get(&state).is_some_and(|succs| succs.contains(&state));
                if !has_self_loop {
                    continue;
                }
            }

            let has_response = scc.iter().any(|s| response_states.contains(s));
            if !has_response {
                let lasso = build_lasso(sm.initial, scc, &adj);
                return LivenessResult::Violated {
                    lasso_trace: lasso.trace,
                    cycle_start: lasso.cycle_start,
                };
            }
        }
    }

    LivenessResult::Satisfied
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Build an adjacency map from a state machine.
fn build_adjacency(sm: &StateMachine) -> FxHashMap<StateId, Vec<StateId>> {
    let mut adj: FxHashMap<StateId, Vec<StateId>> = FxHashMap::default();
    for s in &sm.states {
        adj.entry(s.id).or_default();
    }
    for t in &sm.transitions {
        adj.entry(t.from).or_default().push(t.to);
    }
    adj
}

/// BFS to find all reachable states from `start`.
fn reachable_set(start: StateId, adj: &FxHashMap<StateId, Vec<StateId>>) -> FxHashSet<StateId> {
    let mut visited = FxHashSet::default();
    let mut queue = VecDeque::new();
    visited.insert(start);
    queue.push_back(start);
    while let Some(current) = queue.pop_front() {
        if let Some(succs) = adj.get(&current) {
            for &next in succs {
                if visited.insert(next) {
                    queue.push_back(next);
                }
            }
        }
    }
    visited
}

/// Tarjan's SCC algorithm. Returns SCCs in reverse topological order.
fn tarjan_scc(
    states: &FxHashSet<StateId>,
    adj: &FxHashMap<StateId, Vec<StateId>>,
) -> Vec<Vec<StateId>> {
    struct TarjanState {
        index_counter: usize,
        stack: Vec<StateId>,
        on_stack: FxHashSet<StateId>,
        index: FxHashMap<StateId, usize>,
        lowlink: FxHashMap<StateId, usize>,
        sccs: Vec<Vec<StateId>>,
    }

    fn strongconnect(
        v: StateId,
        states: &FxHashSet<StateId>,
        adj: &FxHashMap<StateId, Vec<StateId>>,
        ts: &mut TarjanState,
    ) {
        ts.index.insert(v, ts.index_counter);
        ts.lowlink.insert(v, ts.index_counter);
        ts.index_counter += 1;
        ts.stack.push(v);
        ts.on_stack.insert(v);

        if let Some(succs) = adj.get(&v) {
            for &w in succs {
                if !states.contains(&w) {
                    continue;
                }
                if !ts.index.contains_key(&w) {
                    strongconnect(w, states, adj, ts);
                    let w_ll = ts.lowlink[&w];
                    let v_ll = ts.lowlink.get_mut(&v).expect("invariant: v in lowlink");
                    *v_ll = (*v_ll).min(w_ll);
                } else if ts.on_stack.contains(&w) {
                    let w_idx = ts.index[&w];
                    let v_ll = ts.lowlink.get_mut(&v).expect("invariant: v in lowlink");
                    *v_ll = (*v_ll).min(w_idx);
                }
            }
        }

        if ts.lowlink[&v] == ts.index[&v] {
            let mut scc = Vec::new();
            while let Some(w) = ts.stack.pop() {
                ts.on_stack.remove(&w);
                scc.push(w);
                if w == v {
                    break;
                }
            }
            ts.sccs.push(scc);
        }
    }

    let mut ts = TarjanState {
        index_counter: 0,
        stack: Vec::new(),
        on_stack: FxHashSet::default(),
        index: FxHashMap::default(),
        lowlink: FxHashMap::default(),
        sccs: Vec::new(),
    };

    // Sort for deterministic order
    let mut sorted_states: Vec<StateId> = states.iter().copied().collect();
    sorted_states.sort();

    for &v in &sorted_states {
        if !ts.index.contains_key(&v) {
            strongconnect(v, states, adj, &mut ts);
        }
    }

    ts.sccs
}

/// A lasso-shaped trace: prefix leading to a cycle.
struct Lasso {
    trace: Vec<StateId>,
    cycle_start: usize,
}

/// Build a lasso-shaped counterexample: path from initial to an SCC node,
/// then a cycle within the SCC.
fn build_lasso(initial: StateId, scc: &[StateId], adj: &FxHashMap<StateId, Vec<StateId>>) -> Lasso {
    let scc_set: FxHashSet<StateId> = scc.iter().copied().collect();
    let scc_entry = scc[0];

    // BFS from initial to scc_entry (prefix)
    let prefix = bfs_path(initial, scc_entry, adj);

    // Find a cycle within the SCC starting and ending at scc_entry
    let cycle = find_cycle_in_scc(scc_entry, &scc_set, adj);

    let cycle_start = prefix.len();
    let mut trace = prefix;
    trace.extend_from_slice(&cycle);

    Lasso { trace, cycle_start }
}

/// BFS shortest path from `start` to `target`.
fn bfs_path(
    start: StateId,
    target: StateId,
    adj: &FxHashMap<StateId, Vec<StateId>>,
) -> Vec<StateId> {
    if start == target {
        return vec![start];
    }

    let mut visited = FxHashSet::default();
    let mut parent: FxHashMap<StateId, StateId> = FxHashMap::default();
    let mut queue = VecDeque::new();
    visited.insert(start);
    queue.push_back(start);

    while let Some(current) = queue.pop_front() {
        if let Some(succs) = adj.get(&current) {
            for &next in succs {
                if visited.insert(next) {
                    parent.insert(next, current);
                    if next == target {
                        let mut path = vec![target];
                        let mut cur = target;
                        while let Some(&prev) = parent.get(&cur) {
                            path.push(prev);
                            cur = prev;
                        }
                        path.reverse();
                        return path;
                    }
                    queue.push_back(next);
                }
            }
        }
    }

    vec![start]
}

/// Find a cycle within an SCC starting at `entry`.
fn find_cycle_in_scc(
    entry: StateId,
    scc_set: &FxHashSet<StateId>,
    adj: &FxHashMap<StateId, Vec<StateId>>,
) -> Vec<StateId> {
    // DFS to find a path from entry back to entry within the SCC
    let mut visited = FxHashSet::default();
    let mut parent: FxHashMap<StateId, StateId> = FxHashMap::default();
    let mut stack = Vec::new();

    if let Some(succs) = adj.get(&entry) {
        for &next in succs {
            if scc_set.contains(&next) {
                stack.push(next);
                parent.insert(next, entry);
            }
        }
    }

    while let Some(current) = stack.pop() {
        if current == entry {
            // Found cycle, reconstruct
            // Trace back through parent from entry (the second visit)
            // We need to go backwards from the predecessor that led to entry
            if let Some(&pred) = parent.get(&current) {
                let mut back = pred;
                let mut path = vec![entry, back];
                while back != entry {
                    if let Some(&p) = parent.get(&back) {
                        back = p;
                        path.push(back);
                    } else {
                        break;
                    }
                }
                path.reverse();
                return path;
            }
            return vec![entry, entry];
        }
        if !visited.insert(current) {
            continue;
        }
        if let Some(succs) = adj.get(&current) {
            for &next in succs {
                if !visited.contains(&next) && scc_set.contains(&next) {
                    parent.insert(next, current);
                    stack.push(next);
                } else if next == entry {
                    // Found the back-edge to entry
                    parent.insert(next, current);
                    let mut path = vec![entry];
                    let mut back = current;
                    path.push(back);
                    while back != entry {
                        if let Some(&p) = parent.get(&back) {
                            back = p;
                            path.push(back);
                        } else {
                            break;
                        }
                    }
                    path.reverse();
                    return path;
                }
            }
        }
    }

    // Fallback: self-loop
    vec![entry, entry]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{State, StateMachineBuilder, Transition};

    // ---- check_liveness: positives are fenced (R5 checker fence) ----
    //
    // These three tests previously pinned `Satisfied`. The algorithm's
    // SCC-level acceptance is sub-cycle-blind (a verified unsound-positive
    // shape), so ALL positives are demoted; the tests now pin the fence.

    #[test]
    fn test_liveness_simple_satisfied() {
        // Linear: Idle -> Working -> Done(accepting)
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Idle").with_label("idle"))
            .add_state(State::new(StateId(1), "Working").with_label("working"))
            .add_state(State::new(StateId(2), "Done").with_label("done"))
            .add_transition(Transition::new(StateId(0), StateId(1), "start"))
            .add_transition(Transition::new(StateId(1), StateId(2), "finish"))
            .build();

        let prop = LivenessProperty::new("eventually_done", "done");
        // R5 fence: previously `Satisfied` (no cycles => no infinite
        // non-accepting path). The positive path is fenced wholesale pending
        // the checker repair, so this now pins the named demotion.
        let result = check_liveness(&sm, &prop);
        assert_eq!(
            result,
            LivenessResult::Unknown { reason: LIVENESS_POSITIVE_FENCE_REASON.to_string() }
        );
    }

    #[test]
    fn test_liveness_cycle_with_accepting_state() {
        // Cycle: A -> B -> C -> A, where C has accepting label
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A").with_label("a"))
            .add_state(State::new(StateId(1), "B").with_label("b"))
            .add_state(State::new(StateId(2), "C").with_label("goal"))
            .add_transition(Transition::new(StateId(0), StateId(1), "ab"))
            .add_transition(Transition::new(StateId(1), StateId(2), "bc"))
            .add_transition(Transition::new(StateId(2), StateId(0), "ca"))
            .build();

        let prop = LivenessProperty::new("reach_goal", "goal");
        // R5 fence: previously `Satisfied` via SCC-level acceptance — the
        // exact algorithm shape that is sub-cycle-blind. Pins the demotion.
        let result = check_liveness(&sm, &prop);
        assert_eq!(
            result,
            LivenessResult::Unknown { reason: LIVENESS_POSITIVE_FENCE_REASON.to_string() }
        );
    }

    #[test]
    fn test_liveness_empty_machine() {
        let sm = StateMachineBuilder::new(StateId(0)).build();
        let prop = LivenessProperty::new("test", "anything");
        // R5 fence: previously the vacuous `Satisfied`. All positives from
        // this checker are demoted, including the vacuous one.
        let result = check_liveness(&sm, &prop);
        assert_eq!(
            result,
            LivenessResult::Unknown { reason: LIVENESS_POSITIVE_FENCE_REASON.to_string() }
        );
    }

    // ---- R5 fence anti-fixtures ----

    #[test]
    fn fence_demotes_sub_cycle_blind_scc_acceptance() {
        // A <-> B <-> C where only C is accepting. The single SCC {A,B,C}
        // contains an accepting state, so the pre-fence checker returned
        // `Satisfied` — an UNSOUND POSITIVE: the sub-cycle A <-> B never
        // visits C, so "eventually goal" is genuinely violated on that path.
        // The fence pins this shape to Unknown with the named reason (the
        // checker cannot see the sub-cycle, so no validated counterexample
        // can be published either).
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A").with_label("a"))
            .add_state(State::new(StateId(1), "B").with_label("b"))
            .add_state(State::new(StateId(2), "C").with_label("goal"))
            .add_transition(Transition::new(StateId(0), StateId(1), "ab"))
            .add_transition(Transition::new(StateId(1), StateId(0), "ba"))
            .add_transition(Transition::new(StateId(1), StateId(2), "bc"))
            .add_transition(Transition::new(StateId(2), StateId(1), "cb"))
            .build();

        let prop = LivenessProperty::new("reach_goal", "goal");
        let result = check_liveness(&sm, &prop);
        assert_eq!(
            result,
            LivenessResult::Unknown { reason: LIVENESS_POSITIVE_FENCE_REASON.to_string() },
            "the sub-cycle-blind unsound positive must be fenced, never Satisfied"
        );
    }

    #[test]
    fn fence_rejects_lasso_with_prefix_through_accepting_state() {
        // 0(start) -> 1(goal) -> 2 <-> 3: every infinite path visits the
        // accepting state 1 before entering the non-accepting 2 <-> 3 cycle,
        // so `F goal` genuinely HOLDS — yet the pre-fence checker published
        // `Violated` with a lasso whose prefix runs through the accepting
        // state (a non-witness). The replay validator rejects it; the fence
        // returns Unknown, never a bogus Violated (and never Satisfied).
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Start").with_label("start"))
            .add_state(State::new(StateId(1), "Goal").with_label("goal"))
            .add_state(State::new(StateId(2), "L1"))
            .add_state(State::new(StateId(3), "L2"))
            .add_transition(Transition::new(StateId(0), StateId(1), "reach"))
            .add_transition(Transition::new(StateId(1), StateId(2), "enter"))
            .add_transition(Transition::new(StateId(2), StateId(3), "step"))
            .add_transition(Transition::new(StateId(3), StateId(2), "back"))
            .build();

        let prop = LivenessProperty::new("reach_goal", "goal");
        let result = check_liveness(&sm, &prop);
        match &result {
            LivenessResult::Unknown { reason } => {
                assert!(
                    reason.contains(LIVENESS_VIOLATION_REPLAY_FENCE_REASON),
                    "the withheld counterexample must carry the replay fence reason: {reason}"
                );
                assert!(
                    reason.contains("accepting"),
                    "the replay detail must name the accepting-state hit: {reason}"
                );
            }
            other => panic!("expected fenced Unknown, got {other:?}"),
        }
    }

    // ---- check_liveness: violated ----

    #[test]
    fn test_liveness_violation_self_loop() {
        // Idle -> Spin(self-loop, no accepting label)
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Idle").with_label("idle"))
            .add_state(State::new(StateId(1), "Spin").with_label("spinning"))
            .add_transition(Transition::new(StateId(0), StateId(1), "enter"))
            .add_transition(Transition::new(StateId(1), StateId(1), "spin"))
            .build();

        let prop = LivenessProperty::new("eventually_done", "done");
        let result = check_liveness(&sm, &prop);

        match &result {
            LivenessResult::Violated { lasso_trace, cycle_start } => {
                // Prefix ends before cycle
                assert!(*cycle_start > 0 || lasso_trace[0] == StateId(1));
                // Cycle must include Spin
                let cycle = &lasso_trace[*cycle_start..];
                assert!(cycle.contains(&StateId(1)));
            }
            other => panic!("expected replay-validated violation, got {other:?}"),
        }
    }

    #[test]
    fn test_liveness_violation_cycle_no_accepting() {
        // A -> B -> A (cycle), neither has "done" label
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A").with_label("a"))
            .add_state(State::new(StateId(1), "B").with_label("b"))
            .add_transition(Transition::new(StateId(0), StateId(1), "ab"))
            .add_transition(Transition::new(StateId(1), StateId(0), "ba"))
            .build();

        let prop = LivenessProperty::new("eventually_done", "done");
        let result = check_liveness(&sm, &prop);

        match &result {
            LivenessResult::Violated { lasso_trace, cycle_start } => {
                assert!(!lasso_trace.is_empty());
                let cycle = &lasso_trace[*cycle_start..];
                assert!(cycle.len() >= 2, "cycle should have at least 2 states");
            }
            other => panic!("expected replay-validated violation, got {other:?}"),
        }
    }

    #[test]
    fn test_liveness_lasso_structure() {
        // Init -> Loop1 -> Loop2 -> Loop1 (trapped cycle)
        // Init has no accepting labels; the cycle has none either
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Init"))
            .add_state(State::new(StateId(1), "Loop1"))
            .add_state(State::new(StateId(2), "Loop2"))
            .add_transition(Transition::new(StateId(0), StateId(1), "enter"))
            .add_transition(Transition::new(StateId(1), StateId(2), "step"))
            .add_transition(Transition::new(StateId(2), StateId(1), "back"))
            .build();

        let prop = LivenessProperty::new("reach_goal", "goal");
        let result = check_liveness(&sm, &prop);

        match &result {
            LivenessResult::Violated { lasso_trace, cycle_start } => {
                // Prefix: path from Init to the cycle
                let prefix = &lasso_trace[..*cycle_start];
                assert!(prefix.contains(&StateId(0)), "prefix should start from init");

                // Cycle: should contain loop states
                let cycle = &lasso_trace[*cycle_start..];
                assert!(!cycle.is_empty(), "cycle should not be empty");
            }
            other => panic!("expected replay-validated violation, got {other:?}"),
        }
    }

    // ---- check_response ----

    #[test]
    fn test_response_satisfied() {
        // request -> process -> response -> idle -> request -> ...
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Idle").with_label("idle"))
            .add_state(State::new(StateId(1), "Requested").with_label("request"))
            .add_state(State::new(StateId(2), "Processing").with_label("processing"))
            .add_state(State::new(StateId(3), "Responded").with_label("response"))
            .add_transition(Transition::new(StateId(0), StateId(1), "req"))
            .add_transition(Transition::new(StateId(1), StateId(2), "process"))
            .add_transition(Transition::new(StateId(2), StateId(3), "respond"))
            .add_transition(Transition::new(StateId(3), StateId(0), "reset"))
            .build();

        let prop = ResponseProperty::new("req_resp", "request", "response");
        let result = check_response(&sm, &prop);
        assert!(result.is_satisfied());
    }

    #[test]
    fn test_response_violated_stuck_after_trigger() {
        // request -> spin(self-loop) — never reaches response
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Idle").with_label("idle"))
            .add_state(State::new(StateId(1), "Requested").with_label("request"))
            .add_state(State::new(StateId(2), "Spin").with_label("stuck"))
            .add_transition(Transition::new(StateId(0), StateId(1), "req"))
            .add_transition(Transition::new(StateId(1), StateId(2), "enter_spin"))
            .add_transition(Transition::new(StateId(2), StateId(2), "spin"))
            .build();

        let prop = ResponseProperty::new("req_resp", "request", "response");
        let result = check_response(&sm, &prop);
        assert!(!result.is_satisfied());
    }

    #[test]
    fn test_response_no_trigger_vacuously_true() {
        // No state has the trigger label
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A").with_label("a"))
            .add_state(State::new(StateId(1), "B").with_label("b"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        let prop = ResponseProperty::new("req_resp", "request", "response");
        let result = check_response(&sm, &prop);
        assert!(result.is_satisfied());
    }

    // ---- ResponseProperty conversion ----

    #[test]
    fn test_response_to_liveness() {
        let rp = ResponseProperty::new("req_resp", "request", "response");
        let lp = rp.to_liveness();
        assert_eq!(lp.name, "req_resp");
        assert_eq!(lp.eventually_formula, "response");
    }
}
