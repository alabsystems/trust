// trust-temporal/fairness.rs: Fairness constraints and starvation detection
//
// Provides weak and strong fairness constraints for concurrent state machines,
// fair schedule generation, liveness checking under fairness, and starvation
// detection.
//
// Fairness concepts:
// - Weak fairness (justice): if an action is continuously enabled, it must
//   eventually be taken.
// - Strong fairness (compassion): if an action is enabled infinitely often,
//   it must be taken infinitely often.
// - Unconditional fairness: the action must be taken infinitely often,
//   regardless of whether it is enabled.
// - Starvation: a process/action that can be perpetually bypassed by an
//   unfair scheduler.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;
use trust_types::fx::{FxHashMap, FxHashSet};

#[cfg(test)]
use crate::Trace;
use crate::liveness::{LivenessResult, replay_lasso_f_violation};
use crate::{LivenessProperty, StateId, StateMachine};

// ---------------------------------------------------------------------------
// Trust: R5 checker fence (2026-07-18 R5 temporal-lane blueprint, slice S2).
//
// Code-verified defects being fenced (NOT repaired):
// - `check_under_fairness` filters fairness at SCC granularity (the strong-
//   fairness "enabled somewhere / taken somewhere" test especially): a
//   sub-cycle of the SCC can be fair on its own (the constrained action never
//   enabled along it) while the SCC-level filter discards the whole SCC as
//   unfair — so `Satisfied` can be a false positive (sub-cycle escape).
// - The lasso builder shares liveness.rs's fabricated `vec![entry, entry]`
//   self-loop fallback, and the extracted cycle can differ from the SCC the
//   fairness filter reasoned about.
//
// Fence: positives demoted to `Unknown` with a named reason; `Violated`
// publishes only after the lasso replays step-by-step AND its cycle can
// actually satisfy every fairness constraint (validate-before-publish).
// ---------------------------------------------------------------------------

/// Trust: R5 fence — named reason attached to every demoted positive verdict
/// from the in-process fairness-filtered liveness checker.
pub const FAIRNESS_POSITIVE_FENCE_REASON: &str = "in-process temporal fairness positive fenced: \
     SCC-granularity fairness filtering is sub-cycle-blind pending the R5 checker repair";

/// Trust: R5 fence — named reason attached when a claimed fair violation's
/// lasso fails in-process replay (structural step replay or cycle-level
/// fairness validation).
pub const FAIRNESS_VIOLATION_REPLAY_FENCE_REASON: &str = "in-process temporal fairness violation \
     fenced: lasso counterexample failed fair-step replay against the machine pending the R5 \
     checker repair";

/// An action in the state machine, identified by its event label.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Action(pub String);

impl Action {
    /// Create a new action.
    #[must_use]
    pub fn new(name: impl Into<String>) -> Self {
        Self(name.into())
    }
}

/// A fairness constraint on the scheduler.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum FairnessConstraint {
    /// Weak fairness (justice): if the action is continuously enabled from
    /// some point on, it must eventually be taken.
    WeakFairness(Action),
    /// Strong fairness (compassion): if the action is enabled infinitely
    /// often, it must be taken infinitely often.
    StrongFairness(Action),
    /// Unconditional fairness: the action must be taken infinitely often,
    /// regardless of enablement.
    Unconditional(Action),
}

impl FairnessConstraint {
    /// Get the action this constraint applies to.
    #[must_use]
    fn action(&self) -> &Action {
        match self {
            FairnessConstraint::WeakFairness(a)
            | FairnessConstraint::StrongFairness(a)
            | FairnessConstraint::Unconditional(a) => a,
        }
    }
}

#[cfg(test)]
impl FairnessConstraint {
    /// Returns `true` if this is a weak fairness constraint.
    #[must_use]
    fn is_weak(&self) -> bool {
        matches!(self, FairnessConstraint::WeakFairness(_))
    }

    /// Returns `true` if this is a strong fairness constraint.
    #[must_use]
    fn is_strong(&self) -> bool {
        matches!(self, FairnessConstraint::StrongFairness(_))
    }

    /// Returns `true` if this is an unconditional fairness constraint.
    #[must_use]
    fn is_unconditional(&self) -> bool {
        matches!(self, FairnessConstraint::Unconditional(_))
    }
}

/// Describes how a fairness constraint was violated in a trace.
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
#[allow(clippy::enum_variant_names)]
enum FairnessViolation {
    /// Weak fairness violated: the action was continuously enabled from
    /// `enabled_from_index` onward but never taken.
    WeakViolation {
        /// The action that was starved.
        action: String,
        /// The trace index from which the action became continuously enabled.
        enabled_from_index: usize,
    },
    /// Strong fairness violated: the action was enabled at these trace indices
    /// but never taken after the last occurrence.
    StrongViolation {
        /// The action that was starved.
        action: String,
        /// Indices where the action was enabled.
        enabled_at_indices: Vec<usize>,
    },
    /// Unconditional fairness violated: the action was not taken at all
    /// (or not taken often enough) in the trace suffix.
    UnconditionalViolation {
        /// The action that should have been taken.
        action: String,
        /// How many times the action was taken in the trace.
        taken_count: usize,
    },
}

#[cfg(test)]
impl FairnessViolation {
    /// Get the action name involved in this violation.
    #[must_use]
    fn action(&self) -> &str {
        match self {
            FairnessViolation::WeakViolation { action, .. }
            | FairnessViolation::StrongViolation { action, .. }
            | FairnessViolation::UnconditionalViolation { action, .. } => action,
        }
    }
}

/// A witness that a particular action (or process) can be starved.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StarvationWitness {
    /// The action/event that is starved.
    pub action: String,
    /// States from which the action is enabled but can be avoided forever.
    pub enabled_states: Vec<StateId>,
    /// A cycle that avoids the action entirely.
    pub avoiding_cycle: Vec<StateId>,
}

/// A step in a fair schedule.
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
struct ScheduleStep {
    /// Current state.
    pub state: StateId,
    /// Event/action taken.
    pub event: String,
    /// Next state.
    pub next_state: StateId,
}

/// A fair schedule: a sequence of steps satisfying fairness constraints.
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
struct FairSchedule {
    /// Ordered steps of the schedule.
    pub steps: Vec<ScheduleStep>,
}

/// Annotation on a single trace step indicating fairness-relevant information.
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
struct FairnessAnnotation {
    /// Index in the trace (state position).
    pub trace_index: usize,
    /// The state at this position.
    pub state: StateId,
    /// Actions that are enabled at this state.
    pub enabled_actions: Vec<String>,
    /// Actions that are taken (transition from this state to the next).
    pub taken_action: Option<String>,
    /// Whether this step is relevant to any fairness constraint.
    pub fairness_relevant: bool,
}

/// An annotated trace with fairness information on each step.
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
struct AnnotatedTrace {
    /// Per-step annotations.
    pub annotations: Vec<FairnessAnnotation>,
}

/// Checks execution traces against a set of fairness constraints.
#[cfg(test)]
#[derive(Debug, Clone)]
struct FairnessChecker {
    machine: StateMachine,
    constraints: Vec<FairnessConstraint>,
}

#[cfg(test)]
impl FairnessChecker {
    #[must_use]
    fn new(machine: StateMachine, constraints: Vec<FairnessConstraint>) -> Self {
        Self { machine, constraints }
    }

    #[must_use]
    fn check_trace(&self, trace: &Trace) -> Vec<FairnessViolation> {
        let mut violations = Vec::new();
        for constraint in &self.constraints {
            match constraint {
                FairnessConstraint::WeakFairness(action) => {
                    if let Some(v) = check_weak_fairness_trace(&self.machine, trace, &action.0) {
                        violations.push(v);
                    }
                }
                FairnessConstraint::StrongFairness(action) => {
                    if let Some(v) = check_strong_fairness_trace(&self.machine, trace, &action.0) {
                        violations.push(v);
                    }
                }
                FairnessConstraint::Unconditional(action) => {
                    if let Some(v) = check_unconditional_trace(trace, &self.machine, &action.0) {
                        violations.push(v);
                    }
                }
            }
        }
        violations
    }

    #[must_use]
    fn check_liveness(&self, property: &LivenessProperty) -> LivenessResult {
        check_under_fairness(&self.machine, property, &self.constraints)
    }

    #[must_use]
    fn detect_starvation(&self) -> Vec<StarvationWitness> {
        detect_starvation(&self.machine)
    }
}

// ---------------------------------------------------------------------------
// Test-only standalone functions
// ---------------------------------------------------------------------------

#[cfg(test)]
#[must_use]
fn check_weak_fairness(
    sm: &StateMachine,
    trace: &Trace,
    action: &str,
) -> Option<FairnessViolation> {
    check_weak_fairness_trace(sm, trace, action)
}

#[cfg(test)]
#[must_use]
fn check_strong_fairness(
    sm: &StateMachine,
    trace: &Trace,
    action: &str,
) -> Option<FairnessViolation> {
    check_strong_fairness_trace(sm, trace, action)
}

#[cfg(test)]
#[must_use]
fn annotate_trace(
    sm: &StateMachine,
    trace: &Trace,
    constraints: &[FairnessConstraint],
) -> AnnotatedTrace {
    let fair_actions: FxHashSet<&str> = constraints.iter().map(|c| c.action().0.as_str()).collect();

    let mut annotations = Vec::with_capacity(trace.states.len());

    for (i, &state_id) in trace.states.iter().enumerate() {
        let enabled: Vec<String> =
            sm.transitions.iter().filter(|t| t.from == state_id).map(|t| t.event.clone()).collect();

        let taken = if i + 1 < trace.states.len() {
            let next = trace.states[i + 1];
            sm.transitions
                .iter()
                .find(|t| t.from == state_id && t.to == next)
                .map(|t| t.event.clone())
        } else {
            None
        };

        let fairness_relevant = enabled.iter().any(|e| fair_actions.contains(e.as_str()))
            || taken.as_deref().is_some_and(|t| fair_actions.contains(t));

        annotations.push(FairnessAnnotation {
            trace_index: i,
            state: state_id,
            enabled_actions: enabled,
            taken_action: taken,
            fairness_relevant,
        });
    }

    AnnotatedTrace { annotations }
}

#[cfg(test)]
#[must_use]
fn generate_fair_schedule(
    sm: &StateMachine,
    fairness: &[FairnessConstraint],
    max_steps: usize,
) -> Option<FairSchedule> {
    if sm.transitions.is_empty() {
        return None;
    }

    let fair_actions: Vec<&str> = fairness.iter().map(|f| f.action().0.as_str()).collect();

    let mut steps = Vec::new();
    let mut current = sm.initial;

    for (fair_idx, _) in (0..max_steps).enumerate() {
        let outgoing = sm.outgoing(current);
        if outgoing.is_empty() {
            break;
        }

        let chosen = if !fair_actions.is_empty() {
            let preferred = fair_actions[fair_idx % fair_actions.len()];
            outgoing.iter().find(|t| t.event == preferred).or_else(|| outgoing.first()).copied()
        } else {
            outgoing.first().copied()
        };

        let Some(transition) = chosen else {
            break;
        };

        steps.push(ScheduleStep {
            state: current,
            event: transition.event.clone(),
            next_state: transition.to,
        });

        current = transition.to;
    }

    if steps.is_empty() { None } else { Some(FairSchedule { steps }) }
}

/// Check a liveness property under fairness constraints.
///
/// Without fairness, a cycle that avoids accepting states violates liveness.
/// With fairness, we only consider cycles that also satisfy the fairness
/// constraints — i.e., cycles where fair actions are not perpetually ignored
/// while enabled.
///
/// Algorithm:
/// 1. Find all non-trivial SCCs reachable from the initial state.
/// 2. For each SCC that has no accepting state:
///    a. Check if the SCC violates any fairness constraint.
///    b. If an action is weakly-fair and continuously enabled in the SCC
///    but never taken, the cycle is unfair and filtered out.
///    c. If an action is strongly-fair and enabled in any SCC state but
///    never taken, the cycle is unfair and filtered out.
///    d. If an action has unconditional fairness but is never taken in the
///    SCC, the cycle is unfair and filtered out.
///    e. If the SCC passes all fairness filters, it is a genuine violation.
///
/// Trust: R5 fence — this function never returns `Satisfied` (the SCC-level
/// fairness filter is sub-cycle-blind); positives are demoted to `Unknown`
/// with [`FAIRNESS_POSITIVE_FENCE_REASON`], and `Violated` publishes only
/// after [`validate_fair_lasso`] replays the lasso against the machine and
/// confirms its cycle can satisfy every constraint.
#[must_use]
pub fn check_under_fairness(
    sm: &StateMachine,
    property: &LivenessProperty,
    fairness: &[FairnessConstraint],
) -> LivenessResult {
    if sm.states.is_empty() {
        // Trust: R5 fence — vacuous positive demoted with the rest.
        return LivenessResult::Unknown { reason: FAIRNESS_POSITIVE_FENCE_REASON.to_string() };
    }

    // Accepting states
    let accepting: FxHashSet<StateId> = sm
        .states
        .iter()
        .filter(|s| s.labels.contains(&property.eventually_formula))
        .map(|s| s.id)
        .collect();

    let adj = build_adjacency(sm);
    let reachable = reachable_set(sm.initial, &adj);
    let sccs = tarjan_scc(&reachable, &adj);

    // Pre-compute: for each state, which events are enabled
    let mut state_events: FxHashMap<StateId, FxHashSet<&str>> = FxHashMap::default();
    for t in &sm.transitions {
        state_events.entry(t.from).or_default().insert(t.event.as_str());
    }

    let mut replay_failure: Option<String> = None;
    for scc in &sccs {
        // Skip trivial SCCs
        if scc.len() == 1 {
            let state = scc[0];
            let has_self_loop = adj.get(&state).is_some_and(|succs| succs.contains(&state));
            if !has_self_loop {
                continue;
            }
        }

        let has_accepting = scc.iter().any(|s| accepting.contains(s));
        if has_accepting {
            continue;
        }

        let scc_set: FxHashSet<StateId> = scc.iter().copied().collect();

        // Events taken within the SCC (transitions where both endpoints are in SCC)
        let taken_events: FxHashSet<&str> = sm
            .transitions
            .iter()
            .filter(|t| scc_set.contains(&t.from) && scc_set.contains(&t.to))
            .map(|t| t.event.as_str())
            .collect();

        // Check fairness constraints
        let mut is_fair_cycle = true;
        for constraint in fairness {
            let action_name = constraint.action().0.as_str();

            match constraint {
                FairnessConstraint::WeakFairness(_) => {
                    // Weak fairness: if the action is enabled in ALL SCC states
                    // (continuously enabled), it must be taken.
                    let enabled_everywhere = scc.iter().all(|s| {
                        state_events.get(s).is_some_and(|evts| evts.contains(action_name))
                    });
                    if enabled_everywhere && !taken_events.contains(action_name) {
                        is_fair_cycle = false;
                        break;
                    }
                }
                FairnessConstraint::StrongFairness(_) => {
                    // Strong fairness: if the action is enabled in ANY SCC state
                    // (enabled infinitely often since SCC cycles), it must be taken.
                    let enabled_somewhere = scc.iter().any(|s| {
                        state_events.get(s).is_some_and(|evts| evts.contains(action_name))
                    });
                    if enabled_somewhere && !taken_events.contains(action_name) {
                        is_fair_cycle = false;
                        break;
                    }
                }
                FairnessConstraint::Unconditional(_) => {
                    // Unconditional fairness: the action must be taken in the SCC,
                    // regardless of enablement.
                    if !taken_events.contains(action_name) {
                        is_fair_cycle = false;
                        break;
                    }
                }
            }
        }

        if is_fair_cycle {
            // Candidate violation under fairness. Trust: R5 fence — publish
            // only if the lasso replays against the machine and its cycle can
            // actually satisfy every fairness constraint
            // (validate-before-publish; the extracted cycle may differ from
            // the SCC the filter reasoned about).
            let lasso = build_lasso(sm.initial, scc, &adj);
            match validate_fair_lasso(sm, &accepting, fairness, &lasso.trace, lasso.cycle_start) {
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

    // Trust: R5 fence — no validated counterexample; the pre-fence
    // `Satisfied` is demoted (SCC-granularity fairness filtering is
    // sub-cycle-blind).
    match replay_failure {
        Some(detail) => LivenessResult::Unknown {
            reason: format!("{FAIRNESS_VIOLATION_REPLAY_FENCE_REASON} ({detail})"),
        },
        None => LivenessResult::Unknown { reason: FAIRNESS_POSITIVE_FENCE_REASON.to_string() },
    }
}

/// Trust: R5 fence — validate a claimed fair-violation lasso before it may
/// publish.
///
/// On top of the structural + accepting-state replay from
/// [`replay_lasso_f_violation`], the infinitely-repeated cycle must be able
/// to satisfy every fairness constraint, checked at CYCLE granularity (the
/// SCC-level filter is what is being fenced):
/// - weak fairness on `a`: some cycle state does not enable `a`, or some
///   cycle step admits a transition labeled `a`;
/// - strong fairness on `a`: no cycle state enables `a`, or some cycle step
///   admits `a`;
/// - unconditional fairness on `a`: some cycle step admits `a`.
///
/// "Admits" is existential over the event labeling of the step (the trace
/// carries states only); across infinitely many cycle iterations each
/// admitting step can be labeled with the required action infinitely often,
/// so an existential witness per constraint suffices for a fair labeling.
fn validate_fair_lasso(
    sm: &StateMachine,
    accepting: &FxHashSet<StateId>,
    fairness: &[FairnessConstraint],
    lasso_trace: &[StateId],
    cycle_start: usize,
) -> Result<(), String> {
    replay_lasso_f_violation(sm, accepting, lasso_trace, cycle_start)?;

    let cycle = &lasso_trace[cycle_start..];
    // The infinitely-repeated steps: consecutive cycle pairs, plus the
    // closing edge when the extractor did not already wrap through the entry,
    // plus the validated self-loop for a single-state cycle.
    let mut steps: Vec<(StateId, StateId)> = cycle.windows(2).map(|w| (w[0], w[1])).collect();
    let first = cycle[0];
    let last = *cycle.last().expect("replay validated a non-empty cycle");
    if first != last {
        steps.push((last, first));
    } else if cycle.len() < 2 {
        steps.push((first, first));
    }

    let enabled = |s: StateId, action: &str| {
        sm.transitions.iter().any(|t| t.from == s && t.event == action)
    };
    let step_admits = |action: &str| {
        steps.iter().any(|&(a, b)| {
            sm.transitions.iter().any(|t| t.from == a && t.to == b && t.event == action)
        })
    };

    for constraint in fairness {
        let action = constraint.action().0.as_str();
        let fair_labeling_exists = match constraint {
            FairnessConstraint::WeakFairness(_) => {
                cycle.iter().any(|&s| !enabled(s, action)) || step_admits(action)
            }
            FairnessConstraint::StrongFairness(_) => {
                cycle.iter().all(|&s| !enabled(s, action)) || step_admits(action)
            }
            FairnessConstraint::Unconditional(_) => step_admits(action),
        };
        if !fair_labeling_exists {
            return Err(format!(
                "cycle cannot satisfy the fairness constraint on action `{action}`: the published \
                 lasso is not a fair counterexample"
            ));
        }
    }

    Ok(())
}

/// Detect starvation: find actions that can be perpetually avoided by an
/// unfair scheduler.
///
/// An action is starved if there exists a reachable cycle where:
/// 1. The action is enabled in at least one state of the cycle.
/// 2. The action is never taken within the cycle.
#[must_use]
pub fn detect_starvation(sm: &StateMachine) -> Vec<StarvationWitness> {
    if sm.states.is_empty() || sm.transitions.is_empty() {
        return Vec::new();
    }

    let adj = build_adjacency(sm);
    let reachable = reachable_set(sm.initial, &adj);
    let sccs = tarjan_scc(&reachable, &adj);

    // For each state, which events are enabled
    let mut state_events: FxHashMap<StateId, FxHashSet<&str>> = FxHashMap::default();
    for t in &sm.transitions {
        state_events.entry(t.from).or_default().insert(t.event.as_str());
    }

    // All event names
    let all_events: FxHashSet<&str> = sm.transitions.iter().map(|t| t.event.as_str()).collect();

    let mut witnesses = Vec::new();

    for event in &all_events {
        for scc in &sccs {
            // Skip trivial SCCs
            if scc.len() == 1 {
                let state = scc[0];
                let has_self_loop = adj.get(&state).is_some_and(|succs| succs.contains(&state));
                if !has_self_loop {
                    continue;
                }
            }

            let scc_set: FxHashSet<StateId> = scc.iter().copied().collect();

            // Is the action enabled in any SCC state?
            let enabled_states: Vec<StateId> = scc
                .iter()
                .filter(|s| state_events.get(s).is_some_and(|evts| evts.contains(event)))
                .copied()
                .collect();

            if enabled_states.is_empty() {
                continue;
            }

            // Is the action taken within the SCC?
            let taken_in_scc = sm.transitions.iter().any(|t| {
                t.event.as_str() == *event && scc_set.contains(&t.from) && scc_set.contains(&t.to)
            });

            if !taken_in_scc {
                witnesses.push(StarvationWitness {
                    action: event.to_string(),
                    enabled_states,
                    avoiding_cycle: scc.clone(),
                });
            }
        }
    }

    // Additionally check for self-loop starvation: a state with a self-loop
    // can starve any other action enabled at that state if the self-loop uses
    // a different event.
    for s in &sm.states {
        if !reachable.contains(&s.id) {
            continue;
        }
        let has_self_loop = adj.get(&s.id).is_some_and(|succs| succs.contains(&s.id));
        if !has_self_loop {
            continue;
        }
        // Events used in self-loops at this state
        let self_loop_events: FxHashSet<&str> = sm
            .transitions
            .iter()
            .filter(|t| t.from == s.id && t.to == s.id)
            .map(|t| t.event.as_str())
            .collect();

        // Events enabled at this state but not in any self-loop
        if let Some(enabled) = state_events.get(&s.id) {
            for &evt in enabled {
                if !self_loop_events.contains(evt) {
                    witnesses.push(StarvationWitness {
                        action: evt.to_string(),
                        enabled_states: vec![s.id],
                        avoiding_cycle: vec![s.id],
                    });
                }
            }
        }
    }

    // Deduplicate by action name (keep first witness per action)
    let mut seen = FxHashSet::default();
    witnesses.retain(|w| seen.insert(w.action.clone()));

    witnesses
}

// ---------------------------------------------------------------------------
// Internal trace-level checking helpers (test-only)
// ---------------------------------------------------------------------------

/// Check weak fairness on a single trace for one action.
#[cfg(test)]
fn check_weak_fairness_trace(
    sm: &StateMachine,
    trace: &Trace,
    action: &str,
) -> Option<FairnessViolation> {
    if trace.states.len() < 2 {
        return None;
    }

    // Build enabled-at-state map
    let enabled_at: Vec<bool> = trace
        .states
        .iter()
        .map(|&sid| sm.transitions.iter().any(|t| t.from == sid && t.event == action))
        .collect();

    // Build taken-at-step map (step i = transition from states[i] to states[i+1])
    let taken_at: Vec<bool> = (0..trace.states.len().saturating_sub(1))
        .map(|i| {
            let from = trace.states[i];
            let to = trace.states[i + 1];
            sm.transitions.iter().any(|t| t.from == from && t.to == to && t.event == action)
        })
        .collect();

    // Find the longest suffix where the action is continuously enabled but
    // never taken.
    let mut suffix_start = None;
    for start in 0..trace.states.len() {
        let continuously_enabled = enabled_at[start..].iter().all(|&e| e);
        if !continuously_enabled {
            continue;
        }
        let never_taken = taken_at[start..].iter().all(|&t| !t);
        if never_taken {
            suffix_start = Some(start);
            break;
        }
    }

    suffix_start.map(|idx| FairnessViolation::WeakViolation {
        action: action.to_string(),
        enabled_from_index: idx,
    })
}

/// Check strong fairness on a single trace for one action.
#[cfg(test)]
fn check_strong_fairness_trace(
    sm: &StateMachine,
    trace: &Trace,
    action: &str,
) -> Option<FairnessViolation> {
    if trace.states.len() < 2 {
        return None;
    }

    let enabled_indices: Vec<usize> = trace
        .states
        .iter()
        .enumerate()
        .filter(|&(_, &sid)| sm.transitions.iter().any(|t| t.from == sid && t.event == action))
        .map(|(i, _)| i)
        .collect();

    if enabled_indices.len() < 2 {
        return None;
    }

    // Check if the action was ever taken
    let ever_taken = (0..trace.states.len().saturating_sub(1)).any(|i| {
        let from = trace.states[i];
        let to = trace.states[i + 1];
        sm.transitions.iter().any(|t| t.from == from && t.to == to && t.event == action)
    });

    if !ever_taken {
        Some(FairnessViolation::StrongViolation {
            action: action.to_string(),
            enabled_at_indices: enabled_indices,
        })
    } else {
        None
    }
}

/// Check unconditional fairness on a trace for one action.
#[cfg(test)]
fn check_unconditional_trace(
    trace: &Trace,
    sm: &StateMachine,
    action: &str,
) -> Option<FairnessViolation> {
    if trace.states.len() < 2 {
        return Some(FairnessViolation::UnconditionalViolation {
            action: action.to_string(),
            taken_count: 0,
        });
    }

    let taken_count = (0..trace.states.len().saturating_sub(1))
        .filter(|&i| {
            let from = trace.states[i];
            let to = trace.states[i + 1];
            sm.transitions.iter().any(|t| t.from == from && t.to == to && t.event == action)
        })
        .count();

    if taken_count == 0 {
        Some(FairnessViolation::UnconditionalViolation {
            action: action.to_string(),
            taken_count: 0,
        })
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Internal graph helpers (duplicated from liveness.rs to avoid coupling)
// ---------------------------------------------------------------------------

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

    let mut sorted_states: Vec<StateId> = states.iter().copied().collect();
    sorted_states.sort();

    for &v in &sorted_states {
        if !ts.index.contains_key(&v) {
            strongconnect(v, states, adj, &mut ts);
        }
    }

    ts.sccs
}

struct Lasso {
    trace: Vec<StateId>,
    cycle_start: usize,
}

fn build_lasso(initial: StateId, scc: &[StateId], adj: &FxHashMap<StateId, Vec<StateId>>) -> Lasso {
    let scc_set: FxHashSet<StateId> = scc.iter().copied().collect();
    let scc_entry = scc[0];

    let prefix = bfs_path(initial, scc_entry, adj);
    let cycle = find_cycle_in_scc(scc_entry, &scc_set, adj);

    let cycle_start = prefix.len();
    let mut trace = prefix;
    trace.extend_from_slice(&cycle);

    Lasso { trace, cycle_start }
}

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

fn find_cycle_in_scc(
    entry: StateId,
    scc_set: &FxHashSet<StateId>,
    adj: &FxHashMap<StateId, Vec<StateId>>,
) -> Vec<StateId> {
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

    vec![entry, entry]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{State, StateMachineBuilder, Transition};

    // ---- FairnessConstraint ----

    #[test]
    fn test_fairness_constraint_action() {
        let wf = FairnessConstraint::WeakFairness(Action::new("send"));
        assert_eq!(wf.action().0, "send");
        assert!(wf.is_weak());
        assert!(!wf.is_strong());

        let sf = FairnessConstraint::StrongFairness(Action::new("recv"));
        assert_eq!(sf.action().0, "recv");
        assert!(sf.is_strong());

        let uf = FairnessConstraint::Unconditional(Action::new("tick"));
        assert_eq!(uf.action().0, "tick");
        assert!(uf.is_unconditional());
    }

    // ---- generate_fair_schedule ----

    #[test]
    fn test_fair_schedule_basic() {
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        let fairness = vec![FairnessConstraint::WeakFairness(Action::new("go"))];
        let schedule = generate_fair_schedule(&sm, &fairness, 4);
        assert!(schedule.is_some());

        let schedule = schedule.unwrap();
        assert!(!schedule.steps.is_empty());
        assert!(schedule.steps.len() <= 4);
    }

    #[test]
    fn test_fair_schedule_no_transitions() {
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Lonely"))
            .build();

        let schedule = generate_fair_schedule(&sm, &[], 10);
        assert!(schedule.is_none());
    }

    #[test]
    fn test_fair_schedule_round_robin() {
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Hub"))
            .add_state(State::new(StateId(1), "Left"))
            .add_state(State::new(StateId(2), "Right"))
            .add_transition(Transition::new(StateId(0), StateId(1), "left"))
            .add_transition(Transition::new(StateId(0), StateId(2), "right"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .add_transition(Transition::new(StateId(2), StateId(0), "back"))
            .build();

        let fairness = vec![
            FairnessConstraint::WeakFairness(Action::new("left")),
            FairnessConstraint::WeakFairness(Action::new("right")),
        ];
        let schedule = generate_fair_schedule(&sm, &fairness, 6);
        assert!(schedule.is_some());

        let schedule = schedule.unwrap();
        let events: Vec<&str> = schedule.steps.iter().map(|s| s.event.as_str()).collect();
        assert!(events.contains(&"left") || events.contains(&"right"));
    }

    // ---- check_under_fairness ----

    #[test]
    fn test_under_fairness_filters_unfair_cycle() {
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A").with_label("a"))
            .add_state(State::new(StateId(1), "B").with_label("goal"))
            .add_transition(Transition::new(StateId(0), StateId(0), "spin"))
            .add_transition(Transition::new(StateId(0), StateId(1), "escape"))
            .build();

        let prop = LivenessProperty::new("reach_goal", "goal");

        let result_no_fair = crate::liveness::check_liveness(&sm, &prop);
        assert!(!result_no_fair.is_satisfied());

        let fairness = vec![FairnessConstraint::WeakFairness(Action::new("escape"))];
        // R5 fence: previously `Satisfied` (the spin cycle is filtered as
        // unfair at SCC granularity). SCC-granularity filtering is
        // sub-cycle-blind — an unsound-positive shape — so the positive is
        // demoted; this now pins the fence.
        let result_fair = check_under_fairness(&sm, &prop, &fairness);
        assert_eq!(
            result_fair,
            LivenessResult::Unknown { reason: FAIRNESS_POSITIVE_FENCE_REASON.to_string() }
        );
    }

    #[test]
    fn test_under_fairness_genuine_violation_passes_filter() {
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A").with_label("a"))
            .add_state(State::new(StateId(1), "B").with_label("b"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        let prop = LivenessProperty::new("reach_goal", "goal");
        let fairness = vec![FairnessConstraint::WeakFairness(Action::new("go"))];
        let result = check_under_fairness(&sm, &prop, &fairness);
        assert!(!result.is_satisfied());
    }

    #[test]
    fn test_under_strong_fairness_filters_cycle() {
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A").with_label("a"))
            .add_state(State::new(StateId(1), "B").with_label("goal"))
            .add_transition(Transition::new(StateId(0), StateId(0), "spin"))
            .add_transition(Transition::new(StateId(0), StateId(1), "escape"))
            .build();

        let prop = LivenessProperty::new("reach_goal", "goal");
        let fairness = vec![FairnessConstraint::StrongFairness(Action::new("escape"))];
        // R5 fence: previously `Satisfied` via the SCC-granularity strong-
        // fairness filter (the sub-cycle-blind unsound-positive shape); the
        // positive is demoted and this pins the fence.
        let result = check_under_fairness(&sm, &prop, &fairness);
        assert_eq!(
            result,
            LivenessResult::Unknown { reason: FAIRNESS_POSITIVE_FENCE_REASON.to_string() }
        );
    }

    #[test]
    fn fence_demotes_sf_sub_cycle_escape_positive() {
        // Blueprint S2 anti-fixture "SF sub-cycle escape": A <-> B <-> C with
        // `exit` enabled only at C (leading to the accepting D). Under strong
        // fairness on `exit`, the SCC-level filter discards the WHOLE SCC
        // {A,B,C} as unfair (`exit` enabled somewhere, never taken inside) and
        // the pre-fence checker returned `Satisfied` — an UNSOUND POSITIVE:
        // the sub-cycle A <-> B never enables `exit`, so it is a perfectly
        // fair infinite path that never reaches the goal. The fence pins the
        // demotion.
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A").with_label("a"))
            .add_state(State::new(StateId(1), "B").with_label("b"))
            .add_state(State::new(StateId(2), "C").with_label("c"))
            .add_state(State::new(StateId(3), "D").with_label("goal"))
            .add_transition(Transition::new(StateId(0), StateId(1), "ab"))
            .add_transition(Transition::new(StateId(1), StateId(0), "ba"))
            .add_transition(Transition::new(StateId(1), StateId(2), "bc"))
            .add_transition(Transition::new(StateId(2), StateId(1), "cb"))
            .add_transition(Transition::new(StateId(2), StateId(3), "exit"))
            .build();

        let prop = LivenessProperty::new("reach_goal", "goal");
        let fairness = vec![FairnessConstraint::StrongFairness(Action::new("exit"))];
        let result = check_under_fairness(&sm, &prop, &fairness);
        assert_eq!(
            result,
            LivenessResult::Unknown { reason: FAIRNESS_POSITIVE_FENCE_REASON.to_string() },
            "the SF sub-cycle-escape unsound positive must be fenced, never Satisfied"
        );
    }

    #[test]
    fn test_under_fairness_empty_constraints_same_as_plain() {
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A").with_label("a"))
            .add_state(State::new(StateId(1), "B").with_label("b"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        let prop = LivenessProperty::new("reach_goal", "goal");
        let result = check_under_fairness(&sm, &prop, &[]);
        assert!(!result.is_satisfied());
    }

    // ---- detect_starvation ----

    #[test]
    fn test_starvation_detected() {
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(0), "fast"))
            .add_transition(Transition::new(StateId(0), StateId(1), "slow"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        let witnesses = detect_starvation(&sm);
        let starved_actions: Vec<&str> = witnesses.iter().map(|w| w.action.as_str()).collect();
        assert!(starved_actions.contains(&"slow"));
    }

    #[test]
    fn test_no_starvation_single_action_per_state() {
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_state(State::new(StateId(2), "C"))
            .add_transition(Transition::new(StateId(0), StateId(1), "step1"))
            .add_transition(Transition::new(StateId(1), StateId(2), "step2"))
            .build();

        let witnesses = detect_starvation(&sm);
        assert!(witnesses.is_empty());
    }

    #[test]
    fn test_starvation_empty_machine() {
        let sm =
            StateMachineBuilder::new(StateId(0)).add_state(State::new(StateId(0), "A")).build();

        let witnesses = detect_starvation(&sm);
        assert!(witnesses.is_empty());
    }

    #[test]
    fn test_starvation_all_actions_in_cycle() {
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        let witnesses = detect_starvation(&sm);
        assert!(witnesses.is_empty());
    }

    // ---- FairnessChecker ----

    #[test]
    fn test_fairness_checker_check_trace_no_violations() {
        // Trace: A -> B, action "go" is taken and trace ends at B where
        // "go" is not enabled, so no suffix violation.
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        let checker =
            FairnessChecker::new(sm, vec![FairnessConstraint::WeakFairness(Action::new("go"))]);

        // Trace ends at B where "go" is not enabled => no weak fairness violation
        let trace = Trace::new(vec![StateId(0), StateId(1)]);
        let violations = checker.check_trace(&trace);
        assert!(violations.is_empty());
    }

    #[test]
    fn test_fairness_checker_weak_violation_on_trace() {
        // Trace stays at A (spin) but "escape" is always enabled and never taken
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(0), "spin"))
            .add_transition(Transition::new(StateId(0), StateId(1), "escape"))
            .build();

        let checker =
            FairnessChecker::new(sm, vec![FairnessConstraint::WeakFairness(Action::new("escape"))]);

        // Trace: A -> A -> A (spin self-loop, escape never taken)
        let trace = Trace::new(vec![StateId(0), StateId(0), StateId(0)]);
        let violations = checker.check_trace(&trace);
        assert_eq!(violations.len(), 1);
        assert_eq!(violations[0].action(), "escape");
        assert!(matches!(
            &violations[0],
            FairnessViolation::WeakViolation { enabled_from_index: 0, .. }
        ));
    }

    #[test]
    fn test_fairness_checker_strong_violation_on_trace() {
        // Action "escape" is enabled at multiple points but never taken
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(0), "spin"))
            .add_transition(Transition::new(StateId(0), StateId(1), "escape"))
            .build();

        let checker = FairnessChecker::new(
            sm,
            vec![FairnessConstraint::StrongFairness(Action::new("escape"))],
        );

        let trace = Trace::new(vec![StateId(0), StateId(0), StateId(0), StateId(0)]);
        let violations = checker.check_trace(&trace);
        assert_eq!(violations.len(), 1);
        assert!(matches!(
            &violations[0],
            FairnessViolation::StrongViolation { action, enabled_at_indices }
                if action == "escape" && enabled_at_indices.len() == 4
        ));
    }

    #[test]
    fn test_fairness_checker_unconditional_violation() {
        // Action "tick" never appears in the trace
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        let checker =
            FairnessChecker::new(sm, vec![FairnessConstraint::Unconditional(Action::new("tick"))]);

        let trace = Trace::new(vec![StateId(0), StateId(1), StateId(0)]);
        let violations = checker.check_trace(&trace);
        assert_eq!(violations.len(), 1);
        assert!(matches!(
            &violations[0],
            FairnessViolation::UnconditionalViolation { action, taken_count: 0 }
                if action == "tick"
        ));
    }

    // ---- annotate_trace ----

    #[test]
    fn test_annotate_trace_marks_relevant_steps() {
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_state(State::new(StateId(2), "C"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .add_transition(Transition::new(StateId(1), StateId(2), "finish"))
            .build();

        let constraints = vec![FairnessConstraint::WeakFairness(Action::new("go"))];
        let trace = Trace::new(vec![StateId(0), StateId(1), StateId(2)]);
        let annotated = annotate_trace(&sm, &trace, &constraints);

        assert_eq!(annotated.annotations.len(), 3);

        // Step 0: "go" is enabled and taken => fairness_relevant
        assert!(annotated.annotations[0].fairness_relevant);
        assert!(annotated.annotations[0].enabled_actions.contains(&"go".to_string()));
        assert_eq!(annotated.annotations[0].taken_action.as_deref(), Some("go"));

        // Step 1: "finish" is enabled, "go" is not => not fairness_relevant
        assert!(!annotated.annotations[1].fairness_relevant);

        // Step 2: terminal, no outgoing => not fairness_relevant
        assert!(!annotated.annotations[2].fairness_relevant);
    }

    #[test]
    fn test_annotate_trace_empty() {
        let sm =
            StateMachineBuilder::new(StateId(0)).add_state(State::new(StateId(0), "A")).build();

        let trace = Trace::new(vec![]);
        let annotated = annotate_trace(&sm, &trace, &[]);
        assert!(annotated.annotations.is_empty());
    }

    // ---- check_weak_fairness / check_strong_fairness standalone ----

    #[test]
    fn test_check_weak_fairness_standalone_satisfied() {
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        // Trace takes "go", so weak fairness on "go" is satisfied
        let trace = Trace::new(vec![StateId(0), StateId(1)]);
        let result = check_weak_fairness(&sm, &trace, "go");
        assert!(result.is_none());
    }

    #[test]
    fn test_check_strong_fairness_standalone_violated() {
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(0), "spin"))
            .add_transition(Transition::new(StateId(0), StateId(1), "escape"))
            .build();

        // escape enabled repeatedly but never taken
        let trace = Trace::new(vec![StateId(0), StateId(0), StateId(0)]);
        let result = check_strong_fairness(&sm, &trace, "escape");
        assert!(result.is_some());
        assert_eq!(result.unwrap().action(), "escape");
    }

    // ---- Unconditional fairness in SCC check ----

    #[test]
    fn test_unconditional_fairness_filters_cycle() {
        // Cycle A->B->A avoids "tick" entirely. With unconditional fairness
        // on "tick", the cycle is unfair and should be filtered.
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A").with_label("a"))
            .add_state(State::new(StateId(1), "B").with_label("b"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        let prop = LivenessProperty::new("reach_goal", "goal");
        // Without unconditional fairness: violated
        let result_no = check_under_fairness(&sm, &prop, &[]);
        assert!(!result_no.is_satisfied());

        // With unconditional fairness on "tick" (not in cycle): the cycle is
        // filtered as unfair at SCC granularity.
        // R5 fence: previously `Satisfied`; the positive is demoted and this
        // pins the fence (sub-cycle-blind filter shape).
        let fairness = vec![FairnessConstraint::Unconditional(Action::new("tick"))];
        let result = check_under_fairness(&sm, &prop, &fairness);
        assert_eq!(
            result,
            LivenessResult::Unknown { reason: FAIRNESS_POSITIVE_FENCE_REASON.to_string() }
        );
    }

    // ---- FairnessChecker integration ----

    #[test]
    fn test_fairness_checker_liveness_integration() {
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A").with_label("a"))
            .add_state(State::new(StateId(1), "B").with_label("goal"))
            .add_transition(Transition::new(StateId(0), StateId(0), "spin"))
            .add_transition(Transition::new(StateId(0), StateId(1), "escape"))
            .build();

        let checker =
            FairnessChecker::new(sm, vec![FairnessConstraint::WeakFairness(Action::new("escape"))]);

        let prop = LivenessProperty::new("reach_goal", "goal");
        // R5 fence: previously `Satisfied` through the same SCC-granularity
        // filter; the positive is demoted and this pins the fence.
        let result = checker.check_liveness(&prop);
        assert_eq!(
            result,
            LivenessResult::Unknown { reason: FAIRNESS_POSITIVE_FENCE_REASON.to_string() }
        );
    }

    #[test]
    fn test_fairness_checker_detect_starvation_integration() {
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(0), "fast"))
            .add_transition(Transition::new(StateId(0), StateId(1), "slow"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        let checker =
            FairnessChecker::new(sm, vec![FairnessConstraint::StrongFairness(Action::new("slow"))]);

        let witnesses = checker.detect_starvation();
        let starved: Vec<&str> = witnesses.iter().map(|w| w.action.as_str()).collect();
        assert!(starved.contains(&"slow"));
    }

    #[test]
    fn test_fairness_violation_action_accessor() {
        let wv =
            FairnessViolation::WeakViolation { action: "send".to_string(), enabled_from_index: 3 };
        assert_eq!(wv.action(), "send");

        let sv = FairnessViolation::StrongViolation {
            action: "recv".to_string(),
            enabled_at_indices: vec![0, 2, 4],
        };
        assert_eq!(sv.action(), "recv");

        let uv = FairnessViolation::UnconditionalViolation {
            action: "tick".to_string(),
            taken_count: 0,
        };
        assert_eq!(uv.action(), "tick");
    }
}
