// trust-router/ty_backend.rs: Temporal model-checking backend using tla-mc-core
//
// Bridges trust-temporal::StateMachine to tla_mc_core::TransitionSystem and
// dispatches temporal VCs to the generic BFS model checker.
//
// Wired CTL/LTL/liveness/fairness via trust-temporal infrastructure.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use tla_mc_core::{NoopObserver, explore_bfs};
use trust_temporal::ctl::{CtlModelChecker, parse_ctl};
use trust_temporal::fairness::{
    Action, FairnessConstraint as TemporalFairnessConstraint, check_under_fairness,
};
use trust_temporal::liveness::{self, LivenessProperty as TemporalLivenessProp};
use trust_temporal::ltl::parse_ltl;
pub(crate) use trust_temporal::ty_bridge::StateMachineAdapter;
// Re-export the adapter from trust-temporal's ty_bridge module.
use trust_temporal::{State, StateId, StateMachine, Transition};
use trust_types::*;

use crate::{BackendRole, VerificationBackend};

// ---------------------------------------------------------------------------
// Trust: R5 checker fence (2026-07-18 R5 temporal-lane blueprint, slice S2).
// The in-process liveness/fairness lanes are fenced, not repaired; the CTL
// safety lane (`check_temporal`, the only lane with a production VC producer
// — the mmap safety machine from trust-vcgen's sep_engine) is untouched.
// ---------------------------------------------------------------------------

/// Trust: R5 fence — the liveness lowering at [`TyBackend::check_liveness`]
/// historically dropped `LivenessProperty::operator` and `::consequent`: a
/// `P ~> Q` property was checked as bare `eventually P` and never inspected
/// Q, so whatever was verified was NOT the user's property. Until the
/// post-R5 repair, any property shape the lowering cannot represent
/// faithfully is demoted to Unknown with this reason before dispatch.
pub const TY_TEMPORAL_LOWERING_FENCE_REASON: &str =
    "ty_backend temporal lowering fenced: operator/consequent dropped pending R5";

/// Trust: R5 fence — the fairness lane's verdicts come from SCC-granularity
/// starvation analysis plus a synthetic liveness property that conflates
/// action (transition-event) names with state labels; its positives are
/// unsound and its counterexamples are SCC state-sets, not replayable
/// traces. All fairness-constraint verdicts are demoted pending R5.
pub const TY_FAIRNESS_FENCE_REASON: &str = "ty_backend fairness lane fenced: SCC-granularity \
     starvation analysis with an action-name/state-label-conflating synthetic property pending R5";

/// Choose between ExhaustiveFinite and bounded ProofStrength
/// based on whether the state space exploration was complete.
///
/// When BFS/DFS fully explores all reachable states (complete=true), the
/// result is an exhaustive finite-state check. When exploration is bounded
/// (e.g., depth limit, state limit), it's a bounded model check.
fn ty_proof_strength(states: u64, complete: bool) -> ProofStrength {
    if complete {
        ProofStrength {
            reasoning: ReasoningKind::ExplicitStateModel,
            assurance: AssuranceLevel::Sound,
        }
    } else {
        ProofStrength::bounded(states)
    }
}

/// Trust: Temporal verification backend powered by tla_mc_core::explore_bfs.
///
/// Handles VcKind::DeadState, VcKind::Deadlock, VcKind::Temporal, VcKind::Liveness,
/// and VcKind::Fairness. When a StateMachine is available (via `verify_with_machine`
/// or `StateMachineMetadata`), the backend explores the state space and checks
/// the property using trust-temporal's CTL/LTL/liveness/fairness infrastructure.
/// Convert serialized metadata into the single-initial-state representation
/// consumed by `trust-temporal`.
///
/// `StateMachineMetadata` historically exposed a vector of initial states even
/// though every in-process temporal checker accepts exactly one. Silently
/// selecting the first entry (or defaulting an empty vector to state zero)
/// under-approximates the reachable state space and can turn a counterexample
/// reachable from another initial state into a false proof. Reject every shape
/// that cannot be represented exactly, including dangling state references.
pub(crate) fn metadata_to_state_machine(md: &StateMachineMetadata) -> Result<StateMachine, String> {
    let initial = match md.init_states.as_slice() {
        [initial] => *initial,
        [] => {
            return Err("StateMachineMetadata must contain exactly one initial state; found none"
                .to_string());
        }
        initial_states => {
            return Err(format!(
                "StateMachineMetadata must contain exactly one initial state; found {}",
                initial_states.len()
            ));
        }
    };
    if initial >= md.states.len() {
        return Err(format!(
            "StateMachineMetadata initial state index {initial} is out of range for {} state(s)",
            md.states.len()
        ));
    }
    for (from, _, to) in &md.transitions {
        if *from >= md.states.len() || *to >= md.states.len() {
            return Err(format!(
                "StateMachineMetadata transition {from} -> {to} references a state outside 0..{}",
                md.states.len()
            ));
        }
    }
    // Snapshotting FxHashMap keys triggers rustc's query-instability lint even
    // though no iteration order escapes: sort before validation or diagnostics.
    #[allow(rustc::potential_query_instability)]
    // The Fx map's raw order never reaches a verdict or diagnostic: normalize
    // it before selecting the first invalid key.
    #[allow(rustc::potential_query_instability)]
    let mut label_states: Vec<_> = md.labels.keys().copied().collect();
    label_states.sort_unstable();
    for state in label_states {
        if state >= md.states.len() {
            return Err(format!(
                "StateMachineMetadata labels reference state {state} outside 0..{}",
                md.states.len()
            ));
        }
    }

    let initial = StateId(initial);
    let mut machine = StateMachine::new(initial);
    for (idx, name) in md.states.iter().enumerate() {
        let mut state = State::new(StateId(idx), name.clone());
        if let Some(labels) = md.labels.get(&idx) {
            for label in labels {
                state = state.with_label(label.clone());
            }
        }
        machine.add_state(state);
    }
    for (from, event, to) in &md.transitions {
        machine.add_transition(Transition::new(StateId(*from), StateId(*to), event.clone()));
    }
    Ok(machine)
}

/// Trust: true only when BFS provably explored the machine's full reachable
/// state space. Failed or truncated exploration ⇒ false, so callers stamp
/// `BoundedSound` (below the full lane's `Sound` floor) instead of a spurious
/// exhaustive claim. Shared by the CTL, liveness, and fairness Proved paths.
fn machine_exploration_complete(machine: &StateMachine) -> bool {
    let adapter = StateMachineAdapter::new(machine.clone());
    let mut observer = NoopObserver::<StateMachineAdapter>::default();
    match explore_bfs(&adapter, &mut observer) {
        Ok(outcome) => outcome.completed,
        Err(_) => false,
    }
}

pub struct TyBackend;

impl TyBackend {
    /// Trust: Extract a StateMachine from VC metadata.
    ///
    /// Attempts to extract a `trust_temporal::StateMachine` from the VC's
    /// `StateMachineMetadata`. Returns None if no metadata is present.
    fn extract_state_machine(vc: &VerificationCondition) -> Result<Option<StateMachine>, String> {
        // Temporal and liveness VCs may carry `StateMachineMetadata` on their
        // variants. Convert it once at this boundary so malformed or ambiguous
        // transport stays fail-closed instead of reaching a model checker with
        // an under-approximated graph.
        let md = match &vc.kind {
            VcKind::Temporal { machine: Some(md), .. }
            | VcKind::Liveness { machine: Some(md), .. } => md,
            _ => return Ok(None),
        };
        metadata_to_state_machine(md).map(Some)
    }

    /// Trust: Run BFS exploration on a StateMachine and check for deadlocks.
    ///
    /// Returns Proved if the exploration completes with no deadlock states
    /// (i.e., every reachable state has at least one successor). Returns
    /// Failed if a deadlock state is found.
    fn check_deadlock(machine: &StateMachine) -> VerificationResult {
        let adapter = StateMachineAdapter::new(machine.clone());
        let mut observer = NoopObserver::<StateMachineAdapter>::default();

        match explore_bfs(&adapter, &mut observer) {
            Ok(outcome) => {
                // Check every discovered state for deadlock (no outgoing transitions)
                let reachable = machine.reachable_states(outcome.states_discovered);
                let deadlocked: Vec<_> =
                    reachable.iter().filter(|id| machine.is_deadlock_state(**id)).collect();

                if deadlocked.is_empty() {
                    VerificationResult::Proved {
                        solver: "ty".into(),
                        time_ms: 0,
                        // ExplicitStateModel when BFS is complete
                        strength: ty_proof_strength(
                            outcome.states_discovered as u64,
                            outcome.completed,
                        ),
                        proof_certificate: None,
                        solver_warnings: None,
                        native_proof_envelope: None,
                    }
                } else {
                    // Encode deadlocked state IDs as counterexample assignments
                    let assignments: Vec<_> = deadlocked
                        .iter()
                        .enumerate()
                        .map(|(i, id)| {
                            (format!("deadlock_state_{i}"), CounterexampleValue::Int(id.0 as i128))
                        })
                        .collect();
                    VerificationResult::Failed {
                        solver: "ty".into(),
                        time_ms: 0,
                        counterexample: Some(Counterexample::new(assignments)),
                    }
                }
            }
            Err(e) => VerificationResult::Unknown {
                solver: "ty".into(),
                time_ms: 0,
                reason: format!("BFS exploration failed: {e}"),
            },
        }
    }

    /// Trust: Run BFS and check whether a named dead-state is reachable.
    fn check_dead_state(machine: &StateMachine, state_name: &str) -> VerificationResult {
        let adapter = StateMachineAdapter::new(machine.clone());
        let mut observer = NoopObserver::<StateMachineAdapter>::default();

        match explore_bfs(&adapter, &mut observer) {
            Ok(outcome) => {
                let reachable = machine.reachable_states(outcome.states_discovered);
                let found = reachable.iter().any(|id| {
                    machine.state(*id).is_some_and(|s| {
                        s.name == state_name || s.labels.contains(&state_name.to_string())
                    })
                });

                if found {
                    VerificationResult::Failed {
                        solver: "ty".into(),
                        time_ms: 0,
                        counterexample: Some(Counterexample::new(vec![(
                            "dead_state_reachable".to_string(),
                            CounterexampleValue::Bool(true),
                        )])),
                    }
                } else {
                    VerificationResult::Proved {
                        solver: "ty".into(),
                        time_ms: 0,
                        // ExplicitStateModel when BFS is complete
                        strength: ty_proof_strength(
                            outcome.states_discovered as u64,
                            outcome.completed,
                        ),
                        proof_certificate: None,
                        solver_warnings: None,
                        native_proof_envelope: None,
                    }
                }
            }
            Err(e) => VerificationResult::Unknown {
                solver: "ty".into(),
                time_ms: 0,
                reason: format!("BFS exploration failed: {e}"),
            },
        }
    }

    /// Trust: Check a CTL temporal property against a StateMachine.
    ///
    /// Parses the property string as a CTL formula and runs the labeling
    /// algorithm. Returns Proved if the initial state satisfies the formula,
    /// Failed with a counterexample path otherwise.
    fn check_temporal(machine: &StateMachine, property: &str) -> VerificationResult {
        let formula = match parse_ctl(property) {
            Ok(f) => f,
            Err(e) => {
                // Trust: Fall back to LTL parsing if CTL parse fails
                match parse_ltl(property) {
                    Ok(_ltl_formula) => {
                        // Trust: LTL property detected. Convert to equivalent CTL check
                        // where possible (G phi -> AG phi, F phi -> EF phi).
                        // For full LTL, use VcKind::Liveness.
                        return VerificationResult::Unknown {
                            solver: "ty".into(),
                            time_ms: 0,
                            reason: format!(
                                "property `{property}` parses as LTL but not CTL; \
                                 use VcKind::Liveness for LTL checking (CTL parse error: {e})"
                            ),
                        };
                    }
                    Err(_) => {
                        return VerificationResult::Unknown {
                            solver: "ty".into(),
                            time_ms: 0,
                            reason: format!(
                                "failed to parse temporal property `{property}` as CTL: {e}"
                            ),
                        };
                    }
                }
            }
        };

        let checker = CtlModelChecker::new(machine);
        let result = checker.check(&formula);

        if result.holds_at_initial(machine.initial) {
            // CTL labeling is exhaustive ONLY over a COMPLETE
            // state machine. The previous `true` was hardcoded — a universal
            // property (e.g. `AG p`) over a bounded/truncated machine would
            // spuriously hold (the violating state was never explored) yet be
            // stamped `Sound` and pass the report floor. Determine completeness
            // the same way check_deadlock/check_dead_state do — via explore_bfs —
            // so an under-explored machine yields `BoundedSound` (below floor),
            // never a false `Sound` proof. Failed exploration => not provably
            // complete => fail closed to bounded.
            let complete = machine_exploration_complete(machine);
            VerificationResult::Proved {
                solver: "ty".into(),
                time_ms: 0,
                strength: ty_proof_strength(machine.states.len() as u64, complete),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            }
        } else {
            // Trust: Build counterexample from witness trace if available.
            // Carry the actual state id at each step (the state SEQUENCE is
            // the counterexample); consumers resolve names via the machine.
            let counterexample = result.witness.map(|trace| {
                let assignments: Vec<_> = trace
                    .states
                    .iter()
                    .enumerate()
                    .map(|(i, sid)| {
                        let state_name = machine
                            .state(*sid)
                            .map_or_else(|| format!("state_{}", sid.0), |s| s.name.clone());
                        (format!("step_{i}_{state_name}"), CounterexampleValue::Int(sid.0 as i128))
                    })
                    .collect();
                Counterexample::new(assignments)
            });
            VerificationResult::Failed { solver: "ty".into(), time_ms: 0, counterexample }
        }
    }

    /// Trust: Check a liveness property against a StateMachine.
    ///
    /// Uses trust-temporal's SCC-based liveness checking.
    ///
    /// Trust: R5 fence — the lowering below builds a bare
    /// `eventually {predicate}` property, discarding `property.operator` and
    /// `property.consequent`. For any shape that discard does not represent
    /// faithfully (`P ~> Q`, `[]P`, or any property with a consequent) the VC
    /// is demoted to Unknown BEFORE dispatch: verifying the wrong property
    /// can neither prove nor refute the user's property. For the faithful
    /// shapes (`<>P` / `[]<>P`, no consequent) the fenced trust-temporal
    /// checker never returns a positive, and a `Violated` arrives only after
    /// in-process lasso replay, so `Failed` still publishes with a validated
    /// trace.
    fn check_liveness(
        machine: &StateMachine,
        property: &trust_types::LivenessProperty,
    ) -> VerificationResult {
        let faithful_lowering = property.consequent.is_none()
            && matches!(
                property.operator,
                TemporalOperator::Eventually | TemporalOperator::AlwaysEventually
            );
        if !faithful_lowering {
            return VerificationResult::Unknown {
                solver: "ty".into(),
                time_ms: 0,
                reason: format!(
                    "{TY_TEMPORAL_LOWERING_FENCE_REASON} (operator `{}`{} cannot be represented \
                     as the bare `eventually {}` the in-process checker receives)",
                    property.operator.tla_notation(),
                    if property.consequent.is_some() {
                        ", with its consequent dropped,"
                    } else {
                        ""
                    },
                    property.predicate
                ),
            };
        }

        let temporal_prop = TemporalLivenessProp::new(&property.name, &property.predicate);

        // Trust: If fairness constraints are specified, check under fairness
        if !property.fairness.is_empty() {
            let mut temporal_fairness = Vec::with_capacity(property.fairness.len());
            for fc in &property.fairness {
                let temporal_constraint = match fc {
                    trust_types::FairnessConstraint::Weak { action, .. } => {
                        TemporalFairnessConstraint::WeakFairness(Action::new(action.as_str()))
                    }
                    trust_types::FairnessConstraint::Strong { action, .. } => {
                        TemporalFairnessConstraint::StrongFairness(Action::new(action.as_str()))
                    }
                    // non-panicking fallback for #[non_exhaustive] forward compat
                    _ => {
                        return VerificationResult::Unknown {
                            solver: "ty".into(),
                            time_ms: 0,
                            reason: "unhandled variant".to_string(),
                        };
                    }
                };
                temporal_fairness.push(temporal_constraint);
            }

            let result = check_under_fairness(machine, &temporal_prop, &temporal_fairness);
            return Self::liveness_result_to_vr(machine, &result);
        }

        let result = liveness::check_liveness(machine, &temporal_prop);
        Self::liveness_result_to_vr(machine, &result)
    }

    /// Trust: Check fairness constraints against a StateMachine.
    ///
    /// Trust: R5 fence — this lane is fenced whole. Its former `Proved`
    /// verdicts rested on SCC-granularity starvation analysis (sub-cycle
    /// blind) driven through a synthetic `eventually {action}` property that
    /// conflates action (transition-event) names with state LABELS, so even
    /// its check subject was not the user's constraint; and its former
    /// `Failed` published the starvation witness's SCC state-set — not a
    /// replayed trace — so it does not meet the validate-before-publish bar
    /// either. Every fairness-constraint VC is demoted to Unknown with the
    /// named reason pending the post-R5 checker repair. No capability is
    /// invented and none is silently kept: both directions were unsound or
    /// unvalidated.
    fn check_fairness(
        _machine: &StateMachine,
        constraint: &trust_types::FairnessConstraint,
    ) -> VerificationResult {
        let action_name = match constraint {
            trust_types::FairnessConstraint::Weak { action, .. }
            | trust_types::FairnessConstraint::Strong { action, .. } => action.as_str(),
            // non-panicking fallback for #[non_exhaustive] forward compat
            _ => "<unknown action>",
        };
        VerificationResult::Unknown {
            solver: "ty".into(),
            time_ms: 0,
            reason: format!("{TY_FAIRNESS_FENCE_REASON} (constraint on action `{action_name}`)"),
        }
    }

    /// Trust: Convert trust-temporal LivenessResult to VerificationResult.
    fn liveness_result_to_vr(
        machine: &StateMachine,
        result: &trust_temporal::LivenessResult,
    ) -> VerificationResult {
        match result {
            // Trust: R5 fence (belt over the trust-temporal fence, which no
            // longer emits `Satisfied` at all): a positive from the
            // in-process SCC-level liveness/fairness analysis is an
            // unsound-positive shape and must never mint `Proved`.
            trust_temporal::LivenessResult::Satisfied => VerificationResult::Unknown {
                solver: "ty".into(),
                time_ms: 0,
                reason: liveness::LIVENESS_POSITIVE_FENCE_REASON.to_string(),
            },
            trust_temporal::LivenessResult::Violated { lasso_trace, cycle_start } => {
                let mut assignments: Vec<_> = lasso_trace
                    .iter()
                    .enumerate()
                    .map(|(i, sid)| {
                        let label = if i < *cycle_start { "prefix" } else { "cycle" };
                        let state_name = machine
                            .state(*sid)
                            .map_or_else(|| format!("state_{}", sid.0), |s| s.name.clone());
                        (
                            format!("{label}_step_{i}_{state_name}"),
                            CounterexampleValue::Int(sid.0 as i128),
                        )
                    })
                    .collect();
                assignments.push((
                    "cycle_start_index".to_string(),
                    CounterexampleValue::Int(*cycle_start as i128),
                ));
                VerificationResult::Failed {
                    solver: "ty".into(),
                    time_ms: 0,
                    counterexample: Some(Counterexample::new(assignments)),
                }
            }
            // Trust: R5 fence — carry the checker's named demotion reason
            // through verbatim (machine-readable fence provenance).
            trust_temporal::LivenessResult::Unknown { reason } => VerificationResult::Unknown {
                solver: "ty".into(),
                time_ms: 0,
                reason: reason.clone(),
            },
            _ => VerificationResult::Unknown {
                solver: "ty".into(),
                time_ms: 0,
                reason: "unexpected liveness result variant".to_string(),
            },
        }
    }

    /// Trust: Verify a VC with an explicit StateMachine.
    ///
    /// This is the primary entry point for temporal verification when the
    /// caller has already extracted a StateMachine. Dispatches to the
    /// appropriate checker based on VcKind.
    #[must_use]
    pub fn verify_with_machine(
        vc: &VerificationCondition,
        machine: &StateMachine,
    ) -> VerificationResult {
        match &vc.kind {
            VcKind::Deadlock => Self::check_deadlock(machine),
            VcKind::DeadState { state } => Self::check_dead_state(machine, state),
            VcKind::Temporal { property, .. } => Self::check_temporal(machine, property),
            VcKind::Liveness { property, .. } => Self::check_liveness(machine, property),
            VcKind::Fairness { constraint } => Self::check_fairness(machine, constraint),
            VcKind::RefinementViolation { spec_file, action } => VerificationResult::Unknown {
                solver: "ty".into(),
                time_ms: 0,
                reason: format!(
                    "refinement checking for spec {spec_file} action {action} not yet implemented"
                ),
            },
            VcKind::ProtocolViolation { protocol, violation } => VerificationResult::Unknown {
                solver: "ty".into(),
                time_ms: 0,
                reason: format!(
                    "protocol violation checking for {protocol}: {violation} not yet implemented"
                ),
            },
            _ => VerificationResult::Unknown {
                solver: "ty".into(),
                time_ms: 0,
                reason: format!("VcKind {:?} not handled by ty backend", vc.kind.description()),
            },
        }
    }
}

impl VerificationBackend for TyBackend {
    fn name(&self) -> &str {
        "ty"
    }

    fn role(&self) -> BackendRole {
        BackendRole::Temporal
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        // Trust: Handle liveness, fairness, refinement, protocol, and
        // termination VCs. NonTermination is a liveness property:
        // "the program eventually terminates" requires Buchi automata /
        // well-founded order checking, not safety model checking (PDR/IC3).
        matches!(
            vc.kind,
            VcKind::DeadState { .. }
                | VcKind::Deadlock
                | VcKind::Temporal { .. }
                | VcKind::Liveness { .. }
                | VcKind::Fairness { .. }
                | VcKind::RefinementViolation { .. }
                | VcKind::ProtocolViolation { .. }
                | VcKind::NonTermination { .. }
        )
    }

    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        if let Some(result) = crate::backend_trait::unsupported_mir_unknown(vc, "ty", 0) {
            return result;
        }

        // Try to extract state machine from VC metadata
        match Self::extract_state_machine(vc) {
            Ok(Some(machine)) => Self::verify_with_machine(vc, &machine),
            Ok(None) => {
                // Trust: Handle refinement/protocol specially (no SM needed for message)
                if let VcKind::RefinementViolation { spec_file, action } = &vc.kind {
                    return VerificationResult::Unknown {
                        solver: "ty".into(),
                        time_ms: 0,
                        reason: format!(
                            "refinement checking for spec {spec_file} action {action} \
                             requires StateMachine metadata; wire via trust-mir-extract"
                        ),
                    };
                }
                VerificationResult::Unknown {
                    solver: "ty".into(),
                    time_ms: 0,
                    reason: "no StateMachine metadata in VC; \
                             use TyBackend::verify_with_machine() or populate metadata \
                             via trust-mir-extract"
                        .to_string(),
                }
            }
            Err(reason) => VerificationResult::Unknown {
                solver: "ty".into(),
                time_ms: 0,
                reason: format!("invalid StateMachine metadata: {reason}"),
            },
        }
    }
}

/// Trust: Convenience function to verify a deadlock-freedom VC directly
/// from a StateMachine, bypassing VC metadata extraction.
///
/// Useful for tests and direct integration before VC metadata wiring
/// is complete.
#[must_use]
pub fn verify_deadlock_freedom(machine: &StateMachine) -> VerificationResult {
    TyBackend::check_deadlock(machine)
}

/// Trust: Convenience function to verify dead-state unreachability directly
/// from a StateMachine.
#[must_use]
pub fn verify_dead_state_unreachable(
    machine: &StateMachine,
    state_name: &str,
) -> VerificationResult {
    TyBackend::check_dead_state(machine, state_name)
}

/// Trust: Convenience function to check a CTL temporal property.
#[must_use]
pub fn verify_temporal_property(machine: &StateMachine, property: &str) -> VerificationResult {
    TyBackend::check_temporal(machine, property)
}

/// Trust: Convenience function to check a liveness property.
#[must_use]
pub fn verify_liveness(
    machine: &StateMachine,
    property: &trust_types::LivenessProperty,
) -> VerificationResult {
    TyBackend::check_liveness(machine, property)
}

/// Trust: Convenience function to check a fairness constraint.
#[must_use]
pub fn verify_fairness(
    machine: &StateMachine,
    constraint: &trust_types::FairnessConstraint,
) -> VerificationResult {
    TyBackend::check_fairness(machine, constraint)
}

#[cfg(test)]
mod tests {
    use tla_mc_core::TransitionSystem;
    use trust_temporal::{
        State, StateId, StateMachineBuilder, Transition, tla_spec_gen as spec_gen,
    };

    use super::*;

    fn serialized_two_state_machine(init_states: Vec<usize>) -> StateMachineMetadata {
        let mut labels = trust_types::fx::FxHashMap::default();
        labels.insert(0, vec!["safe".to_string()]);
        StateMachineMetadata {
            states: vec!["safe-initial".to_string(), "unsafe-initial".to_string()],
            init_states,
            transitions: vec![(0, "stay-safe".to_string(), 0), (1, "stay-unsafe".to_string(), 1)],
            labels,
        }
    }

    fn temporal_vc_with_metadata(md: StateMachineMetadata) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Temporal { property: "AG safe".to_string(), machine: Some(md) },
            function: "metadata_boundary".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    #[test]
    fn metadata_conversion_rejects_missing_initial_state() {
        let error = metadata_to_state_machine(&serialized_two_state_machine(Vec::new()))
            .expect_err("an absent initial state must fail closed");
        assert!(error.contains("exactly one initial state"), "{error}");
    }

    #[test]
    fn metadata_conversion_rejects_out_of_range_initial_state() {
        let error = metadata_to_state_machine(&serialized_two_state_machine(vec![2]))
            .expect_err("a dangling initial state must fail closed");
        assert!(error.contains("out of range"), "{error}");
    }

    #[test]
    fn metadata_conversion_never_ignores_a_second_initial_state() {
        // State zero satisfies AG safe, while state one does not. The old
        // `.first()` conversion explored only state zero and falsely Proved.
        // Until trust-temporal supports a set of initials, ambiguity must be
        // rejected instead of under-approximated.
        let result =
            TyBackend.verify(&temporal_vc_with_metadata(serialized_two_state_machine(vec![0, 1])));
        assert!(
            matches!(result, VerificationResult::Unknown { ref reason, .. }
                if reason.contains("exactly one initial state")),
            "multiple initial states must stay fail-closed, got {result:?}"
        );
    }

    #[test]
    fn ty_handles_temporal_kinds_only() {
        let backend = TyBackend;
        let temporal = VerificationCondition {
            kind: VcKind::Temporal { property: "eventually done".into(), machine: None },
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let l0 = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };

        assert!(backend.can_handle(&temporal));
        assert!(!backend.can_handle(&l0));
    }

    #[test]
    fn temporal_vc_with_carried_machine_is_model_checked() {
        use trust_types::fx::FxHashMap;
        let mut labels: FxHashMap<usize, Vec<String>> = FxHashMap::default();
        labels.insert(1, vec!["done".to_string()]);
        let md = StateMachineMetadata {
            states: vec!["start".into(), "done".into()],
            init_states: vec![0],
            transitions: vec![(0, "go".into(), 1)],
            labels,
        };
        // With a machine carried on the VC, extract_state_machine now returns it
        // and ty MODEL-CHECKS the property (EF done is reachable ⇒ proved) — not
        // the old "no StateMachine metadata" unknown. Closes the producer gap.
        let vc = VerificationCondition {
            kind: VcKind::Temporal { property: "EF done".into(), machine: Some(md) },
            function: "t".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let r = TyBackend.verify(&vc);
        assert!(
            matches!(r, VerificationResult::Proved { .. } | VerificationResult::Failed { .. }),
            "ty must model-check the carried machine, got {r:?}"
        );

        // No carried machine ⇒ stays fail-closed unknown.
        let vc_none = VerificationCondition {
            kind: VcKind::Temporal { property: "EF done".into(), machine: None },
            ..vc
        };
        assert!(
            matches!(TyBackend.verify(&vc_none), VerificationResult::Unknown { .. }),
            "no carried machine must stay fail-closed unknown"
        );
    }

    #[test]
    fn mmap_temporal_model_catches_truncation_proves_under_single_writer() {
        let prop = "AG !bad";
        let temporal = |md: StateMachineMetadata| VerificationCondition {
            kind: VcKind::Temporal { property: prop.into(), machine: Some(md) },
            function: "mmap".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        // Truncatable file (no single-writer invariant): the env can shrink the
        // mapping, so an access-while-stale is reachable ⇒ ty CATCHES the hazard.
        // This is the SOUND result — re-validation would NOT change it (TOCTOU).
        let hazard = TyBackend.verify(&temporal(StateMachineMetadata::mmap_temporal_model(false)));
        assert!(
            matches!(hazard, VerificationResult::Failed { .. }),
            "without single-writer, ty must catch the truncate->stale-access hazard, got {hazard:?}"
        );
        // Single-writer invariant (map_mut's unsafe contract): Truncate disabled,
        // bad state unreachable ⇒ ty PROVES temporal safety.
        let safe = TyBackend.verify(&temporal(StateMachineMetadata::mmap_temporal_model(true)));
        assert!(
            matches!(safe, VerificationResult::Proved { .. }),
            "under single-writer, ty must prove temporal safety, got {safe:?}"
        );
    }

    #[test]
    fn ty_verify_returns_unknown_without_metadata() {
        let backend = TyBackend;
        let vc = VerificationCondition {
            kind: VcKind::Deadlock,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };

        let result = backend.verify(&vc);
        assert!(matches!(result, VerificationResult::Unknown { solver, .. } if solver == "ty"));
    }

    #[test]
    fn ty_handles_refinement_violations() {
        let backend = TyBackend;
        let vc = VerificationCondition {
            kind: VcKind::RefinementViolation {
                spec_file: "Bank.tla".into(),
                action: "overdraft".into(),
            },
            function: "bank_step".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };

        assert!(backend.can_handle(&vc));
        let result = backend.verify(&vc);
        assert!(matches!(result, VerificationResult::Unknown { solver, .. } if solver == "ty"));
    }

    #[test]
    fn adapter_implements_transition_system() {
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Start"))
            .add_state(State::new(StateId(1), "End"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .build();

        let adapter = StateMachineAdapter::new(machine);
        assert_eq!(adapter.initial_states(), vec![0]);
        assert_eq!(adapter.successors(&0), vec![("go".to_string(), 1)]);
        assert!(adapter.successors(&1).is_empty());
        assert_eq!(adapter.fingerprint(&42), 42);
    }

    #[test]
    fn adapter_bfs_explores_full_state_space() {
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_state(State::new(StateId(2), "C"))
            .add_transition(Transition::new(StateId(0), StateId(1), "ab"))
            .add_transition(Transition::new(StateId(1), StateId(2), "bc"))
            .build();

        let adapter = StateMachineAdapter::new(machine);
        let mut observer = NoopObserver::<StateMachineAdapter>::default();
        let outcome = explore_bfs(&adapter, &mut observer).expect("BFS should succeed");

        assert!(outcome.completed);
        assert_eq!(outcome.states_discovered, 3);
    }

    #[test]
    fn verify_deadlock_freedom_proves_on_cycle() {
        // A->B->A cycle: no deadlock states
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "forward"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        let result = verify_deadlock_freedom(&machine);
        assert!(result.is_proved(), "cycle should be deadlock-free: {result:?}");
    }

    #[test]
    fn verify_deadlock_freedom_fails_on_terminal_state() {
        // A->B with B terminal: deadlock
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .build();

        let result = verify_deadlock_freedom(&machine);
        assert!(result.is_failed(), "terminal state should be detected as deadlock: {result:?}");
    }

    #[test]
    fn verify_dead_state_unreachable_proves_when_not_reachable() {
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Start"))
            .add_state(State::new(StateId(1), "OK"))
            .add_state(State::new(StateId(2), "Error").with_label("error"))
            .add_transition(Transition::new(StateId(0), StateId(1), "proceed"))
            .build();

        let result = verify_dead_state_unreachable(&machine, "Error");
        assert!(result.is_proved(), "unreachable Error state should be proved safe: {result:?}");
    }

    #[test]
    fn verify_dead_state_unreachable_fails_when_reachable() {
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Start"))
            .add_state(State::new(StateId(1), "Error").with_label("error"))
            .add_transition(Transition::new(StateId(0), StateId(1), "fail"))
            .build();

        let result = verify_dead_state_unreachable(&machine, "Error");
        assert!(result.is_failed(), "reachable Error state should be detected: {result:?}");
    }

    // Trust: Liveness and fairness backend tests.

    #[test]
    fn ty_handles_liveness_vcs() {
        let backend = TyBackend;
        let liveness_vc = VerificationCondition {
            kind: VcKind::Liveness {
                property: trust_types::LivenessProperty {
                    name: "termination".into(),
                    operator: TemporalOperator::Eventually,
                    predicate: "done".into(),
                    consequent: None,
                    fairness: vec![],
                },
                machine: None,
            },
            function: "async_main".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };

        assert!(backend.can_handle(&liveness_vc));
        let result = backend.verify(&liveness_vc);
        assert!(matches!(result, VerificationResult::Unknown { solver, .. } if solver == "ty"));
    }

    #[test]
    fn ty_handles_fairness_vcs() {
        let backend = TyBackend;
        let fairness_vc = VerificationCondition {
            kind: VcKind::Fairness {
                constraint: trust_types::FairnessConstraint::Weak {
                    action: "schedule".into(),
                    vars: vec!["tasks".into()],
                },
            },
            function: "scheduler".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };

        assert!(backend.can_handle(&fairness_vc));
        let result = backend.verify(&fairness_vc);
        assert_eq!(result.solver_name(), "ty");
    }

    #[test]
    fn ty_rejects_l0_safety_vcs() {
        let backend = TyBackend;
        let safety_kinds = [VcKind::DivisionByZero, VcKind::IndexOutOfBounds, VcKind::Unreachable];
        for kind in safety_kinds {
            let vc = VerificationCondition {
                kind,
                function: "f".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(true),
                contract_metadata: None,
            };
            assert!(!backend.can_handle(&vc), "ty should not handle L0 safety VCs");
        }
    }

    // ---- New tests for wired temporal pipeline ----

    /// Helper: build a simple state machine for testing temporal properties.
    /// States: Idle(start) -> Working(active) -> Done(done,terminal)
    /// Working also has a self-loop.
    fn test_machine() -> StateMachine {
        StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Idle").with_label("start"))
            .add_state(State::new(StateId(1), "Working").with_label("active"))
            .add_state(State::new(StateId(2), "Done").with_label("done").with_label("terminal"))
            .add_transition(Transition::new(StateId(0), StateId(1), "begin"))
            .add_transition(Transition::new(StateId(1), StateId(1), "work"))
            .add_transition(Transition::new(StateId(1), StateId(2), "finish"))
            .build()
    }

    #[test]
    fn test_ctl_ef_error_detection() {
        // Test EF(done): can we reach a done state?
        let machine = test_machine();
        let result = verify_temporal_property(&machine, "EF done");
        assert!(result.is_proved(), "EF(done) should hold from Idle: {result:?}");
    }

    #[test]
    fn test_ctl_ag_property_fails() {
        // AG(start): globally start should fail since Working is not start
        let machine = test_machine();
        let result = verify_temporal_property(&machine, "AG start");
        assert!(result.is_failed(), "AG(start) should fail: {result:?}");
    }

    #[test]
    fn test_ctl_ef_unreachable_state() {
        // Build a machine where "error" is not reachable
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "OK").with_label("ok"))
            .add_state(State::new(StateId(1), "Error").with_label("error"))
            .add_transition(Transition::new(StateId(0), StateId(0), "loop"))
            .build();

        let result = verify_temporal_property(&machine, "EF error");
        assert!(result.is_failed(), "EF(error) should fail since Error unreachable: {result:?}");
    }

    #[test]
    fn test_ctl_parse_error_returns_unknown() {
        let machine = test_machine();
        let result = verify_temporal_property(&machine, "@@@invalid");
        assert!(
            matches!(result, VerificationResult::Unknown { .. }),
            "invalid property should return Unknown: {result:?}"
        );
    }

    #[test]
    fn test_liveness_satisfied_with_accepting_cycle() {
        // All cycles pass through Done (done label) so GF(done) holds
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A").with_label("a"))
            .add_state(State::new(StateId(1), "B").with_label("done"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        let property = trust_types::LivenessProperty {
            name: "reach_done".into(),
            operator: TemporalOperator::AlwaysEventually,
            predicate: "done".into(),
            consequent: None,
            fairness: vec![],
        };

        // R5 fence: previously `Proved` — minted by the SCC-level acceptance
        // that is sub-cycle-blind (the verified unsound-positive shape). The
        // positive path is fenced; this pins the named demotion.
        let result = verify_liveness(&machine, &property);
        assert!(
            matches!(&result, VerificationResult::Unknown { reason, .. }
                if reason == trust_temporal::liveness::LIVENESS_POSITIVE_FENCE_REASON),
            "in-process liveness positives must be fenced to Unknown, got {result:?}"
        );
    }

    #[test]
    fn test_liveness_violated_spin_cycle() {
        // A self-loops on A forever, never reaches "done"
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Spin").with_label("spinning"))
            .add_transition(Transition::new(StateId(0), StateId(0), "spin"))
            .build();

        let property = trust_types::LivenessProperty {
            name: "eventually_done".into(),
            operator: TemporalOperator::Eventually,
            predicate: "done".into(),
            consequent: None,
            fairness: vec![],
        };

        let result = verify_liveness(&machine, &property);
        assert!(result.is_failed(), "liveness should be violated by spin: {result:?}");
    }

    #[test]
    fn test_liveness_under_fairness_satisfied() {
        // A: spin (self-loop) + escape to B(done). Under weak fairness on
        // "escape", the spin cycle is unfair, so liveness holds.
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A").with_label("a"))
            .add_state(State::new(StateId(1), "B").with_label("done"))
            .add_transition(Transition::new(StateId(0), StateId(0), "spin"))
            .add_transition(Transition::new(StateId(0), StateId(1), "escape"))
            .build();

        let property = trust_types::LivenessProperty {
            name: "eventually_done".into(),
            operator: TemporalOperator::Eventually,
            predicate: "done".into(),
            consequent: None,
            fairness: vec![trust_types::FairnessConstraint::Weak {
                action: "escape".into(),
                vars: vec![],
            }],
        };

        // R5 fence: previously `Proved` via the SCC-granularity fairness
        // filter (sub-cycle-blind unsound-positive shape). Pins the demotion.
        let result = verify_liveness(&machine, &property);
        assert!(
            matches!(&result, VerificationResult::Unknown { reason, .. }
                if reason == trust_temporal::fairness::FAIRNESS_POSITIVE_FENCE_REASON),
            "fairness-filtered liveness positives must be fenced to Unknown, got {result:?}"
        );
    }

    #[test]
    fn test_fairness_no_starvation() {
        // A -> B -> A cycle, both actions always taken. No starvation.
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        let constraint =
            trust_types::FairnessConstraint::Weak { action: "go".into(), vars: vec![] };

        // R5 fence: previously `Proved` off detect_starvation's SCC-level
        // analysis (unsound-positive shape; the lane's synthetic property
        // also conflates action names with state labels). The whole fairness
        // lane is fenced; this pins the named demotion.
        let result = verify_fairness(&machine, &constraint);
        assert!(
            matches!(&result, VerificationResult::Unknown { reason, .. }
                if reason.contains(TY_FAIRNESS_FENCE_REASON) && reason.contains("`go`")),
            "fairness verdicts must be fenced to Unknown, got {result:?}"
        );
    }

    #[test]
    fn test_fairness_starvation_detected() {
        // A: fast (self-loop) + slow (to B). "slow" can be starved.
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A").with_label("slow"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(0), "fast"))
            .add_transition(Transition::new(StateId(0), StateId(1), "slow"))
            .build();

        let constraint =
            trust_types::FairnessConstraint::Weak { action: "slow".into(), vars: vec![] };

        // R5 fence: previously `Proved` ("under weak fairness the spin cycle
        // is filtered") — exactly the SCC-granularity filtering shape the
        // fence exists for. Pins the named demotion.
        let result = verify_fairness(&machine, &constraint);
        assert!(
            matches!(&result, VerificationResult::Unknown { reason, .. }
                if reason.contains(TY_FAIRNESS_FENCE_REASON) && reason.contains("`slow`")),
            "fairness verdicts must be fenced to Unknown, got {result:?}"
        );
    }

    // ---- R5 checker-fence pins ----

    #[test]
    fn fence_leadsto_lowering_never_inspects_consequent() {
        // `P ~> Q` anti-fixture (blueprint S2 "leadsto with never-served
        // consequent"): `request` is reached and then the machine spins
        // forever; `served` never holds anywhere, so request ~> served is
        // genuinely violated. The pre-fence lowering dropped the operator and
        // consequent and checked bare `eventually request` — which the
        // machine satisfies on every path — minting an unsound `Proved` for
        // a property the checker never looked at. The fence demotes BEFORE
        // dispatch with the named lowering reason.
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Idle").with_label("idle"))
            .add_state(State::new(StateId(1), "Requested").with_label("request"))
            .add_transition(Transition::new(StateId(0), StateId(1), "req"))
            .add_transition(Transition::new(StateId(1), StateId(1), "spin"))
            .build();

        let property = trust_types::LivenessProperty {
            name: "request_served".into(),
            operator: TemporalOperator::LeadsTo,
            predicate: "request".into(),
            consequent: Some("served".into()),
            fairness: vec![],
        };

        let result = verify_liveness(&machine, &property);
        assert!(
            matches!(&result, VerificationResult::Unknown { reason, .. }
                if reason.contains(TY_TEMPORAL_LOWERING_FENCE_REASON)
                    && reason.contains("~>")),
            "leads-to must be fenced before dispatch with the named reason, got {result:?}"
        );
    }

    #[test]
    fn fence_always_operator_lowering() {
        // `[]P` lowered to `eventually P` is a category error (safety checked
        // as reachability); fenced before dispatch.
        let machine = test_machine();
        let property = trust_types::LivenessProperty {
            name: "always_start".into(),
            operator: TemporalOperator::Always,
            predicate: "start".into(),
            consequent: None,
            fairness: vec![],
        };

        let result = verify_liveness(&machine, &property);
        assert!(
            matches!(&result, VerificationResult::Unknown { reason, .. }
                if reason.contains(TY_TEMPORAL_LOWERING_FENCE_REASON)),
            "[]P must be fenced before dispatch, got {result:?}"
        );
    }

    #[test]
    fn fence_keeps_replayed_liveness_violation_publishing() {
        // Belt for battery item (c): the genuine spin-cycle refutation of
        // `eventually done` still publishes `Failed`, and its counterexample
        // carries the replay-validated lasso (prefix/cycle step assignments
        // plus the cycle_start index).
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Spin").with_label("spinning"))
            .add_transition(Transition::new(StateId(0), StateId(0), "spin"))
            .build();

        let property = trust_types::LivenessProperty {
            name: "eventually_done".into(),
            operator: TemporalOperator::Eventually,
            predicate: "done".into(),
            consequent: None,
            fairness: vec![],
        };

        let result = verify_liveness(&machine, &property);
        match &result {
            VerificationResult::Failed { counterexample: Some(ce), .. } => {
                assert!(
                    ce.assignments.iter().any(|(name, _)| name == "cycle_start_index"),
                    "validated lasso must carry its cycle_start: {ce:?}"
                );
                assert!(
                    ce.assignments
                        .iter()
                        .any(|(name, _)| name.starts_with("cycle_step_") || name.contains("cycle")),
                    "validated lasso must carry cycle steps: {ce:?}"
                );
            }
            other => panic!("replay-validated violation must still publish Failed, got {other:?}"),
        }
    }

    #[test]
    fn test_verify_with_machine_dispatches_correctly() {
        let machine = test_machine();

        // Deadlock
        let vc = VerificationCondition {
            kind: VcKind::Deadlock,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let result = TyBackend::verify_with_machine(&vc, &machine);
        // Machine has terminal state Done, so deadlock detected
        assert!(result.is_failed(), "Done is a deadlock state: {result:?}");

        // CTL temporal
        let vc = VerificationCondition {
            kind: VcKind::Temporal { property: "EF done".into(), machine: None },
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let result = TyBackend::verify_with_machine(&vc, &machine);
        assert!(result.is_proved(), "EF(done) should hold: {result:?}");
    }

    // ---- TLA+ spec generation tests ----

    #[test]
    fn test_tla_spec_generation_from_machine() {
        let machine = test_machine();
        let spec = spec_gen::generate_tla_spec(&machine, "RouterTest");
        assert!(spec.contains("MODULE RouterTest"), "should have module header");
        assert!(spec.contains("Init == state = \"Idle\""), "should have init from Idle");
        assert!(spec.contains("state' = \"Working\""), "should have working transition");
        assert!(spec.contains("state' = \"Done\""), "should have done transition");
        assert!(spec.contains("Spec =="), "should have spec definition");
    }

    #[test]
    fn test_tla_full_spec_with_property() {
        let machine = test_machine();
        let property = trust_temporal::TemporalProperty::Eventually { condition: "done".into() };
        let spec = spec_gen::generate_full_spec(&machine, &property, "PropTest");
        assert!(spec.contains("Property == <>done"), "should have property definition");
        assert!(spec.contains("Init =="), "should have init");
        assert!(spec.contains("===="), "should have module footer");
    }

    #[test]
    fn test_bridge_adapter_reexported_from_trust_temporal() {
        // Verify the StateMachineAdapter from trust-temporal works
        // the same as the previously local one.
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Start"))
            .add_state(State::new(StateId(1), "End"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .build();

        let adapter = StateMachineAdapter::new(machine);
        assert_eq!(adapter.initial_states(), vec![0]);
        assert_eq!(adapter.successors(&0), vec![("go".to_string(), 1)]);
        assert!(adapter.successors(&1).is_empty());
        assert_eq!(adapter.fingerprint(&42), 42);
    }

    #[test]
    fn test_bridge_explore_via_trust_temporal() {
        // Verify BFS exploration works through the trust-temporal bridge.
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_state(State::new(StateId(2), "C"))
            .add_transition(Transition::new(StateId(0), StateId(1), "ab"))
            .add_transition(Transition::new(StateId(1), StateId(2), "bc"))
            .build();

        let outcome = trust_temporal::ty_bridge::explore(&machine).expect("BFS should succeed");
        assert!(outcome.completed);
        assert_eq!(outcome.states_discovered, 3);
    }

    #[test]
    fn test_bridge_deadlock_check() {
        // Verify deadlock freedom check via trust-temporal bridge.
        let cycle = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "forward"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();
        assert!(trust_temporal::ty_bridge::check_deadlock_freedom(&cycle));

        let terminal = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .build();
        assert!(!trust_temporal::ty_bridge::check_deadlock_freedom(&terminal));
    }
}
