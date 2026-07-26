// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_temporal::{
    BmcEngine, BmcResult, CtlFormula, CtlModelChecker, LtlFormula, SafetyProperty, State, StateId,
    StateMachine, StateMachineBuilder, TemporalProperty, TemporalSpec, Trace, Transition,
    ltl::parse_ltl,
};

fn sample_machine() -> StateMachine {
    StateMachineBuilder::new(StateId(0))
        .add_state(State::new(StateId(0), "Idle"))
        .add_state(State::new(StateId(1), "Busy"))
        .add_state(State::new(StateId(2), "Done"))
        .add_transition(Transition::new(StateId(0), StateId(1), "start"))
        .add_transition(Transition::new(StateId(1), StateId(2), "finish"))
        .build()
}

fn safe_cycle_machine() -> StateMachine {
    StateMachineBuilder::new(StateId(0))
        .add_state(State::new(StateId(0), "S0").with_label("safe"))
        .add_state(State::new(StateId(1), "S1").with_label("safe"))
        .add_state(State::new(StateId(2), "S2").with_label("safe").with_label("terminal"))
        .add_transition(Transition::new(StateId(0), StateId(1), "step_0"))
        .add_transition(Transition::new(StateId(1), StateId(2), "step_1"))
        .add_transition(Transition::new(StateId(2), StateId(0), "step_2"))
        .build()
}

fn unsafe_machine() -> StateMachine {
    StateMachineBuilder::new(StateId(0))
        .add_state(State::new(StateId(0), "S0").with_label("safe"))
        .add_state(State::new(StateId(1), "S1").with_label("safe"))
        .add_state(State::new(StateId(2), "Error").with_label("error"))
        .add_transition(Transition::new(StateId(0), StateId(1), "step_0"))
        .add_transition(Transition::new(StateId(1), StateId(2), "step_1"))
        .build()
}

#[test]
fn test_state_machine_construction_and_reachability() {
    let machine = sample_machine();
    let depth_one = machine.reachable_states(1);
    let depth_two = machine.reachable_states(2);

    assert_eq!(depth_one.len(), 2);
    assert_eq!(depth_two.len(), 3);
    assert!(depth_one.contains(&StateId(0)));
    assert!(depth_one.contains(&StateId(1)));
    assert!(depth_two.contains(&StateId(2)));
}

#[test]
fn test_bounded_traces_enumeration() {
    let machine = StateMachineBuilder::new(StateId(0))
        .add_state(State::new(StateId(0), "Start"))
        .add_state(State::new(StateId(1), "Loop"))
        .add_transition(Transition::new(StateId(0), StateId(1), "enter"))
        .add_transition(Transition::new(StateId(1), StateId(1), "stay"))
        .build();

    let traces: Vec<Trace> = machine.bounded_traces(2);

    assert!(traces.iter().all(|trace| trace.len() <= 3));
    assert!(traces.iter().all(|trace| trace.starts_at(StateId(0))));
}

#[test]
fn test_bmc_safe_model() {
    let machine = safe_cycle_machine();
    let engine = BmcEngine::new(&machine);
    let property = SafetyProperty::new("all_safe", "safe");
    let result = engine.check_bounded(&property, 5);

    assert!(result.is_safe());
    assert!(matches!(result, BmcResult::Safe { bound: 5 }));
}

#[test]
fn test_bmc_unsafe_model_finds_counterexample() {
    let machine = unsafe_machine();
    let engine = BmcEngine::new(&machine);
    let property = SafetyProperty::new("all_safe", "safe");
    let result = engine.check_bounded(&property, 3);

    assert!(result.is_unsafe());
    assert!(matches!(result, BmcResult::Unsafe { depth: 2, .. }));
    assert!(result.counterexample().unwrap().visits(StateId(2)));
}

#[test]
fn test_ctl_ag_safety() {
    let machine = safe_cycle_machine();
    let checker = CtlModelChecker::new(&machine);
    let formula = CtlFormula::AG(Box::new(CtlFormula::Atom("safe".to_string())));
    let result = checker.check(&formula);

    assert!(result.holds_at_initial(StateId(0)));
}

#[test]
fn test_ctl_ef_reachability() {
    let machine = safe_cycle_machine();
    let checker = CtlModelChecker::new(&machine);
    let formula = CtlFormula::EF(Box::new(CtlFormula::Atom("terminal".to_string())));
    let result = checker.check(&formula);

    assert!(result.holds_at_initial(StateId(0)));
    assert!(result.witness.unwrap().visits(StateId(2)));
}

#[test]
fn test_ltl_parse_and_negate() {
    let formula = parse_ltl("G safe").unwrap();
    let negated = trust_temporal::ltl::negate(&formula);

    assert_eq!(formula, LtlFormula::Always(Box::new(LtlFormula::Atomic("safe".to_string()))));
    assert_eq!(negated, LtlFormula::Not(Box::new(formula.clone())));
}

#[test]
fn test_temporal_spec_composition() {
    let spec = TemporalSpec::new(
        sample_machine(),
        TemporalProperty::Eventually { condition: "Done".to_string() },
    );

    assert_eq!(spec.property.description(), "eventually Done");
    assert_eq!(spec.machine.state(StateId(2)).unwrap().name, "Done");
}
