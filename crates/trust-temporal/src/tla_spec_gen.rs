// trust-temporal/tla_spec_gen.rs: TLA+ specification text generation
//
// Generates TLA+ module text from trust-temporal's StateMachine
// and TemporalProperty types. The generated spec can be fed to the ty
// binary for model checking.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt::Write;

use crate::{StateMachine, TemporalProperty};

/// Generate a TLA+ specification from a `StateMachine`.
///
/// Produces a complete TLA+ module with Init, Next, and Spec definitions.
/// The state variable tracks the current state ID as an integer.
///
/// # Arguments
/// * `machine` - The state machine to encode
/// * `module_name` - Name for the TLA+ module (e.g., "StateMachineSpec")
#[must_use]
pub fn generate_tla_spec(machine: &StateMachine, module_name: &str) -> String {
    let mut spec = String::new();

    // Module header
    let dashes = "-".repeat(module_name.len() + 8);
    let _ = writeln!(spec, "---- MODULE {module_name} {dashes}");
    let _ = writeln!(spec);

    // Variables
    let _ = writeln!(spec, "VARIABLE state");
    let _ = writeln!(spec);

    // State set
    let state_names: Vec<String> =
        machine.states.iter().map(|s| format!("\"{}\"", s.name)).collect();
    let _ = writeln!(spec, "States == {{{}}}", state_names.join(", "));
    let _ = writeln!(spec);

    // Init predicate
    let initial_name = machine
        .state(machine.initial)
        .map_or_else(|| format!("state_{}", machine.initial.0), |s| s.name.clone());
    let _ = writeln!(spec, "Init == state = \"{}\"", initial_name);
    let _ = writeln!(spec);

    // Next predicate: disjunction of transitions
    if machine.transitions.is_empty() {
        let _ = writeln!(spec, "Next == FALSE");
    } else {
        let mut transition_disjuncts = Vec::new();
        for t in &machine.transitions {
            let from_name = machine
                .state(t.from)
                .map_or_else(|| format!("state_{}", t.from.0), |s| s.name.clone());
            let to_name =
                machine.state(t.to).map_or_else(|| format!("state_{}", t.to.0), |s| s.name.clone());

            let disjunct = if let Some(guard) = &t.guard {
                format!(
                    "  /\\ state = \"{from_name}\"\n  /\\ {guard}\n  /\\ state' = \"{to_name}\""
                )
            } else {
                format!("  /\\ state = \"{from_name}\"\n  /\\ state' = \"{to_name}\"")
            };
            transition_disjuncts.push(disjunct);
        }
        let _ = writeln!(spec, "Next ==");
        for d in &transition_disjuncts {
            let _ = writeln!(spec, "  \\/ {d}");
        }
    }
    let _ = writeln!(spec);

    // Spec definition
    let _ = writeln!(spec, "Spec == Init /\\ [][Next]_state");
    let _ = writeln!(spec);

    // Module footer
    let _ = writeln!(spec, "====");

    spec
}

/// Generate a TLA+ temporal property expression.
///
/// Converts a `TemporalProperty` to its TLA+ syntax equivalent.
#[must_use]
fn generate_property_check(property: &TemporalProperty) -> String {
    match property {
        TemporalProperty::Always { condition } => format!("[]{condition}"),
        TemporalProperty::Eventually { condition } => format!("<>{condition}"),
        TemporalProperty::LeadsTo { antecedent, consequent } => {
            format!("{antecedent} ~> {consequent}")
        }
        TemporalProperty::Until { left, right } => format!("({left}) \\U ({right})"),
    }
}

/// Generate a label-based state predicate for TLA+ specs.
///
/// Converts a state label reference to a TLA+ predicate that checks
/// if the current state has that label.
#[cfg(test)]
#[must_use]
fn generate_label_predicate(machine: &StateMachine, label: &str) -> String {
    let matching_states: Vec<String> = machine
        .states
        .iter()
        .filter(|s| s.labels.contains(&label.to_string()) || s.name == label)
        .map(|s| format!("\"{}\"", s.name))
        .collect();

    if matching_states.is_empty() {
        "FALSE".to_string()
    } else if matching_states.len() == 1 {
        format!("state = {}", matching_states[0])
    } else {
        format!("state \\in {{{}}}", matching_states.join(", "))
    }
}

/// Generate a complete TLA+ spec with a property to check.
///
/// Combines the state machine encoding with a temporal property assertion.
#[must_use]
pub fn generate_full_spec(
    machine: &StateMachine,
    property: &TemporalProperty,
    module_name: &str,
) -> String {
    let mut spec = generate_tla_spec(machine, module_name);

    // Remove the trailing ==== line to insert property before it
    let footer_pos = spec.rfind("====").unwrap_or(spec.len());
    spec.truncate(footer_pos);

    // Add property
    let prop_text = generate_property_check(property);
    let _ = writeln!(spec, "Property == {prop_text}");
    let _ = writeln!(spec);
    let _ = writeln!(spec, "====");

    spec
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{State, StateId, StateMachineBuilder, Transition};

    fn test_machine() -> StateMachine {
        StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Idle").with_label("start"))
            .add_state(State::new(StateId(1), "Working").with_label("active"))
            .add_state(State::new(StateId(2), "Done").with_label("done"))
            .add_transition(Transition::new(StateId(0), StateId(1), "begin"))
            .add_transition(Transition::new(StateId(1), StateId(2), "finish"))
            .build()
    }

    #[test]
    fn generate_spec_has_module_header() {
        let machine = test_machine();
        let spec = generate_tla_spec(&machine, "TestSpec");
        assert!(spec.contains("---- MODULE TestSpec"));
        assert!(spec.contains("===="));
    }

    #[test]
    fn generate_spec_has_init() {
        let machine = test_machine();
        let spec = generate_tla_spec(&machine, "TestSpec");
        assert!(spec.contains("Init == state = \"Idle\""));
    }

    #[test]
    fn generate_spec_has_next_transitions() {
        let machine = test_machine();
        let spec = generate_tla_spec(&machine, "TestSpec");
        assert!(spec.contains("state = \"Idle\""));
        assert!(spec.contains("state' = \"Working\""));
        assert!(spec.contains("state = \"Working\""));
        assert!(spec.contains("state' = \"Done\""));
    }

    #[test]
    fn generate_spec_has_spec_definition() {
        let machine = test_machine();
        let spec = generate_tla_spec(&machine, "TestSpec");
        assert!(spec.contains("Spec == Init /\\ [][Next]_state"));
    }

    #[test]
    fn generate_spec_has_state_set() {
        let machine = test_machine();
        let spec = generate_tla_spec(&machine, "TestSpec");
        assert!(spec.contains("States =="));
        assert!(spec.contains("\"Idle\""));
        assert!(spec.contains("\"Working\""));
        assert!(spec.contains("\"Done\""));
    }

    #[test]
    fn generate_spec_no_transitions() {
        let machine =
            StateMachineBuilder::new(StateId(0)).add_state(State::new(StateId(0), "Only")).build();
        let spec = generate_tla_spec(&machine, "EmptySpec");
        assert!(spec.contains("Next == FALSE"));
    }

    #[test]
    fn generate_spec_with_guard() {
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go").with_guard("x > 0"))
            .build();
        let spec = generate_tla_spec(&machine, "GuardSpec");
        assert!(spec.contains("x > 0"));
    }

    #[test]
    fn property_always() {
        let prop = TemporalProperty::Always { condition: "safe".into() };
        assert_eq!(generate_property_check(&prop), "[]safe");
    }

    #[test]
    fn property_eventually() {
        let prop = TemporalProperty::Eventually { condition: "done".into() };
        assert_eq!(generate_property_check(&prop), "<>done");
    }

    #[test]
    fn property_leads_to() {
        let prop = TemporalProperty::LeadsTo {
            antecedent: "request".into(),
            consequent: "response".into(),
        };
        assert_eq!(generate_property_check(&prop), "request ~> response");
    }

    #[test]
    fn property_until() {
        let prop = TemporalProperty::Until { left: "running".into(), right: "done".into() };
        assert_eq!(generate_property_check(&prop), "(running) \\U (done)");
    }

    #[test]
    fn label_predicate_single_match() {
        let machine = test_machine();
        let pred = generate_label_predicate(&machine, "done");
        assert_eq!(pred, "state = \"Done\"");
    }

    #[test]
    fn label_predicate_no_match() {
        let machine = test_machine();
        let pred = generate_label_predicate(&machine, "nonexistent");
        assert_eq!(pred, "FALSE");
    }

    #[test]
    fn label_predicate_name_match() {
        let machine = test_machine();
        let pred = generate_label_predicate(&machine, "Idle");
        assert_eq!(pred, "state = \"Idle\"");
    }

    #[test]
    fn full_spec_includes_property() {
        let machine = test_machine();
        let property = TemporalProperty::Eventually { condition: "done".into() };
        let spec = generate_full_spec(&machine, &property, "FullSpec");
        assert!(spec.contains("Property == <>done"));
        assert!(spec.contains("Init =="));
        assert!(spec.contains("===="));
    }
}
