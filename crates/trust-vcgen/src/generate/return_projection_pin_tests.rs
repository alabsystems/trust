use trust_types::{Formula, Sort};

use super::{formula_has_complete_return_projection_pins, formula_has_return_slot_pin};

fn var(name: &str) -> Formula {
    Formula::var(name, Sort::Int)
}

fn eq(lhs: &str, rhs: &str) -> Formula {
    Formula::Eq(Box::new(var(lhs)), Box::new(var(rhs)))
}

fn two_field_postcondition() -> Formula {
    Formula::Eq(Box::new(var("_0.0")), Box::new(var("_0.1")))
}

#[test]
fn complete_positive_spine_projection_pins_ground_the_postcondition() {
    let postcondition = two_field_postcondition();
    let formula = Formula::And(vec![
        eq("_0.0#s0_1", "x"),
        eq("_0.1#s0_1", "x"),
        Formula::Not(Box::new(postcondition.clone())),
    ]);

    assert!(formula_has_complete_return_projection_pins(&formula, &postcondition));
    assert!(!formula_has_return_slot_pin(&formula));
}

#[test]
fn missing_sibling_projection_pin_fails_closed() {
    let postcondition = two_field_postcondition();
    let formula = Formula::And(vec![
        eq("_0.0", "x"),
        Formula::Not(Box::new(postcondition.clone())),
    ]);

    assert!(!formula_has_complete_return_projection_pins(&formula, &postcondition));
}

#[test]
fn negated_or_cyclic_equalities_are_not_projection_pins() {
    let postcondition = two_field_postcondition();
    let negated_pin = Formula::And(vec![
        eq("_0.0", "x"),
        Formula::Not(Box::new(eq("_0.1", "x"))),
        Formula::Not(Box::new(postcondition.clone())),
    ]);
    assert!(!formula_has_complete_return_projection_pins(
        &negated_pin,
        &postcondition
    ));

    let cyclic = Formula::And(vec![
        eq("_0.0", "_0.1"),
        eq("_0.1", "_0.0"),
        Formula::Not(Box::new(postcondition.clone())),
    ]);
    assert!(!formula_has_complete_return_projection_pins(&cyclic, &postcondition));
}

#[test]
fn projection_pins_do_not_replace_a_required_whole_slot_pin() {
    let postcondition = Formula::And(vec![eq("_0.0", "x"), eq("_0", "x")]);
    let projections_only = Formula::And(vec![
        eq("_0.0", "x"),
        Formula::Not(Box::new(postcondition.clone())),
    ]);
    assert!(!formula_has_complete_return_projection_pins(
        &projections_only,
        &postcondition
    ));
    assert!(!formula_has_return_slot_pin(&projections_only));

    let with_whole_slot =
        Formula::And(vec![eq("_0", "x"), eq("_0.0", "x"), projections_only]);
    assert!(formula_has_return_slot_pin(&with_whole_slot));
}
