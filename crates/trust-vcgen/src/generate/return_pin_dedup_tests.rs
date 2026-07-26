use trust_types::{Formula, Sort};

use super::dedup_identical_return_slot_pin;

fn eq(lhs: &str, rhs: &str) -> Formula {
    Formula::Eq(Box::new(Formula::var(lhs, Sort::Int)), Box::new(Formula::var(rhs, Sort::Int)))
}

#[test]
fn removes_only_an_ast_identical_unconditional_return_pin() {
    let pin = eq("_0", "_4.0");
    let guard = Formula::Gt(Box::new(Formula::var("x", Sort::Int)), Box::new(Formula::Int(0)));
    let obligation = Formula::Not(Box::new(guard.clone()));
    let body = Formula::And(vec![guard.clone(), pin.clone(), obligation.clone()]);
    let duplicated = Formula::And(vec![pin.clone(), body.clone()]);
    assert_eq!(dedup_identical_return_slot_pin(duplicated), body);

    let different_pin = eq("_0", "_5.0");
    let nonidentical =
        Formula::And(vec![pin.clone(), Formula::And(vec![different_pin, obligation])]);
    assert_eq!(dedup_identical_return_slot_pin(nonidentical.clone()), nonidentical);

    let conditional_copy =
        Formula::And(vec![pin, Formula::Or(vec![eq("_0", "_4.0"), Formula::Bool(false)])]);
    assert_eq!(dedup_identical_return_slot_pin(conditional_copy.clone()), conditional_copy);
}
