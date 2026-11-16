//! Conditional value definitions must not turn possible allocations into
//! guaranteed violations. These checks exercise the public classification API.

use trust_router::{alloc_over_ceiling_forced, violation_is_forced};
use trust_types::{Formula, Sort};

const CEILING: i128 = 1 << 28;

fn count() -> Formula {
    Formula::Var("count".into(), Sort::Int)
}

fn definition(n: i128) -> Formula {
    Formula::Eq(Box::new(count()), Box::new(Formula::Int(n)))
}

fn violation() -> Formula {
    Formula::Ge(Box::new(count()), Box::new(Formula::Int(CEILING)))
}

#[test]
fn inactive_saturation_arm_is_not_a_constant_definition() {
    for guard in [Formula::Bool(false), Formula::Var("overflow".into(), Sort::Bool)] {
        let conditional = Formula::Implies(Box::new(guard), Box::new(definition(CEILING)));
        for facts in [
            vec![conditional.clone(), violation()],
            vec![conditional.clone(), definition(1), violation()],
            vec![definition(1), conditional, violation()],
        ] {
            let formula = Formula::And(facts);
            assert!(!alloc_over_ceiling_forced(&formula), "{formula:?}");
            assert!(!violation_is_forced(&formula), "{formula:?}");
        }
    }
}

#[test]
fn alternative_and_negated_definitions_do_not_bind_the_count() {
    for definition in [
        Formula::Or(vec![definition(CEILING), definition(1)]),
        Formula::Not(Box::new(definition(CEILING))),
    ] {
        let formula = Formula::And(vec![definition, violation()]);
        assert!(!alloc_over_ceiling_forced(&formula), "{formula:?}");
    }
}

#[test]
fn boolean_operands_are_not_positive_allocation_findings() {
    for operand in [
        Formula::Not(Box::new(violation())),
        Formula::Implies(Box::new(Formula::Bool(false)), Box::new(violation())),
        Formula::Eq(Box::new(Formula::Bool(false)), Box::new(violation())),
        Formula::Or(vec![
            Formula::Bool(true),
            Formula::And(vec![Formula::Var("branch".into(), Sort::Bool), violation()]),
        ]),
    ] {
        let formula = Formula::And(vec![definition(CEILING), operand]);
        assert!(!alloc_over_ceiling_forced(&formula), "{formula:?}");
    }
}

#[test]
fn unreachable_and_inconsistent_allocations_are_not_forced() {
    for facts in [
        vec![definition(CEILING), Formula::Bool(false), violation()],
        vec![definition(CEILING), definition(1), violation()],
        vec![definition(1), definition(CEILING), violation()],
    ] {
        let formula = Formula::And(facts);
        assert!(!alloc_over_ceiling_forced(&formula), "{formula:?}");
    }
}

#[test]
fn direct_constant_allocations_remain_forced_with_unknown_reaching_guards() {
    for guard in [Formula::Bool(true), Formula::Var("reached".into(), Sort::Bool)] {
        for atom in [violation(), Formula::Or(vec![Formula::Bool(false), violation()])] {
            let formula = Formula::And(vec![definition(CEILING), guard.clone(), atom]);
            assert!(alloc_over_ceiling_forced(&formula), "{formula:?}");
        }
    }
    assert!(violation_is_forced(&Formula::And(vec![definition(CEILING), violation()])));
}
