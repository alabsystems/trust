// trust-types/const_array_tests.rs: `Formula::ConstArray` across the formula
// consumers this crate owns (sort checking, logic selection, sort positions,
// generics substitution, the formula DAG and the serde payload).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_ir_contract::formula_dag::FormulaDag;

use crate::formula_merkle::formula_digest;
use crate::{Formula, Sort};

fn int_array() -> Sort {
    Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int))
}

/// `[v; N]` as vcgen states it: `arr == ((as const (Array Int Int)) v)`.
fn seed(v: Formula) -> Formula {
    Formula::Eq(
        Box::new(Formula::Var("arr".into(), int_array())),
        Box::new(Formula::const_array(Sort::Int, Sort::Int, v)),
    )
}

#[test]
fn const_array_is_well_sorted_exactly_when_its_value_has_the_element_sort() {
    let splat = Formula::const_array(Sort::Int, Sort::Int, Formula::Var("v".into(), Sort::Int));
    assert_eq!(crate::check_formula_sort(&splat), Ok(int_array()));
    assert_eq!(crate::infer_sort(&splat), int_array());
    assert_eq!(crate::check_formula_sort(&seed(Formula::Int(7))), Ok(Sort::Bool));
    let read = Formula::Select(Box::new(splat), Box::new(Formula::Var("i".into(), Sort::Int)));
    assert_eq!(crate::check_formula_sort(&read), Ok(Sort::Int));
    // A value whose sort is not the carried element sort is ill-sorted.
    let wrong = Formula::const_array(Sort::Int, Sort::BitVec(8), Formula::Int(7));
    assert!(crate::check_formula_sort(&wrong).is_err());
    assert_eq!(crate::infer_sort(&wrong), Sort::Int, "the ill-sorted sentinel");
}

#[test]
fn const_array_selects_an_array_logic_and_reports_its_sort_position() {
    assert_eq!(crate::smt_logic::select_logic(&seed(Formula::Int(7))), "QF_ALIA");
    // A mixed `(Array Int (_ BitVec 8))` is charged through the sort position
    // the constant array spells, exactly as an array-sorted variable is.
    let bytes = Formula::Eq(
        Box::new(Formula::Var(
            "b".into(),
            Sort::Array(Box::new(Sort::Int), Box::new(Sort::BitVec(8))),
        )),
        Box::new(Formula::const_array(
            Sort::Int,
            Sort::BitVec(8),
            Formula::BitVec { value: 0, width: 8 },
        )),
    );
    let bare = Formula::Eq(
        Box::new(Formula::Var(
            "b".into(),
            Sort::Array(Box::new(Sort::Int), Box::new(Sort::BitVec(8))),
        )),
        Box::new(Formula::Var(
            "c".into(),
            Sort::Array(Box::new(Sort::Int), Box::new(Sort::BitVec(8))),
        )),
    );
    assert_eq!(
        crate::smt_logic::select_logic(&bytes),
        crate::smt_logic::select_logic(&bare),
        "the constant array needs exactly what an array-sorted variable of its sort needs"
    );
    let mut positions = Vec::new();
    crate::smt_logic::visit_sort_positions(
        &Formula::const_array(Sort::Int, Sort::Bool, Formula::Bool(true)),
        &mut |sort| positions.push(sort.clone()),
    );
    assert_eq!(positions, vec![Sort::Array(Box::new(Sort::Int), Box::new(Sort::Bool))]);
}

#[test]
fn generics_substitution_reaches_the_value_and_the_sorts() {
    let subst = crate::generics::Substitution::new();
    let formula = Formula::const_array(Sort::Int, Sort::Int, Formula::Var("v".into(), Sort::Int));
    assert_eq!(subst.apply_formula(&formula), formula);
}

/// T3 L4 (C06): the formula DAG, which replaced the deleted formula arena.
#[test]
fn the_formula_dag_round_trips_a_const_array_and_sees_inside_it() {
    let value = Formula::Var("v".into(), Sort::Int);
    let formula = seed(value.clone());
    let mut dag = FormulaDag::new();
    let root = dag.intern(&formula);
    assert_eq!(dag.expand(root), formula);
    // The value is the constant array's child node: the DAG sees inside it.
    let array = dag.intern(&Formula::const_array(Sort::Int, Sort::Int, value.clone()));
    let value_node = dag.intern(&value);
    assert_eq!(dag.kids(array).collect::<Vec<_>>(), vec![value_node]);
    let free = dag.expand(root).free_variables();
    assert!(free.contains("v"), "the value's variable is free: {free:?}");
    assert!(free.contains("arr"));
    // Two constant arrays of the same value but different element sorts are
    // different terms, with different digests.
    let a = Formula::const_array(Sort::Int, Sort::Int, Formula::Int(0));
    let b = Formula::const_array(Sort::Int, Sort::Bool, Formula::Int(0));
    let c = Formula::const_array(Sort::Int, Sort::Int, Formula::Int(0));
    assert_ne!(dag.intern(&a), dag.intern(&b));
    assert_ne!(formula_digest(&a).ok(), formula_digest(&b).ok());
    assert_eq!(dag.intern(&a), dag.intern(&c));
    assert_eq!(formula_digest(&a).ok(), formula_digest(&c).ok());
}

#[test]
fn a_formula_payload_with_a_const_array_round_trips_and_old_formulas_are_unchanged() {
    // The `trust-types.Formula@1` payload is the serde JSON of `Formula`. A
    // formula without the node serializes as before, and one with it names
    // the node explicitly, so a reader that predates it refuses the payload
    // (unknown variant) instead of misreading it.
    let old = Formula::Eq(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(1)));
    assert_eq!(serde_json::to_string(&old).unwrap(), r#"{"Eq":[{"Var":["x","Int"]},{"Int":1}]}"#);
    let new = seed(Formula::Int(7));
    let json = serde_json::to_string(&new).unwrap();
    assert!(json.contains(r#""ConstArray""#), "{json}");
    assert_eq!(serde_json::from_str::<Formula>(&json).unwrap(), new);
}
