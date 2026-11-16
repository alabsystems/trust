//! Trust (step 2 increment 4c): the drop-glue oracle's pure verdict (`compare_events`,
//! `traces`). The MIR side (`shim_events`) and the executed side (`execute_glue`) need a
//! `TyCtxt`; they are exercised by channel C over the corpus in
//! `tests/run-make/trust-cg-f1-drop-glue`.

use super::*;

fn dtor(name: &str) -> GlueEvent {
    GlueEvent::Destructor { callee: name.to_string() }
}

fn field(f: u32, glue: &str) -> GlueEvent {
    GlueEvent::Child { path: vec![PathElem::Field(f)], glue: glue.to_string() }
}

fn arm(v: u32, f: u32, glue: &str) -> GlueEvent {
    GlueEvent::Child {
        path: vec![PathElem::Variant(v), PathElem::Field(f)],
        glue: glue.to_string(),
    }
}

#[test]
fn identical_events_agree() {
    let events = vec![dtor("S::drop"), field(0, "a"), field(2, "b")];
    let c = compare_events(&events, &events);
    assert!(c.agrees(), "{c:?}");
}

#[test]
fn a_child_the_shim_drops_and_the_plan_lacks_is_a_miss() {
    let oracle = vec![dtor("S::drop"), field(0, "a"), field(2, "b")];
    let producer = vec![dtor("S::drop"), field(0, "a")];
    let c = compare_events(&oracle, &producer);
    assert_eq!(c.misses, vec![field(2, "b")]);
    assert!(c.extras.is_empty());
    assert!(!c.agrees());
}

#[test]
fn a_child_the_plan_drops_and_the_shim_does_not_is_an_extra() {
    let oracle = vec![field(0, "a")];
    let producer = vec![field(0, "a"), field(1, "a")];
    let c = compare_events(&oracle, &producer);
    assert!(c.misses.is_empty());
    assert_eq!(c.extras, vec![field(1, "a")]);
    assert!(!c.agrees());
}

#[test]
fn a_missing_destructor_is_a_miss_and_a_wrong_child_glue_is_both() {
    let oracle = vec![dtor("S::drop"), field(0, "a")];
    let producer = vec![field(0, "b")];
    let c = compare_events(&oracle, &producer);
    assert_eq!(c.misses, vec![dtor("S::drop"), field(0, "a")]);
    assert_eq!(c.extras, vec![field(0, "b")]);
}

#[test]
fn the_same_children_in_another_order_disagree_on_order_only() {
    let oracle = vec![dtor("S::drop"), field(0, "a"), field(1, "b")];
    let producer = vec![dtor("S::drop"), field(1, "b"), field(0, "a")];
    let c = compare_events(&oracle, &producer);
    assert!(c.misses.is_empty() && c.extras.is_empty());
    assert!(!c.order_agrees);
    // The destructor after the fields is an order disagreement too.
    let late = vec![field(0, "a"), field(1, "b"), dtor("S::drop")];
    assert!(!compare_events(&oracle, &late).order_agrees);
}

#[test]
fn enum_arms_compare_per_variant_trace_whatever_order_the_switch_lists_them() {
    let oracle = vec![dtor("E::drop"), arm(1, 0, "y"), arm(1, 2, "x"), arm(0, 0, "x")];
    let producer = vec![dtor("E::drop"), arm(0, 0, "x"), arm(1, 0, "y"), arm(1, 2, "x")];
    let c = compare_events(&oracle, &producer);
    assert!(c.agrees(), "{c:?}");
    let t = traces(&oracle);
    assert_eq!(t.get(&Some(1)), Some(&vec![dtor("E::drop"), arm(1, 0, "y"), arm(1, 2, "x")]));
    assert_eq!(t.get(&Some(0)), Some(&vec![dtor("E::drop"), arm(0, 0, "x")]));
    // Two fields of ONE variant swapped is an order disagreement.
    let swapped = vec![dtor("E::drop"), arm(0, 0, "x"), arm(1, 2, "x"), arm(1, 0, "y")];
    assert!(!compare_events(&oracle, &swapped).order_agrees);
}

#[test]
fn an_unmodelled_shim_event_can_only_be_a_miss() {
    let oracle = vec![GlueEvent::Unmodelled { what: "call of `free`".to_string() }];
    let c = compare_events(&oracle, &[]);
    assert_eq!(c.misses.len(), 1);
    assert!(!c.agrees());
}

#[test]
fn slice_shapes_are_events_too() {
    let oracle = vec![GlueEvent::SliceDelegate { glue: "s".to_string(), len: 3 }];
    assert!(compare_events(&oracle, &oracle).agrees());
    let wrong_len = vec![GlueEvent::SliceDelegate { glue: "s".to_string(), len: 4 }];
    assert!(!compare_events(&oracle, &wrong_len).agrees());
    let lp = vec![GlueEvent::ElementLoop { glue: "e".to_string() }];
    assert!(compare_events(&lp, &lp).agrees());
}
