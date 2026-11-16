// Trust: 2026-09-16 — THE CONDUIT GATE, PINNED AT THE PREDICATE.
//
// `iterator_origin_def` readmits the `LocalWrite::Escape` channel — the channel behind
// `x3::pesc`, a kernel-certified false proof — for the `for`-loop iterator tracers,
// and the ONLY thing that licenses it is `iter_mut_borrows_only_feed_next`: an
// affirmative allow-list over everything a `&mut iter` conduit may do. These rows pin
// that allow-list one refusal at a time, on synthetic bodies, so a widening of the gate
// is a visible failure here before it is a verdict anywhere. The end-to-end rows over
// real compiler MIR are `tests/escaped_local_seam_realmir.rs`.

use trust_types::VerifiableFunction;

use super::iterator_yield::{iter_mut_borrows_only_feed_next, iterator_origin_def};

const SPAN: &str = r#"{"file":"f.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}"#;
const USIZE: &str = r#"{"Int":{"width":64,"signed":false}}"#;
const NEXT: &str =
    "<core::ops::range::Range<usize> as core::iter::traits::iterator::Iterator>::next";

/// `fn f(_1: usize, _2: usize) -> usize`; `_3` is the iterator local, `_4` its conduit,
/// `_5` a scratch temp. Types are irrelevant to the gate (it reads shapes, never types)
/// and are all `usize`.
fn func(blocks_json: &str) -> VerifiableFunction {
    let locals = (0..6)
        .map(|i| format!(r#"{{"index":{i},"ty":{USIZE},"name":null}}"#))
        .collect::<Vec<_>>()
        .join(",");
    let json = format!(
        r#"{{"name":"f","def_path":"f","span":{SPAN},"body":{{"locals":[{locals}],
           "blocks":[{blocks_json}],"arg_count":2,"return_ty":{USIZE}}},"contracts":[]}}"#
    );
    serde_json::from_str(&json).expect("the synthetic body must deserialize")
}

fn block(id: usize, stmts: &str, term: &str) -> String {
    format!(r#"{{"id":{id},"stmts":[{stmts}],"terminator":{term}}}"#)
}

/// `_3 = const 7` — the iterator's one initializer.
fn init_iter() -> String {
    format!(
        r#"{{"Assign":{{"place":{{"local":3,"projections":[]}},
           "rvalue":{{"Use":{{"Constant":{{"Uint":[7,64]}}}}}},"span":{SPAN}}}}}"#
    )
}

/// `_4 = &mut _3` — the conduit.
fn conduit() -> String {
    format!(
        r#"{{"Assign":{{"place":{{"local":4,"projections":[]}},
           "rvalue":{{"Ref":{{"mutable":true,"place":{{"local":3,"projections":[]}}}}}},
           "span":{SPAN}}}}}"#
    )
}

/// `(*_4) = const 7` — a STORE THROUGH the conduit: reseats the iterator.
fn store_through_conduit() -> String {
    format!(
        r#"{{"Assign":{{"place":{{"local":4,"projections":["Deref"]}},
           "rvalue":{{"Use":{{"Constant":{{"Uint":[7,64]}}}}}},"span":{SPAN}}}}}"#
    )
}

/// `_5 = Copy(_4)` — a READ of the conduit.
fn read_conduit() -> String {
    format!(
        r#"{{"Assign":{{"place":{{"local":5,"projections":[]}},
           "rvalue":{{"Use":{{"Copy":{{"local":4,"projections":[]}}}}}},"span":{SPAN}}}}}"#
    )
}

/// `SetDiscriminant((*_4), 0)` — a discriminant write through the conduit.
fn set_discriminant_through_conduit() -> String {
    r#"{"SetDiscriminant":{"place":{"local":4,"projections":["Deref"]},"variant_index":0}}"#
        .to_string()
}

/// `_5 = <callee>(move _4) -> bb<target>`.
fn call(callee: &str, dst: usize, target: usize) -> String {
    format!(
        r#"{{"Call":{{"func":"{callee}","args":[{{"Move":{{"local":4,"projections":[]}}}}],
           "dest":{{"local":{dst},"projections":[]}},"target":{target},"span":{SPAN},
           "atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}}}"#
    )
}

/// `drop((*_4)) -> bb<target>`.
fn drop_through_conduit(target: usize) -> String {
    format!(
        r#"{{"Drop":{{"place":{{"local":4,"projections":["Deref"]}},"target":{target},
           "span":{SPAN}}}}}"#
    )
}

const RETURN: &str = r#""Return""#;

/// THE ADMITTED SHAPE — the `for`-loop desugar: one initializer, one conduit, the
/// conduit's only use is argument 0 of `Iterator::next`. The VALUE resolver refuses the
/// local (it is on the alias channel); the ORIGIN question answers.
#[test]
fn a_conduit_that_only_feeds_next_passes_and_the_origin_answers() {
    let f = func(&format!(
        "{},{}",
        block(0, &format!("{},{}", init_iter(), conduit()), &call(NEXT, 5, 1)),
        block(1, "", RETURN)
    ));
    assert!(iter_mut_borrows_only_feed_next(&f, 3), "the desugar's conduit discipline");
    assert!(
        crate::local_defs::unique_value_def(&f, 3).is_none(),
        "the VALUE resolver refuses the aliased local"
    );
    assert!(
        iterator_origin_def(&f, 3).is_some(),
        "the ORIGIN question answers under the gate — this is the whole recovery"
    );
}

/// THE HALF THAT WAS MISSING. A store THROUGH the conduit names `_4` as its PLACE, not
/// as an operand, so the operand walk never saw it and `let mut it = 0..5; let p = &mut
/// it; *p = 0..100; for i in it {..}` passed. It is a write to the iterator this gate
/// vouches for; it must refuse. This is also the `pesc` shape, `*p = pick(c)`.
#[test]
fn a_store_through_the_conduit_is_refused() {
    let f = func(&format!(
        "{},{}",
        block(
            0,
            &format!("{},{},{}", init_iter(), conduit(), store_through_conduit()),
            &call(NEXT, 5, 1)
        ),
        block(1, "", RETURN)
    ));
    assert!(!iter_mut_borrows_only_feed_next(&f, 3), "a write rooted at the conduit");
    assert!(iterator_origin_def(&f, 3).is_none(), "and so the origin question is not asked");

    // The `pesc` shape proper: the conduit is used ONLY for the store, never for `next`.
    let pesc = func(&block(
        0,
        &format!("{},{},{}", init_iter(), conduit(), store_through_conduit()),
        RETURN,
    ));
    assert!(!iter_mut_borrows_only_feed_next(&pesc, 3), "pesc's conduit is written through");
    assert!(iterator_origin_def(&pesc, 3).is_none());
    assert!(crate::local_defs::unique_value_def(&pesc, 3).is_none());
}

/// A `SetDiscriminant` through the conduit is a write to the iterator too.
#[test]
fn a_discriminant_write_through_the_conduit_is_refused() {
    let f = func(&format!(
        "{},{}",
        block(
            0,
            &format!("{},{},{}", init_iter(), conduit(), set_discriminant_through_conduit()),
            &call(NEXT, 5, 1)
        ),
        block(1, "", RETURN)
    ));
    assert!(!iter_mut_borrows_only_feed_next(&f, 3));
    assert!(iterator_origin_def(&f, 3).is_none());
}

/// A `Drop` rooted at the conduit means it was not a plain receiver temp.
#[test]
fn a_drop_through_the_conduit_is_refused() {
    let f = func(&format!(
        "{},{},{}",
        block(0, &format!("{},{}", init_iter(), conduit()), &call(NEXT, 5, 1)),
        block(1, "", &drop_through_conduit(2)),
        block(2, "", RETURN)
    ));
    assert!(!iter_mut_borrows_only_feed_next(&f, 3));
    assert!(iterator_origin_def(&f, 3).is_none());
}

/// The conduit as a call DESTINATION is a second definition of it, and a receiver
/// temp is never redefined.
#[test]
fn the_conduit_as_a_call_destination_is_refused() {
    let f = func(&format!(
        "{},{},{}",
        block(0, &format!("{},{}", init_iter(), conduit()), &call(NEXT, 5, 1)),
        block(1, "", &call("g", 4, 2)),
        block(2, "", RETURN)
    ));
    assert!(!iter_mut_borrows_only_feed_next(&f, 3));
    assert!(iterator_origin_def(&f, 3).is_none());
}

/// The two refusals the gate always had, kept as controls so the hardening reads as an
/// extension of the allow-list and not a rewrite: a READ of the conduit, and the conduit
/// passed to any call that is not `Iterator::next` (`mem::swap`, `by_ref`, `nth`, ...).
#[test]
fn a_read_of_the_conduit_or_a_non_next_call_is_still_refused() {
    let read = func(&format!(
        "{},{}",
        block(0, &format!("{},{},{}", init_iter(), conduit(), read_conduit()), &call(NEXT, 5, 1)),
        block(1, "", RETURN)
    ));
    assert!(!iter_mut_borrows_only_feed_next(&read, 3));
    assert!(iterator_origin_def(&read, 3).is_none());

    let other = func(&format!(
        "{},{}",
        block(0, &format!("{},{}", init_iter(), conduit()), &call("core::mem::swap", 5, 1)),
        block(1, "", RETURN)
    ));
    assert!(!iter_mut_borrows_only_feed_next(&other, 3));
    assert!(iterator_origin_def(&other, 3).is_none());
}

/// The origin question's OTHER refusals are not the gate's to relax: a second whole
/// write of the iterator makes the initializer non-unique, and the gate passing does
/// not change that.
#[test]
fn a_second_initializer_is_refused_by_the_origin_question_itself() {
    let f = func(&format!(
        "{},{}",
        block(0, &format!("{},{},{}", init_iter(), init_iter(), conduit()), &call(NEXT, 5, 1)),
        block(1, "", RETURN)
    ));
    assert!(iter_mut_borrows_only_feed_next(&f, 3), "the conduit discipline itself holds");
    assert!(iterator_origin_def(&f, 3).is_none(), "but two initializers are not an origin");
}
