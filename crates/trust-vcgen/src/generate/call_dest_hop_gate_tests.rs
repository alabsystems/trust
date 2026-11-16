// Trust: 2026-09-16 — THE CALL-DESTINATION HOP GATE, PINNED AT THE PREDICATE.
//
// Every iterator tracer in this family — `trace_local_to_range_aggregate`,
// `trace_local_to_enumerated_slice`, `container_len::trace_slice_iter_item`,
// `loop_bounds::trace_iter_to_into_iter_arg` — hops from a call-destination local into
// the producing call's `args[0]` through ONE entrance, `iterator_yield::call_dest_hop`:
// `local_defs::unique_value_call` (the call is the local's only write channel), or its
// origin twin `unique_initializing_call` under the `iter_mut_borrows_only_feed_next`
// conduit gate (the alias is the only other channel, and every conduit only feeds
// `next`). These rows pin the gate one channel at a time on synthetic bodies, so a
// widening is a visible failure here before it is a verdict anywhere; the end-to-end
// rows on the compiler's own MIR are `tests/escaped_local_seam_realmir.rs` (the
// `reseated call destination` section).

use trust_types::{Operand, VerifiableFunction};

use super::container_len::trace_slice_iter_item;
use super::iterator_yield::{
    call_dest_hop, trace_local_to_enumerated_slice, trace_local_to_range_aggregate,
};
use super::loop_bounds::trace_iter_to_into_iter_arg;

const SPAN: &str = r#"{"file":"f.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}"#;
const USIZE: &str = r#"{"Int":{"width":64,"signed":false}}"#;
const REV: &str = "<core::ops::range::Range<usize> as core::iter::traits::iterator::Iterator>::rev";
const INTO_ITER: &str = "<core::iter::adapters::rev::Rev<core::ops::range::Range<usize>> as core::iter::traits::collect::IntoIterator>::into_iter";
const SLICE_ITER: &str = "core::slice::<impl [u8]>::iter";
const ENUMERATE: &str =
    "<core::slice::iter::Iter<'_, u8> as core::iter::traits::iterator::Iterator>::enumerate";
const WINDOWS: &str = "core::slice::<impl [u8]>::windows";

/// `fn f(_1: usize, _2: usize) -> usize`; locals `_3.._9` are scratch. Types are
/// irrelevant to the gate (it reads write channels, never types) and are all `usize`.
fn func(blocks_json: &str) -> VerifiableFunction {
    let locals = (0..10)
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

/// `_<dst> = Range { start: 0, end: <end> }`.
fn range(dst: usize, end: u64) -> String {
    format!(
        r#"{{"Assign":{{"place":{{"local":{dst},"projections":[]}},
           "rvalue":{{"Aggregate":[{{"Adt":{{"name":"core::ops::range::Range","variant":0,
           "active_field":null,"args":"core::ops::range::Range<usize>"}}}},
           [{{"Constant":{{"Uint":[0,64]}}}},{{"Constant":{{"Uint":[{end},64]}}}}]]}},
           "span":{SPAN}}}}}"#
    )
}

/// `_<dst> = move _<src>`.
fn mv(dst: usize, src: usize) -> String {
    format!(
        r#"{{"Assign":{{"place":{{"local":{dst},"projections":[]}},
           "rvalue":{{"Use":{{"Move":{{"local":{src},"projections":[]}}}}}},"span":{SPAN}}}}}"#
    )
}

/// `_<dst> = &mut _<src>`.
fn mut_borrow(dst: usize, src: usize) -> String {
    format!(
        r#"{{"Assign":{{"place":{{"local":{dst},"projections":[]}},
           "rvalue":{{"Ref":{{"mutable":true,"place":{{"local":{src},"projections":[]}}}}}},
           "span":{SPAN}}}}}"#
    )
}

/// `_<dst> = <callee>(move _<arg>, ..) -> bb<target>`.
fn call(callee: &str, dst: usize, args: &[usize], target: usize) -> String {
    let args = args
        .iter()
        .map(|a| format!(r#"{{"Move":{{"local":{a},"projections":[]}}}}"#))
        .collect::<Vec<_>>()
        .join(",");
    format!(
        r#"{{"Call":{{"func":"{callee}","args":[{args}],
           "dest":{{"local":{dst},"projections":[]}},"target":{target},"span":{SPAN},
           "atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}}}"#
    )
}

/// `call`, carrying the `callee_key` the extractor mints for a `core` callee
/// (`krate_is_real_sysroot: true`, no modeled tag). SLICE-INHERENT-1 (2026-10-04):
/// the `<[T]>` recognizers the slice tracers hop through decide on that key, so a
/// keyless `core::slice::<impl [u8]>::iter` is (correctly) not std's.
fn sysroot_call(callee: &str, dst: usize, args: &[usize], target: usize) -> String {
    let plain = call(callee, dst, args, target);
    let key = concat!(
        r#","callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"#,
        r#""stable_crate_id":1,"krate_name":"core"}}}"#
    );
    let body = plain.strip_suffix("}}").expect("call() closes its two objects");
    format!("{body}{key}")
}

const RETURN: &str = r#""Return""#;

fn end_of(f: &VerifiableFunction, local: usize) -> Option<u64> {
    let origin = trace_local_to_range_aggregate(f, local, 16)?;
    match origin.end {
        Operand::Constant(trust_types::ConstValue::Uint(v, _)) => Some(*v as u64),
        _ => None,
    }
}

/// THE ADMITTED SHAPE: `_4 = Range{0,5}; _3 = rev(move _4)` — one call, nothing else
/// touches `_3`. The hop answers and the tracer reaches the aggregate.
#[test]
fn a_call_destination_with_one_write_channel_hops_into_its_argument() {
    let f = func(&format!(
        "{},{}",
        block(0, &range(4, 5), &call(REV, 3, &[4], 1)),
        block(1, "", RETURN)
    ));
    assert!(call_dest_hop(&f, 3).is_some(), "the one-call shape is the hop's whole purpose");
    assert_eq!(end_of(&f, 3), Some(5));
}

/// THE WITNESS (`dbl_rev`): `_3 = rev(Range{0,5})` then `_3 = move _5` where
/// `_5 = rev(Range{0,100})`. A NAMED second write beside the call. The ungated hop took
/// the first call and read `end = 5`; the program indexes 99. Now: no hop, no origin.
#[test]
fn a_named_reseat_beside_the_call_refuses_the_hop() {
    let f = func(&format!(
        "{},{},{}",
        block(0, &range(4, 5), &call(REV, 3, &[4], 1)),
        block(1, &range(6, 100), &call(REV, 5, &[6], 2)),
        block(2, &mv(3, 5), RETURN)
    ));
    assert!(call_dest_hop(&f, 3).is_none(), "two write channels on `_3`");
    assert_eq!(end_of(&f, 3), None, "the tracer must decline, never read the first constructor");
}

/// TWO CALLS writing the same local (`dbl_into` at a copy-propagated shape): the second
/// `WholeOpaque` write is a second value, and the hop has no single call to name.
#[test]
fn a_second_call_destination_refuses_the_hop() {
    let f = func(&format!(
        "{},{},{}",
        block(0, &range(4, 5), &call(REV, 3, &[4], 1)),
        block(1, &range(6, 100), &call(REV, 3, &[6], 2)),
        block(2, "", RETURN)
    ));
    assert!(call_dest_hop(&f, 3).is_none());
    assert_eq!(end_of(&f, 3), None);
}

/// `(*_<conduit>) = Range{0,100}` — a STORE THROUGH the conduit: reseats the iterator.
fn store_through(conduit: usize) -> String {
    format!(
        r#"{{"Assign":{{"place":{{"local":{conduit},"projections":["Deref"]}},
           "rvalue":{{"Aggregate":[{{"Adt":{{"name":"core::ops::range::Range","variant":0,
           "active_field":null,"args":"core::ops::range::Range<usize>"}}}},
           [{{"Constant":{{"Uint":[0,64]}}}},{{"Constant":{{"Uint":[100,64]}}}}]]}},
           "span":{SPAN}}}}}"#
    )
}

const NEXT: &str = "<core::iter::adapters::rev::Rev<core::ops::range::Range<usize>> as core::iter::traits::iterator::Iterator>::next";

/// THE ALIAS WITNESS (`alias_rev` / `alias_into` / `enum_reseat`): `_5 = &mut _3` is an
/// `Escape`, and the store `(*_5) = ..` that reseats `_3` names `_5` as its place and
/// leaves no other trace on `_3`. The VALUE question refuses on the alias alone; the
/// ORIGIN question is only asked under the conduit gate, and a conduit that is written
/// through fails it. No hop, no origin — whether or not the conduit also feeds `next`.
#[test]
fn a_call_destination_reseated_through_its_conduit_refuses_the_hop() {
    let f = func(&format!(
        "{},{}",
        block(0, &range(4, 5), &call(REV, 3, &[4], 1)),
        block(1, &format!("{},{}", mut_borrow(5, 3), store_through(5)), RETURN)
    ));
    assert!(crate::local_defs::unique_value_call(&f, 3).is_none(), "the alias is a channel");
    assert!(call_dest_hop(&f, 3).is_none(), "and the conduit is written through");
    assert_eq!(end_of(&f, 3), None);

    // The same with the conduit ALSO feeding `next` afterwards — the real `alias_rev`
    // shape has a second conduit for the loop; one conduit doing both is refused too.
    let both = func(&format!(
        "{},{},{}",
        block(0, &range(4, 5), &call(REV, 3, &[4], 1)),
        block(1, &format!("{},{}", mut_borrow(5, 3), store_through(5)), &call(NEXT, 6, &[5], 2)),
        block(2, "", RETURN)
    ));
    assert!(call_dest_hop(&both, 3).is_none());
    assert_eq!(end_of(&both, 3), None);
}

/// THE ADMITTED ALIAS: the `for`-loop desugar with the identity copy folded away —
/// `_3 = rev(Range{0,5}); _5 = &mut _3; next(move _5)` — the bounded-reduction lane's
/// fixture shape and every `-Copt-level=1` body. The VALUE question refuses the alias;
/// the ORIGIN question answers under the conduit gate, because the local's only
/// mutation is `next` on itself. This row is what keeps the reviewer's gate from
/// turning that lane's refutation producer off.
#[test]
fn a_call_destination_whose_only_alias_feeds_next_is_admitted_by_the_origin_question() {
    let f = func(&format!(
        "{},{},{}",
        block(0, &range(4, 5), &call(REV, 3, &[4], 1)),
        block(1, &mut_borrow(5, 3), &call(NEXT, 6, &[5], 2)),
        block(2, "", RETURN)
    ));
    assert!(crate::local_defs::unique_value_call(&f, 3).is_none(), "the VALUE question refuses");
    assert!(
        crate::local_defs::unique_initializing_call(&f, 3).is_some(),
        "the ORIGIN question has an answer"
    );
    assert!(call_dest_hop(&f, 3).is_some(), "and the conduit gate licenses asking it");
    assert_eq!(end_of(&f, 3), Some(5));
}

/// A conduit handed to any call that is NOT `Iterator::next` (`mem::swap`, `by_ref`,
/// `nth`, ..) fails the gate, so the origin question is not asked and the hop refuses.
#[test]
fn a_call_destination_whose_alias_feeds_a_non_next_call_refuses_the_hop() {
    let f = func(&format!(
        "{},{},{}",
        block(0, &range(4, 5), &call(REV, 3, &[4], 1)),
        block(1, &mut_borrow(5, 3), &call("core::mem::swap", 6, &[5], 2)),
        block(2, "", RETURN)
    ));
    assert!(call_dest_hop(&f, 3).is_none());
    assert_eq!(end_of(&f, 3), None);
}

/// A PARAMETER written by one call holds two values (entry + the call); no hop.
#[test]
fn a_parameter_call_destination_refuses_the_hop() {
    let f = func(&format!(
        "{},{}",
        block(0, &range(4, 5), &call(REV, 1, &[4], 1)),
        block(1, "", RETURN)
    ));
    assert!(call_dest_hop(&f, 1).is_none());
    assert_eq!(end_of(&f, 1), None);
}

/// The gate holds THROUGH the chain: the `for`-loop desugar's `_7 = into_iter(move _8)`
/// is a clean one-call local, `_8 = move _3` a clean copy — and `_3` is the reseated
/// call destination. The trace crosses two sound hops and refuses at the third, exactly
/// where the reseat is; it does not remember the first constructor from anywhere.
#[test]
fn the_gate_refuses_at_the_reseated_hop_of_a_multi_hop_chain() {
    let f = func(&format!(
        "{},{},{},{}",
        block(0, &range(4, 5), &call(REV, 3, &[4], 1)),
        block(1, &range(6, 100), &call(REV, 5, &[6], 2)),
        block(2, &format!("{},{}", mv(3, 5), mv(8, 3)), &call(INTO_ITER, 7, &[8], 3)),
        block(3, "", RETURN)
    ));
    assert!(call_dest_hop(&f, 7).is_some(), "the desugar's `into_iter` dest is clean");
    assert_eq!(end_of(&f, 7), None, "but the chain ends at the reseated `_3`");

    // The control: the same chain over an UNRESEATED `_3` reaches the aggregate.
    let ok = func(&format!(
        "{},{},{}",
        block(0, &range(4, 5), &call(REV, 3, &[4], 1)),
        block(1, &mv(8, 3), &call(INTO_ITER, 7, &[8], 2)),
        block(2, "", RETURN)
    ));
    assert_eq!(end_of(&ok, 7), Some(5));
}

/// The ENUMERATE tracer's hop is the same gate: `_3 = iter(move _1)` reseated by
/// `_3 = move _5` (`_5 = iter(move _2)`) yields no slice; unreseated, it yields `_1`.
#[test]
fn the_enumerated_slice_hop_is_gated() {
    let ok = func(&format!(
        "{},{}",
        block(0, "", &sysroot_call(SLICE_ITER, 3, &[1], 1)),
        block(1, "", RETURN)
    ));
    assert!(matches!(
        trace_local_to_enumerated_slice(&ok, 3, 16),
        Some(Operand::Move(p)) if p.local == 1
    ));

    let reseated = func(&format!(
        "{},{},{}",
        block(0, "", &sysroot_call(SLICE_ITER, 3, &[1], 1)),
        block(1, "", &sysroot_call(SLICE_ITER, 5, &[2], 2)),
        block(2, &mv(3, 5), RETURN)
    ));
    assert!(trace_local_to_enumerated_slice(&reseated, 3, 16).is_none());

    // Through `enumerate`: `_4 = enumerate(move _3)`, `_3` reseated -> None.
    let via_enumerate = func(&format!(
        "{},{},{},{}",
        block(0, "", &sysroot_call(SLICE_ITER, 3, &[1], 1)),
        block(1, "", &sysroot_call(SLICE_ITER, 5, &[2], 2)),
        block(2, &mv(3, 5), &call(ENUMERATE, 4, &[3], 3)),
        block(3, "", RETURN)
    ));
    assert!(call_dest_hop(&via_enumerate, 4).is_some(), "the `enumerate` dest itself is clean");
    assert!(trace_local_to_enumerated_slice(&via_enumerate, 4, 16).is_none());
}

/// The `windows`/`chunks` tracer's hop is the same gate: a reseated `windows` dest has
/// no size operand to hand back.
#[test]
fn the_slice_iter_call_hop_is_gated() {
    let ok = func(&format!(
        "{},{}",
        block(0, "", &sysroot_call(WINDOWS, 3, &[1, 2], 1)),
        block(1, "", RETURN)
    ));
    assert!(trace_slice_iter_item(&ok, 3, &[], 16).is_some());

    let reseated = func(&format!(
        "{},{}",
        block(0, "", &sysroot_call(WINDOWS, 3, &[1, 2], 1)),
        block(1, &format!("{},{}", mut_borrow(5, 3), store_through(5)), RETURN)
    ));
    assert!(trace_slice_iter_item(&reseated, 3, &[], 16).is_none());
}

/// The `into_iter`-argument tracer's hop is the same gate. No `-Copt-level=0` source
/// program reaches a reseated dest here (the desugar's `into_iter` dest is a one-write
/// compiler temp), so this synthetic row is the pin for that hop.
#[test]
fn the_into_iter_arg_hop_is_gated() {
    let ok =
        func(&format!("{},{}", block(0, "", &call(INTO_ITER, 3, &[1], 1)), block(1, "", RETURN)));
    assert!(matches!(
        trace_iter_to_into_iter_arg(&ok, 3, 16),
        Some(Operand::Move(p)) if p.local == 1
    ));

    let reseated = func(&format!(
        "{},{},{}",
        block(0, "", &call(INTO_ITER, 3, &[1], 1)),
        block(1, "", &call(INTO_ITER, 3, &[2], 2)),
        block(2, "", RETURN)
    ));
    assert!(trace_iter_to_into_iter_arg(&reseated, 3, 16).is_none());

    let reseated_through_conduit = func(&format!(
        "{},{}",
        block(0, "", &call(INTO_ITER, 3, &[1], 1)),
        block(1, &format!("{},{}", mut_borrow(5, 3), store_through(5)), RETURN)
    ));
    assert!(trace_iter_to_into_iter_arg(&reseated_through_conduit, 3, 16).is_none());
}

// ── THE ENTRANCE HOP (2026-09-16, second round) ─────────────────────────────────
//
// The tracers are ENTERED from the `next` RESULT local through
// `iterator_yield::next_call_receiver` = `local_defs::unique_value_call`. These rows
// pin that gate on synthetic bodies; the compiler-MIR rows are the `two_next_*`
// section of `tests/escaped_local_seam_realmir.rs`.

const RANGE_NEXT: &str =
    "<core::ops::range::Range<usize> as core::iter::traits::iterator::Iterator>::next";

fn entrance_end_of(f: &VerifiableFunction, next_result: usize) -> Option<u64> {
    let origin = super::iterator_yield::next_call_range_operands(f, next_result, 16)?;
    match origin.end {
        Operand::Constant(trust_types::ConstValue::Uint(v, _)) => Some(*v as u64),
        _ => None,
    }
}

/// THE ADMITTED SHAPE: `_3 = Range{0,5}; _6 = &mut _3; _5 = next(move _6)` — one `next`
/// writes `_5`, and `_3`'s only conduit feeds it. The entrance answers `_6` and the
/// tracer reaches `end = 5`.
#[test]
fn a_next_result_with_one_write_channel_enters_the_tracer() {
    let f = func(&format!(
        "{},{}",
        block(0, &format!("{},{}", range(3, 5), mut_borrow(6, 3)), &call(RANGE_NEXT, 5, &[6], 1)),
        block(1, "", RETURN)
    ));
    assert_eq!(super::iterator_yield::next_call_receiver(&f, 5), Some(6));
    assert_eq!(entrance_end_of(&f, 5), Some(5));
}

/// THE WITNESS (`two_next_if`): `_5 = next(&mut _3)` in one branch and `_5 = next(&mut
/// _4)` in the other, `_3 = Range{0,5}`, `_4 = Range{50,100}`. The ungated entrance took
/// the FIRST call in block order and minted `small`'s `end = 5` onto a payload the
/// `big` branch produced. Now: no receiver, no origin — whichever call is spelled first.
#[test]
fn a_next_result_written_by_two_next_calls_refuses_the_entrance() {
    for (first, second) in [(3usize, 4usize), (4, 3)] {
        let f = func(&format!(
            "{},{},{},{}",
            block(0, &format!("{},{}", range(3, 5), range(4, 100)), r#"{"Goto":1}"#),
            block(1, &mut_borrow(6, first), &call(RANGE_NEXT, 5, &[6], 2)),
            block(2, &mut_borrow(7, second), &call(RANGE_NEXT, 5, &[7], 3)),
            block(3, "", RETURN)
        ));
        assert_eq!(super::iterator_yield::next_call_receiver(&f, 5), None, "two `next` writes");
        assert_eq!(
            entrance_end_of(&f, 5),
            None,
            "the tracer must decline, never read the first `next`"
        );
    }
}

/// A `&mut` alias of the `next` RESULT (`_8 = &mut _5`) is a channel through which the
/// Option can be reseated at a place no scan keyed on `_5` names; the entrance asks the
/// VALUE question, which refuses `Escape` outright — no desugar produces this shape, so
/// nothing is lost.
#[test]
fn an_aliased_next_result_refuses_the_entrance() {
    let f = func(&format!(
        "{},{}",
        block(0, &format!("{},{}", range(3, 5), mut_borrow(6, 3)), &call(RANGE_NEXT, 5, &[6], 1)),
        block(1, &mut_borrow(8, 5), RETURN)
    ));
    assert_eq!(super::iterator_yield::next_call_receiver(&f, 5), None);
    assert_eq!(entrance_end_of(&f, 5), None);
}

// Inclusive recovery shares every origin/payload gate above, but must never
// enter the exclusive cardinality API or exclude its closed endpoint.
const INCLUSIVE_NEW: &str = "core::ops::range::RangeInclusive::<usize>::new";
const INCLUSIVE_NEXT: &str =
    "<core::ops::range::RangeInclusive<usize> as core::iter::traits::iterator::Iterator>::next";

fn inclusive_range(dst: usize, end: u64, exhausted: serde_json::Value) -> String {
    let mut value: serde_json::Value = serde_json::from_str(&range(dst, end)).unwrap();
    let aggregate = value["Assign"]["rvalue"]["Aggregate"].as_array_mut().unwrap();
    aggregate[0]["Adt"]["name"] = "core::ops::range::RangeInclusive".into();
    aggregate[0]["Adt"]["args"] = "core::ops::range::RangeInclusive<usize>".into();
    aggregate[1].as_array_mut().unwrap().push(exhausted);
    value.to_string()
}

fn some_payload(dst: usize, src: usize) -> String {
    let mut value: serde_json::Value = serde_json::from_str(&mv(dst, src)).unwrap();
    value["Assign"]["rvalue"]["Use"]["Move"]["projections"] =
        serde_json::json!([{"Downcast": 1}, {"Field": 0}]);
    value.to_string()
}

fn inclusive_payload_body() -> VerifiableFunction {
    func(&format!(
        "{},{},{}",
        block(0, "", &call(INCLUSIVE_NEW, 4, &[1, 2], 1)),
        block(1, &mut_borrow(5, 4), &call(INCLUSIVE_NEXT, 7, &[5], 2)),
        block(2, &format!("{},{}", some_payload(6, 7), mv(0, 6)), RETURN),
    ))
}

fn inclusive_facts(f: &VerifiableFunction) -> Vec<super::Formula> {
    super::build_range_yield_guard_map(f).remove(&trust_types::BlockId(2)).unwrap_or_default()
}

#[test]
fn inclusive_yield_recovery_does_not_widen_the_exclusive_trip_count_api() {
    let f = inclusive_payload_body();
    let origin = super::trace_local_to_range_yield_origin(&f, 5, 16, true).unwrap();
    assert!(origin.end_inclusive);
    assert!(trace_local_to_range_aggregate(&f, 5, 16).is_none());
    assert!(super::next_call_range_operands(&f, 7, 16).is_none());
    assert!(super::next_call_range_origins(&f, 7, 16).is_none());
    let facts = inclusive_facts(&f);
    assert_eq!(facts.len(), 2, "both original yield-set bounds");
    assert!(facts.iter().any(|f| matches!(f, super::Formula::Le(..))));
    assert!(!facts.iter().any(|f| matches!(f, super::Formula::Lt(..))));
}

#[test]
fn inclusive_machine_maximum_is_a_closed_endpoint_without_increment() {
    let f = func(&format!(
        "{},{},{}",
        block(
            0,
            &inclusive_range(4, u64::MAX, serde_json::json!({"Constant":{"Bool":false}})),
            &call(INTO_ITER, 3, &[4], 1)
        ),
        block(1, &mut_borrow(5, 3), &call(INCLUSIVE_NEXT, 7, &[5], 2)),
        block(2, &format!("{},{}", some_payload(6, 7), mv(0, 6)), RETURN),
    ));
    let payload = super::Formula::var("_6", super::Sort::Int);
    assert!(inclusive_facts(&f).contains(&super::Formula::Le(
        Box::new(payload),
        Box::new(super::Formula::Int(u64::MAX.into())),
    )));
}

#[test]
fn inclusive_aggregate_requires_a_fresh_known_exhaustion_flag() {
    for exhausted in [
        serde_json::json!({"Constant":{"Bool":true}}),
        serde_json::json!({"Copy":{"local":1,"projections":[]}}),
    ] {
        let f = func(&block(0, &inclusive_range(4, 5, exhausted), RETURN));
        assert!(super::trace_local_to_range_yield_origin(&f, 4, 16, true).is_none());
    }
}

#[test]
fn inclusive_recovery_refuses_spoofed_constructor_and_unresolved_integer_types() {
    let mut spoofed = inclusive_payload_body();
    let trust_types::Terminator::Call { func: callee, .. } = &mut spoofed.body.blocks[0].terminator
    else {
        panic!("constructor")
    };
    *callee = "user::RangeInclusive::<usize>::new".into();
    assert!(inclusive_facts(&spoofed).is_empty());
    for ty in [
        trust_types::Ty::PtrSizedInt { signed: false },
        trust_types::Ty::Bool,
        trust_types::Ty::Int { width: 0, signed: false },
        trust_types::Ty::Int { width: 64, signed: true },
    ] {
        let mut f = inclusive_payload_body();
        f.body.locals[1].ty = ty;
        assert!(inclusive_facts(&f).is_empty());
    }
}

#[test]
fn inclusive_recovery_preserves_payload_reseat_and_conduit_refusals() {
    let mut payload = inclusive_payload_body();
    payload.body.blocks[2].stmts.insert(1, serde_json::from_str(&mv(6, 1)).unwrap());
    assert!(inclusive_facts(&payload).is_empty());

    let mut named = inclusive_payload_body();
    named.body.blocks[1].stmts.insert(0, serde_json::from_str(&mv(4, 1)).unwrap());
    assert!(inclusive_facts(&named).is_empty());

    let mut alias = inclusive_payload_body();
    alias.body.blocks[1].stmts.push(serde_json::from_str(&store_through(5)).unwrap());
    assert!(inclusive_facts(&alias).is_empty());

    let mut bound = inclusive_payload_body();
    bound.body.blocks[2].stmts.insert(0, serde_json::from_str(&mv(2, 1)).unwrap());
    assert!(inclusive_facts(&bound).is_empty());
}

#[test]
fn inclusive_and_exclusive_join_disjoins_both_endpoint_polarities() {
    let f = func(&format!(
        "{},{},{}",
        block(
            0,
            &format!(
                "{},{}",
                inclusive_range(4, 9, serde_json::json!({"Constant":{"Bool":false}})),
                mut_borrow(5, 4)
            ),
            &call(INCLUSIVE_NEXT, 7, &[5], 2)
        ),
        block(1, &format!("{},{}", range(3, 5), mut_borrow(8, 3)), &call(NEXT, 7, &[8], 2)),
        block(2, &format!("{},{}", some_payload(6, 7), mv(0, 6)), RETURN),
    ));
    let facts = inclusive_facts(&f);
    let [super::Formula::Or(groups)] = facts.as_slice() else { panic!("join: {facts:?}") };
    assert_eq!(groups.len(), 2);
    assert!(groups.iter().any(|g| matches!(g, super::Formula::And(xs)
        if xs.iter().any(|x| matches!(x, super::Formula::Le(..))))));
    assert!(groups.iter().any(|g| matches!(g, super::Formula::And(xs)
        if xs.iter().any(|x| matches!(x, super::Formula::Lt(..))))));

    let mut unknown = f;
    let trust_types::Statement::Assign {
        rvalue: trust_types::Rvalue::Aggregate(trust_types::AggregateKind::Adt { name, .. }, _),
        ..
    } = &mut unknown.body.blocks[1].stmts[0]
    else {
        panic!("range")
    };
    *name = "user::Range".into();
    assert!(inclusive_facts(&unknown).is_empty(), "one unmodeled origin denies the join");
}
