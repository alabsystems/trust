// Trust: the PARAMETER-ENTRY-DEF budget, pinned at the predicate rather than only at
// a verdict. `is_single_static_assignment` licenses treating a local's BARE name as a
// function-wide symbol; a PARAMETER's definition is the implicit ENTRY one, which
// `body.blocks` never carries, so a parameter reassigned once holds TWO values while a
// block scan reads one. Nothing but a unit test can hold that distinction: at the
// verdict level a wrong budget only shows up when some producer happens to key that
// local.
//
// THE ENTRY DEFINITION IS COUNTED UNCONDITIONALLY. A liveness relaxation — "no block
// can reach a mention of the parameter before its store, so the bare name still means
// one value" — was tried and REMOVED: it is a `body.blocks` analysis and the two
// channels that broke it (a `Call` destination's UNWIND edge, and the function's
// PRECONDITIONS, which `vc.formula` carries and which speak about the ENTRY value) are
// both outside `body.blocks`. `local_defs_tests` pins both channels at the count.

use trust_types::{ValueCount, VerifiableFunction};

use super::induction::build_downward_induction_facts;
use crate::local_defs::{is_single_static_assignment, value_count};

/// `_3 = Copy(_local)` — a READ of `_local`, which keeps a parameter's ENTRY value
/// live across a later store to it.
fn read(local: usize) -> String {
    format!(
        r#"{{"Assign":{{"place":{{"local":3,"projections":[]}},
           "rvalue":{{"Use":{{"Copy":{{"local":{local},"projections":[]}}}}}},
           "span":{{"file":"f.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}}}}}}"#
    )
}

/// `read(local)` followed by `assign(local)` — the parameter is read BEFORE it is
/// stored to, so its entry value is live and the store is its second value.
fn read_then_assign(local: usize) -> String {
    format!("{},{}", read(local), assign(local))
}

/// `fn f(_1: usize, _2: usize) -> usize`, one block, `stmts_json` as its statements
/// and `term_json` as its terminator. Locals `_0.._3` are all `usize` and
/// `arg_count = 2`, so `_1`/`_2` are PARAMETERS, `_3` is a temp and `_0` is the
/// return place.
fn body_with(stmts_json: &str, term_json: &str) -> VerifiableFunction {
    const SPAN: &str = r#"{"file":"f.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}"#;
    const USIZE: &str = r#"{"Int":{"width":64,"signed":false}}"#;
    let locals = (0..4)
        .map(|i| format!(r#"{{"index":{i},"ty":{USIZE},"name":null}}"#))
        .collect::<Vec<_>>()
        .join(",");
    let json = format!(
        r#"{{"name":"f","def_path":"f","span":{SPAN},"body":{{"locals":[{locals}],
           "blocks":[{{"id":0,"stmts":[{stmts_json}],"terminator":{term_json}}}],
           "arg_count":2,"return_ty":{USIZE}}},"contracts":[]}}"#
    );
    serde_json::from_str(&json).expect("the synthetic body must deserialize")
}

/// `_local = const 7`.
fn assign(local: usize) -> String {
    format!(
        r#"{{"Assign":{{"place":{{"local":{local},"projections":[]}},
           "rvalue":{{"Use":{{"Constant":{{"Uint":[7,64]}}}}}},
           "span":{{"file":"f.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}}}}}}"#
    )
}

const RETURN: &str = r#""Return""#;

/// The count IS the whole fix: a parameter's ENTRY definition is one of its values.
///
/// Killed by mutant D1-REVERT (`value_count` returns the raw explicit-def count).
#[test]
fn the_entry_definition_counts_as_a_parameter_value() {
    let f = body_with("", RETURN);
    assert_eq!(
        value_count(&f, 1),
        ValueCount::Exactly(1),
        "_1 is a parameter with no explicit def"
    );
    assert_eq!(
        value_count(&f, 2),
        ValueCount::Exactly(1),
        "_2 is a parameter with no explicit def"
    );
    assert_eq!(value_count(&f, 3), ValueCount::Exactly(0), "_3 is a temp with no def at all");
    assert_eq!(
        value_count(&f, 0),
        ValueCount::Exactly(0),
        "_0 is the return place, not a parameter"
    );

    let g = body_with(&read_then_assign(1), RETURN);
    assert_eq!(
        value_count(&g, 1),
        ValueCount::Exactly(2),
        "a read-then-stored parameter holds two values"
    );
    assert_eq!(
        value_count(&g, 3),
        ValueCount::Exactly(1),
        "the temp holds the one value it is assigned"
    );
}

/// The D1 hole, at the predicate. A parameter written ONCE holds two values — its
/// entry value and the written one — and must FAIL.
///
/// Killed by mutant D1-REVERT (`count == 1` for every local), under which this
/// asserts `false == true`.
#[test]
fn a_parameter_written_once_is_not_single_assignment() {
    let f = body_with(&read_then_assign(1), RETURN);
    assert!(!is_single_static_assignment(&f, 1));
}

/// A parameter stored to with NOTHING in `body.blocks` able to read it first is STILL
/// two-valued. Its ENTRY value is what the function's `#[requires]` speaks about, and
/// the preconditions ride in `vc.formula` — they are not in `body.blocks`, so no
/// liveness analysis of the blocks can see them. `deadentry_pre`
/// (`tests/entry_def_structural.rs`) is the end-to-end row.
///
/// Killed by mutant D1-DEADENTRY (restoring the removed liveness relaxation), under
/// which this asserts `true == false`. The precision that costs is measured in
/// `tests/entry_def_structural.rs` (§ THE PRICE).
#[test]
fn a_parameter_stored_to_before_any_read_is_still_two_valued() {
    let f = body_with(&assign(1), RETURN);
    assert_eq!(value_count(&f, 1), ValueCount::Exactly(2));
    assert!(!is_single_static_assignment(&f, 1));
}

/// The other half of the budget, and the reason it is not simply "reject parameters":
/// a NEVER-written parameter has exactly one value for the whole body, so it PASSES.
///
/// Killed by mutant D1-BLANKET (`is_parameter(..) => false` unconditionally), under
/// which every parameter-keyed fact disappears and this asserts `false == true`.
#[test]
fn a_never_written_parameter_is_single_assignment() {
    let f = body_with(&assign(3), RETURN);
    assert!(is_single_static_assignment(&f, 1));
    assert!(is_single_static_assignment(&f, 2));
}

/// The non-parameter arm is unchanged: exactly one def, never zero and never two.
#[test]
fn a_temp_still_needs_exactly_one_def() {
    assert!(!is_single_static_assignment(&body_with("", RETURN), 3), "no def at all");
    assert!(is_single_static_assignment(&body_with(&assign(3), RETURN), 3), "one def");
    let two = format!("{},{}", assign(3), assign(3));
    assert!(!is_single_static_assignment(&body_with(&two, RETURN), 3), "two defs");
}

/// A parameter stored to TWICE holds THREE values — the entry one and the two stores.
#[test]
fn a_parameter_written_twice_is_never_single_assignment() {
    let twice = format!("{},{}", assign(1), assign(1));
    assert!(!is_single_static_assignment(&body_with(&twice, RETURN), 1));
}

/// A parameter with zero explicit stores is still killed by a `&mut` borrow — the
/// write channel a def scan cannot see. The budget must be ANDed with that kill, not
/// substituted for it.
///
/// Killed by mutant D1-DROP-BORROW-KILL (returning on the budget before the
/// `Ref { mutable: true }` scan).
#[test]
fn a_mutably_borrowed_parameter_is_still_rejected() {
    let borrow = r#"{"Assign":{"place":{"local":3,"projections":[]},
        "rvalue":{"Ref":{"mutable":true,"place":{"local":1,"projections":[]}}},
        "span":{"file":"f.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}}}"#;
    let f = body_with(borrow, RETURN);
    assert!(!is_single_static_assignment(&f, 1));
}

/// A CALL destination counts toward the budget exactly like an `Assign` place, so a
/// parameter that receives a call result also fails — and a temp that receives one
/// still passes.
#[test]
fn a_parameter_written_by_a_call_dest_is_rejected() {
    let call = |dest: usize| {
        format!(
            r#"{{"Call":{{"func":"g","args":[],"dest":{{"local":{dest},"projections":[]}},
               "target":0,
               "span":{{"file":"f.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}},
               "atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}}}"#
        )
    };
    assert!(!is_single_static_assignment(&body_with(&read(1), &call(1)), 1));
    assert!(is_single_static_assignment(&body_with("", &call(3)), 3));
}

/// A store THROUGH a parameter (`*p = ..`, a `Deref`-first projection) mutates the
/// POINTEE, not the parameter, so it does not spend the budget.
#[test]
fn a_deref_store_through_a_parameter_does_not_spend_the_budget() {
    let deref_store = r#"{"Assign":{"place":{"local":1,"projections":["Deref"]},
        "rvalue":{"Use":{"Constant":{"Uint":[7,64]}}},
        "span":{"file":"f.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}}}"#;
    let f = body_with(deref_store, RETURN);
    assert!(is_single_static_assignment(&f, 1));
}

// ── THE SPLIT: two questions, and why one predicate could not answer both ──
//
// `is_single_static_assignment` above answers "may this local's BARE NAME carry a
// function-wide invariant?". `dest_fact_is_version_pinnable` answers "does this call's
// POST-CALL TOKEN `{dest}#s{b}_t` name one value?". They were ONE predicate until
// 2026-08-31, and that is why `callee_postcondition_is_injectable` — a
// version-pinned lane — was gated on the bare-name question, and why the bare-name
// producers were gated on a predicate that admitted a reassigned parameter.
//
// The two answers differ on EXACTLY ONE shape, the `mut` parameter written by one
// `Call` destination, and both answers are required:
//
//   * admitting it at a BARE-NAME site is a live kernel-certified false proof —
//     `pub fn wc(mut i: u8, j: u8, c: bool) -> u8 { if c { i = j.min(3); } i + 200 }`,
//     whose `min` call lands directly on the parameter at `-Copt-level=1`. Stock
//     rustc 1.96.0 with `-C debug-assertions=on -C opt-level=1`, executed over the
//     swept input space, panics on 51,200 of 131,072 inputs (first `wc(56,0,false)`);
//   * refusing it at the VERSION-PINNED site destroys real proofs and prevents no
//     false one, because nothing reads the entry value under the pinned spelling.

/// A `Call` terminator whose destination is `dest`, self-looping so the single-block
/// fixture stays well-formed.
fn call_dest(dest: usize) -> String {
    format!(
        r#"{{"Call":{{"func":"g","args":[],"dest":{{"local":{dest},"projections":[]}},
           "target":0,
           "span":{{"file":"f.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}},
           "atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}}}"#
    )
}

/// THE SPLIT, asserted in both directions on the one shape that separates the two
/// questions. Asserting only the admission would let them silently re-merge — a
/// re-merge in either direction is a defect, so both halves are pinned.
#[test]
fn the_two_definition_questions_differ_on_a_call_written_parameter() {
    // The shape: `_1` is a PARAMETER and this call is its only whole write.
    let param_dest = body_with("", &call_dest(1));
    assert!(
        crate::local_defs::dest_fact_is_version_pinnable(&param_dest, 1),
        "the post-call token names one value: this call is the dest's only whole write"
    );
    assert!(
        !is_single_static_assignment(&param_dest, 1),
        "the BARE name does not: the parameter's ENTRY definition is a second value \
         it also denotes (witness `wc`)"
    );

    // Everywhere else the two agree. A fresh temp written by the same call:
    let temp_dest = body_with("", &call_dest(3));
    assert!(crate::local_defs::dest_fact_is_version_pinnable(&temp_dest, 3));
    assert!(is_single_static_assignment(&temp_dest, 3));
    // ...and a local with no whole write at all is admitted by neither.
    assert!(!crate::local_defs::dest_fact_is_version_pinnable(&body_with("", RETURN), 3));
    assert!(!is_single_static_assignment(&body_with("", RETURN), 3));
}

/// THE PAIRING THAT MAKES THE SPLIT SOUND, asserted rather than left to a comment.
///
/// A version-pinned fact is safe only because `{dest}#s{b}_t` is name-disjoint from the
/// bare name the ENTRY value is read under. TWO passes rewrite a versioned token to the
/// bare name — `discharge::normalize_ssa_version_tokens` and
/// `discharge::bare_ssa_guard_variant` — and they are the complete set (every other
/// `split('#')` in the crate READS a base name to classify or match, and none of them
/// renames). BOTH are gated on the SAME predicate, `local_versions_collapse_to_bare`,
/// which is therefore the one seam this test has to pin; and that predicate's PARAMETER
/// arm requires `!local_has_call_dest_write`, which every destination admitted here has
/// by construction.
///
/// So the entailment below is not a coincidence of these fixtures; it is
/// `dest_fact_is_version_pinnable`'s own precondition read through the collapse
/// predicate. Deleting the `!local_has_call_dest_write` clause of
/// `local_versions_collapse_to_bare` would make the injection lane unsound, and it
/// fails HERE rather than as a false proof somewhere downstream.
#[test]
fn a_version_pinned_parameter_dest_can_never_collapse_to_the_bare_name() {
    for (what, f, local) in [
        ("the parameter destination", body_with("", &call_dest(1)), 1usize),
        ("a parameter read before the call", body_with(&read(1), &call_dest(1)), 1),
        ("the second parameter", body_with("", &call_dest(2)), 2),
    ] {
        assert!(
            crate::local_defs::dest_fact_is_version_pinnable(&f, local),
            "{what}: the shape under test must be one the injection lane admits"
        );
        assert!(
            !super::discharge::local_versions_collapse_to_bare(&f, local),
            "{what}: a parameter with a call-dest write must NEVER collapse its \
             versioned tokens to the bare name — that collapse is the only thing \
             that could bind the post-call fact to the entry value"
        );
    }
}

/// What the version-pinned question still refuses. Each of these would break the
/// blanket base-name rewrite `version_terminator_dest_fact` performs: it retimes EVERY
/// occurrence of the dest's base name to this call's token, which equals the targeted
/// rewrite only when this call is the local's one whole write.
#[test]
fn the_version_pinned_question_refuses_every_other_write_channel() {
    // A second whole write — an `Assign` beside the call — is a version this pin does
    // not name, and the blanket rewrite would retime its reads too.
    assert!(!crate::local_defs::dest_fact_is_version_pinnable(
        &body_with(&assign(1), &call_dest(1)),
        1
    ));
    assert!(!crate::local_defs::dest_fact_is_version_pinnable(
        &body_with(&assign(3), &call_dest(3)),
        3
    ));

    // A MUTABLE ALIAS: a store through it names a different place, mints no token, and
    // leaves the pin on a stale value.
    let borrow = r#"{"Assign":{"place":{"local":3,"projections":[]},
        "rvalue":{"Ref":{"mutable":true,"place":{"local":1,"projections":[]}}},
        "span":{"file":"f.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}}}"#;
    assert!(!crate::local_defs::dest_fact_is_version_pinnable(
        &body_with(borrow, &call_dest(1)),
        1
    ));

    // A PARTIAL write — a field store — changes the local at a point that mints no
    // token here.
    let field_store = r#"{"Assign":{"place":{"local":1,"projections":[{"Field":0}]},
        "rvalue":{"Use":{"Constant":{"Uint":[7,64]}}},
        "span":{"file":"f.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}}}"#;
    assert!(!crate::local_defs::dest_fact_is_version_pinnable(
        &body_with(field_store, &call_dest(1)),
        1
    ));

    // And an `Assign`-written local with NO call at all: there is no post-call token to
    // pin to, so the question answers `false` even though the bare-name question — for
    // a non-parameter — says yes.
    assert!(!crate::local_defs::dest_fact_is_version_pinnable(&body_with(&assign(3), RETURN), 3));
    assert!(is_single_static_assignment(&body_with(&assign(3), RETURN), 3));
}

// ── the DECREMENT-TUPLE gate (`generate/induction.rs`) ─────────────────────
//
// `build_downward_induction_facts` and `build_countdown_trip_facts` key their bounds
// on `_t.0`, the FIELD of the `CheckedSub` destination. The def scan that qualifies a
// downward-induction variable constrains the CURSOR, never that tuple — so a `_t` with
// a second definition would have carried a bound about a value it no longer holds.
// rustc-built MIR gives every `CheckedBinaryOp` its own temp, so no capture of the
// merged shape exists; these two fixtures are the SAME real capture, one of them with
// a second whole-local def of `_7` inserted, and they pin the gate's contract.

/// `-Ztrust-dump=mir` capture of
///
///   pub fn p15_induction(mut i: usize, c: bool, s: &[u8; 4]) -> u8 {
///       let mut t = 0u8;
///       if c { i = 4; while i > 0 { i -= 1; t = t.wrapping_add(s[i]); } t } else { s[i] }
///   }
///
/// The producer emits `_7.0 <= 3` — `_7` is the `SubWithOverflow` destination of
/// `i -= 1`.
const MIR_P15_INDUCTION: &str = r##"{"name":"p15_induction","def_path":"p15_induction::p15_induction","span":{"file":"probes/p15_induction.rs","line_start":1,"col_start":0,"line_end":4,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":1,"ty":{"Int":{"width":64,"signed":false}},"name":"i"},{"index":2,"ty":"Bool","name":"c"},{"index":3,"ty":{"Ref":{"mutable":false,"inner":{"Array":{"elem":{"Int":{"width":8,"signed":false}},"len":4}}}},"name":"s"},{"index":4,"ty":{"Int":{"width":8,"signed":false}},"name":"t"},{"index":5,"ty":"Bool","name":null},{"index":6,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":7,"ty":{"Tuple":[{"Int":{"width":64,"signed":false}},"Bool"]},"name":null},{"index":8,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":9,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":10,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":11,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":12,"ty":"Bool","name":null},{"index":13,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":14,"ty":"Bool","name":null}],"blocks":[{"id":0,"stmts":[{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,8]}}},"span":{"file":"probes/p15_induction.rs","line_start":2,"col_start":16,"line_end":2,"col_end":19}}}],"terminator":{"SwitchInt":{"discr":{"Copy":{"local":2,"projections":[]}},"targets":[[0,8]],"otherwise":1,"exhaustive_enum_unreachable":false,"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":7,"line_end":3,"col_end":8}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":1,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[4,64]}}},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":11,"line_end":3,"col_end":16}}}],"terminator":{"Goto":2}},{"id":2,"stmts":[{"Assign":{"place":{"local":6,"projections":[]},"rvalue":{"Use":{"Copy":{"local":1,"projections":[]}}},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":24,"line_end":3,"col_end":25}}},{"Assign":{"place":{"local":5,"projections":[]},"rvalue":{"BinaryOp":["Gt",{"Move":{"local":6,"projections":[]}},{"Constant":{"Uint":[0,64]}}]},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":24,"line_end":3,"col_end":29}}}],"terminator":{"SwitchInt":{"discr":{"Move":{"local":5,"projections":[]}},"targets":[[0,7]],"otherwise":3,"exhaustive_enum_unreachable":false,"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":24,"line_end":3,"col_end":29}}}},{"id":3,"stmts":[{"Assign":{"place":{"local":7,"projections":[]},"rvalue":{"CheckedBinaryOp":["Sub",{"Copy":{"local":1,"projections":[]}},{"Constant":{"Uint":[1,64]}}]},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":32,"line_end":3,"col_end":38}}}],"terminator":{"Assert":{"cond":{"Move":{"local":7,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Sub"},"target":4,"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":32,"line_end":3,"col_end":38},"unwind":"Continue"}}},{"id":4,"stmts":[{"Assign":{"place":{"local":1,"projections":[]},"rvalue":{"Use":{"Move":{"local":7,"projections":[{"Field":0}]}}},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":32,"line_end":3,"col_end":38}}},{"Assign":{"place":{"local":9,"projections":[]},"rvalue":{"Use":{"Copy":{"local":4,"projections":[]}}},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":44,"line_end":3,"col_end":45}}},{"Assign":{"place":{"local":11,"projections":[]},"rvalue":{"Use":{"Copy":{"local":1,"projections":[]}}},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":61,"line_end":3,"col_end":62}}},{"Assign":{"place":{"local":12,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":11,"projections":[]}},{"Constant":{"Uint":[4,64]}}]},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":59,"line_end":3,"col_end":63}}}],"terminator":{"Assert":{"cond":{"Move":{"local":12,"projections":[]}},"expected":true,"msg":"BoundsCheck","target":5,"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":59,"line_end":3,"col_end":63},"unwind":"Continue"}}},{"id":5,"stmts":[{"Assign":{"place":{"local":10,"projections":[]},"rvalue":{"Use":{"Copy":{"local":3,"projections":["Deref",{"Index":11}]}}},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":59,"line_end":3,"col_end":63}}}],"terminator":{"Call":{"func":"@trust-rustc-total-primitive-method::core::num::<impl u8>::wrapping_add","args":[{"Move":{"local":9,"projections":[]}},{"Move":{"local":10,"projections":[]}}],"dest":{"local":8,"projections":[]},"target":6,"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":44,"line_end":3,"col_end":64},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}},{"id":6,"stmts":[{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"Use":{"Move":{"local":8,"projections":[]}}},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":40,"line_end":3,"col_end":64}}}],"terminator":{"Goto":2}},{"id":7,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":4,"projections":[]}}},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":68,"line_end":3,"col_end":69}}}],"terminator":{"Goto":10}},{"id":8,"stmts":[{"Assign":{"place":{"local":13,"projections":[]},"rvalue":{"Use":{"Copy":{"local":1,"projections":[]}}},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":81,"line_end":3,"col_end":82}}},{"Assign":{"place":{"local":14,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":13,"projections":[]}},{"Constant":{"Uint":[4,64]}}]},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":79,"line_end":3,"col_end":83}}}],"terminator":{"Assert":{"cond":{"Move":{"local":14,"projections":[]}},"expected":true,"msg":"BoundsCheck","target":9,"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":79,"line_end":3,"col_end":83},"unwind":"Continue"}}},{"id":9,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":3,"projections":["Deref",{"Index":13}]}}},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":79,"line_end":3,"col_end":83}}}],"terminator":{"Goto":10}},{"id":10,"stmts":[],"terminator":"Return"}],"arg_count":3,"return_ty":{"Int":{"width":8,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["i","Int"]},{"Int":0}]},{"Le":[{"Var":["i","Int"]},{"Int":18446744073709551615}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"##;

/// The same capture with a `Call` terminator whose DESTINATION is `_7` appended.
/// `unique_value_def` — which is what qualifies the decrement — scans only
/// `Statement::Assign`, so it does NOT see a call-dest write and still reports one
/// def; only the explicit-budget gate rejects this body.
const MIR_P15_INDUCTION_MERGED_TUPLE: &str = r##"{"name":"p15_induction_calldest_tuple","def_path":"p15_induction::p15_induction","span":{"file":"probes/p15_induction.rs","line_start":1,"col_start":0,"line_end":4,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":1,"ty":{"Int":{"width":64,"signed":false}},"name":"i"},{"index":2,"ty":"Bool","name":"c"},{"index":3,"ty":{"Ref":{"mutable":false,"inner":{"Array":{"elem":{"Int":{"width":8,"signed":false}},"len":4}}}},"name":"s"},{"index":4,"ty":{"Int":{"width":8,"signed":false}},"name":"t"},{"index":5,"ty":"Bool","name":null},{"index":6,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":7,"ty":{"Tuple":[{"Int":{"width":64,"signed":false}},"Bool"]},"name":null},{"index":8,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":9,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":10,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":11,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":12,"ty":"Bool","name":null},{"index":13,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":14,"ty":"Bool","name":null}],"blocks":[{"id":0,"stmts":[{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,8]}}},"span":{"file":"probes/p15_induction.rs","line_start":2,"col_start":16,"line_end":2,"col_end":19}}}],"terminator":{"SwitchInt":{"discr":{"Copy":{"local":2,"projections":[]}},"targets":[[0,8]],"otherwise":1,"exhaustive_enum_unreachable":false,"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":7,"line_end":3,"col_end":8}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":1,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[4,64]}}},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":11,"line_end":3,"col_end":16}}}],"terminator":{"Goto":2}},{"id":2,"stmts":[{"Assign":{"place":{"local":6,"projections":[]},"rvalue":{"Use":{"Copy":{"local":1,"projections":[]}}},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":24,"line_end":3,"col_end":25}}},{"Assign":{"place":{"local":5,"projections":[]},"rvalue":{"BinaryOp":["Gt",{"Move":{"local":6,"projections":[]}},{"Constant":{"Uint":[0,64]}}]},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":24,"line_end":3,"col_end":29}}}],"terminator":{"SwitchInt":{"discr":{"Move":{"local":5,"projections":[]}},"targets":[[0,7]],"otherwise":3,"exhaustive_enum_unreachable":false,"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":24,"line_end":3,"col_end":29}}}},{"id":3,"stmts":[{"Assign":{"place":{"local":7,"projections":[]},"rvalue":{"CheckedBinaryOp":["Sub",{"Copy":{"local":1,"projections":[]}},{"Constant":{"Uint":[1,64]}}]},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":32,"line_end":3,"col_end":38}}}],"terminator":{"Assert":{"cond":{"Move":{"local":7,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Sub"},"target":4,"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":32,"line_end":3,"col_end":38},"unwind":"Continue"}}},{"id":4,"stmts":[{"Assign":{"place":{"local":1,"projections":[]},"rvalue":{"Use":{"Move":{"local":7,"projections":[{"Field":0}]}}},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":32,"line_end":3,"col_end":38}}},{"Assign":{"place":{"local":9,"projections":[]},"rvalue":{"Use":{"Copy":{"local":4,"projections":[]}}},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":44,"line_end":3,"col_end":45}}},{"Assign":{"place":{"local":11,"projections":[]},"rvalue":{"Use":{"Copy":{"local":1,"projections":[]}}},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":61,"line_end":3,"col_end":62}}},{"Assign":{"place":{"local":12,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":11,"projections":[]}},{"Constant":{"Uint":[4,64]}}]},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":59,"line_end":3,"col_end":63}}}],"terminator":{"Assert":{"cond":{"Move":{"local":12,"projections":[]}},"expected":true,"msg":"BoundsCheck","target":5,"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":59,"line_end":3,"col_end":63},"unwind":"Continue"}}},{"id":5,"stmts":[{"Assign":{"place":{"local":10,"projections":[]},"rvalue":{"Use":{"Copy":{"local":3,"projections":["Deref",{"Index":11}]}}},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":59,"line_end":3,"col_end":63}}}],"terminator":{"Call":{"func":"@trust-rustc-total-primitive-method::core::num::<impl u8>::wrapping_add","args":[{"Move":{"local":9,"projections":[]}},{"Move":{"local":10,"projections":[]}}],"dest":{"local":8,"projections":[]},"target":6,"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":44,"line_end":3,"col_end":64},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}},{"id":6,"stmts":[{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"Use":{"Move":{"local":8,"projections":[]}}},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":40,"line_end":3,"col_end":64}}}],"terminator":{"Goto":2}},{"id":7,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":4,"projections":[]}}},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":68,"line_end":3,"col_end":69}}}],"terminator":{"Goto":10}},{"id":8,"stmts":[{"Assign":{"place":{"local":13,"projections":[]},"rvalue":{"Use":{"Copy":{"local":1,"projections":[]}}},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":81,"line_end":3,"col_end":82}}},{"Assign":{"place":{"local":14,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":13,"projections":[]}},{"Constant":{"Uint":[4,64]}}]},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":79,"line_end":3,"col_end":83}}}],"terminator":{"Assert":{"cond":{"Move":{"local":14,"projections":[]}},"expected":true,"msg":"BoundsCheck","target":9,"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":79,"line_end":3,"col_end":83},"unwind":"Continue"}}},{"id":9,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":3,"projections":["Deref",{"Index":13}]}}},"span":{"file":"probes/p15_induction.rs","line_start":3,"col_start":79,"line_end":3,"col_end":83}}}],"terminator":{"Goto":10}},{"id":10,"stmts":[],"terminator":"Return"},{"id":11,"stmts":[],"terminator":{"Call":{"func":"reseat","args":[],"dest":{"local":7,"projections":[]},"target":11,"span":{"file":"p15","line_start":1,"col_start":1,"line_end":1,"col_end":1},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}}],"arg_count":3,"return_ty":{"Int":{"width":8,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["i","Int"]},{"Int":0}]},{"Le":[{"Var":["i","Int"]},{"Int":18446744073709551615}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"##;

/// Killed by mutant IND-TUPLE-DROP (deleting the three
/// `is_single_static_assignment(func, t*)` gates from `generate/induction.rs`), which
/// is otherwise a SURVIVOR of the whole `trust-vcgen` suite.
#[test]
fn a_merged_decrement_tuple_loses_its_downward_bound() {
    let stable: VerifiableFunction =
        serde_json::from_str(MIR_P15_INDUCTION).expect("the stable-tuple capture must deserialize");
    let merged: VerifiableFunction = serde_json::from_str(MIR_P15_INDUCTION_MERGED_TUPLE)
        .expect("the call-dest-tuple fixture must deserialize");
    let facts = |f: &VerifiableFunction| -> Vec<String> {
        build_downward_induction_facts(f).iter().map(|x| format!("{x:?}")).collect()
    };
    let stable_facts = facts(&stable);
    assert!(
        stable_facts.iter().any(|f| f.contains("_7.0")),
        "the single-def decrement tuple carries its bound: {stable_facts:?}"
    );
    let merged_facts = facts(&merged);
    assert!(
        merged_facts.iter().all(|f| !f.contains("_7.0")),
        "a call-dest-written decrement tuple must carry NO bound: {merged_facts:?}"
    );
}

// ── the CharIndices shared-slice ROOT gate (`generate/iterator_yield.rs`) ───

/// `fn f(_1: &[u8], _2: usize)` that READS the slice parameter `_1` and then
/// redefines it. The reaching def is a CONSTANT `Use`, so the root trace stops at `_1`
/// itself rather than hopping through a copy — the root under test IS the reassigned
/// parameter, and the leading read keeps its ENTRY value live.
fn reassigned_slice_param() -> VerifiableFunction {
    const SPAN: &str = r#"{"file":"f.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}"#;
    const SLICE: &str = r#"{"Ref":{"mutable":false,"inner":{"Slice":{"elem":{"Int":{"width":8,"signed":false}}}}}}"#;
    const USIZE: &str = r#"{"Int":{"width":64,"signed":false}}"#;
    let json = format!(
        r#"{{"name":"f","def_path":"f","span":{SPAN},"body":{{"locals":[
           {{"index":0,"ty":{USIZE},"name":null}},
           {{"index":1,"ty":{SLICE},"name":"s"}},
           {{"index":2,"ty":{USIZE},"name":"n"}}],
           "blocks":[{{"id":0,"stmts":[
             {{"Assign":{{"place":{{"local":0,"projections":[]}},
               "rvalue":{{"Use":{{"Copy":{{"local":1,"projections":[]}}}}}},"span":{SPAN}}}}},
             {{"Assign":{{"place":{{"local":1,"projections":[]}},
               "rvalue":{{"Use":{{"Constant":{{"Uint":[0,64]}}}}}},"span":{SPAN}}}}}],
             "terminator":"Return"}}],
           "arg_count":2,"return_ty":{USIZE}}},"contracts":[]}}"#
    );
    serde_json::from_str(&json).expect("the synthetic body must deserialize")
}

/// The CharIndices yield lane traces a `&str`/`&[T]` operand to its ROOT and treats
/// that root's bare name as a stable slice symbol. Its root gate used to read
/// `is_parameter(l) || <explicit def count>(l) == 1` — a disjunction that let a
/// PARAMETER skip the def count entirely, so a reassigned `mut s: &[u8]` qualified
/// while its bare name still means the ENTRY slice. Same class as the budget above.
///
/// Killed by mutant CHARINDICES-REVERT (restoring that disjunction), which is
/// otherwise a SURVIVOR of the whole `trust-vcgen` suite.
#[test]
fn a_reassigned_slice_parameter_is_not_a_stable_charindices_root() {
    let f = reassigned_slice_param();
    let op = trust_types::Operand::Copy(trust_types::Place::local(1));
    assert_eq!(super::iterator_yield::charindices_shared_slice_root(&f, &op), None);
}

/// The same body with the redefinition removed: a never-written slice parameter IS a
/// stable root, so the gate is a budget and not a ban.
#[test]
fn a_never_written_slice_parameter_is_still_a_stable_charindices_root() {
    let mut f = reassigned_slice_param();
    f.body.blocks[0].stmts.truncate(1);
    let op = trust_types::Operand::Copy(trust_types::Place::local(1));
    assert_eq!(super::iterator_yield::charindices_shared_slice_root(&f, &op), Some(1));
}
