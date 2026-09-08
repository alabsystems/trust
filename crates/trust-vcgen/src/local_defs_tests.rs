// Trust: the DEFINITION SEAM, pinned at the predicate.
//
// Three rounds of site-by-site patching did not converge on the parameter-entry-def
// class because every round fixed the sites it happened to enumerate. The structural
// answer is that `body.blocks` is scanned in ONE module and every other caller asks a
// question that already knows about the entry definition. These rows pin the questions
// themselves; the end-to-end verdicts live in `tests/entry_def_structural.rs`.

use trust_types::{ValueCount, VerifiableFunction};

use super::{
    has_one_explicit_def, holds_one_value, is_single_static_assignment, never_explicitly_reseated,
    unique_value_def, value_count,
};

const SPAN: &str = r#"{"file":"f.rs","line_start":1,"col_start":1,"line_end":1,"col_end":1}"#;
const USIZE: &str = r#"{"Int":{"width":64,"signed":false}}"#;

/// `fn f(_1: usize, _2: usize) -> usize` with `blocks_json` as its whole CFG. Locals
/// `_0.._4` are all `usize`; `arg_count = 2`, so `_1`/`_2` are PARAMETERS, `_3`/`_4`
/// are temps and `_0` is the return place.
fn func(blocks_json: &str) -> VerifiableFunction {
    let locals = (0..5)
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

/// `_dst = const 7`.
fn store(dst: usize) -> String {
    format!(
        r#"{{"Assign":{{"place":{{"local":{dst},"projections":[]}},
           "rvalue":{{"Use":{{"Constant":{{"Uint":[7,64]}}}}}},"span":{SPAN}}}}}"#
    )
}

/// `_4 = Copy(_src)` — a read of `_src`.
fn read(src: usize) -> String {
    format!(
        r#"{{"Assign":{{"place":{{"local":4,"projections":[]}},
           "rvalue":{{"Use":{{"Copy":{{"local":{src},"projections":[]}}}}}},"span":{SPAN}}}}}"#
    )
}

const RETURN: &str = r#""Return""#;

fn goto(t: usize) -> String {
    format!(r#"{{"Goto":{t}}}"#)
}

/// `switch _2 { 0 => a, _ => b }`.
fn switch(a: usize, b: usize) -> String {
    format!(
        r#"{{"SwitchInt":{{"discr":{{"Copy":{{"local":2,"projections":[]}}}},
           "targets":[[0,{a}]],"otherwise":{b},"exhaustive_enum_unreachable":false,
           "span":{SPAN}}}}}"#
    )
}

// ── the count ──────────────────────────────────────────────────────────────

/// The ENTRY definition is what the class is about: a parameter starts with one value
/// and nothing in `body.blocks` says so.
#[test]
fn a_parameter_starts_with_one_value_and_a_temp_with_none() {
    let f = func(&block(0, "", RETURN));
    assert_eq!(value_count(&f, 1), ValueCount::Exactly(1), "_1 is a parameter");
    assert_eq!(value_count(&f, 3), ValueCount::Exactly(0), "_3 is an undefined temp");
    assert_eq!(
        value_count(&f, 0),
        ValueCount::Exactly(0),
        "_0 is the return place, not a parameter"
    );
    assert!(holds_one_value(&f, 1));
    assert!(!holds_one_value(&f, 3));
    assert!(never_explicitly_reseated(&f, 1));
    assert!(!has_one_explicit_def(&f, 1), "a parameter has no statement to inspect");
}

/// The whole defect, at the count. `_1 = 7` on a parameter whose entry value is LIVE
/// (bb0 reads it, bb1 stores to it) is its SECOND value.
#[test]
fn a_live_entry_parameter_stored_to_once_holds_two_values() {
    let f = func(&format!("{},{}", block(0, &read(1), &goto(1)), block(1, &store(1), RETURN)));
    assert_eq!(value_count(&f, 1), ValueCount::Exactly(2));
    assert!(!holds_one_value(&f, 1));
    assert!(!is_single_static_assignment(&f, 1));
    assert!(!has_one_explicit_def(&f, 1));
    assert!(!never_explicitly_reseated(&f, 1));
    assert!(unique_value_def(&f, 1).is_none(), "the store is not the parameter's value");
}

/// The non-parameter arm is untouched: exactly one whole-local definition.
#[test]
fn a_temp_holds_one_value_per_definition() {
    assert_eq!(value_count(&func(&block(0, &store(3), RETURN)), 3), ValueCount::Exactly(1));
    let two = format!("{},{}", store(3), store(3));
    assert_eq!(value_count(&func(&block(0, &two, RETURN)), 3), ValueCount::Exactly(2));
    assert!(has_one_explicit_def(&func(&block(0, &store(3), RETURN)), 3));
}

// ── the entry definition, counted unconditionally ─────────────────────────
//
// A liveness relaxation lived here: "no block can reach a mention of the parameter
// before its store, so the bare name means one value". It was REMOVED. It is an
// analysis of `body.blocks`, and both channels that broke it are outside
// `body.blocks` — the rows below are those two channels, each stated as the count.

/// R2. `_1 = 7; _4 = _1` — the store dominates every mention of `_1` in the whole
/// body, which is exactly what the removed relaxation certified as a dead entry value.
/// It is still TWO values, because `vc.formula` also carries the function's
/// PRECONDITIONS and `#[core::contracts::requires(..)]` is stated about the parameter's
/// ENTRY value; a post-store fact renamed onto that symbol contradicts the
/// precondition and empties the path.
/// End-to-end: `tests/entry_def_structural.rs::a_requires_contract_on_a_stored_
/// parameter_still_refutes` (`deadentry_pre`).
#[test]
fn a_stored_parameter_is_two_valued_even_when_no_block_reads_it_first() {
    let f = func(&block(0, &format!("{},{}", store(1), read(1)), RETURN));
    assert_eq!(value_count(&f, 1), ValueCount::Exactly(2));
    assert!(!holds_one_value(&f, 1));
    assert!(!is_single_static_assignment(&f, 1));
    assert!(unique_value_def(&f, 1).is_none());
}

/// R1. `bb0: _1 = g() -> [return: bb1, unwind: Cleanup(bb2)]`, `bb2: _4 = _1`. On the
/// UNWIND edge the call never wrote `_1`, so the cleanup region reads the ENTRY value.
/// The removed relaxation treated a definition block as ABSORBING — it stopped the
/// walk there and never explored the cleanup successor — so `bb2` was classified as
/// dominated by the definition and this parameter counted as SINGLE-valued.
#[test]
fn a_call_dest_written_parameter_is_two_valued_because_of_the_unwind_edge() {
    let call = format!(
        r#"{{"Call":{{"func":"g","args":[],"dest":{{"local":1,"projections":[]}},"target":1,
           "span":{SPAN},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,
           "unwind":{{"Cleanup":2}}}}}}"#
    );
    let f = func(&format!(
        "{},{},{}",
        block(0, "", &call),
        block(1, "", RETURN),
        block(2, &read(1), r#""Resume""#)
    ));
    assert_eq!(value_count(&f, 1), ValueCount::Exactly(2));
    assert!(!holds_one_value(&f, 1));
    assert!(!is_single_static_assignment(&f, 1));
}

/// The shape every earlier witness has, and the one the relaxation always rejected:
/// `if c { k = .. } use(k)`. It must keep counting two.
#[test]
fn a_conditionally_stored_parameter_is_two_valued() {
    let f = func(&format!(
        "{},{},{}",
        block(0, "", &switch(1, 2)),
        block(1, &store(1), &goto(2)),
        block(2, &read(1), RETURN)
    ));
    assert_eq!(value_count(&f, 1), ValueCount::Exactly(2));
}

// ── the resolver ───────────────────────────────────────────────────────────

/// The resolver channel, which INLINES what it returns. A `Deref`-first store writes
/// the pointee, so it neither spends a value nor blocks resolution.
#[test]
fn a_deref_store_through_a_local_is_not_a_definition_of_it() {
    let deref_store = format!(
        r#"{{"Assign":{{"place":{{"local":1,"projections":["Deref"]}},
           "rvalue":{{"Use":{{"Constant":{{"Uint":[7,64]}}}}}},"span":{SPAN}}}}}"#
    );
    let f = func(&block(0, &format!("{},{}", read(1), deref_store), RETURN));
    assert_eq!(value_count(&f, 1), ValueCount::Exactly(1));
    assert!(is_single_static_assignment(&f, 1));
}

/// The split this row used to PIN is gone: a `Call` destination was counted by
/// [`value_count`] and invisible to [`unique_value_def`], so the resolver handed back
/// the `Assign` — a value the local does not hold on the path the call took. That was
/// X1, a live kernel-certified false proof (`pmod`). Both halves now see the channel,
/// in either statement order.
#[test]
fn call_dest_before_the_assign_is_also_not_a_unique_value() {
    let call = format!(
        r#"{{"Call":{{"func":"g","args":[],"dest":{{"local":3,"projections":[]}},"target":1,
           "span":{SPAN},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,
           "unwind":"Continue"}}}}"#
    );
    let f = func(&format!("{},{}", block(0, "", &call), block(1, &store(3), RETURN)));
    assert_eq!(
        value_count(&f, 3),
        ValueCount::Exactly(2),
        "the call dest and the store are two values"
    );
    assert!(!holds_one_value(&f, 3));
    assert!(unique_value_def(&f, 3).is_none());
}

/// A parameter written by a CALL destination is two-valued when its entry value is
/// live — the channel `unique_value_def` cannot see and `value_count` can.
#[test]
fn a_parameter_written_by_a_call_dest_is_two_valued() {
    let call = format!(
        r#"{{"Call":{{"func":"g","args":[],"dest":{{"local":1,"projections":[]}},"target":1,
           "span":{SPAN},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,
           "unwind":"Continue"}}}}"#
    );
    let f = func(&format!("{},{}", block(0, &read(1), &call), block(1, "", RETURN)));
    assert_eq!(value_count(&f, 1), ValueCount::Exactly(2));
    assert!(!is_single_static_assignment(&f, 1));
}

/// A `&mut` borrow is a write channel no definition scan can see, so it kills SSA
/// independently of the count. The count must be ANDed with that kill, never
/// substituted for it.
#[test]
fn a_mutably_borrowed_parameter_is_not_single_static_assignment() {
    let borrow = format!(
        r#"{{"Assign":{{"place":{{"local":3,"projections":[]}},
           "rvalue":{{"Ref":{{"mutable":true,"place":{{"local":1,"projections":[]}}}}}},
           "span":{SPAN}}}}}"#
    );
    let f = func(&block(0, &borrow, RETURN));
    assert_eq!(value_count(&f, 1), ValueCount::Exactly(1), "the borrow is not a definition");
    assert!(!is_single_static_assignment(&f, 1), "but it is a mutation channel");
}

// ── agreement with the predicates that keep their own scan ─────────────────

/// `guards::value_local_is_unstable` and `crate::place_source_is_stable` both scan
/// blocks for kills this module does not model (a projected store, a `&mut` passed as
/// a call argument). They must still agree with the seam on THE PARAMETER QUESTION:
/// neither may call a live-entry parameter stable.
#[test]
fn the_scan_keeping_predicates_agree_on_a_live_entry_parameter() {
    let f = func(&format!("{},{}", block(0, &read(1), &goto(1)), block(1, &store(1), RETURN)));
    assert!(!holds_one_value(&f, 1));
    assert!(crate::guards::value_local_is_unstable(&f, 1));
    assert!(!crate::place_source_is_stable(&f, 1));
}

/// The `place_source_is_stable` row the prose promised and the code did not deliver:
/// it read "at most one whole-local store (a single construction, or zero for a
/// parameter)" while counting `<= 1` for every local, so a reassigned parameter passed
/// — and roughly a dozen of its callers have no parameter refinement of their own.
#[test]
fn place_source_is_stable_rejects_a_reassigned_parameter() {
    let live = func(&format!("{},{}", block(0, &read(1), &goto(1)), block(1, &store(1), RETURN)));
    assert!(!crate::place_source_is_stable(&live, 1));
    let never = func(&block(0, "", RETURN));
    assert!(crate::place_source_is_stable(&never, 1), "an untouched parameter is stable");
    assert!(
        crate::place_source_is_stable(&func(&block(0, &store(3), RETURN)), 3),
        "a singly-defined temp is stable"
    );
}

// ── the CHANNEL SET, not just the entry definition ─────────────────────────
//
// `body_unique_value_def` scanned `Statement::Assign` only. Every row below is a
// channel it was blind to; each makes a NON-parameter local hold a second value, so
// none of them is caught by the entry-definition arm.

/// X1, at the predicate. `let mut m = 4; if s { m = pick(c); }` lowers at `-O` to one
/// `Assign` and one `Call` whose destination IS `m`. Resolving `m` to `4` and inlining
/// it as a modulo divisor was a live kernel-certified false proof
/// (`call_dest_reassigned_modulo_divisor_still_refutes`).
#[test]
fn call_dest_and_assign_is_not_a_unique_value() {
    let call = format!(
        r#"{{"Call":{{"func":"g","args":[],"dest":{{"local":3,"projections":[]}},"target":1,
           "span":{SPAN},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,
           "unwind":"Continue"}}}}"#
    );
    let f = func(&format!("{},{}", block(0, &store(3), &call), block(1, "", RETURN)));
    assert_eq!(
        value_count(&f, 3),
        ValueCount::Exactly(2),
        "the `Assign` and the `Call` dest are two values"
    );
    assert!(unique_value_def(&f, 3).is_none(), "so the resolver must decline");
    assert!(!is_single_static_assignment(&f, 3));
    assert!(!has_one_explicit_def(&f, 3));
}

/// X2, at the predicate. The cross-block guard resolver asks for the ONE block that
/// writes the local; a `Call` destination is one of the writes.
#[test]
fn unique_defining_block_counts_the_call_dest() {
    let call = format!(
        r#"{{"Call":{{"func":"g","args":[],"dest":{{"local":3,"projections":[]}},"target":1,
           "span":{SPAN},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,
           "unwind":"Continue"}}}}"#
    );
    let two = func(&format!("{},{}", block(0, &store(3), &call), block(1, "", RETURN)));
    assert!(super::unique_defining_block(&two, 3).is_none());

    let one = func(&format!("{},{}", block(0, &store(3), &goto(1)), block(1, "", RETURN)));
    assert_eq!(super::unique_defining_block(&one, 3), Some(0));

    let param = func(&format!("{},{}", block(0, &store(1), &goto(1)), block(1, "", RETURN)));
    assert!(
        super::unique_defining_block(&param, 1).is_none(),
        "a parameter's entry value is a second value the block scan cannot see"
    );
}

/// A `TailCall` writes the implicit return place, so `_0` is written even though no
/// statement and no `Call` destination names it.
#[test]
fn tail_call_writes_the_return_place() {
    let tail = format!(
        r#"{{"TailCall":{{"func":"g","args":[],"span":{SPAN},"atomic":null,
           "is_foreign":false,"is_unsafe_sig":false}}}}"#
    );
    let f = func(&block(0, "", &tail));
    assert_eq!(value_count(&f, 0), ValueCount::Exactly(1));
    assert!(!never_explicitly_reseated(&f, 0));
    assert_eq!(
        value_count(&f, 3),
        ValueCount::Exactly(0),
        "a TailCall writes only the return place"
    );
}

/// `SetDiscriminant` and `Deinit` change a local's value with no `Rvalue` to name —
/// the PARTIAL channel. The resolver and SSA refuse it; `value_count` deliberately
/// does not fold it in (see `body_value_count`'s doc for the callers that adjudicate
/// this channel themselves).
#[test]
fn discriminant_and_deinit_writes_are_partial() {
    let set_disc =
        r#"{"SetDiscriminant":{"place":{"local":3,"projections":[]},"variant_index":1}}"#;
    let f = func(&block(0, &format!("{},{}", store(3), set_disc), RETURN));
    assert_eq!(
        value_count(&f, 3),
        ValueCount::Exactly(1),
        "the whole-value count sees only the `Assign`"
    );
    assert!(unique_value_def(&f, 3).is_none(), "but the resolver refuses the partial write");
    assert!(!is_single_static_assignment(&f, 3));

    let deinit = r#"{"Deinit":{"place":{"local":3,"projections":[]}}}"#;
    let g = func(&block(0, &format!("{},{}", store(3), deinit), RETURN));
    assert!(unique_value_def(&g, 3).is_none());
    assert!(!is_single_static_assignment(&g, 3));
}

/// An `Opaque` terminator (inline asm) and the pointer-write statements have no
/// destination `Place`, so the seam cannot rule any local out and DECLINES for all of
/// them.
///
/// It declines; it does not count. Scoring an unlocatable write as ONE VALUE is
/// FAIL-OPEN, and this row is where that shows: `_3` has no whole-local write at all,
/// so `+1` would take its count from 0 to 1 and hand `holds_one_value` — the license a
/// GLOBAL fact keyed on the bare name needs — and `has_one_explicit_def` — which
/// asserts a defining statement EXISTS in `body.blocks` — to a local that has neither.
/// The count is therefore [`ValueCount::AtLeast`] and EVERY affirmative question
/// answers `false`. Deleting the `plus_unlocatable` arm in favour of `plus(1)` makes
/// the four `false` assertions below fail.
#[test]
fn unlocatable_writes_fail_closed_for_every_local() {
    let opaque = format!(r#"{{"Opaque":{{"kind":"asm","targets":[],"span":{SPAN}}}}}"#);
    let f = func(&block(0, "", &opaque));
    assert_eq!(value_count(&f, 3), ValueCount::AtLeast(0), "a temp the asm may have written");
    assert!(!holds_one_value(&f, 3), "no license: the seam did not see a value, it saw a gap");
    assert!(!has_one_explicit_def(&f, 3), "and there is no defining statement to inspect");
    assert_eq!(
        value_count(&f, 1),
        ValueCount::AtLeast(1),
        "a parameter's entry value, and a write that may have replaced it"
    );
    assert!(!holds_one_value(&f, 1));
    assert!(!is_single_static_assignment(&f, 3));
    assert!(unique_value_def(&f, 3).is_none());
    assert!(!never_explicitly_reseated(&f, 3));

    // The same gap ALONGSIDE a whole-local write: the located total is 1, but the
    // total is not known to be 1, so the affirmative questions still decline.
    let unsupported =
        format!(r#"{{"Unsupported":{{"kind":"k","detail":"d","operands":[],"span":{SPAN}}}}}"#);
    let g = func(&block(0, &format!("{},{}", store(3), unsupported), RETURN));
    assert_eq!(value_count(&g, 3), ValueCount::AtLeast(1));
    assert!(!holds_one_value(&g, 3));
    assert!(!has_one_explicit_def(&g, 3));
    assert!(unique_value_def(&g, 3).is_none());

    // A PARTIAL write plus the gap — the third D1 row. The partial store is not a
    // value on any reading, so the located total is still 0 and the count still
    // declines: `has_one_explicit_def` must not claim a definition that is not there.
    let field = format!(
        r#"{{"Assign":{{"place":{{"local":3,"projections":[{{"Field":0}}]}},
           "rvalue":{{"Use":{{"Constant":{{"Uint":[7,64]}}}}}},"span":{SPAN}}}}}"#
    );
    let h = func(&block(0, &field, &opaque));
    assert_eq!(value_count(&h, 3), ValueCount::AtLeast(0));
    assert!(!holds_one_value(&h, 3));
    assert!(!has_one_explicit_def(&h, 3));
}

/// A `Drop` runs glue that takes `&mut self`, so the dropped local's value after it is
/// not the value before — the PARTIAL channel again, on a TERMINATOR.
#[test]
fn drop_is_a_partial_write_of_the_dropped_local() {
    let drop = format!(
        r#"{{"Drop":{{"place":{{"local":3,"projections":[]}},"target":1,"span":{SPAN},
           "unwind":"Continue"}}}}"#
    );
    let f = func(&format!("{},{}", block(0, &store(3), &drop), block(1, "", RETURN)));
    assert!(unique_value_def(&f, 3).is_none(), "the resolver refuses the dropped local");
    assert!(!is_single_static_assignment(&f, 3));
    assert!(
        !never_explicitly_reseated(&f, 3),
        "the `Assign` reseats the slot; the `Drop` alone would not"
    );
}

/// THE ESCAPE CHANNEL — THE SEAM'S OPEN DEFECT, PINNED SO IT CANNOT BE MISTAKEN FOR A
/// RULE.
///
/// A store through a `&mut _3` names a DIFFERENT place, so a write can arrive where no
/// scan keyed on `_3` sees it. Two of the three questions below answer that correctly:
/// `is_single_static_assignment` and `unique_defining_block` DISQUALIFY an aliased
/// local. `unique_value_def` DOES NOT, and it is the resolver — its answer is INLINED
/// into a formula — so that is the dangerous one. `x3::pesc` compiled WITHOUT `-O` is
/// the live witness; `body_unique_value_def`'s `Escape` arm carries it in full,
/// together with the reason the obvious tightening is not the fix and the name of the
/// parked report.
///
/// THIS ROW ASSERTS THE DEFECTIVE ANSWER ON PURPOSE. It is not an endorsement: the
/// point is that repairing the alias channel is a VISIBLE change that must fail here
/// and be re-adjudicated with a measurement, not a silent one. Whoever makes
/// `unique_value_def` decline on an alias must flip the first assertion, delete this
/// paragraph, and re-measure the `for`-loop precision the parked report enumerates.
#[test]
fn the_resolver_still_admits_an_escaped_local_which_is_the_open_defect() {
    let borrow = format!(
        r#"{{"Assign":{{"place":{{"local":4,"projections":[]}},
           "rvalue":{{"Ref":{{"mutable":true,"place":{{"local":3,"projections":[]}}}}}},
           "span":{SPAN}}}}}"#
    );
    let f = func(&block(0, &format!("{},{}", store(3), borrow), RETURN));
    assert!(
        unique_value_def(&f, 3).is_some(),
        "OPEN DEFECT: the resolver hands back the one `Assign` it saw even though a \
         write may have arrived through the alias — see `body_unique_value_def`"
    );
    assert!(
        !is_single_static_assignment(&f, 3),
        "the SSA question, which is not the defective one, refuses the alias"
    );
    assert_eq!(
        value_count(&f, 3),
        ValueCount::Exactly(1),
        "OPEN RESIDUAL: the COUNT does not charge an alias either"
    );

    // The CONTROL for the classifier underneath, so that a future refusal cannot be
    // written as a blanket one: a SHARED borrow cannot mutate
    // (`Statement::escapes_local`) and is not on the escape channel at all.
    let shared = format!(
        r#"{{"Assign":{{"place":{{"local":4,"projections":[]}},
           "rvalue":{{"Ref":{{"mutable":false,"place":{{"local":3,"projections":[]}}}}}},
           "span":{SPAN}}}}}"#
    );
    let g = func(&block(0, &format!("{},{}", store(3), shared), RETURN));
    assert!(unique_value_def(&g, 3).is_some(), "a shared borrow is not a write channel");
    assert!(
        is_single_static_assignment(&g, 3),
        "and the SSA question accepts it, so its refusal above is the alias and not the borrow"
    );
}

/// A local with ONE whole definition and a PARTIAL or ALIAS write elsewhere has no
/// unique defining block. `body_value_count` scores neither channel, so the `== 1`
/// budget does not exclude them, and the block index alone would claim a dominance that
/// the second write breaks. Deleting either arm of the disqualification makes the first
/// two assertions answer `Some(1)` — the block of the write that is not a definition.
#[test]
fn a_partially_written_local_has_no_unique_defining_block() {
    let field = format!(
        r#"{{"Assign":{{"place":{{"local":3,"projections":[{{"Field":0}}]}},
           "rvalue":{{"Use":{{"Constant":{{"Uint":[7,64]}}}}}},"span":{SPAN}}}}}"#
    );
    let partial = func(&format!(
        "{},{},{}",
        block(0, &store(3), &goto(1)),
        block(1, &field, &goto(2)),
        block(2, "", RETURN)
    ));
    assert_eq!(
        value_count(&partial, 3),
        ValueCount::Exactly(1),
        "the projected store is not a VALUE"
    );
    assert!(
        super::unique_defining_block(&partial, 3).is_none(),
        "a field store elsewhere breaks the dominance the block index would assert"
    );

    let borrow = format!(
        r#"{{"Assign":{{"place":{{"local":4,"projections":[]}},
           "rvalue":{{"Ref":{{"mutable":true,"place":{{"local":3,"projections":[]}}}}}},
           "span":{SPAN}}}}}"#
    );
    let aliased = func(&format!(
        "{},{},{}",
        block(0, &store(3), &goto(1)),
        block(1, &borrow, &goto(2)),
        block(2, "", RETURN)
    ));
    assert_eq!(
        value_count(&aliased, 3),
        ValueCount::Exactly(1),
        "OPEN RESIDUAL: an alias is not a value"
    );
    assert!(
        super::unique_defining_block(&aliased, 3).is_none(),
        "an alias handed out elsewhere can carry a write this index never names"
    );

    // The CONTROL: the same single definition with nothing else touching the local
    // still answers, so the disqualification is not a blanket refusal.
    let clean = func(&format!(
        "{},{},{}",
        block(0, &store(3), &goto(1)),
        block(1, &read(3), &goto(2)),
        block(2, "", RETURN)
    ));
    assert_eq!(super::unique_defining_block(&clean, 3), Some(0));
}

// ── the `WholeOpaque` resolver: `unique_value_call` ─────────────────────────
//
// `unique_value_def` answers the `WholeNamed` half of the resolver channel and
// REFUSES `WholeOpaque` (a call destination has no `Rvalue`). A caller that wants to
// INSPECT the producing call had no seam question to ask, so
// `termination::resolve_saturating_add_increment` re-derived a block scan and was blind
// to the entry definition. These rows are that question, answered here once.

/// `dst = g() -> target` as a `Call` terminator.
fn call_to(dst: usize, target: usize) -> String {
    format!(
        r#"{{"Call":{{"func":"g","args":[],"dest":{{"local":{dst},"projections":[]}},
           "target":{target},"span":{SPAN},"atomic":null,"is_foreign":false,
           "is_unsafe_sig":false,"unwind":"Continue"}}}}"#
    )
}

/// The answering case: ONE call destination, nothing else, and the local is not a
/// parameter.
#[test]
fn a_temp_defined_by_one_call_resolves_to_that_call() {
    let f = func(&format!("{},{}", block(0, "", &call_to(3, 1)), block(1, &read(3), RETURN)));
    assert_eq!(value_count(&f, 3), ValueCount::Exactly(1));
    assert!(
        matches!(super::unique_value_call(&f, 3), Some(trust_types::Terminator::Call { .. })),
        "one call destination and nothing else is one value"
    );
    assert!(
        unique_value_def(&f, 3).is_none(),
        "the `WholeNamed` resolver still refuses the opaque channel — the two are disjoint"
    );
}

/// THE ROW THE `termination` DEFECT WENT THROUGH. A PARAMETER's definition is at ENTRY
/// and is in no block, so a call writing it is its SECOND value: on any path that skips
/// the call, the bare name still means the incoming argument. The block scan this
/// replaces saw one definition and answered with the call.
#[test]
fn a_parameter_written_by_one_call_has_no_unique_defining_call() {
    let f = func(&format!(
        "{},{},{}",
        block(0, "", &switch(1, 2)),
        block(1, "", &call_to(1, 2)),
        block(2, &read(1), RETURN)
    ));
    assert_eq!(
        value_count(&f, 1),
        ValueCount::Exactly(2),
        "the entry definition and the call destination"
    );
    assert!(
        super::unique_value_call(&f, 1).is_none(),
        "the entry value reaches the read on the path that skips the call"
    );
}

/// Every other channel declines too, and each for its own reason. `WholeNamed` is a
/// second value the call did not produce; `Partial` changes the local after the call;
/// `Escape` can carry a store this scan never names — and UNLIKE `unique_value_def`,
/// whose `Escape` residual is parked, this question refuses it; `Unlocatable` is the
/// absence of the information.
#[test]
fn every_other_channel_declines_the_unique_defining_call() {
    let with_assign =
        func(&format!("{},{}", block(0, &store(3), &call_to(3, 1)), block(1, "", RETURN)));
    assert!(super::unique_value_call(&with_assign, 3).is_none(), "a second, named value");

    let two_calls = func(&format!(
        "{},{},{}",
        block(0, "", &call_to(3, 1)),
        block(1, "", &call_to(3, 2)),
        block(2, "", RETURN)
    ));
    assert!(super::unique_value_call(&two_calls, 3).is_none(), "two call destinations");

    let deinit = format!(r#"{{"Deinit":{{"place":{{"local":3,"projections":[]}}}}}}"#);
    let partial = func(&format!("{},{}", block(0, "", &call_to(3, 1)), block(1, &deinit, RETURN)));
    assert!(super::unique_value_call(&partial, 3).is_none(), "a partial write after the call");

    let borrow = format!(
        r#"{{"Assign":{{"place":{{"local":4,"projections":[]}},
           "rvalue":{{"Ref":{{"mutable":true,"place":{{"local":3,"projections":[]}}}}}},
           "span":{SPAN}}}}}"#
    );
    let aliased = func(&format!("{},{}", block(0, "", &call_to(3, 1)), block(1, &borrow, RETURN)));
    assert!(
        super::unique_value_call(&aliased, 3).is_none(),
        "the alias channel is REFUSED here, not admitted as it still is by `unique_value_def`"
    );

    let opaque = format!(r#"{{"Opaque":{{"kind":"asm","targets":[],"span":{SPAN}}}}}"#);
    let unlocatable = func(&format!("{},{}", block(0, "", &call_to(3, 1)), block(1, "", &opaque)));
    assert!(super::unique_value_call(&unlocatable, 3).is_none(), "an unlocatable write");

    // The CONTROL: the same call with nothing else still answers, so none of the five
    // refusals above is a blanket decline.
    let clean = func(&format!("{},{}", block(0, "", &call_to(3, 1)), block(1, "", RETURN)));
    assert!(super::unique_value_call(&clean, 3).is_some());
}

/// A `TailCall` writes only the implicit return place and has no destination of its
/// own, so it is counted as a value like any other write and can never BE the answer.
#[test]
fn a_tail_call_is_never_the_unique_defining_call() {
    let tail = format!(
        r#"{{"TailCall":{{"func":"g","args":[],"span":{SPAN},"atomic":null,
           "is_foreign":false,"is_unsafe_sig":false}}}}"#
    );
    let f = func(&block(0, "", &tail));
    assert_eq!(value_count(&f, 0), ValueCount::Exactly(1), "the return place is written");
    assert!(
        super::unique_value_call(&f, 0).is_none(),
        "a `TailCall` is not a `Call`; the resolver hands back only the latter"
    );
}
