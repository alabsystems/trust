// Trust: the DEFINITION SEAM, pinned at the predicate.
//
// Three rounds of site-by-site patching did not converge on the parameter-entry-def
// class because every round fixed the sites it happened to enumerate. The structural
// answer is that `body.blocks` is scanned in ONE module and every other caller asks a
// question that already knows about the entry definition. These rows pin the questions
// themselves; the end-to-end verdicts live in `tests/entry_def_structural.rs`.

use trust_types::{ValueCount, VerifiableFunction};

use super::{
    every_write_is_whole_named, has_one_explicit_def, holds_one_value, is_single_static_assignment,
    never_explicitly_reseated, path_is_single_static_assignment, pointer_is_pinned,
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

/// UF-1 review, 2026-10-03: a `&raw const` borrow is a mutation channel. A
/// `*const` is a valid `*const -> *mut` cast root, and under Tree Borrows the
/// write through it to a `mut` local is defined, so `p = &raw const r as *mut _;
/// *p = Err(())` changes `r`. `place_source_is_stable` admitted it (only
/// `&raw mut` was refused) and the unwrap lane's call-pinned shape published
/// `r.unwrap()` proved after `r.is_ok()` and that write. A SHARED `&` borrow
/// stays admitted: writing through it is UB under both models.
#[test]
fn place_source_is_stable_refuses_a_raw_const_borrow() {
    let raw = func(&block(0, &format!("{},{}", store(3), address_of(4, 3, "")), RETURN));
    assert!(!crate::place_source_is_stable(&raw, 3), "a temp borrowed `&raw const`");
    let raw_param = func(&block(0, &address_of(4, 1, ""), RETURN));
    assert!(!crate::place_source_is_stable(&raw_param, 1), "a parameter borrowed `&raw const`");
    let raw_field = func(&block(0, &address_of(4, 1, r#"{"Field":0}"#), RETURN));
    assert!(!crate::place_source_is_stable(&raw_field, 1), "a field borrowed `&raw const`");
    let shared = format!(
        r#"{{"Assign":{{"place":{{"local":4,"projections":[]}},
           "rvalue":{{"Ref":{{"mutable":false,"place":{{"local":3,"projections":[]}}}}}},"span":{SPAN}}}}}"#
    );
    let shared = func(&block(0, &format!("{},{}", store(3), shared), RETURN));
    assert!(crate::place_source_is_stable(&shared, 3), "a shared `&` borrow is no channel");
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

// ── THE PATH QUESTION (round A8) ─────────────────────────────────────────────────
//
// `path_is_single_static_assignment` licenses a NAME whose value lives in the place
// itself (a fat pointer's length metadata) and not in its contents. Its whole
// difference from `is_single_static_assignment` is that writes and mutable aliases
// STRICTLY INSIDE the path are ignored; everything at or above it is charged exactly
// as before, and siblings fail closed.

fn place_json(local: usize, projections: &str) -> String {
    format!(r#"{{"local":{local},"projections":[{projections}]}}"#)
}

fn place(local: usize, projections: &[trust_types::Projection]) -> trust_types::Place {
    trust_types::Place { local, projections: projections.to_vec() }
}

/// `<place> = const 7`.
fn store_to(local: usize, projections: &str) -> String {
    format!(
        r#"{{"Assign":{{"place":{},"rvalue":{{"Use":{{"Constant":{{"Uint":[7,64]}}}}}},"span":{SPAN}}}}}"#,
        place_json(local, projections)
    )
}

/// `_dst = &mut <place>` / `_dst = &raw const <place>`.
fn borrow_mut(dst: usize, local: usize, projections: &str) -> String {
    format!(
        r#"{{"Assign":{{"place":{{"local":{dst},"projections":[]}},"rvalue":{{"Ref":{{"mutable":true,"place":{}}}}},"span":{SPAN}}}}}"#,
        place_json(local, projections)
    )
}
fn address_of(dst: usize, local: usize, projections: &str) -> String {
    format!(
        r#"{{"Assign":{{"place":{{"local":{dst},"projections":[]}},"rvalue":{{"AddressOf":[false,{}]}},"span":{SPAN}}}}}"#,
        place_json(local, projections)
    )
}

const DEREF: trust_types::Projection = trust_types::Projection::Deref;

/// THE ROW THE QUESTION EXISTS FOR: a `&mut [T]` parameter `_1` whose body stores an
/// element through it (`(*_1)[_3] = v`) and reborrows the pointee both ways (`&raw
/// const (*_1)`, the `<[T]>::len` spelling; `&mut (*_1)`, the `IndexMut` spelling).
/// None of those can change `_1`'s length metadata, so the PATH `_1` is bound once (at
/// entry) — while `is_single_static_assignment(_1)` refuses the reborrow as an
/// `Escape`. That refusal is what turned `for i in 0..s.len() { s[i] = 0 }` into a
/// refuted program at `-Copt-level=1` (`tests/escaped_local_seam_realmir.rs`, the
/// `a8_ctl_mut_*` rows).
#[test]
fn element_stores_and_pointee_reborrows_are_inside_the_path() {
    let stmts = format!(
        "{},{},{}",
        store_to(1, r#""Deref",{"Index":3}"#),
        address_of(4, 1, r#""Deref""#),
        borrow_mut(4, 1, r#""Deref""#)
    );
    let f = func(&block(0, &stmts, RETURN));
    assert!(path_is_single_static_assignment(&f, &place(1, &[])));
    assert!(!is_single_static_assignment(&f, 1), "the local question still refuses the alias");
    // The unsized pointee `(*_1)` is NOT the metadata owner: a borrow of it is a
    // `Prefix` of that path and refuses it. `slice_len_licence::metadata_owner` is what
    // maps `(*_1)` back to `_1` before asking.
    assert!(!path_is_single_static_assignment(&f, &place(1, &[DEREF])));
}

/// A mutable or raw alias of the path ITSELF (`&mut _1`, `&raw mut _1`) can reseat the
/// fat pointer through a store this walk never names: refused, exactly as for the
/// local question.
#[test]
fn a_mutable_alias_of_the_path_itself_disqualifies() {
    let f = func(&block(0, &borrow_mut(4, 1, ""), RETURN));
    assert!(!path_is_single_static_assignment(&f, &place(1, &[])));
    let g = func(&block(0, &address_of(4, 1, ""), RETURN));
    assert!(!path_is_single_static_assignment(&g, &place(1, &[])));
    // ...and so does an alias of a PREFIX of a projected path.
    assert!(!path_is_single_static_assignment(
        &f,
        &place(1, &[DEREF, trust_types::Projection::Field(0)])
    ));
}

/// A whole write of a prefix is a second binding of every path below it: a parameter
/// stored to once holds two values on every path through it.
#[test]
fn a_whole_write_of_a_prefix_rebinds_every_path_below_it() {
    let f = func(&block(0, &store(1), RETURN));
    assert!(!path_is_single_static_assignment(&f, &place(1, &[])));
    assert!(!path_is_single_static_assignment(&f, &place(1, &[DEREF])));
    // A temp with exactly one whole write, read through a deref: bound once.
    let g = func(&block(0, &store(3), RETURN));
    assert!(path_is_single_static_assignment(&g, &place(3, &[])));
    assert!(path_is_single_static_assignment(&g, &place(3, &[DEREF])));
    // And a temp with none: not bound at all.
    assert!(!path_is_single_static_assignment(&g, &place(4, &[])));
}

/// The three prefix relations on a field store `_3.0 = 7` beside the whole write
/// `_3 = 7`: INSIDE the path `_3` (ignored — one binding), a PREFIX of the path `_3.0`
/// (a second binding — refused), a SIBLING of the path `_3.1` (refused: whether the two
/// overlap is an ADT question this module does not answer).
#[test]
fn a_field_store_is_inside_its_parent_a_binding_of_itself_and_a_sibling_of_its_neighbour() {
    let f = func(&block(0, &format!("{},{}", store(3), store_to(3, r#"{"Field":0}"#)), RETURN));
    let field = |i| place(3, &[trust_types::Projection::Field(i)]);
    assert!(path_is_single_static_assignment(&f, &place(3, &[])));
    assert!(!path_is_single_static_assignment(&f, &field(0)));
    assert!(!path_is_single_static_assignment(&f, &field(1)));
    // The local question refuses the whole local outright (a `Partial` write).
    assert!(!is_single_static_assignment(&f, 3));
}

/// A DESTRUCTION (`SetDiscriminant`, `Deinit`, `Drop`) of a prefix ends the path's
/// value without binding a new one: refused. Strictly inside the path it is ignored.
#[test]
fn a_destruction_of_a_prefix_disqualifies_and_one_inside_is_ignored() {
    let payload =
        place(3, &[trust_types::Projection::Downcast(1), trust_types::Projection::Field(0)]);
    let set_disc =
        r#"{"SetDiscriminant":{"place":{"local":3,"projections":[]},"variant_index":1}}"#;
    let f = func(&block(0, &format!("{},{}", store(3), set_disc), RETURN));
    assert!(!path_is_single_static_assignment(&f, &payload));
    assert!(!path_is_single_static_assignment(&f, &place(3, &[])));
    let deinit = r#"{"Deinit":{"place":{"local":3,"projections":[]}}}"#;
    let g = func(&block(0, &format!("{},{}", store(3), deinit), RETURN));
    assert!(!path_is_single_static_assignment(&g, &payload));
    let drop = format!(
        r#"{{"Drop":{{"place":{{"local":3,"projections":[]}},"target":1,"span":{SPAN},
           "unwind":"Continue"}}}}"#
    );
    let h = func(&format!("{},{}", block(0, &store(3), &drop), block(1, "", RETURN)));
    assert!(!path_is_single_static_assignment(&h, &place(3, &[])));
    // Inside: a discriminant write on the POINTEE of `_3` leaves the path `_3` alone.
    let set_disc_inside =
        r#"{"SetDiscriminant":{"place":{"local":3,"projections":["Deref"]},"variant_index":1}}"#;
    let k = func(&block(0, &format!("{},{}", store(3), set_disc_inside), RETURN));
    assert!(path_is_single_static_assignment(&k, &place(3, &[])));
}

/// A `Call` destination binds the path like an `Assign`; an unlocatable write fails
/// closed for every path, as everywhere in this module.
#[test]
fn a_call_destination_binds_the_path_and_an_unlocatable_write_refuses_it() {
    let call = format!(
        r#"{{"Call":{{"func":"g","args":[],"dest":{{"local":3,"projections":[]}},
           "target":1,"span":{SPAN},"atomic":null,"is_foreign":false,
           "is_unsafe_sig":false,"unwind":"Continue"}}}}"#
    );
    let f = func(&format!("{},{}", block(0, "", &call), block(1, &read(3), RETURN)));
    assert!(path_is_single_static_assignment(&f, &place(3, &[])));
    assert!(path_is_single_static_assignment(&f, &place(3, &[DEREF])));
    // A call destination INSIDE the path (`(*_3) = g()`) is ignored for `_3`...
    let call_inside = format!(
        r#"{{"Call":{{"func":"g","args":[],"dest":{{"local":3,"projections":["Deref"]}},
           "target":1,"span":{SPAN},"atomic":null,"is_foreign":false,
           "is_unsafe_sig":false,"unwind":"Continue"}}}}"#
    );
    let g = func(&format!("{},{}", block(0, &store(3), &call_inside), block(1, "", RETURN)));
    assert!(path_is_single_static_assignment(&g, &place(3, &[])));
    // ...and is a second binding of the path `(*_3)` itself.
    assert!(!path_is_single_static_assignment(&g, &place(3, &[DEREF])));
    let opaque = format!(r#"{{"Opaque":{{"kind":"asm","targets":[],"span":{SPAN}}}}}"#);
    let h = func(&block(0, &store(3), &opaque));
    assert!(!path_is_single_static_assignment(&h, &place(3, &[])));
    assert!(!path_is_single_static_assignment(&h, &place(1, &[])));
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

/// THE ESCAPE CHANNEL — THE RESOLVER REFUSES IT. Trust: 2026-09-15, SOUNDNESS.
///
/// A store through a `&mut _3` names a DIFFERENT place (`(*_4) = v`, whose place-local
/// is `_4`), so a write can arrive where no scan keyed on `_3` sees it. Until
/// 2026-09-15 `unique_value_def` — the RESOLVER, whose answer is INLINED into a formula
/// and so is beyond the reach of version renaming — handed its one `Assign` back
/// anyway. That was a LIVE, kernel-certified false proof through the real compiler
/// (`x3::pesc` at `-Copt-level=0`: `2 proved, 0 failed` under `-Ztrust-policy=certify`
/// on a program that panics `index out of bounds` at runtime).
/// `body_unique_value_def`'s `Escape` arm carries the witness, the measured cost of
/// closing it, and the three obvious "precision recoveries" that are NOT sound.
///
/// THE ROW IS THE REFUSAL, AND ITS TWO CONTROLS ARE WHAT KEEP IT FROM BEING A BLANKET
/// ONE: a SHARED borrow is not on the channel (`Statement::escapes_local` requires
/// `Ref { mutable: true }` / `AddressOf`), and an unaliased local with the same single
/// `Assign` still resolves. If either control ever fails, the refusal has grown into a
/// capability loss and must be re-adjudicated with a measurement.
#[test]
fn the_resolver_refuses_an_escaped_local() {
    let borrow = format!(
        r#"{{"Assign":{{"place":{{"local":4,"projections":[]}},
           "rvalue":{{"Ref":{{"mutable":true,"place":{{"local":3,"projections":[]}}}}}},
           "span":{SPAN}}}}}"#
    );
    let f = func(&block(0, &format!("{},{}", store(3), borrow), RETURN));
    assert!(
        unique_value_def(&f, 3).is_none(),
        "SOUNDNESS: a write may have arrived through the alias, so the one `Assign` this \
         scan saw is not the local's value — see `body_unique_value_def`'s `Escape` arm"
    );
    assert!(
        !is_single_static_assignment(&f, 3),
        "the SSA question refuses the alias too, as it always has"
    );
    assert_eq!(
        value_count(&f, 3),
        ValueCount::Exactly(1),
        "OPEN RESIDUAL: the COUNT still does not charge an alias — declared in \
         `body_value_count`'s own `Escape` arm, and weaker in kind than the resolver's was"
    );

    // A RAW address-of is on the same channel (`*const` is a valid `*const -> *mut`
    // cast root), so it must be refused identically — this is the half a fix written
    // against `Rvalue::Ref` alone would miss.
    let raw = format!(
        r#"{{"Assign":{{"place":{{"local":4,"projections":[]}},
           "rvalue":{{"AddressOf":[false,{{"local":3,"projections":[]}}]}},
           "span":{SPAN}}}}}"#
    );
    let r = func(&block(0, &format!("{},{}", store(3), raw), RETURN));
    assert!(unique_value_def(&r, 3).is_none(), "a raw address-of escapes just as a `&mut` does");

    // CONTROL 1 — a SHARED borrow cannot mutate (`Statement::escapes_local`) and is not
    // on the escape channel at all, so the refusal above is the ALIAS and not "a borrow".
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

    // CONTROL 2 — the same single definition with nothing else touching the local still
    // resolves. THE PRECISION FLOOR: this change must not cost an unaliased local.
    let clean = func(&block(0, &store(3), RETURN));
    assert!(
        unique_value_def(&clean, 3).is_some(),
        "an unaliased local with one `Assign` must resolve exactly as before"
    );
}

/// Trust: 2026-09-17 (round A12, pass 2) — THE POINTEE-BORROW QUESTION, pinned to be
/// EXACTLY ONE PROJECTION WIDE.
///
/// `unique_value_def_modulo_pointee_borrows` is `unique_value_def` with `Deref`-first
/// borrows off the escape channel, and nothing else. The rows below are the full
/// difference: a borrow reached THROUGH the local resolves, a borrow of the local's OWN
/// storage still refuses on BOTH questions, and the raw spelling of each behaves like
/// its reference spelling. If the second group ever resolves, the 2026-09-15 closure
/// has been reopened and a kernel-certified false proof is back (`x3::pesc`, on
/// `body_unique_value_def`'s `Escape` arm).
#[test]
fn the_pointee_borrow_question_is_exactly_one_projection_wide() {
    use super::unique_value_def_modulo_pointee_borrows as narrow;

    // THE RECOVERY — `&mut (*_3)[_2]`, `&mut (*_3).0`, `&raw const (*_3)`: a pointer to
    // `_3`'s POINTEE. Writing through it cannot change what `_3` holds.
    for (what, stmt) in [
        ("&mut (*_3)", borrow_mut(4, 3, r#""Deref""#)),
        ("&mut (*_3)[_2]", borrow_mut(4, 3, r#""Deref",{"Index":2}"#)),
        ("&mut (*_3).0", borrow_mut(4, 3, r#""Deref",{"Field":0}"#)),
        ("&raw const (*_3)", address_of(4, 3, r#""Deref""#)),
    ] {
        let f = func(&block(0, &format!("{},{}", store(3), stmt), RETURN));
        assert!(
            narrow(&f, 3).is_some(),
            "{what} addresses the pointee, not `_3`'s own bytes, so `_3` still holds one value"
        );
        assert!(
            unique_value_def(&f, 3).is_none(),
            "{what} IS refused by the wider question — that difference is the whole change, \
             and a caller that needs 'nothing mutates my pointee' must keep asking it"
        );
    }

    // THE REFUSAL, UNCHANGED — a borrow of `_3`'s own storage. Through it `_3` itself can
    // be reseated at a place no scan keyed on `_3` ever names.
    for (what, stmt) in [("&mut _3", borrow_mut(4, 3, "")), ("&raw const _3", address_of(4, 3, ""))]
    {
        let f = func(&block(0, &format!("{},{}", store(3), stmt), RETURN));
        assert!(
            narrow(&f, 3).is_none(),
            "SOUNDNESS: {what} can reseat `_3`; the narrowing is `Deref`-first borrows and \
             nothing else"
        );
        assert!(unique_value_def(&f, 3).is_none(), "and the wider question refuses it too");
    }

    // EVERY OTHER CHANNEL still refuses on the narrow question exactly as on the wide
    // one: a second whole write, and a projected (partial) write.
    let two = func(&block(0, &format!("{},{}", store(3), store(3)), RETURN));
    assert!(narrow(&two, 3).is_none(), "two whole writes is not one value, on either question");
    let partial =
        func(&block(0, &format!("{},{}", store(3), store_to(3, r#"{"Field":0}"#)), RETURN));
    assert!(narrow(&partial, 3).is_none(), "a partial write still disqualifies");
    let param = func(&block(0, &store(1), RETURN));
    assert!(
        narrow(&param, 1).is_none(),
        "the ENTRY definition is still a value it cannot hand back"
    );
}

/// Trust: 2026-09-17 (round A12, pass 2) — the guard filter in
/// `crate::referent_fold::is_stable` is `is_single_static_assignment(g) &&
/// never_explicitly_reseated(g)`. A review of this round read that conjunction as
/// UNSATISFIABLE ("SSA wants `whole == 1`, `never_explicitly_reseated` wants `whole ==
/// 0`") and asked for it to be replaced by `never_explicitly_reseated` alone. Both
/// halves of that are wrong, and this row is the measurement that says so, so the
/// question is not re-litigated from the prose:
///
///  * the conjunction IS satisfiable, by exactly the guard its comment names — a
///    never-written PARAMETER, whose `whole` is seeded from `body_is_parameter` and
///    whose body-write tally is zero.
///  * `never_explicitly_reseated` ALONE would be unsound as the filter: it does not
///    charge the `Escape` channel (an alias of the slot is not a reseat of it), so a
///    parameter that is `&mut`-borrowed and written through would be DROPPED from the
///    guard set and the fold would then spell a cell the store never landed in.
///
/// Trust: 2026-09-17 (round A13) — a THIRD conjunct,
/// `!referent_fold::local_storage_borrowed_anywhere(g.local)`, and the last assertion
/// here is why it had to be added rather than left implied. Both predicates above are
/// written in terms of `Statement::escapes_local`, which sees `Rvalue::Ref { mutable:
/// true }` and `AddressOf` and NOT a shared `&g` — so a never-written parameter with a
/// shared borrow of it satisfied both, was dropped here, and the round-A12 pass-2
/// widening of `slot_is_aliased_anywhere` (which does see that borrow) was never
/// reached for it. `v3_shared_param_cast_store_bug` — `let pj = launder(&j); *pj = k;`
/// with `j` a parameter — is that shape. (NOT `u1_shared_cast_bug` /
/// `j1_param_shared_launder_bug`, which this comment used to cite: both take `&raw
/// const j`, an `AddressOf` that `escapes_local` already counts, so the conjunction
/// above already keeps their guard and this conjunct never decides them.)
#[test]
fn the_fold_guard_filter_drops_a_never_written_parameter_and_not_an_aliased_one() {
    let untouched = func(&block(0, &read(1), RETURN));
    assert!(
        is_single_static_assignment(&untouched, 1) && never_explicitly_reseated(&untouched, 1),
        "a never-written parameter satisfies BOTH halves: the filter is live, not dead code"
    );

    let written = func(&block(0, &store(3), RETURN));
    assert!(
        !(is_single_static_assignment(&written, 3) && never_explicitly_reseated(&written, 3)),
        "a local with one whole write is kept — its single `Assign` re-executes inside a loop"
    );

    let aliased = func(&block(0, &format!("{},{}", read(1), borrow_mut(4, 1, "")), RETURN));
    assert!(
        never_explicitly_reseated(&aliased, 1),
        "the reseat question alone ACCEPTS an aliased parameter — `Escape` is not a reseat"
    );
    assert!(
        !(is_single_static_assignment(&aliased, 1) && never_explicitly_reseated(&aliased, 1)),
        "SOUNDNESS: the conjunction still keeps it, which is why the SSA half may not be \
         dropped from the filter"
    );

    // Trust: 2026-09-17 (round A13) — THE SHARED borrow, which is what the two halves
    // above cannot see and the third conjunct exists for.
    let shared = format!(
        r#"{{"Assign":{{"place":{{"local":4,"projections":[]}},
           "rvalue":{{"Ref":{{"mutable":false,"place":{{"local":1,"projections":[]}}}}}},
           "span":{SPAN}}}}}"#
    );
    let shared_borrowed = func(&block(0, &format!("{},{}", read(1), shared), RETURN));
    assert!(
        is_single_static_assignment(&shared_borrowed, 1)
            && never_explicitly_reseated(&shared_borrowed, 1),
        "MEASURED: a never-written parameter with a SHARED borrow of it satisfies both \
         halves — which is exactly how it used to be dropped from the guard set"
    );
    assert!(
        crate::referent_fold::local_storage_borrowed_anywhere(&shared_borrowed, 1),
        "SOUNDNESS: the third conjunct SEES that borrow, so the guard is kept and the \
         round-A12 pass-2 widening of `slot_is_aliased_anywhere` can be asked about it"
    );
    assert!(
        !crate::referent_fold::local_storage_borrowed_anywhere(&untouched, 1),
        "and it does not keep a parameter nothing borrows: the third conjunct narrows \
         the drop, it does not disable it"
    );
}

/// THE CAPABILITY SPLIT, pinned as a predicate pair rather than only through the real-MIR
/// rows it decides.
///
/// Trust: 2026-09-17 (round A13, pass 2) — `callee_may_rebind` asks
/// `slot_is_writably_aliased_anywhere`, not `slot_is_aliased_anywhere`, and the whole
/// difference is a SHARED `&g`: a callee handed one cannot rebind `g`. Three correct,
/// panic-free, entirely safe programs were refuted with a counterexample because the
/// wide question was asked here (`v2_shared_param_call_ctl`,
/// `v6_shared_param_drop_ctl`, `v7_shared_param_borrow_after_ctl`; real-MIR pins for
/// all three live in `tests/escaped_local_seam_realmir.rs`).
///
/// The two assertions that keep the split from widening into a false PROVE: `&mut g`
/// counts, and `&raw const g` counts — the raw half is `escapes_local`'s own line and
/// is what keeps `u1_shared_cast_bug` / `j1_param_shared_launder_bug` closed through
/// the CALLEE channel, not only through the store this body happens to spell.
#[test]
fn the_callee_rebind_question_counts_write_capable_aliases_only() {
    use crate::referent_fold::{slot_is_aliased_anywhere, slot_is_writably_aliased_anywhere};
    let g = trust_types::Place { local: 1, projections: vec![] };

    let shared = format!(
        r#"{{"Assign":{{"place":{{"local":4,"projections":[]}},
           "rvalue":{{"Ref":{{"mutable":false,"place":{{"local":1,"projections":[]}}}}}},
           "span":{SPAN}}}}}"#
    );
    let shared_borrowed = func(&block(0, &shared, RETURN));
    assert!(
        slot_is_aliased_anywhere(&shared_borrowed, &g),
        "the WIDE question still sees a shared borrow — `written_place_rebinds` asks it \
         and `v3_shared_param_cast_store_bug` is closed by that answer"
    );
    assert!(
        !slot_is_writably_aliased_anywhere(&shared_borrowed, &g),
        "PRECISION: a callee handed `&g` cannot rebind `g`; asking the wide question here \
         refuted three correct safe programs both baselines prove"
    );

    let mut_borrowed = func(&block(0, &borrow_mut(4, 1, ""), RETURN));
    assert!(
        slot_is_writably_aliased_anywhere(&mut_borrowed, &g),
        "SOUNDNESS: `&mut g` is a write capability"
    );

    let raw_const = func(&block(0, &address_of(4, 1, ""), RETURN));
    assert!(
        slot_is_writably_aliased_anywhere(&raw_const, &g),
        "SOUNDNESS: a RAW borrow counts at either mutability — `escapes_local`'s line, and \
         the reason `&raw const j` laundered into a callee stays closed"
    );

    let untouched = func(&block(0, &read(1), RETURN));
    assert!(
        !slot_is_aliased_anywhere(&untouched, &g)
            && !slot_is_writably_aliased_anywhere(&untouched, &g),
        "neither question fires on a body that borrows nothing"
    );
}

/// THE ORIGIN QUESTION, and the row that keeps it from being mistaken for the resolver.
///
/// `unique_initializing_def` readmits the escape channel ON PURPOSE, because "what was
/// this local BUILT FROM" is true at the point after its one `Assign` whether or not an
/// alias later reseats it. Every OTHER channel must still refuse — a second whole
/// write, a call destination, a partial write and an unlocatable write each leave the
/// initializer either non-unique or unnameable — so this row is the difference being
/// exactly one channel wide and nothing more.
#[test]
fn the_origin_question_readmits_only_the_alias_channel() {
    let borrow = format!(
        r#"{{"Assign":{{"place":{{"local":4,"projections":[]}},
           "rvalue":{{"Ref":{{"mutable":true,"place":{{"local":3,"projections":[]}}}}}},
           "span":{SPAN}}}}}"#
    );
    let aliased = func(&block(0, &format!("{},{}", store(3), borrow), RETURN));
    assert!(unique_value_def(&aliased, 3).is_none(), "the VALUE question refuses the alias");
    assert!(
        super::unique_initializing_def(&aliased, 3).is_some(),
        "the ORIGIN question answers with the one `Assign` that initialized the local"
    );

    // A PARAMETER has no in-block initializer to hand back — its entry definition is in
    // no block — so the origin question refuses it exactly as the resolver does.
    let param = func(&block(0, &store(1), RETURN));
    assert!(super::unique_initializing_def(&param, 1).is_none(), "no in-block initializer");

    // A second whole write makes the initializer non-unique.
    let twice = func(&format!("{},{}", block(0, &store(3), &goto(1)), block(1, &store(3), RETURN)));
    assert!(super::unique_initializing_def(&twice, 3).is_none(), "two whole writes");

    // A CALL destination has no `Rvalue` to name, and a projected store leaves a value
    // the one `Assign` does not describe.
    let with_call =
        func(&format!("{},{}", block(0, &store(3), &call_to(3, 1)), block(1, "", RETURN)));
    assert!(super::unique_initializing_def(&with_call, 3).is_none(), "a call destination");

    let field = format!(
        r#"{{"Assign":{{"place":{{"local":3,"projections":[{{"Field":0}}]}},
           "rvalue":{{"Use":{{"Constant":{{"Uint":[7,64]}}}}}},"span":{SPAN}}}}}"#
    );
    let partial = func(&block(0, &format!("{},{}", store(3), field), RETURN));
    assert!(super::unique_initializing_def(&partial, 3).is_none(), "a projected store");

    let opaque = format!(r#"{{"Opaque":{{"kind":"asm","targets":[],"span":{SPAN}}}}}"#);
    let unlocatable = func(&format!("{},{}", block(0, &store(3), &goto(1)), block(1, "", &opaque)));
    assert!(super::unique_initializing_def(&unlocatable, 3).is_none(), "an unlocatable write");
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
/// `Escape` can carry a store this scan never names, so this question refuses it — as
/// `unique_value_def` now does too; `Unlocatable` is the absence of the information.
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
        "the alias channel is REFUSED here, as it now is by `unique_value_def` too"
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

// Trust: 2026-09-16 (round A5) — THE JOIN QUESTION, `value_calls`: every call
// destination when call destinations are the local's ONLY write channel. The
// consumer (`iterator_yield::next_call_receivers`) may mint only a DISJUNCTION over
// the returned calls, so what this question refuses is exactly what would put a value
// no call produced into the local.

/// Two call destinations and nothing else: BOTH are returned, and `unique_value_call`
/// (the one-call form of the same question) declines — the two answers differ on
/// exactly this shape.
#[test]
fn two_call_destinations_and_nothing_else_are_the_joinable_calls() {
    let f = func(&format!(
        "{},{},{},{}",
        block(0, "", &switch(1, 2)),
        block(1, "", &call_to(3, 3)),
        block(2, "", &call_to(3, 3)),
        block(3, &read(3), RETURN)
    ));
    let calls = super::value_calls(&f, 3).expect("two calls and nothing else joins");
    assert_eq!(calls.len(), 2);
    assert!(calls.iter().all(|t| matches!(t, trust_types::Terminator::Call { .. })));
    assert!(super::unique_value_call(&f, 3).is_none(), "one-call form declines two calls");
    // The one-call shape answers both questions.
    let one = func(&format!("{},{}", block(0, "", &call_to(3, 1)), block(1, &read(3), RETURN)));
    assert_eq!(super::value_calls(&one, 3).map(|c| c.len()), Some(1));
}

/// Every other channel refuses: a `WholeNamed` `Assign` beside the calls (a value no
/// call produced), a `Partial` write, an `Escape`, an `Unlocatable` write, a parameter's
/// entry definition, a `TailCall`, and a local no call writes at all.
#[test]
fn every_other_channel_declines_the_joinable_calls() {
    let two = |tail: &str| {
        format!(
            "{},{},{},{}",
            block(0, "", &switch(1, 2)),
            block(1, "", &call_to(3, 3)),
            block(2, "", &call_to(3, 3)),
            tail
        )
    };
    let with_assign = func(&two(&block(3, &store(3), RETURN)));
    assert!(super::value_calls(&with_assign, 3).is_none(), "a named `Assign` beside the calls");

    let deinit = format!(r#"{{"Deinit":{{"place":{{"local":3,"projections":[]}}}}}}"#);
    let partial = func(&two(&block(3, &deinit, RETURN)));
    assert!(super::value_calls(&partial, 3).is_none(), "a partial write");

    let borrow = format!(
        r#"{{"Assign":{{"place":{{"local":4,"projections":[]}},
           "rvalue":{{"Ref":{{"mutable":true,"place":{{"local":3,"projections":[]}}}}}},
           "span":{SPAN}}}}}"#
    );
    let aliased = func(&two(&block(3, &borrow, RETURN)));
    assert!(super::value_calls(&aliased, 3).is_none(), "an alias");

    let opaque = format!(r#"{{"Opaque":{{"kind":"asm","targets":[],"span":{SPAN}}}}}"#);
    let unlocatable = func(&two(&block(3, "", &opaque)));
    assert!(super::value_calls(&unlocatable, 3).is_none(), "an unlocatable write");

    let param = func(&format!(
        "{},{},{},{}",
        block(0, "", &switch(1, 2)),
        block(1, "", &call_to(1, 3)),
        block(2, "", &call_to(1, 3)),
        block(3, &read(1), RETURN)
    ));
    assert!(super::value_calls(&param, 1).is_none(), "a parameter's entry definition");

    let tail = format!(
        r#"{{"TailCall":{{"func":"g","args":[],"span":{SPAN},"atomic":null,
           "is_foreign":false,"is_unsafe_sig":false}}}}"#
    );
    let tail_call = func(&block(0, "", &tail));
    assert!(super::value_calls(&tail_call, 0).is_none(), "a `TailCall` has no destination");

    let never = func(&block(0, &read(1), RETURN));
    assert!(super::value_calls(&never, 3).is_none(), "no call writes the local");
}

// Trust: 2026-09-16 (round A6) — THE CALL-THROUGH-TEMP SPELLING of the join question.
// rustc lowers a loop-carried `o = it.next()` at `-O0` as `_tmp = next(..); _o = move
// _tmp`: a `WholeNamed` write beside `_o`'s direct call, which `value_calls` refused,
// withholding the join AND the havoc lane's candidate, so a correct program refuted
// (`ctl_two_next_loopcarried`, real MIR in `tests/escaped_local_seam_realmir.rs`).
// The admission is exact: the temp's only write is one `Call` destination and its only
// reads are whole-local `Use`s. These rows pin the admission and every refusal around it.

/// `_0 = copy _src` — a read of `_src` into the return place (NOT into `_4`, which
/// `read` writes and which is the local under test in these rows).
fn ret(src: usize) -> String {
    format!(
        r#"{{"Assign":{{"place":{{"local":0,"projections":[]}},
           "rvalue":{{"Use":{{"Copy":{{"local":{src},"projections":[]}}}}}},"span":{SPAN}}}}}"#
    )
}

/// `_dst = move _src` — a whole-local `Use` of `_src` into `_dst`.
fn carry(dst: usize, src: usize) -> String {
    format!(
        r#"{{"Assign":{{"place":{{"local":{dst},"projections":[]}},
           "rvalue":{{"Use":{{"Move":{{"local":{src},"projections":[]}}}}}},"span":{SPAN}}}}}"#
    )
}

/// The admitted shape: `_4 = g()` directly in bb1, `_3 = g()` in bb2 carried by
/// `_4 = move _3` in bb3. BOTH calls are `_4`'s producing calls; the one-call form still
/// declines (`_4` has a named write beside its call).
#[test]
fn a_call_carried_through_a_result_temp_joins_the_calls() {
    let f = func(&format!(
        "{},{},{},{},{}",
        block(0, "", &switch(1, 2)),
        block(1, "", &call_to(4, 4)),
        block(2, "", &call_to(3, 3)),
        block(3, &carry(4, 3), &goto(4)),
        block(4, &ret(4), RETURN)
    ));
    let calls = super::value_calls(&f, 4).expect("a direct call and a carried call join");
    assert_eq!(calls.len(), 2, "the temp's call is recorded beside the direct destination");
    assert!(calls.iter().all(|t| matches!(t, trust_types::Terminator::Call { .. })));
    assert!(super::unique_value_call(&f, 4).is_none(), "the one-call form still declines");
    // The carried-only shape (no direct call) answers with exactly the temp's call.
    let carried_only = func(&format!(
        "{},{},{}",
        block(0, "", &call_to(3, 1)),
        block(1, &carry(4, 3), &goto(2)),
        block(2, &ret(4), RETURN)
    ));
    assert_eq!(super::value_calls(&carried_only, 4).map(|c| c.len()), Some(1));
}

/// Every way the temp can fail to be a pure call-result carrier refuses the whole
/// join: a temp with a NAMED write beside its call (a value no call produced), a temp
/// that is a PARAMETER (its entry value), a temp with two calls, an ALIASED temp, a
/// temp READ anywhere but a whole-local `Use` (a call argument, a borrow, a projected
/// read), a carried PROJECTED place, and a carry of the local into itself.
#[test]
fn a_temp_that_is_not_a_pure_call_result_carrier_refuses_the_join() {
    let carried = |mid: &str| {
        format!(
            "{},{},{}",
            block(0, "", &call_to(3, 1)),
            block(1, mid, &goto(2)),
            block(2, &ret(4), RETURN)
        )
    };
    // `_3 = const 7` beside the call, then carried.
    let named = func(&carried(&format!("{},{}", store(3), carry(4, 3))));
    assert!(super::value_calls(&named, 4).is_none(), "a named write beside the temp's call");

    // The temp is a PARAMETER (`_1`) written by one call.
    let param_temp = func(&format!(
        "{},{},{}",
        block(0, "", &call_to(1, 1)),
        block(1, &carry(4, 1), &goto(2)),
        block(2, &ret(4), RETURN)
    ));
    assert!(super::value_calls(&param_temp, 4).is_none(), "a parameter is never a result temp");

    // Two calls into the temp.
    let two_calls = func(&format!(
        "{},{},{},{}",
        block(0, "", &call_to(3, 1)),
        block(1, "", &call_to(3, 2)),
        block(2, &carry(4, 3), &goto(3)),
        block(3, &ret(4), RETURN)
    ));
    assert!(super::value_calls(&two_calls, 4).is_none(), "two calls write the temp");

    // `&mut _3` handed out.
    let borrow = format!(
        r#"{{"Assign":{{"place":{{"local":0,"projections":[]}},
           "rvalue":{{"Ref":{{"mutable":true,"place":{{"local":3,"projections":[]}}}}}},
           "span":{SPAN}}}}}"#
    );
    let aliased = func(&carried(&format!("{},{}", borrow, carry(4, 3))));
    assert!(super::value_calls(&aliased, 4).is_none(), "an aliased temp");

    // The temp is also passed as a call ARGUMENT.
    let arg_call = format!(
        r#"{{"Call":{{"func":"h","args":[{{"Copy":{{"local":3,"projections":[]}}}}],
           "dest":{{"local":0,"projections":[]}},"target":2,"span":{SPAN},"atomic":null,
           "is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}}}"#
    );
    let read_as_arg = func(&format!(
        "{},{},{}",
        block(0, "", &call_to(3, 1)),
        block(1, &carry(4, 3), &arg_call),
        block(2, &ret(4), RETURN)
    ));
    assert!(super::value_calls(&read_as_arg, 4).is_none(), "a temp read as a call argument");

    // The temp is read through a PROJECTION (`_0 = copy _3.0`).
    let projected_read = format!(
        r#"{{"Assign":{{"place":{{"local":0,"projections":[]}},
           "rvalue":{{"Use":{{"Copy":{{"local":3,"projections":[{{"Field":0}}]}}}}}},"span":{SPAN}}}}}"#
    );
    let read_projected = func(&carried(&format!("{},{}", carry(4, 3), projected_read)));
    assert!(super::value_calls(&read_projected, 4).is_none(), "a projected read of the temp");

    // The carried operand is a PROJECTED place (`_4 = move _3.0`).
    let carry_projected = format!(
        r#"{{"Assign":{{"place":{{"local":4,"projections":[]}},
           "rvalue":{{"Use":{{"Move":{{"local":3,"projections":[{{"Field":0}}]}}}}}},"span":{SPAN}}}}}"#
    );
    let projected_carry = func(&carried(&carry_projected));
    assert!(super::value_calls(&projected_carry, 4).is_none(), "a projected carry");

    // The CONTROL: the same temp with nothing else answers, so none of the refusals
    // above is a blanket decline of the spelling.
    let clean = func(&carried(&carry(4, 3)));
    assert_eq!(super::value_calls(&clean, 4).map(|c| c.len()), Some(1));
}

/// A temp copied into TWO locals is still a pure carrier: every read is a whole-local
/// `Use`, and the value each receives is the one call's result. (`let mut q = o; .. let
/// r = it.next(); q = r; o = r;` lowers to `_6 = copy _13; _4 = copy _13`.) A read that is
/// not a `Use` — a `SwitchInt` on the temp — refuses.
#[test]
fn a_temp_copied_into_two_locals_is_still_a_carrier() {
    let copy_into = |dst: usize| {
        format!(
            r#"{{"Assign":{{"place":{{"local":{dst},"projections":[]}},
               "rvalue":{{"Use":{{"Copy":{{"local":3,"projections":[]}}}}}},"span":{SPAN}}}}}"#
        )
    };
    let shared = func(&format!(
        "{},{},{}",
        block(0, "", &call_to(3, 1)),
        block(1, &format!("{},{}", copy_into(4), copy_into(0)), &goto(2)),
        block(2, &ret(4), RETURN)
    ));
    // (`_0` is written again by `ret`, so only `_4` is the subject here.)
    assert_eq!(super::value_calls(&shared, 4).map(|c| c.len()), Some(1));

    let switch_on_temp = format!(
        r#"{{"SwitchInt":{{"discr":{{"Copy":{{"local":3,"projections":[]}}}},
           "targets":[[0,2]],"otherwise":2,"exhaustive_enum_unreachable":false,
           "span":{SPAN}}}}}"#
    );
    let switched = func(&format!(
        "{},{},{}",
        block(0, "", &call_to(3, 1)),
        block(1, &copy_into(4), &switch_on_temp),
        block(2, &ret(4), RETURN)
    ));
    assert!(super::value_calls(&switched, 4).is_none(), "a terminator read of the temp");
}

// ── the N-DEFINITION list: `value_defs` ─────────────────────────────────────
//
// `unique_value_def` answers only for a single-valued local, so a caller recognizing
// a TWO-definition idiom — a loop counter `i = 0 … i = i + s` — had no seam question
// and re-derived a block scan. `generate::loop_bounds::counter_init_stride_block` was
// that scan: it enumerated `Assign`, the `Call` destination and the mutable alias by
// hand, and was blind to `Partial` and to `TailCall`. These rows are the question.

/// The answering case: a non-parameter with two whole-local `Assign`s gets both, in
/// block order, and the list length IS the value count.
#[test]
fn two_named_definitions_are_both_returned() {
    let f = func(&format!("{},{}", block(0, &store(3), &goto(1)), block(1, &store(3), RETURN)));
    let defs = super::value_defs(&f, 3).expect("two named writes and nothing else");
    assert_eq!(defs.len(), 2, "both definitions, not the first");
    assert_eq!(defs[0].0, 0, "the block index of the first");
    assert_eq!(defs[1].0, 1);
    assert_eq!(value_count(&f, 3), ValueCount::Exactly(defs.len()));
    assert_eq!(
        super::value_defs(&f, 4).map(|d| d.len()),
        Some(0),
        "a never-written temp has no values"
    );
}

/// A PARAMETER answers `None` — the ENTRY definition is in no block, so no list built
/// from `body.blocks` can contain it, and a caller reading `Some(defs)` as "these are
/// all the values" would be reading a list one short. This is the row the counter
/// recognizer's own `arg_count` bail used to write by hand.
#[test]
fn a_parameter_has_no_value_def_list() {
    let f = func(&format!("{},{}", block(0, &read(1), &goto(1)), block(1, &store(1), RETURN)));
    assert_eq!(value_count(&f, 1), ValueCount::Exactly(2), "entry + the store");
    assert!(
        super::value_defs(&f, 1).is_none(),
        "the entry definition has no rvalue this list could carry"
    );
    // The same body with the parameter swapped for a temp still answers.
    let temp = func(&format!("{},{}", block(0, &read(3), &goto(1)), block(1, &store(3), RETURN)));
    assert_eq!(super::value_defs(&temp, 3).map(|d| d.len()), Some(1));
}

/// Every other channel declines, each for the reason `unique_value_def` declines it:
/// a `Call` dest is a value with no `Rvalue` to return, a `Partial` write leaves a
/// value no returned rvalue names, an `Escape` can carry a store this walk never sees,
/// and an `Unlocatable` write is the absence of the information.
#[test]
fn every_unnamed_channel_declines_the_value_def_list() {
    let with_call =
        func(&format!("{},{}", block(0, &store(3), &call_to(3, 1)), block(1, "", RETURN)));
    assert!(super::value_defs(&with_call, 3).is_none(), "a `Call` destination");

    let deinit = r#"{"Deinit":{"place":{"local":3,"projections":[]}}}"#.to_string();
    let partial = func(&format!("{},{}", block(0, &store(3), &goto(1)), block(1, &deinit, RETURN)));
    assert!(super::value_defs(&partial, 3).is_none(), "a partial write");

    let borrow = format!(
        r#"{{"Assign":{{"place":{{"local":4,"projections":[]}},
           "rvalue":{{"Ref":{{"mutable":true,"place":{{"local":3,"projections":[]}}}}}},
           "span":{SPAN}}}}}"#
    );
    let aliased = func(&format!("{},{}", block(0, &store(3), &goto(1)), block(1, &borrow, RETURN)));
    assert!(super::value_defs(&aliased, 3).is_none(), "a mutable alias");

    let opaque = format!(r#"{{"Opaque":{{"kind":"asm","targets":[],"span":{SPAN}}}}}"#);
    let unlocatable = func(&format!("{},{}", block(0, &store(3), &goto(1)), block(1, "", &opaque)));
    assert!(super::value_defs(&unlocatable, 3).is_none(), "an unlocatable write");

    // The CONTROL: the same single store with nothing else still answers, so none of
    // the four refusals above is a blanket decline.
    let clean = func(&block(0, &store(3), RETURN));
    assert_eq!(super::value_defs(&clean, 3).map(|d| d.len()), Some(1));
}

// ── a pointer handed out ───────────────────────────────────────────────────

/// `f` with `_1: &mut usize` and one call `g(<arg>)`.
fn pointer_call(arg: &str, mutable: bool) -> VerifiableFunction {
    let mut f = func(&format!(
        "{},{}",
        block(
            0,
            "",
            &format!(
                r#"{{"Call":{{"func":"g","args":[{arg}],"dest":{{"local":3,"projections":[]}},
                   "target":1,"span":{SPAN},"atomic":null,"is_foreign":false,
                   "is_unsafe_sig":false,"unwind":"Continue"}}}}"#
            )
        ),
        block(1, "", RETURN)
    ));
    f.body.locals[1].ty = trust_types::Ty::Ref {
        mutable,
        inner: Box::new(trust_types::Ty::Int { width: 64, signed: false }),
    };
    f
}

#[test]
fn a_mutable_pointer_passed_to_a_call_may_write_what_it_points_to() {
    // `zero(x)`: the callee can write `*x` with no store naming `x`
    // (trip-count lane review and ascii audit, 2026-09-29).
    let pointee =
        trust_types::Place { local: 1, projections: vec![trust_types::Projection::Deref] };
    let bare = r#"{"Copy":{"local":1,"projections":[]}}"#;
    assert!(!super::deref_read_is_never_written(&pointer_call(bare, true), &pointee));
    // Reading the pointee (`g(*x)`) hands out nothing.
    let deref = r#"{"Copy":{"local":1,"projections":["Deref"]}}"#;
    assert!(super::deref_read_is_never_written(&pointer_call(deref, true), &pointee));
    // Nothing can be written through a shared reference to a place with no `UnsafeCell`.
    assert!(super::deref_read_is_never_written(&pointer_call(bare, false), &pointee));
}

/// `f` with `_1: &mut <pointee>` and one statement storing into `(*_1).1`; `None` leaves
/// the pointee's kind unrecorded, as every synthetic `Ty::adt`.
fn sibling_field_store(pointee_kind: Option<trust_types::AdtKind>) -> VerifiableFunction {
    let store = format!(
        r#"{{"Assign":{{"place":{{"local":1,"projections":["Deref",{{"Field":1}}]}},
           "rvalue":{{"Use":{{"Constant":{{"Uint":[7,64]}}}}}},"span":{SPAN}}}}}"#
    );
    let mut f = func(&block(0, &store, RETURN));
    let mut pointee = trust_types::Ty::adt(
        "U",
        vec![
            ("a".into(), trust_types::Ty::Int { width: 64, signed: false }),
            ("b".into(), trust_types::Ty::Int { width: 64, signed: false }),
        ],
    );
    if let trust_types::Ty::Adt { adt_kind, .. } = &mut pointee {
        *adt_kind = pointee_kind;
    }
    f.body.locals[1].ty = trust_types::Ty::Ref { mutable: true, inner: Box::new(pointee) };
    f
}

#[test]
fn a_store_to_a_union_sibling_writes_the_read() {
    // `(*u).1 = 7` overlaps `(*u).0` in a union, although the names spell them as
    // disjoint siblings (the pointer-family check's precondition audit, 2026-09-29).
    let read = trust_types::Place {
        local: 1,
        projections: vec![trust_types::Projection::Deref, trust_types::Projection::Field(0)],
    };
    assert!(!super::deref_read_is_never_written(
        &sibling_field_store(Some(trust_types::AdtKind::Union)),
        &read
    ));
    // A variant-less ADT whose kind was not recorded may be a union, as for the union
    // write cover and `place_is_body_stable` (until 2026-10-16 this read was granted).
    assert!(!super::deref_read_is_never_written(&sibling_field_store(None), &read));
    // The control: in a struct the sibling store leaves the read alone.
    assert!(super::deref_read_is_never_written(
        &sibling_field_store(Some(trust_types::AdtKind::Struct)),
        &read
    ));
}

/// Trust: 2026-10-16 (the review of the INTERIOR-MUT-CHANNEL-2 fix) — the family check's
/// union refusal is the union write cover's walk: it refuses exactly where
/// `generate::union_write_cover_len` (over `field_base_may_overlap_siblings`, as the slot
/// half's cover and `place_is_body_stable`'s union step ask) sees a possible union.
#[test]
fn the_union_refusal_is_the_union_write_cover_walk() {
    use trust_types::AdtKind;
    let read = trust_types::Place {
        local: 1,
        projections: vec![trust_types::Projection::Deref, trust_types::Projection::Field(0)],
    };
    for kind in [Some(AdtKind::Union), None, Some(AdtKind::Struct)] {
        let f = sibling_field_store(kind);
        let may_be_union = crate::generate::union_write_cover_len(&f, &read).is_some();
        assert_eq!(may_be_union, kind != Some(AdtKind::Struct), "{kind:?}");
        assert_eq!(super::deref_read_is_never_written(&f, &read), !may_be_union, "{kind:?}");
    }
}

#[test]
fn a_pointer_loaded_through_a_union_field_refuses() {
    // `_3 = copy (*_1).0` loads `u.a` out of `union U { a: &S, b: &S }`; `(*_3).0` reads
    // `u.a.n`, and a store to `u.b` would write the same pointer (review8 `p2_union`).
    let load = format!(
        r#"{{"Assign":{{"place":{{"local":3,"projections":[]}},
           "rvalue":{{"Use":{{"Copy":{{"local":1,"projections":["Deref",{{"Field":0}}]}}}}}},
           "span":{SPAN}}}}}"#
    );
    let holder = |kind: Option<trust_types::AdtKind>| {
        // `S` is stamped, so only `U`'s kind decides.
        let mut s = trust_types::Ty::adt("S", vec![("n".into(), trust_types::Ty::usize())]);
        if let trust_types::Ty::Adt { adt_kind, .. } = &mut s {
            *adt_kind = Some(trust_types::AdtKind::Struct);
        }
        let r = trust_types::Ty::Ref { mutable: false, inner: Box::new(s.clone()) };
        let mut u =
            trust_types::Ty::adt("U", vec![("a".into(), r.clone()), ("b".into(), r.clone())]);
        if let trust_types::Ty::Adt { adt_kind, .. } = &mut u {
            *adt_kind = kind;
        }
        let mut f = func(&block(0, &load, RETURN));
        f.body.locals[1].ty = trust_types::Ty::Ref { mutable: true, inner: Box::new(u) };
        f.body.locals[3].ty = r;
        f
    };
    let read = trust_types::Place {
        local: 3,
        projections: vec![trust_types::Projection::Deref, trust_types::Projection::Field(0)],
    };
    assert!(!super::deref_read_is_never_written(&holder(Some(trust_types::AdtKind::Union)), &read));
    // The holder's kind unrecorded: it may be a union (2026-10-16).
    assert!(!super::deref_read_is_never_written(&holder(None), &read));
    assert!(super::deref_read_is_never_written(&holder(Some(trust_types::AdtKind::Struct)), &read));
}

/// Trust: 2026-09-24 (TRUST-10) — THE PINNED-POINTER QUESTION: a borrow THROUGH the
/// local hands out its pointee and leaves the pointer pinned; a borrow OF the local,
/// a second definition, or a parameter store unpins it.
#[test]
fn a_borrow_through_a_pointer_leaves_it_pinned_and_a_borrow_of_it_does_not() {
    let untouched = func(&block(0, &read(1), RETURN));
    assert!(pointer_is_pinned(&untouched, 1), "a never-written parameter is pinned");

    let through = func(&block(0, &borrow_mut(3, 1, r#""Deref",{"Field":0}"#), RETURN));
    assert!(pointer_is_pinned(&through, 1), "`&mut (*_1).0` cannot reseat `_1`");
    assert!(
        !every_write_is_whole_named(&through, 1),
        "the wider every-write question counts it as an alias of `_1`"
    );

    let of_it = func(&block(0, &borrow_mut(3, 1, ""), RETURN));
    assert!(!pointer_is_pinned(&of_it, 1), "`&mut _1` could reseat `_1`");

    let stored = func(&block(0, &store(1), RETURN));
    assert!(!pointer_is_pinned(&stored, 1), "a stored parameter holds two values");

    let temp_once = func(&block(0, &store(4), RETURN));
    assert!(pointer_is_pinned(&temp_once, 4), "one whole named definition");
    let temp_twice = func(&block(0, &format!("{},{}", store(4), store(4)), RETURN));
    assert!(!pointer_is_pinned(&temp_twice, 4), "two definitions");
}

// ── CL-FOLD-LOCALDEF-1 (2026-10-11): the value question modulo a WHOLE-local `Drop` ──

/// `drop(_place) -> bb<target>`.
fn drop_of(place_json: &str, target: usize) -> String {
    format!(
        r#"{{"Drop":{{"place":{place_json},"target":{target},"span":{SPAN},
           "unwind":"Continue"}}}}"#
    )
}

const WHOLE_3: &str = r#"{"local":3,"projections":[]}"#;
const FIELD_3: &str = r#"{"local":3,"projections":[{"Field":0}]}"#;

/// A `Drop` of the WHOLE local ENDS the value: no read of `_3` can follow it without a
/// re-initialisation, which is a second whole write. So the value question that
/// `alloc_vcs::local_def` inlines answers through it, for both channels, while the plain
/// resolvers keep refusing it (`drop_is_a_partial_write_of_the_dropped_local`).
#[test]
fn whole_drop_ends_the_value_and_the_drop_aware_question_answers_through_it() {
    use super::{WholeDefinition, unique_value_modulo_whole_drops};
    let assign = func(&format!(
        "{},{}",
        block(0, &format!("{},{}", store(3), read(3)), &drop_of(WHOLE_3, 1)),
        block(1, "", RETURN)
    ));
    assert!(unique_value_def(&assign, 3).is_none(), "the plain resolver still refuses it");
    assert!(
        matches!(unique_value_modulo_whole_drops(&assign, 3), Some(WholeDefinition::Assign(_))),
        "the one `Assign` is the value at every read"
    );
    let call = func(&format!(
        "{},{},{}",
        block(0, "", &call_to(3, 1)),
        block(1, &read(3), &drop_of(WHOLE_3, 2)),
        block(2, "", RETURN)
    ));
    assert!(super::unique_value_call(&call, 3).is_none(), "the plain resolver still refuses it");
    assert!(
        matches!(unique_value_modulo_whole_drops(&call, 3), Some(WholeDefinition::Call(_))),
        "the one `Call` destination is the value at every read"
    );
}

/// The narrowing is exactly ONE channel wide. A PROJECTED drop, a projected store in the
/// SAME block as a whole drop (the walk must tell a statement's write from the
/// terminator's), a parameter, a second whole write (`Assign` or `Call`), an alias and an
/// unlocatable write are each refused, as the plain resolvers refuse them.
#[test]
fn whole_drop_narrowing_refuses_every_other_channel() {
    use super::unique_value_modulo_whole_drops as q;
    let field_store = format!(
        r#"{{"Assign":{{"place":{FIELD_3},
           "rvalue":{{"Use":{{"Constant":{{"Uint":[7,64]}}}}}},"span":{SPAN}}}}}"#
    );
    let borrow = format!(
        r#"{{"Assign":{{"place":{{"local":4,"projections":[]}},
           "rvalue":{{"Ref":{{"mutable":true,"place":{WHOLE_3}}}}},"span":{SPAN}}}}}"#
    );
    let opaque = format!(r#"{{"Opaque":{{"kind":"asm","targets":[],"span":{SPAN}}}}}"#);

    let projected_drop =
        func(&format!("{},{}", block(0, &store(3), &drop_of(FIELD_3, 1)), block(1, "", RETURN)));
    assert!(q(&projected_drop, 3).is_none(), "a projected drop");

    let store_beside_whole_drop = func(&format!(
        "{},{}",
        block(0, &format!("{},{}", store(3), field_store), &drop_of(WHOLE_3, 1)),
        block(1, "", RETURN)
    ));
    assert!(q(&store_beside_whole_drop, 3).is_none(), "a projected store beside a whole drop");

    let param = func(&format!("{},{}", block(0, &store(1), &goto(1)), block(1, "", RETURN)));
    assert!(q(&param, 1).is_none(), "a parameter's body store is its second value");
    let untouched_param = func(&block(0, "", RETURN));
    assert!(q(&untouched_param, 1).is_none(), "a parameter's entry value has no definition");

    let twice = func(&format!("{},{}", block(0, &store(3), &goto(1)), block(1, &store(3), RETURN)));
    assert!(q(&twice, 3).is_none(), "two whole writes");
    let assign_and_call =
        func(&format!("{},{}", block(0, &store(3), &call_to(3, 1)), block(1, "", RETURN)));
    assert!(q(&assign_and_call, 3).is_none(), "an `Assign` beside a call destination");

    let aliased = func(&block(0, &format!("{},{}", store(3), borrow), RETURN));
    assert!(q(&aliased, 3).is_none(), "the VALUE question refuses the alias");
    assert!(
        super::unique_initializing_modulo_whole_drops(&aliased, 3).is_some(),
        "the ORIGIN twin readmits exactly the alias"
    );
    let aliased_projected_drop = func(&format!(
        "{},{}",
        block(0, &format!("{},{}", store(3), borrow), &drop_of(FIELD_3, 1)),
        block(1, "", RETURN)
    ));
    assert!(
        super::unique_initializing_modulo_whole_drops(&aliased_projected_drop, 3).is_none(),
        "the ORIGIN twin readmits nothing else"
    );

    let unlocatable = func(&format!("{},{}", block(0, &store(3), &goto(1)), block(1, "", &opaque)));
    assert!(q(&unlocatable, 3).is_none(), "an unlocatable write");
    assert!(super::unique_initializing_modulo_whole_drops(&unlocatable, 3).is_none());
}

/// With no `Drop` anywhere, the drop-aware question IS the two plain resolvers.
#[test]
fn without_a_drop_the_drop_aware_question_is_the_plain_resolvers() {
    use super::{WholeDefinition, unique_value_modulo_whole_drops};
    let bodies = [
        func(&block(0, &store(3), RETURN)),
        func(&format!("{},{}", block(0, "", &call_to(3, 1)), block(1, &read(3), RETURN))),
        func(&format!("{},{}", block(0, &store(3), &goto(1)), block(1, &store(3), RETURN))),
        func(&format!("{},{}", block(0, &store(3), &call_to(3, 1)), block(1, "", RETURN))),
        func(&block(0, &store(1), RETURN)),
    ];
    for (i, f) in bodies.iter().enumerate() {
        for local in 0..5 {
            let plain = match (unique_value_def(f, local), super::unique_value_call(f, local)) {
                (Some(_), None) => "assign",
                (None, Some(_)) => "call",
                (None, None) => "none",
                (Some(_), Some(_)) => panic!("body {i}, _{local}: both resolvers answered"),
            };
            let aware = match unique_value_modulo_whole_drops(f, local) {
                Some(WholeDefinition::Assign(_)) => "assign",
                Some(WholeDefinition::Call(_)) => "call",
                None => "none",
            };
            assert_eq!(plain, aware, "body {i}, _{local}");
        }
    }
}

// ── VCGEN-LIB-REDS-1 (2026-11-06): slot stability modulo a WHOLE-local `Drop` ──

fn shared_slot_is_stable(f: &VerifiableFunction, local: usize) -> bool {
    trust_types::local_defs::source_slot_is_stable(&f.body, local)
}

/// The ny extract-then-guard shape: `_3` is built once and read, one arm drops it
/// whole and returns, the other reads it. Since 354c8202e1 the shared slot reducer
/// refuses `_3` for that drop; the narrowed question answers through exactly it.
#[test]
fn slot_stability_modulo_whole_drops_answers_through_the_whole_drop() {
    use super::body_slot_is_stable_modulo_whole_drops as narrowed;
    let guard_err_drop = func(&format!(
        "{},{},{},{}",
        block(0, &format!("{},{}", store(3), read(3)), &switch(1, 2)),
        block(1, "", &drop_of(WHOLE_3, 3)),
        block(2, &read(3), &goto(3)),
        block(3, "", RETURN)
    ));
    assert!(!shared_slot_is_stable(&guard_err_drop, 3), "the shared reducer refuses the drop");
    assert!(narrowed(&guard_err_drop.body, 3), "the whole drop ends the value; it is not a write");
    // The drop is the only channel the narrowing reads differently.
    for local in [0, 1, 2, 4] {
        assert_eq!(
            narrowed(&guard_err_drop.body, local),
            shared_slot_is_stable(&guard_err_drop, local),
            "_{local}"
        );
    }
}

/// Every other channel still destabilises the slot, with or without a whole drop beside
/// it: a projected drop, a projected store, a re-initialisation after the drop, a second
/// whole write, a `&mut` alias, a store through a pointer rooted at the local, a
/// projected call destination, a parameter's body store and an unlocatable write.
#[test]
fn slot_stability_modulo_whole_drops_refuses_every_other_channel() {
    use super::body_slot_is_stable_modulo_whole_drops as narrowed;
    let field_store = format!(
        r#"{{"Assign":{{"place":{FIELD_3},
           "rvalue":{{"Use":{{"Constant":{{"Uint":[7,64]}}}}}},"span":{SPAN}}}}}"#
    );
    let deref_store = format!(
        r#"{{"Assign":{{"place":{{"local":3,"projections":["Deref"]}},
           "rvalue":{{"Use":{{"Constant":{{"Uint":[7,64]}}}}}},"span":{SPAN}}}}}"#
    );
    let projected_call = format!(
        r#"{{"Call":{{"func":"g","args":[],"dest":{FIELD_3},
           "target":1,"span":{SPAN},"atomic":null,"is_foreign":false,
           "is_unsafe_sig":false,"unwind":"Continue"}}}}"#
    );
    let opaque = format!(r#"{{"Opaque":{{"kind":"asm","targets":[1],"span":{SPAN}}}}}"#);
    let with_drop = |stmts: &str| {
        func(&format!(
            "{},{}",
            block(0, &format!("{},{stmts}", store(3)), &drop_of(WHOLE_3, 1)),
            block(1, "", RETURN)
        ))
    };
    let refused = [
        (
            "projected drop",
            func(&format!(
                "{},{}",
                block(0, &store(3), &drop_of(FIELD_3, 1)),
                block(1, "", RETURN)
            )),
            3,
        ),
        ("projected store beside a whole drop", with_drop(&field_store), 3),
        ("store through the local's pointer beside a whole drop", with_drop(&deref_store), 3),
        ("&mut alias beside a whole drop", with_drop(&borrow_mut(4, 3, "")), 3),
        (
            "re-initialisation after the drop",
            func(&format!(
                "{},{}",
                block(0, &store(3), &drop_of(WHOLE_3, 1)),
                block(1, &store(3), RETURN)
            )),
            3,
        ),
        (
            "second whole write",
            func(&format!("{},{}", block(0, &store(3), &goto(1)), block(1, &store(3), RETURN))),
            3,
        ),
        (
            "projected call destination",
            func(&format!("{},{}", block(0, &store(3), &projected_call), block(1, "", RETURN))),
            3,
        ),
        (
            "parameter stored in the body",
            func(&format!("{},{}", block(0, &store(1), &goto(1)), block(1, "", RETURN))),
            1,
        ),
        (
            "unlocatable write",
            func(&format!("{},{}", block(0, &store(3), &opaque), block(1, "", RETURN))),
            3,
        ),
    ];
    for (name, f, local) in &refused {
        assert!(!narrowed(&f.body, *local), "{name}");
        assert!(!shared_slot_is_stable(f, *local), "{name}: the shared reducer agrees");
    }
}

/// Trust: 2026-10-15 (G2-INDEX-LINEAR-1). The write index lists a SHARED borrow for the
/// local it borrows from exactly when the borrow covers `UnsafeCell` bytes of that local's
/// own storage (`generate::shared_borrow_cell_places`), the only way a shared borrow
/// escapes its root (INTERIOR-MUT-CHANNEL-1). Both directions: `&c` of an owned
/// `c: Cell<usize>` is listed, and its escape reaches the resolver through the index;
/// `&n` of a `usize`, and `&(*r)` THROUGH a reference to a cell (the pointer's own
/// channel), are not listed. Listing every shared borrow made each question about `self`
/// visit all `n` of `shared_reborrow_calls`' `&*self` (`version_ssa_scaling_tests::
/// shared_reborrow_calls_are_linear`).
#[test]
fn the_write_index_lists_a_shared_borrow_exactly_when_it_covers_a_cell() {
    use trust_types::{
        AdtKind, BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue,
        SourceSpan, Statement, Terminator, Ty, VerifiableBody,
    };
    let stamped = |name: &str, fields: Vec<(&str, Ty)>| {
        let mut ty = Ty::adt(name, fields.into_iter().map(|(n, t)| (n.to_string(), t)).collect());
        if let Ty::Adt { adt_kind, .. } = &mut ty {
            *adt_kind = Some(AdtKind::Struct);
        }
        ty
    };
    let cell = stamped(
        "core::cell::Cell<usize>",
        vec![("value", stamped("core::cell::UnsafeCell<usize>", vec![("value", Ty::usize())]))],
    );
    let shared = |t: &Ty| Ty::Ref { mutable: false, inner: Box::new(t.clone()) };
    let assign = |local: usize, rvalue: Rvalue| Statement::Assign {
        place: Place::local(local),
        rvalue,
        span: SourceSpan::default(),
    };
    // `_1: &Cell<usize>` (the parameter), `_2`/`_3: Cell<usize>`, `_4: &Cell<usize>`,
    // `_5: usize`, `_6: &usize`, `_7: &Cell<usize>`.
    let locals = [
        Ty::Unit,
        shared(&cell),
        cell.clone(),
        cell.clone(),
        shared(&cell),
        Ty::usize(),
        shared(&Ty::usize()),
        shared(&cell),
    ];
    let stmts = vec![
        // `_2 = move _3`: `_2`'s one whole definition.
        assign(2, Rvalue::Use(Operand::Move(Place::local(3)))),
        // `_4 = &_2`: covers `_2`'s cell.
        assign(4, Rvalue::Ref { mutable: false, place: Place::local(2) }),
        // `_5 = const 7`: `_5`'s one whole definition.
        assign(5, Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 64)))),
        // `_6 = &_5`: `Freeze` bytes.
        assign(6, Rvalue::Ref { mutable: false, place: Place::local(5) }),
        // `_7 = &(*_1)`: through the reference, not `_1`'s own storage.
        assign(
            7,
            Rvalue::Ref {
                mutable: false,
                place: Place { local: 1, projections: vec![Projection::Deref] },
            },
        ),
    ];
    let f = VerifiableFunction {
        name: "f".into(),
        def_path: "c::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: locals
                .into_iter()
                .enumerate()
                .map(|(index, ty)| LocalDecl { index, ty, name: None })
                .collect(),
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    let index = super::LocalWriteIndex::build(&f.body);
    let listed = |l: usize| index.items_for_local(l).to_vec();
    assert_eq!(listed(2), vec![(0, 0), (0, 1)], "`&_2` covers `_2`'s cell: listed for `_2`");
    assert_eq!(listed(5), vec![(0, 2)], "`&_5` of `Freeze` bytes is not listed for `_5`");
    assert!(listed(1).is_empty(), "`&(*_1)` is the pointer's channel, not `_1`'s storage");
    assert!(index.universal.is_empty());
    // Through the index (a scope bound to `f`): the resolver sees `&_2`'s escape and
    // `_5`'s one value, as the whole-body walk does (the test-time differential
    // compares the two).
    let _scope = crate::generate::FuncAnalysisScope::enter(&f);
    assert!(crate::generate::local_write_index_for(&f.body).is_some());
    assert!(super::body_unique_value_def(&f.body, 2).is_none(), "`&_2` escapes `_2`");
    assert!(matches!(
        super::body_unique_value_def(&f.body, 5),
        Some(Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 64))))
    ));
}

#[test]
fn indexed_write_candidate_queries_skip_unrelated_blocks() {
    use trust_types::{
        BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
        Statement, Terminator, Ty, VerifiableBody,
    };
    // 512 blocks writing to `_2`, while `_1` is an untouched array parameter and `_3` is
    // written once in block 0.
    let locals = vec![
        LocalDecl { index: 0, ty: Ty::Unit, name: None },
        LocalDecl {
            index: 1,
            ty: Ty::Array { elem: Box::new(Ty::usize()), len: 4 },
            name: None,
        },
        LocalDecl { index: 2, ty: Ty::usize(), name: None },
        LocalDecl { index: 3, ty: Ty::usize(), name: None },
    ];
    let mut blocks = Vec::with_capacity(512);
    for b in 0..512usize {
        let mut stmts = vec![Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(b as u128, 64))),
            span: SourceSpan::default(),
        }];
        if b == 0 {
            stmts.push(Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                span: SourceSpan::default(),
            });
            stmts.push(Statement::Assign {
                place: Place {
                    local: 1,
                    projections: vec![Projection::Index(3)],
                },
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(9, 64))),
                span: SourceSpan::default(),
            });
        }
        let terminator = if b + 1 < 512 {
            Terminator::Goto(BlockId(b + 1))
        } else {
            Terminator::Return
        };
        blocks.push(BasicBlock { id: BlockId(b), stmts, terminator });
    }
    let f = VerifiableFunction {
        name: "f".into(),
        def_path: "c::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    let _scope = crate::generate::FuncAnalysisScope::enter(&f);
    let mut visited_for_3 = 0usize;
    crate::visit_local_write_candidates(&f, &f.body.blocks, 3, |_block, _item| {
        visited_for_3 += 1;
    });
    assert_eq!(visited_for_3, 1, "index visits only the single write to `_3`, not 512 blocks");
    assert!(crate::index_local_stable(&f, 3));
    assert!(crate::array_theory_local(&f, 1).is_some());
}
