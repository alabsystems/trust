// Trust (TWO-POINTER-FALSE-REFUTE, 2026-10-06): the underflow certificate a loop
// guard gives a downward-var decrement — `induction::downward_guards`,
// `TrueEdgeReach::certifies`, and the facts `build_downward_induction_facts` and
// `build_converging_pointer_facts` emit from it (the latter gated on the same
// true-edge certificate since CONVERGING-MERGE-1, 2026-10-10; its tests are last).
//
// Every fixture is REAL MIR, extracted with `-Ztrust-dump=mir:<dir>` by the stage-1
// compiler of 46e9afaf95 (main + waves 18-19) from the probe of the same name (span
// paths are already crate-relative). The probe sources and their BEFORE verdicts
// are in the header of `tests/ui/trust/two_pointer_relational_guard.rs`.
//
// WINS (a fact appears that did not): the two-pointer reverse and its spellings
// (`lo < hi` over a local, over a parameter, `hi > lo`, through `swap`).
// LIES CLOSED (a fact disappears that was FALSE before):
//  * `ge_twice` — the second decrement under `i > 1` inherited `_t.0 >= 1`
//    (DOWNWARD-GUARD-SECOND-DEC-1; certify accepted a function that panics);
//  * `stale` — a boolean computed before the first decrement was read as a guard
//    on the cursor (DOWNWARD-GUARD-STALE-1; certify accepted a panicking function);
//  * `conv_stale` — the converging `lo < s.len()` was emitted of an incremented
//    `lo` (CONVERGING-GUARD-STALE-1; certify accepted a panicking function);
//  * `param_cursor` — a `mut` parameter cursor's entry value was ignored
//    (DOWNWARD-PARAM-CURSOR-1; the bounds row was proved and kernel-certified);
//  * `two_dec`, `dowhile` — certificates for a second decrement / a decrement
//    before the first test, each false of the value it was keyed on, but caught
//    today by the decrement's own `overflow:sub` row (hardening).
// TWINS THAT MUST STAY CLOSED: `mut_le` (`<=`), `rel_dec2` (stride 2),
// `rel_twice` (second decrement), `signed_rel` (signed floor).

use super::*;

fn load(fixture: &str) -> VerifiableFunction {
    serde_json::from_str(fixture).expect("fixture MIR must deserialize")
}

fn downward(func: &VerifiableFunction) -> Vec<String> {
    build_downward_induction_facts(func).iter().map(|f| format!("{f:?}")).collect()
}

fn lt_len(t: &str) -> String {
    format!("Lt(Var(\"{t}\", Int), Var(\"s__slice_len\", Int))")
}

/// Every converging fact, flattened and sorted by block, as `bbN: <fact>`.
fn converging(func: &VerifiableFunction) -> Vec<String> {
    let mut out: Vec<String> = build_converging_pointer_facts(func)
        .into_iter()
        .flat_map(|(b, fs)| fs.into_iter().map(move |f| format!("bb{}: {f:?}", b.0)))
        .collect();
    out.sort();
    out
}

const TPR: &str = include_str!("../../tests/fixtures/downward_guard_tpr_mir.json");
const REV_DOWN: &str = include_str!("../../tests/fixtures/downward_guard_rev_down_mir.json");
const TPR_GT: &str = include_str!("../../tests/fixtures/downward_guard_tpr_gt_mir.json");
const TPR_SWAP: &str = include_str!("../../tests/fixtures/downward_guard_tpr_swap_mir.json");
const TPR_CONST: &str = include_str!("../../tests/fixtures/downward_guard_tpr_const_mir.json");
const MUT_LE: &str = include_str!("../../tests/fixtures/downward_guard_mut_le_mir.json");
const MUT_LATE: &str = include_str!("../../tests/fixtures/downward_guard_mut_late_mir.json");
const REL_DEC2: &str = include_str!("../../tests/fixtures/downward_guard_rel_dec2_mir.json");
const REL_TWICE: &str = include_str!("../../tests/fixtures/downward_guard_rel_twice_mir.json");
const TWO_DEC: &str = include_str!("../../tests/fixtures/downward_guard_two_dec_mir.json");
const GE_TWICE: &str = include_str!("../../tests/fixtures/downward_guard_ge_twice_mir.json");
const STALE: &str = include_str!("../../tests/fixtures/downward_guard_stale_mir.json");
const DOWHILE: &str = include_str!("../../tests/fixtures/downward_guard_dowhile_mir.json");
const SIGNED_REL: &str = include_str!("../../tests/fixtures/downward_guard_signed_rel_mir.json");
const PARAM_CURSOR: &str =
    include_str!("../../tests/fixtures/downward_guard_param_cursor_mir.json");
const CONV_STALE: &str = include_str!("../../tests/fixtures/converging_guard_stale_mir.json");
// CONVERGING-MERGE-1 (2026-10-10): dumped by the stage 1 of `5ccf66a518`
// (`integ/wave21`) from `conv_merge.rs` under `--cfg c1..c4` / `--cfg inside`; the
// sources are the `merge_*` revisions of `tests/ui/trust/two_pointer_relational_guard.rs`.
const MERGE_BREAK_LT: &str =
    include_str!("../../tests/fixtures/converging_merge_break_lt_mir.json");
const MERGE_BREAK_GT: &str =
    include_str!("../../tests/fixtures/converging_merge_break_gt_mir.json");
const MERGE_IF_LT: &str = include_str!("../../tests/fixtures/converging_merge_if_lt_mir.json");
const MERGE_IF_GT: &str = include_str!("../../tests/fixtures/converging_merge_if_gt_mir.json");
const MERGE_INSIDE: &str = include_str!("../../tests/fixtures/converging_merge_inside_mir.json");

/// The blocks that carry the converging `lo < s.len()` fact, sorted.
fn lo_bound_blocks(func: &VerifiableFunction) -> Vec<usize> {
    let mut out: Vec<usize> = build_converging_pointer_facts(func)
        .into_iter()
        .filter(|(_, fs)| {
            fs.iter()
                .any(|f| format!("{f:?}") == "Lt(Var(\"lo\", Int), Var(\"s__slice_len\", Int))")
        })
        .map(|(b, _)| b.0)
        .collect();
    out.sort_unstable();
    out
}

// ------------------------------------------------------------------ WINS

#[test]
fn two_pointer_reverse_decrement_is_certified_by_its_relational_guard() {
    // `while lo < hi { hi -= 1; s[lo] <-> s[hi]; lo += 1 }`, `lo: usize`. BEFORE:
    // no fact (only a constant guard certified), so `s[hi]` was refuted with
    // `hi = 2 > s.len() = 1` at the loop head — a state the program cannot reach.
    let func = load(TPR);
    assert_eq!(downward(&func), vec![lt_len("_8.0")]);
}

#[test]
fn relational_guard_is_k_zero_on_its_own_block() {
    // bb1: `_6 = copy lo; _7 = copy hi; _5 = Lt(move _6, move _7); switchInt(_5)`.
    let func = load(TPR);
    assert_eq!(
        downward_guards(&func, 3),
        vec![DownwardGuard { k: 0, block: 1, true_target: BlockId(2) }]
    );
}

#[test]
fn relational_guard_over_a_parameter_floor_certifies() {
    // `zero_down_to(s, lo)`: `while lo < hi { hi -= 1; s[hi] = 0 }`, `lo` a `usize`
    // PARAMETER read directly by the comparison.
    let func = load(REV_DOWN);
    assert_eq!(downward(&func), vec![lt_len("_7.0")]);
}

#[test]
fn gt_spelled_two_pointer_gets_the_decrement_and_converging_facts() {
    // `while hi > lo`: `Gt(hi, lo)` is `Lt(lo, hi)`. BEFORE: neither builder read
    // the `Gt` spelling, and three rows failed (both `s[lo]` and one `s[hi]`).
    let func = load(TPR_GT);
    assert_eq!(downward(&func), vec![lt_len("_8.0")]);
    let conv = converging(&func);
    assert!(
        conv.iter().any(|f| f.ends_with("Lt(Var(\"lo\", Int), Var(\"s__slice_len\", Int))")),
        "the `hi > lo` loop body must carry `lo < s.len()`: {conv:?}"
    );
}

#[test]
fn swap_two_pointer_decrement_is_certified() {
    // `s.swap(lo, hi)` is a call whose destination is `()`: not a write of `hi`.
    let func = load(TPR_SWAP);
    assert_eq!(downward(&func), vec![lt_len("_8.0")]);
}

#[test]
fn constant_guard_twin_keeps_its_fact_and_every_guard_is_a_candidate() {
    // `while lo < hi && hi > 0` — it proved 6/6 before; both guards certify now,
    // and neither shadows the other.
    let func = load(TPR_CONST);
    assert_eq!(downward(&func), vec![lt_len("_10.0")]);
    let guards = downward_guards(&func, 3);
    assert_eq!(guards.len(), 2, "{guards:?}");
    assert!(guards.iter().all(|g| g.k == 0), "{guards:?}");
}

#[test]
fn two_pointer_converging_facts_survive_the_freshness_rule() {
    // The comparison and the `lo` read are in the guard block: the per-block
    // `lo < s.len()` / `lo >= 0` facts are unchanged.
    let conv = converging(&load(TPR));
    assert!(
        conv.iter().any(|f| f.ends_with("Lt(Var(\"lo\", Int), Var(\"s__slice_len\", Int))")),
        "{conv:?}"
    );
    assert!(conv.iter().any(|f| f.ends_with("Ge(Var(\"lo\", Int), Int(0))")), "{conv:?}");
}

// ------------------------------------------------------- TWINS (stay closed)

#[test]
fn le_guard_certifies_nothing() {
    // `while lo <= hi { hi -= 1; .. }` underflows at `lo == hi == 0`.
    let func = load(MUT_LE);
    assert!(downward_guards(&func, 3).is_empty());
    assert!(downward(&func).is_empty(), "{:?}", downward(&func));
}

#[test]
fn late_decrement_fact_is_true_of_its_own_result_only() {
    // `while lo < hi { .. s[hi] ..; hi -= 1; lo += 1 }`. The guard DOES certify
    // the decrement (hi >= 1 there), so `_26.0 < s.len()` is a theorem and is
    // emitted. It says nothing about the OUT-OF-BOUNDS reads: those index the
    // loop-head `hi` (`_14`, `_22` copy `hi` before the decrement), which can be
    // `s.len()`, so the function still refutes end to end (the `mut_late`
    // revision of the ui fixture and `mutant/two_pointer_late_decrement.rs`).
    let func = load(MUT_LATE);
    assert_eq!(downward(&func), vec![lt_len("_26.0")]);
}

#[test]
fn stride_two_under_relational_guard_gets_nothing() {
    // `lo < hi` gives `hi >= 1`, not `hi >= 2`: `hi -= 2` underflows at `hi == 1`.
    let func = load(REL_DEC2);
    assert_eq!(downward_guards(&func, 3).len(), 1, "the guard itself is recognised");
    assert!(downward(&func).is_empty(), "{:?}", downward(&func));
}

#[test]
fn second_decrement_under_relational_guard_inherits_nothing() {
    // `hi -= 1; hi -= 1;` under `lo < hi`: the second sees `hi - 1`, which can be 0.
    let func = load(REL_TWICE);
    assert_eq!(downward(&func), vec![lt_len("_7.0")]);
}

#[test]
fn second_decrement_under_constant_guard_inherits_nothing() {
    // `two_dec`: `while i > 0 { i -= 1; i -= 1; a[i] = 0 }`. BEFORE: both
    // decrements got `_t.0 < a.len()`; the second one's was false of a wrapped
    // result (its own `overflow:sub` row still refuted the function).
    let func = load(TWO_DEC);
    assert_eq!(downward(&func), vec!["Lt(Var(\"_6.0\", Int), Var(\"a__slice_len\", Int))"]);
}

#[test]
fn second_decrement_inherits_no_lower_bound() {
    // DOWNWARD-GUARD-SECOND-DEC-1: `while i > 1 { i -= 1; i -= 1; a[i - 1] = 0 }`.
    // BEFORE: `_7.0 >= 1` was emitted for the SECOND decrement (it is 0 at
    // `i == 2`), discharging the `i - 1` underflow; certify exited 0 with 4/4 rows
    // proved and `ge_twice(&mut [0, 0])` panics "attempt to subtract with overflow".
    let func = load(GE_TWICE);
    assert_eq!(
        downward(&func),
        vec![
            "Lt(Var(\"_6.0\", Int), Var(\"a__slice_len\", Int))".to_string(),
            "Ge(Var(\"_6.0\", Int), Int(1))".to_string(),
        ]
    );
}

#[test]
fn stale_guard_boolean_certifies_nothing() {
    // DOWNWARD-GUARD-STALE-1: `if i != 0 { let c = i > 1; i -= 1; if c { i -= 1;
    // a[i - 1] = 0 } }`. The switch on `c` (bb2) reads a comparison made in bb1
    // BEFORE the first decrement. BEFORE: it was taken as `i > 1` at bb2 and the
    // second decrement got `_9.0 >= 1`; certify exited 0 and the function panics
    // at `a.len() == 2`.
    let func = load(STALE);
    assert!(downward_guards(&func, 2).is_empty(), "{:?}", downward_guards(&func, 2));
    assert!(downward(&func).is_empty(), "{:?}", downward(&func));
}

#[test]
fn decrement_before_the_first_guard_test_is_not_certified() {
    // `loop { i -= 1; a[i] = 0; if i > 0 { continue } else { break } }`: the guard
    // is recognised, but the decrement is reachable from the entry without it
    // (its first pass at `a.len() == 0` underflows).
    let func = load(DOWHILE);
    assert_eq!(downward_guards(&func, 2).len(), 1);
    assert!(downward(&func).is_empty(), "{:?}", downward(&func));
}

#[test]
fn signed_floor_is_not_a_relational_guard() {
    // `lo: i64` can be negative, so `lo < hi` does not give `hi >= 1`.
    let func = load(SIGNED_REL);
    assert!(downward_guards(&func, 3).is_empty(), "{:?}", downward_guards(&func, 3));
    assert!(downward(&func).is_empty(), "{:?}", downward(&func));
}

#[test]
fn parameter_cursor_is_not_a_downward_var() {
    // DOWNWARD-PARAM-CURSOR-1: `fn f(s, mut i: usize, c) { if c { i = s.len() }
    // while i > 0 { i -= 1; s[i] = 0 } }`. BEFORE: `_8.0 < s.len()` was emitted
    // although `i` keeps its caller value when `!c`; the `s[i]` row was proved.
    // The `!c` edge reaches the decrement without an init. (A parameter re-initialised
    // on EVERY path to its loop keeps its bound: `param_entry_gate_tests::
    // a_merged_decrement_tuple_loses_its_downward_bound`, `p15_induction`.)
    let func = load(PARAM_CURSOR);
    assert!(downward_induction_vars(&func).is_empty());
    assert!(downward(&func).is_empty(), "{:?}", downward(&func));
}

#[test]
fn stale_converging_guard_emits_no_lo_bound() {
    // CONVERGING-GUARD-STALE-1: `let c = lo < hi; lo += 1; tick(); if c { hi -= 1;
    // s[lo] = 0 }`. BEFORE: bb5..bb7 carried `lo < s.len()` of the INCREMENTED
    // `lo`; certify exited 0 with 3/3 kernel-certified and `conv_stale3(&mut [0])`
    // indexes `s[1]`.
    let func = load(CONV_STALE);
    assert!(converging(&func).is_empty(), "{:?}", converging(&func));
}

// --------------------------------------- CONVERGING-MERGE-1 (2026-10-10)
//
// `build_converging_pointer_facts` gave `lo < s.len()` to every block reachable from
// the guard's TRUE target (avoiding `lo` writes and the header), including blocks
// the FALSE edge also reaches. Each function below indexes `s[lo]` at such a block
// and panics; on the stage 1 of `5ccf66a518`, under the falsification gate's flags,
// certify proved and kernel-certified every row of each (c1 4/4, c2 4/4, c3 3/3,
// c4 3/3). The fact must now stop at the merge, and stay on the true arm.

#[test]
fn converging_fact_stops_at_an_if_merge() {
    // c3 `if lo < hi { hi -= 1; s[hi] = 0 } s[lo] = 1` and c4 (`hi > lo`), `lo` a
    // parameter. bb0: `_5 = Lt(lo, hi)` (c4: `Gt(hi, lo)`), `switchInt [0 -> bb4],
    // otherwise -> bb1`; bb1 -> bb2 -> bb3 -> bb4, and bb4 holds the `s[lo]`
    // BoundsCheck. BEFORE: bb1..bb5. `c3(&mut [0], 5)` indexes `s[5]`.
    for (name, fixture) in [("c3", MERGE_IF_LT), ("c4", MERGE_IF_GT)] {
        let func = load(fixture);
        assert_eq!(lo_bound_blocks(&func), vec![1, 2, 3], "{name}: {:?}", converging(&func));
    }
}

#[test]
fn converging_fact_stops_at_a_loop_exit_a_break_shares() {
    // c1 `while lo < hi { hi -= 1; if s[hi] == 0 { break } lo += 1 } s[lo] = 1` and
    // c2 (`hi > lo`). bb1 is the guard (`[0 -> bb7], otherwise -> bb2`); bb4's
    // `break` also goes to bb7, which holds the `s[lo]` BoundsCheck. BEFORE: bb2..bb5,
    // bb7, bb8. `c1(&mut [7])` and `c2(&mut [7])` index `s[1]`, `c1(&mut [])` `s[0]`.
    for (name, fixture) in [("c1", MERGE_BREAK_LT), ("c2", MERGE_BREAK_GT)] {
        let func = load(fixture);
        assert_eq!(lo_bound_blocks(&func), vec![2, 3, 4, 5], "{name}: {:?}", converging(&func));
    }
}

#[test]
fn converging_fact_holds_on_the_true_arm() {
    // The control: `if hi > lo { hi -= 1; s[hi] = 0; s[lo] = 1 }`. bb3 (the `s[lo]`
    // BoundsCheck) is reached only through the true edge and keeps its fact; only the
    // return block bb5, which the false edge reaches, loses it (BEFORE: bb1..bb5).
    let func = load(MERGE_INSIDE);
    assert_eq!(lo_bound_blocks(&func), vec![1, 2, 3, 4], "{:?}", converging(&func));
}

#[test]
fn converging_fact_refuses_a_degenerate_switch() {
    // c4 with its false arm pointed at the true target: both edges reach bb1, so the
    // edge says nothing and no block gets the fact.
    let mut func = load(MERGE_IF_GT);
    let Terminator::SwitchInt { targets, otherwise, .. } = &mut func.body.blocks[0].terminator
    else {
        panic!("bb0 must end in the guard switch");
    };
    targets[0].1 = *otherwise;
    assert!(lo_bound_blocks(&func).is_empty(), "{:?}", converging(&func));
}
