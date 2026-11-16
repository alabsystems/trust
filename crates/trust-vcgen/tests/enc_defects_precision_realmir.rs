// Trust (2026-09-26): the vcgen halves of the ENC-DEFECTS precision fixes (13a,
// 13b), pinned on REAL MIR (`-Ztrust-dump=mir`, paths sanitized to
// `enc_defects/`). Each "proved" program refuted on the default lane at stage-1
// `a4b52d0f3` although it cannot panic; each "refuted" program is its unsound
// neighbour and MUST keep its refutation. The end-to-end pins are the revisions of
// `tests/ui/trust/enc_defects_precision.rs`. These are dumps, i.e. optimized MIR;
// they pin the formulas the lanes now mint, not the compiler path.
//
// Sources (one fixture per function):
//   enc13a.rs  local_ok / local_swapped / local_reassigned / signed_ok /
//              signed_swapped / Elevator::tick (d3/p14) / Elevator::tick_param /
//              Elevator::tick_param_swapped / Elevator::tick_overwritten /
//              local_struct
//   enc13x.rs  enum_mut_helper / enum_swap / Q::escaped_then_shared /
//              Q::field_reborrow
//   enc13b.rs  Quota::consume_moved (d5/var/v13a) / consume_moved_guarded /
//              consume_shared /
//              consume_mut_call / Cq::consume_cell
//   enc13m.rs  Machine::step / Machine::step_forced (2026-09-28, dumped by the
//              rebased stage 1 `fed2ab567`; the `Machine` of the ui fixture's
//              havoc revisions, verbatim)
//   enc13d.rs  neg_tag_param / pos_tag_param (2026-09-28, dumped by stage 1
//              `5c4528067`; the independent review's rd01 and its non-negative
//              twin — the discriminant INTERVAL producer 13a's invariant needs)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
use trust_types::{
    BinOp, CounterexampleValue, VcKind, VerifiableFunction, VerificationCondition,
    VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

fn load(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

/// Every `ArithmeticOverflow { op }` row of `func` with its verdict from the SAME
/// in-process ay backend the default lane uses.
fn overflow_rows(func: &VerifiableFunction, op: BinOp) -> Vec<VerificationResult> {
    let r = router();
    let vcs: Vec<VerificationCondition> = trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(&vc.kind, VcKind::ArithmeticOverflow { op: o, .. } if *o == op))
        .collect();
    assert!(!vcs.is_empty(), "{}: no {op:?} overflow row minted (vacuity guard)", func.name);
    vcs.iter().map(|vc| r.verify_one(vc)).collect()
}

fn all_proved(results: &[VerificationResult]) -> bool {
    results.iter().all(|r| matches!(r, VerificationResult::Proved { .. }))
}

/// A refutation whose witness assigns `name` (SSA suffix stripped) the integer
/// `value` — pinning the VALUE, so "still refuted" is a claim about the real bug.
fn refuted_at(results: &[VerificationResult], name: &str, value: i128) -> bool {
    results.iter().any(|result| {
        let VerificationResult::Failed { counterexample: Some(ce), .. } = result else {
            return false;
        };
        ce.assignments.iter().any(|(n, v)| {
            n.split('#').next() == Some(name)
                && matches!(v, CounterexampleValue::Int(x) if *x == value)
        })
    })
}

// ---- 13a: a fieldless enum's value is its discriminant ----

#[test]
fn a_local_fieldless_enum_ties_the_match_to_the_arm_that_built_it() {
    // `let m = if x < 255 { Up } else { Idle }; match m { Up => x + 1, .. }` —
    // refuted at HEAD with `_4 = 1, __trust_mir__discr_m = 0, x = 255`.
    let rows = overflow_rows(&load(include_str!("fixtures/enc_local_ok_mir.json")), BinOp::Add);
    assert!(all_proved(&rows), "the Up arm is only built under x < 255: {rows:?}");
}

#[test]
fn explicit_negative_discriminants_use_the_decoded_tag() {
    // `#[repr(i8)] enum S { Neg = -1, Pos = 5 }`: the switch label for `Neg` is
    // the bit pattern 255, decoded to -1 at the read's type; the construction pins
    // the DECODED tag -1. A raw-vs-decoded mismatch would make the `Neg` arm
    // infeasible, which is a false proof — `signed_swapped` below is its control.
    let rows = overflow_rows(&load(include_str!("fixtures/enc_signed_ok_mir.json")), BinOp::Add);
    assert!(all_proved(&rows), "{rows:?}");
}

#[test]
fn the_unsound_neighbours_keep_their_refutations_at_the_real_witness() {
    for (name, json) in [
        ("local_swapped", include_str!("fixtures/enc_local_swapped_mir.json")),
        ("local_reassigned", include_str!("fixtures/enc_local_reassigned_mir.json")),
        ("signed_swapped", include_str!("fixtures/enc_signed_swapped_mir.json")),
    ] {
        let rows = overflow_rows(&load(json), BinOp::Add);
        assert!(refuted_at(&rows, "x", 255), "{name}: `x + 1` at x == 255 is real: {rows:?}");
    }
}

/// The production split of `func`'s `Sub` overflow rows: how many the interval
/// lane discharged, and the in-process verdict on each one it handed on (with the
/// abstract state conjoined, exactly as the compiler routes it).
fn production_sub_rows(func: &VerifiableFunction) -> (usize, Vec<VerificationResult>) {
    let is_sub = |vc: &VerificationCondition| {
        matches!(&vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. })
    };
    let (solver, discharged) = trust_vcgen::generate_vcs_with_discharge(func);
    let r = router();
    let routed: Vec<VerificationResult> =
        solver.iter().filter(|vc| is_sub(vc)).map(|vc| r.verify_one(vc)).collect();
    (discharged.iter().filter(|(vc, _)| is_sub(vc)).count(), routed)
}

#[test]
fn a_discriminant_read_is_bounded_by_its_tag_hull_not_by_zero() {
    // The review's rd01: `#[repr(i8)] enum S { Neg = -1, Pos = 5 }`,
    // `fn f(s: S) -> i8 { let d = s as i8; d - 127 - 1 }`. The read sits in the
    // ENTRY block, so the abstract interpreter's `[0, i128::MAX]` for EVERY
    // discriminant survived into `merged_interval_environment`, and the second
    // `Sub` was proved — rc=0, and `f(S::Neg)` panics. 13a's invariant ("integer
    // model = decoded tag") requires this producer to agree: the read is now the
    // tag hull `[-1, 5]`. The first `Sub` (`d - 127 >= -128`) still discharges; the
    // second is handed on and refuted at `s = -1`.
    let (discharged, routed) =
        production_sub_rows(&load(include_str!("fixtures/enc_neg_tag_param_mir.json")));
    assert_eq!(discharged + routed.len(), 2, "vacuity guard: both `Sub` rows are minted");
    assert!(refuted_at(&routed, "s", -1), "`S::Neg as i8 - 127 - 1` overflows: {routed:?}");

    // CONTROL: every tag non-negative (`T { Zero = 0, Five = 5 }`), the same body —
    // the hull `[0, 5]` proves both rows.
    let (discharged, routed) =
        production_sub_rows(&load(include_str!("fixtures/enc_pos_tag_param_mir.json")));
    assert_eq!(discharged + routed.len(), 2, "vacuity guard: both `Sub` rows are minted");
    assert!(all_proved(&routed), "a non-negative hull keeps the proof: {routed:?}");
}

#[test]
fn a_fieldless_enum_field_behind_mut_self_ties_the_match_to_its_assignment() {
    // `self.motion = if floor < 255 { Up } else { Idle }; match self.motion { Up =>
    // floor + 1, .. }` — the projected place `self*.2` is linked to the value that
    // was stored into it and to the `Discriminant` read of it.
    let rows = overflow_rows(&load(include_str!("fixtures/enc_tick_param_mir.json")), BinOp::Add);
    assert!(all_proved(&rows), "{rows:?}");
    let rows =
        overflow_rows(&load(include_str!("fixtures/enc_tick_param_swapped_mir.json")), BinOp::Add);
    assert!(refuted_at(&rows, "floor", 255), "{rows:?}");
}

#[test]
fn a_fieldless_enum_field_of_a_local_struct_is_linked() {
    let rows = overflow_rows(&load(include_str!("fixtures/enc_local_struct_mir.json")), BinOp::Add);
    assert!(all_proved(&rows), "{rows:?}");
}

#[test]
fn d3_p14_now_carries_the_link_and_is_blocked_elsewhere() {
    // d3/p14 verbatim. At HEAD: `__trust_mir__discr_self*.2 = 0` beside a read of
    // 1 — nothing tied the read to the stored value. The link is now in the
    // formula: `_10 == self*.2#.. == _5#..`, and `_5#..` is the merged value of the
    // three constructing arms. The rows are still refuted, for two reasons outside
    // this fix (reported, not fixed): the store `self.motion = ..` through the
    // `&mut self` PARAMETER is an opaque deref store, whose whole-function havoc
    // drops the `_7 == self*.0` guard read established before it; and the
    // `else if` operand `_9 == self*.0` lives in a branch-local block whose defs do
    // not survive the join.
    let func = load(include_str!("fixtures/enc_tick_mir.json"));
    let add = trust_vcgen::generate_vcs(&func)
        .into_iter()
        .find(|vc| matches!(&vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .expect("the `floor += 1` row");
    let text = add.formula.to_smtlib();
    assert!(
        text.contains("(= _10 |self*.2#"),
        "the discriminant read is tied to the field: {text}"
    );
    assert!(
        text.contains("(= |self*.2#s6_0| |_5#"),
        "the field is tied to the stored value: {text}"
    );
    assert!(text.contains("(= |_5#s2_0_s4_0_s5_0| 1)"), "the Up arm stores tag 1: {text}");
}

#[test]
fn a_field_overwritten_after_the_guarded_build_keeps_its_refutation() {
    let rows =
        overflow_rows(&load(include_str!("fixtures/enc_tick_overwritten_mir.json")), BinOp::Add);
    assert!(
        rows.iter().any(|r| matches!(r, VerificationResult::Failed { .. })),
        "`self.motion = Up` unconditionally before the match: `floor + 1` at 255 is real: \
         {rows:?}"
    );
}

// ---- 13b: calls that cannot write the `&mut self` fields ----

#[test]
fn a_std_call_over_moved_scalars_keeps_the_mut_self_field_facts() {
    // v13d's guard, then `let _r = self.limit.saturating_sub(self.used);` — the
    // call's arguments are MOVED `u32` temporaries. At HEAD the call havocked
    // `self` and both rows after it refuted.
    let func = load(include_str!("fixtures/enc_consume_moved_guarded_mir.json"));
    let add = overflow_rows(&func, BinOp::Add);
    let sub = overflow_rows(&func, BinOp::Sub);
    assert!(all_proved(&add), "{add:?}");
    assert!(all_proved(&sub), "{sub:?}");
}

#[test]
fn v13a_is_no_longer_refuted_on_a_havocked_field() {
    // d5/var/v13a: `saturating_sub(move _5, move _6)` havocked `self` at HEAD and
    // the row was REFUTED at `self*.0#e_s2_t = 4294967295`. With the havoc gone
    // the field read after the call is the SAME `self*.0` the guard constrained
    // (no version token), so no refutation remains. The in-process ay answers
    // this particular query `Unknown` (`incomplete self-check-rejected` on the
    // saturating-sub case split), which is why this pins "not refuted, and the
    // name is unversioned" rather than "proved".
    let func = load(include_str!("fixtures/enc_consume_moved_mir.json"));
    let rows = overflow_rows(&func, BinOp::Add);
    assert!(!rows.iter().any(|r| matches!(r, VerificationResult::Failed { .. })), "{rows:?}");
    let add = trust_vcgen::generate_vcs(&func)
        .into_iter()
        .find(|vc| matches!(&vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .expect("the `+=` row");
    let text = add.formula.to_smtlib();
    // Trust (2026-09-30, vac Phase 0): the stale-read seal spells an entry-valued read
    // `self*.0#e` (the ENTRY sentinel, not a version the call minted), so the only
    // `#` spelling allowed is exactly that one.
    assert!(
        text.match_indices("self*.0#").all(|(i, _)| text[i..].starts_with("self*.0#e|")),
        "the field must not be re-versioned by the call: {text}"
    );
    assert!(text.contains("(= _6 self*.0)"), "the guard's read must reach the use: {text}");
}

#[test]
fn a_shared_reborrow_of_a_frozen_self_keeps_the_mut_self_field_facts() {
    // `let _r = self.remaining();` between the guard and `self.used += n`.
    let func = load(include_str!("fixtures/enc_consume_shared_mir.json"));
    let add = overflow_rows(&func, BinOp::Add);
    let sub = overflow_rows(&func, BinOp::Sub);
    assert!(all_proved(&add), "{add:?}");
    assert!(all_proved(&sub), "{sub:?}");
}

#[test]
fn a_mut_self_call_keeps_its_refutation() {
    // `self.bump()` really writes `used = u32::MAX`.
    let rows =
        overflow_rows(&load(include_str!("fixtures/enc_consume_mut_call_mir.json")), BinOp::Add);
    assert!(
        rows.iter().any(|r| matches!(r, VerificationResult::Failed { .. })),
        "consume_mut_call: the post-call field is not the guarded one: {rows:?}"
    );
}

#[test]
fn a_cell_beside_the_guarded_fields_does_not_unprotect_them() {
    // Salvage reconciliation (2026-09-28). `Cq { used: u32, limit: u32, c: Cell<u32> }`
    // with `let _r = self.peek()` (`self.c.get()`) between the guard and
    // `self.used += n`. 13b refuses this call (`Cq` is not `Freeze`; pinned at the
    // gate in `generate::enc_defects_13b_gate_tests`), and this row used to pin
    // that refusal as a KEPT refutation. It is not an unsound neighbour: `used`
    // lies outside every `UnsafeCell`, so the program cannot panic, and the TRUST-10
    // sibling (`callee_write_set::refine_shared_reborrow_havoc`, a7b7f9bbf1), which
    // reads the protector premise per byte, now proves it — it havocs the cell and
    // spares the two scalars. The unsound neighbour, where the guarded counter IS
    // the cell and the `&self` call writes it, is `CellQuota::consume_cell` in the
    // `havoc_bug` revision of `tests/ui/trust/enc_defects_precision.rs`.
    let rows = overflow_rows(&load(include_str!("fixtures/enc_consume_cell_mir.json")), BinOp::Add);
    assert!(all_proved(&rows), "consume_cell: {rows:?}");
}

#[test]
fn a_fieldless_enum_pointee_keeps_its_stored_state_across_a_shared_call() {
    // 13b's own coverage since the 2026-09-28 reconciliation made it the fallback
    // of the TRUST-10 sibling: `Machine { phase: Phase }` has no scalar leaf for the
    // sibling to spare, so it is 13b's whole-pointee narrowing that keeps
    // `self.phase` — stored under `x < 255` — tied across `self.is_busy()`, and 13a
    // that ties the match to it.
    let rows = overflow_rows(&load(include_str!("fixtures/enc_machine_step_mir.json")), BinOp::Add);
    assert!(all_proved(&rows), "Machine::step: {rows:?}");
    // The `&mut self` twin really stores `Busy` between the build and the match.
    let rows =
        overflow_rows(&load(include_str!("fixtures/enc_machine_step_forced_mir.json")), BinOp::Add);
    assert!(refuted_at(&rows, "x", 255), "Machine::step_forced: {rows:?}");
}

// ---- the refusal paths of both fixes, on real MIR (enc13x.rs) ----

#[test]
fn an_enum_rewritten_through_a_mut_borrow_keeps_its_refutation() {
    // `flip(&mut m)` and `mem::swap(&mut a, &mut b)` really set `Up` after the
    // guarded build; the call havoc re-versions the enum, and the refutation
    // stands at the real witness.
    for (name, json) in [
        ("enum_mut_helper", include_str!("fixtures/enc_enum_mut_helper_mir.json")),
        ("enum_swap", include_str!("fixtures/enc_enum_swap_mir.json")),
    ] {
        let rows = overflow_rows(&load(json), BinOp::Add);
        assert!(refuted_at(&rows, "x", 255), "{name}: {rows:?}");
    }
}

#[test]
fn an_escaped_root_or_a_field_reborrow_is_not_narrowed() {
    // `stash(&mut self.used)` before the `&self` call: a mutable child of the
    // pointee escaped, so the call keeps its full havoc. `look(&self.limit)`
    // protects only `limit`, so `used` is havocked as before.
    for (name, json) in [
        ("escaped_then_shared", include_str!("fixtures/enc_escaped_then_shared_mir.json")),
        ("field_reborrow", include_str!("fixtures/enc_field_reborrow_mir.json")),
    ] {
        let rows = overflow_rows(&load(json), BinOp::Add);
        assert!(
            rows.iter().any(|r| matches!(r, VerificationResult::Failed { .. })),
            "{name}: the havoc must stay: {rows:?}"
        );
    }
}
