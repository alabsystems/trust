//! REAL-MIR pins for TRUST-KI-1015-1, the aterm-digest top-up shape: a correct
//! `Sha256::update` was reported FAILED because a call that can write no memory of
//! `*self` still re-versioned `self.buf_len`.
//!
//! # The defect (measured 2026-10-15)
//!
//! aterm-digest `Sha256::update` (`sha256.rs:103-106` at aterm `848d791bd`) tops up a
//! partial block:
//!
//! ```text
//! if self.buf_len > 0 {
//!     let take = (BLOCK_LEN - self.buf_len).min(data.len());
//!     self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
//!     self.buf_len += take;
//! ```
//!
//! `BLOCK_LEN - self.buf_len` passed its overflow check, so `buf_len <= 64`, and
//! `take <= 64 - buf_len`: the slice is in `buf` and `buf_len + take` cannot overflow.
//! On main the `[slice]` row of the slice (`105:20`) and the `[overflow:add]` row of
//! `self.buf_len + take` (`105:35`, with its `unix_hardened` twin) were FAILED by
//! `ay-in-process`, with `buf_len` read as 1 before the `min` call and as 65 or
//! `u64::MAX` after it (`self*.2#e_s1_t` vs `self*.2#e_s4_t`).
//!
//! `<usize as Ord>::min` takes two `usize` values. It is the dest-only call arm of
//! `path_defs::terminator_def_names_structured`, which havocs the whole-function list
//! except the names of a protected `&mut` parameter whose pointer NEVER leaves the
//! body (rule (b), `protected_private_mut_param`). `self` leaves it, but only AFTER the
//! call (`&mut self.buf` into `IndexMut::index_mut`), so rule (b) refused it and the
//! `min` call re-versioned `self.buf_len`. Rule (b)'s premise is about the call: no
//! pointer derived from the protected parameter can be held by anyone but this body
//! WHILE THE CALL RUNS, and none is until an escape site has run.
//! `path_defs::escape_havoc_at` asks it there (ESCAPE-HAVOC-FLOW-1).
//!
//! The `[slice]` row was Unknown (`slice-range-bounds-unresolved`) on the channel
//! `b58a105dde` and became FAILED on main through 491bc3c273 ("a slice range bound set
//! on two paths is read at its indexing call", merged by 98b7fad77d): from then on the
//! range's bounds were read at the `index_mut` call, so the obligation was stated and
//! the decorrelation above refuted it.
//!
//! # Fixtures
//!
//! `tests/fixtures/digest_update_topup_<fn>_mir.json` are the compiler's own extraction
//! of [`tests/data/digest_update_topup.rs`], captured with the channel `trustc`
//! (`b58a105dde`):
//!
//! ```text
//! trustc --crate-type lib --edition 2024 --emit=metadata -C debuginfo=2 \
//!        -Ztrust-verify-level=2 -Ztrust-policy=advisory -Ztrust-verify-profile=unix_hardened \
//!        -Ztrust-dump=mir:<dir> digest_update_topup.rs
//! ```
//!
//! Only the `span.file` fields were rewritten to the repo-relative source path. Every
//! wrong program panics natively at the row it pins, in debug and in release (run with
//! the channel's `targo --unverified test` on a copy of the source with its test
//! module). Under Miri (the channel's `targo-miri`), each one's panic is a defined
//! execution under Tree Borrows, and under Stacked Borrows as well, except
//! `reach_sibling_field`. The `premise_*` programs panic only in a debug build, and Miri
//! reports UB under both models.
//!
//! # Falsification control (2026-10-15, crate level)
//!
//! On main `9fa33ffd06`, whose call arm asks the flow-insensitive rule (b),
//! `the_top_up_rows_prove`, `room_past_the_end_stays_refuted` (its correct add) and
//! `a_value_only_call_in_a_loop_before_the_escape_keeps_the_guard` go red, and every
//! refutation of a panicking row stays green. With every rule-(b)-shaped
//! parameter exempt whatever its escape sites, the two `a_pointer_parked_*` tests go
//! red: the stash programs' rows PROVE although they panic. With escape reach taken in
//! TEXT order (a site reaches the blocks after it in `func.body.blocks`, no back edge),
//! `a_pointer_parked_one_loop_round_earlier_stays_refuted` goes red (a false proof), and
//! so does the correct loop (rustc places the loop's exit block, where the escape is,
//! before the loop body).
//!
//! The adversarial review's pins were measured the same way, on main `7f3690ed73`:
//! - On main, and with the fix off, the three cross-invocation `premise_*` tests go red,
//!   because those rows are FAILED there.
//!   `a_pointer_parked_before_the_entry_is_proved_by_the_premise` stays green, because
//!   main's rule (b) PROVES that row.
//! - With reach ignored, all five `reach_*` tests go red.
//! - With text order, `an_escape_after_a_loop_break_reaches_the_next_round` and
//!   `an_escape_in_an_inner_loop_reaches_the_outer_rounds_call` go red.
#[path = "support/realmir_rows.rs"]
mod realmir_rows;

use realmir_rows::{PRIMARY_ADD, PRIMARY_SUB, Row, TWIN_ADD, TWIN_SUB, Verdict, expect};

const SLICE: &str = "SliceBoundsCheck";
const BOUNDS: &str = "IndexOutOfBounds";
const TWIN_BOUNDS: &str = "mir_assert::BoundsCheck";

fn rows(name: &str) -> Vec<Row> {
    realmir_rows::rows("digest_update_topup_", name, &[])
}

/// The one row at `line:col` whose kind contains `needle` has `want`.
fn expect_col(rows: &[Row], line: u32, col: u32, needle: &str, want: Verdict, why: &str) {
    let hits: Vec<&Row> = realmir_rows::at(rows, line, needle)
        .into_iter()
        .filter(|r| r.vc.location.col_start == col)
        .collect();
    assert_eq!(
        hits.len(),
        1,
        "{line}:{col}: expected one `{needle}` row; all rows: {:#?}",
        rows.iter()
            .map(|r| (r.line, r.vc.location.col_start, &r.kind, r.verdict))
            .collect::<Vec<_>>()
    );
    assert_eq!(
        hits[0].verdict, want,
        "{line}:{col} `{needle}`: {why}\nresult: {}\nformula: {:?}",
        hits[0].result, hits[0].vc.formula
    );
}

/// The correct top-up: the slice and the add that `min` sat between prove, on both
/// twins.
#[test]
fn the_top_up_rows_prove() {
    let rows = rows("top_up");
    expect_col(&rows, 20, 20, SLICE, Verdict::Proved, "buf[buf_len..buf_len + take] is in buf");
    expect_col(&rows, 20, 77, SLICE, Verdict::Proved, "data[..take], take <= data.len()");
    expect(&rows, 20, PRIMARY_ADD, 1, Verdict::Proved, "buf_len <= 64 and take <= 64 - buf_len");
    expect(&rows, 20, TWIN_ADD, 1, Verdict::Proved, "the hardened twin of the same add");
}

/// `BLOCK_LEN - self.buf_len` is a real refutation of this program: `buf_len` is a public
/// field, and `buf_len = 65` panics. (In aterm-digest the field is private and the
/// row is the modular refutation TRUST-KI-1015-1 lists apart.)
#[test]
fn the_room_subtraction_stays_refuted() {
    let rows = rows("top_up");
    expect(&rows, 19, PRIMARY_SUB, 1, Verdict::Failed, "buf_len = 65 overflows 64 - buf_len");
    expect(&rows, 19, TWIN_SUB, 1, Verdict::Failed, "its hardened twin");
}

/// OPEN (TRUST-KI-1015-1, the std-callee half): `self.buf_len += take` reads `buf_len`
/// after `index_mut(&mut self.buf, ..)` and `copy_from_slice`, which receive a `&mut`
/// into `*self` and are havocked in full; that they leave `buf_len` alone is a fact of
/// std's code, not of the aliasing model (under Tree Borrows a pointer derived from
/// `&mut self.buf` may reach `buf_len`). Pinned so a fix of that half updates the
/// hazard with this test.
#[test]
fn the_add_after_the_std_copy_is_still_refuted_open() {
    let rows = rows("top_up");
    expect(&rows, 21, PRIMARY_ADD, 1, Verdict::Failed, "OPEN: read after copy_from_slice");
    expect(&rows, 21, TWIN_ADD, 1, Verdict::Failed, "OPEN: its hardened twin");
}

/// One byte of room too many: `buf[1..65]` panics. The add beside it is correct
/// (`buf_len + take <= 65`) and now proves.
#[test]
fn room_past_the_end_stays_refuted() {
    let rows = rows("top_up_room_past_end");
    expect_col(&rows, 31, 20, SLICE, Verdict::Failed, "buf_len = 1, data.len() = 64: buf[1..65]");
    expect(&rows, 31, PRIMARY_ADD, 1, Verdict::Proved, "buf_len <= 65 and take <= 65 - buf_len");
    expect(&rows, 31, TWIN_ADD, 1, Verdict::Proved, "its hardened twin");
}

/// `max` for `min`: `buf[1..101]` and `data[..63]` of an empty `data` both panic.
#[test]
fn max_for_min_stays_refuted() {
    let rows = rows("top_up_max");
    expect_col(&rows, 42, 20, SLICE, Verdict::Failed, "buf_len = 1, data.len() = 100: buf[1..101]");
    expect_col(&rows, 42, 77, SLICE, Verdict::Failed, "buf_len = 1, data empty: data[..63]");
}

/// A callee handed `&mut self` writes `buf_len` between the room read and the slice:
/// `buf[64..65]` panics.
#[test]
fn a_callee_writing_through_mut_self_stays_refuted() {
    let rows = rows("top_up_callee_writes");
    expect_col(&rows, 61, 20, SLICE, Verdict::Failed, "fill_to_end sets buf_len = 64: buf[64..65]");
}

/// `take` wraps on an empty `data`: `buf_len + take` overflows.
#[test]
fn a_wrapped_take_stays_refuted() {
    let rows = rows("top_up_wrapping_take");
    expect(&rows, 73, PRIMARY_ADD, 1, Verdict::Failed, "take = usize::MAX");
    expect(&rows, 73, TWIN_ADD, 1, Verdict::Failed, "its hardened twin");
}

/// The channel rule (b) exists for: a raw child of `&mut self.buf_len` parked by an
/// EARLIER callee (`stash`) is written by the value-only `poke` between the room read
/// and the slice: `buf[64..65]` panics.
#[test]
fn a_pointer_parked_before_a_value_only_call_stays_refuted() {
    let rows = rows("top_up_stashed");
    expect_col(
        &rows,
        122,
        20,
        SLICE,
        Verdict::Failed,
        "poke writes buf_len = 64 through the stash",
    );
}

/// The fix in a loop: the guard `buf_len < 64` and the index `buf[buf_len]` sit around the
/// value-only `mix`, and `buf_len` escapes only after the loop, on no path back to `mix`.
/// Refuted on main (and on the channel `b58a105dde`).
#[test]
fn a_value_only_call_in_a_loop_before_the_escape_keeps_the_guard() {
    let rows = rows("mark_rounds");
    expect_col(&rows, 136, 16, BOUNDS, Verdict::Proved, "buf_len < 64 holds across mix(acc)");
    expect_col(&rows, 136, 16, TWIN_BOUNDS, Verdict::Proved, "its hardened twin");
}

/// The same loop with the escape INSIDE it, after the value-only `poke` in the text: round
/// 1 parks `&mut self.buf_len`, round 2's `poke` writes 64 through it after the guard, and
/// `buf[64]` panics. The escape reaches the call round the back edge.
#[test]
fn a_pointer_parked_one_loop_round_earlier_stays_refuted() {
    let rows = rows("mark_rounds_stashed");
    expect_col(&rows, 151, 16, BOUNDS, Verdict::Failed, "round 2's poke writes buf_len = 64");
    expect_col(&rows, 151, 16, TWIN_BOUNDS, Verdict::Failed, "its hardened twin");
}

/// The `[bounds]` row of `buf[buf_len]` at `line:col` and its hardened twin both have `want`.
fn expect_index(rows: &[Row], line: u32, col: u32, want: Verdict, why: &str) {
    expect_col(rows, line, col, BOUNDS, want, why);
    expect_col(rows, line, col, TWIN_BOUNDS, want, why);
}

// ESCAPE-HAVOC-FLOW-1's reach in real MIR, on the shapes its adversarial review found
// load-bearing (records digest-update-topup-review2). Each program panics natively at the
// pinned row in a DEFINED execution, debug and release alike. Each row stays FAILED only
// because an escape site of `self` reaches the value-only `poke` on some CFG path.

/// The escape on one arm of an `if`, joined before the value-only `poke`: `flag` parks
/// `&mut self.buf_len`, `poke` writes 64 after the guard, and `buf[64]` panics. With reach
/// ignored, this row PROVES.
#[test]
fn an_escape_on_one_arm_reaches_the_call_after_the_join() {
    let rows = rows("reach_join_if");
    expect_index(&rows, 174, 12, Verdict::Failed, "the `flag` arm parks buf_len before poke");
}

/// A `loop` whose `break` sits between the use and the escape: round 1 parks, and round 2's
/// `poke` writes 64 after the guard. With reach taken in text order, this row PROVES.
#[test]
fn an_escape_after_a_loop_break_reaches_the_next_round() {
    let rows = rows("reach_loop_break");
    expect_index(&rows, 188, 16, Verdict::Failed, "round 1 parks buf_len before round 2's poke");
}

/// The escape in an inner loop reaches the outer loop's next round. With reach taken in
/// text order, this row PROVES.
#[test]
fn an_escape_in_an_inner_loop_reaches_the_outer_rounds_call() {
    let rows = rows("reach_nested_loop");
    expect_index(&rows, 206, 16, Verdict::Failed, "the inner loop parks buf_len before round 2");
}

/// Recursion: the inner invocation parks a pointer derived from the outer `self` (the
/// recursive call's `&mut *self` is an escape site before `poke`), and the outer's `poke`
/// writes through it. That is a child write of the outer's own protected `self`, so the
/// execution is defined. With reach ignored, this row PROVES.
#[test]
fn a_pointer_parked_by_the_inner_frame_stays_refuted_in_the_outer() {
    let rows = rows("reach_rec_inner_frame");
    expect_index(&rows, 226, 12, Verdict::Failed, "the inner frame parked a child of this self");
}

/// The SIBLING field `&mut self.buf` is parked, and `poke_past_buf` writes `buf_len` through
/// it. That is defined under Tree Borrows and UB under Stacked Borrows. A fact of one model
/// alone is no premise. With reach ignored, this row PROVES.
#[test]
fn a_sibling_field_parked_before_the_call_stays_refuted() {
    let rows = rows("reach_sibling_field");
    expect_index(&rows, 275, 12, Verdict::Failed, "TB: &mut self.buf's pointer reaches buf_len");
}

// PROVED BY PREMISE: the boundary of rule (b) (docs/TCB.md, "Calls whose arguments grant no
// write"; DECISION_QUEUE ESCAPE-HAVOC-FLOW-1; KNOWN_HAZARDS TRUST-KI-1015-1). Each program below
// panics natively at the pinned row in a DEBUG build. Each panic needs a pointer that ANOTHER
// invocation created (an earlier call, the outer frame of a recursion, or the caller before the
// entry) to write `*self` while this invocation's protected `self` is live. That write is UB:
// - Under Stacked Borrows, the fresh `&mut` the caller or outer frame retags for this invocation
//   pops the parked pointer's item.
// - Under Tree Borrows, the write is a foreign write to a location of this invocation's
//   protected `self` that the guard read initialized.
// rustc relies on the same fact: in a release build, `noalias` lets LLVM fold the reload, and
// none of these programs panics (measured with the channel's `targo --unverified test
// --release`, overflow checks on). The rows are PROVED: on main, only
// `premise_before_entry`'s, because main's rule (b) asked for no escape site anywhere.
// These tests pin the boundary, not a goal. A change that makes one of these rows FAILED
// costs completeness, not soundness, and should update the hazard together with the test.
// A change that makes a `reach_*` or `*_stashed` row PROVED is a false proof.

/// PROVED BY PREMISE: correct within one invocation, because the escape comes after the use.
/// A SECOND call's `poke` writes 64 through the FIRST call's stash.
#[test]
fn a_pointer_parked_by_an_earlier_call_is_proved_by_the_premise() {
    let rows = rows("premise_next_call");
    expect_index(&rows, 301, 12, Verdict::Proved, "another invocation's pointer: UB (protector)");
}

/// PROVED BY PREMISE: the escape is on an early-return path, which reaches no call of this
/// invocation. A later call's `poke` writes through it.
#[test]
fn a_pointer_parked_on_an_earlier_calls_return_path_is_proved_by_the_premise() {
    let rows = rows("premise_early_return");
    expect_index(&rows, 318, 12, Verdict::Proved, "another invocation's pointer: UB (protector)");
}

/// PROVED BY PREMISE: the outer frame parks, then recurses. The inner frame's `poke` writes
/// through the outer's stash, which is a SIBLING of the inner's protected `self`, not a child.
#[test]
fn a_pointer_parked_by_the_outer_frame_is_proved_by_the_premise() {
    let rows = rows("premise_outer_frame");
    expect_index(&rows, 334, 12, Verdict::Proved, "the outer frame's pointer: UB (protector)");
}

/// PROVED BY PREMISE, on main as well: `self` has no escape site at all (main's rule (b)). The
/// CALLER parks `&mut acc.buf_len` before the call. ESCAPE-HAVOC-FLOW-1 extends to another
/// invocation the premise that main already applies here.
#[test]
fn a_pointer_parked_before_the_entry_is_proved_by_the_premise() {
    let rows = rows("premise_before_entry");
    expect_index(&rows, 346, 12, Verdict::Proved, "a pre-entry pointer: UB under the protector");
}
