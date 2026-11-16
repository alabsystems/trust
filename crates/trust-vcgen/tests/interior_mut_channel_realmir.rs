//! INTERIOR-MUT-CHANNEL-1 (G2 of the verifier-gaps design): the `UnsafeCell` bytes a
//! SHARED reference or borrow reaches are a write channel, at the verdict level.
//!
//! rustc keeps `Cell::new`/`get`/`set` as calls in the verify MIR even at
//! `-C opt-level=3`, so on real user MIR a cell's value never reaches a formula as a
//! place read through the cell API, and the false proofs below are latent there. (A
//! union read through its plain field beside a cell does reach one with no edit:
//! `interior_mut_channel_union_realmir.rs`.) They are reachable at the vcgen API, and
//! on any body that reads a cell's bytes as a place: each `*_cell*` fixture is
//! a real stage-1 dump with exactly that edit (the hand edit of the design's Appendix C,
//! scripted in `tests/data/interior_mut_channel_edit.py`), and its native twin (the
//! comments at the end of `tests/data/interior_mut_channel_bases.rs`) panics at `-O0`
//! and `-O3`. Before the rule every `must_refute_*` row here was PROVED, and the
//! cell-holder rows were kernel-certified.
//!
//! # Fixtures
//!
//! `tests/fixtures/interior_mut_channel_*_mir.json` are the compiler's own extraction
//! of the functions in `tests/data/interior_mut_channel_bases.rs`, captured with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -C opt-level=3 -Ztrust-verify=on \
//!        -Ztrust-verify-profile=unix_hardened -Ztrust-verify-level=2 \
//!        -Ztrust-policy=advisory -Ztrust-verify-output=json \
//!        -Ztrust-dump=mir:<dir> interior_mut_channel_bases.rs
//! ```
//!
//! on Trust stage 1 `a7ea88986d` (the design's apparatus), then
//! `python3 tests/data/interior_mut_channel_edit.py <dir> tests/fixtures`, which
//! rewrites `span.file` to the crate-relative source path and makes the edits. The
//! `*_plain` fixtures are the dumps unedited.
//!
//! Measured 2026-10-15 on the landing tree, with three mutants of
//! `generate/path_defs.rs`: no cell places at all (the pre-rule state at this level)
//! turns `must_refute_owned_cell_across_a_shared_borrow_call` and
//! `must_refute_shared_slice_of_cells_across_an_element_borrow_call` red (both rows
//! PROVED again), so those two FAIL FIRST; dropping the pointee half turns the slice
//! row red; dropping the slot half turns no verdict row red here (the borrow temp's
//! pointee half covers it) but fails the unit pin
//! `a_shared_borrow_of_an_owned_cell_names_the_cell_and_not_the_sibling`. The two
//! holder rows (the design's F2) refute without the rule too: on this main
//! CALL-HAVOC-ESCAPE-2 names `w*.0*` at every call, so they are regression guards. The
//! rest of the design's G2-M1..M9 series is a follow-up (`docs/DECISION_QUEUE.md`).
#[path = "support/realmir_rows.rs"]
mod realmir_rows;

use realmir_rows::{Row, Verdict, expect, rows};

const SLICE: &str = "SliceBoundsCheck";
const TWIN: &str = "mir_assert::BoundsCheck";

fn fixture(name: &str) -> Vec<Row> {
    rows("interior_mut_channel_", name, &[])
}

/// The rows at `line`, column `col`, whose kind contains `needle`, all with `want`.
fn expect_at_col(rows: &[Row], line: u32, col: u32, needle: &str, want: Verdict, why: &str) {
    let hits: Vec<&Row> = rows
        .iter()
        .filter(|r| r.line == line && r.vc.location.col_start == col && r.kind.contains(needle))
        .collect();
    assert!(
        !hits.is_empty(),
        "line {line}:{col}: no `{needle}` row; all rows: {:#?}",
        rows.iter()
            .map(|r| (r.line, r.vc.location.col_start, &r.kind, r.verdict))
            .collect::<Vec<_>>()
    );
    for row in hits {
        assert_eq!(
            row.verdict, want,
            "line {line}:{col} `{needle}`: {why}\nresult: {}\nformula: {:?}",
            row.result, row.vc.formula
        );
    }
}

// ─── the SLOT half: an owned cell handed out by a shared borrow ─────────────────

/// `synthetic_cell_interior_callee` (Appendix C.1, source line 60): an owned
/// `c: Cell<usize>` guarded `c < s.len()`, then `poke_cell(&c)`, then `s[c]`. The callee
/// sets `c` to `usize::MAX` through `Cell::set` (defined behaviour), so the bound is
/// unknown at the use. Was PROVED (interval), certified=true.
#[test]
fn must_refute_owned_cell_across_a_shared_borrow_call() {
    let rows = fixture("cell_interior_callee");
    expect(&rows, 60, SLICE, 1, Verdict::Failed, "`poke_cell(&c)` writes `c` through its cell");
    expect(&rows, 60, TWIN, 1, Verdict::Failed, "the hardened twin likewise");
}

/// Its `&mut c` twin refuted before the rule and still does.
#[test]
fn must_refute_owned_cell_across_a_mut_borrow_call() {
    let rows = fixture("cell_interior_callee_mut");
    expect(&rows, 60, SLICE, 1, Verdict::Failed, "`poke_cell(&mut c)` may write `c`");
    expect(&rows, 60, TWIN, 1, Verdict::Failed, "the hardened twin likewise");
}

/// The no-call control: the same body with the call replaced by its `Goto`, the shared
/// borrow `_8 = &c` kept. Nothing runs between the guard and the use, so the rule costs
/// nothing here.
#[test]
fn control_owned_cell_with_no_call_between_proves() {
    let rows = fixture("cell_interior_nocall");
    expect(&rows, 60, SLICE, 1, Verdict::Proved, "no code runs between guard and use");
    expect(&rows, 60, TWIN, 1, Verdict::Proved, "the hardened twin likewise");
}

// ─── the POINTEE half: cells behind a retagged shared reference ─────────────────

/// `synthetic_shared_slice_of_cells` (Appendix C.2, the design's F1; source line 22,
/// `s[a[j]]` at column 8): `a: &[Cell<usize>]`, guard on the interior read
/// `a[j].0.0 < s.len()`, `poke(&a[k])`, then `s[a[j].0.0]` through a FRESH index temp.
/// The immutable-root congruence lane (since VGAPS-G1 the element-read congruence) tied
/// the two interior reads across the call
/// (`Or([Not(Eq(_14, _23)), Eq(a*[_14].0.0, a*[_23].0.0)])`) and PROVED the row
/// (certified=false) although `poke` sets `a[k]` and `k == j` is allowed.
#[test]
fn must_refute_shared_slice_of_cells_across_an_element_borrow_call() {
    let rows = fixture("shared_slice_of_cells");
    expect_at_col(&rows, 22, 8, SLICE, Verdict::Failed, "`poke(&a[k])` may set `a[j]`");
    expect_at_col(&rows, 22, 8, TWIN, Verdict::Failed, "the hardened twin likewise");
}

/// The plain `&[usize]` body, as dumped: the elements are frozen behind the shared
/// reference, so the same row proves (precision control for the pointee half).
#[test]
fn control_shared_slice_of_plain_elements_proves() {
    let rows = fixture("shared_slice_plain");
    expect_at_col(&rows, 22, 8, SLICE, Verdict::Proved, "`a`'s elements are frozen");
    expect_at_col(&rows, 22, 8, TWIN, Verdict::Proved, "the hardened twin likewise");
}

// ─── a zero-argument call and a `&Cell` stored in a holder (the design's F2) ────

/// `synthetic_pv_mut_holder_cell` (Appendix C.3; source line 37): `w: &mut W { r:
/// &Cell<usize> }`, guard `w.r.get() < s.len()`, `poke_global()` with NO argument, then
/// `s[w.r.get()]`. A `&'static Cell` stashed by safe code (`thread_local!`,
/// `Box::leak`) lets the callee set it. Was PROVED, certified=true.
#[test]
fn must_refute_mut_holder_cell_across_a_zero_argument_call() {
    let rows = fixture("pv_mut_holder_cell");
    expect(&rows, 37, SLICE, 1, Verdict::Failed, "`poke_global()` may set `*w.r`");
    expect(&rows, 37, TWIN, 1, Verdict::Failed, "the hardened twin likewise");
}

/// The same through `w: &W` (source line 45).
#[test]
fn must_refute_shared_holder_cell_across_a_zero_argument_call() {
    let rows = fixture("pv_shared_holder_cell");
    expect(&rows, 45, SLICE, 1, Verdict::Failed, "`poke_global()` may set `*w.r`");
    expect(&rows, 45, TWIN, 1, Verdict::Failed, "the hardened twin likewise");
}

// ─── real-MIR regression guards (the design's Appendix A.6) ─────────────────────
//
// `tests/fixtures/interior_mut_channel_guard_*_mir.json`: the stage-1 `a7ea88986d`
// `-C opt-level=0` dumps of `tests/data/interior_mut_channel.rs`, unedited (same flags
// as above; `interior_mut_channel_edit.py --guards`). The cell API stays calls here, so
// these do not fail first: every `must_refute_*` refuted before the rule and must still,
// and the plain-sibling controls must keep proving (the rule names cell bytes, never a
// frozen sibling: the design's G2-M3 precision pins on real code).

/// Every `SliceBoundsCheck` row and its hardened twin at `line:col` (the `s[..]` index
/// of the guard fixture `name`; at least one of each) has `want`.
fn guard(name: &str, line: u32, col: u32, want: Verdict) {
    let rows = rows("interior_mut_channel_guard_", name, &[]);
    for needle in [SLICE, TWIN] {
        let hits: Vec<&Row> = rows
            .iter()
            .filter(|r| r.line == line && r.vc.location.col_start == col && r.kind.contains(needle))
            .collect();
        assert!(
            !hits.is_empty(),
            "{name} line {line}:{col}: no `{needle}` row; all rows: {:#?}",
            rows.iter()
                .map(|r| (r.line, r.vc.location.col_start, &r.kind, r.verdict))
                .collect::<Vec<_>>()
        );
        for row in hits {
            assert_eq!(
                row.verdict, want,
                "{name} line {line}:{col} `{needle}`\nresult: {}\nformula: {:?}",
                row.result, row.vc.formula
            );
        }
    }
}

#[test]
fn real_mir_guards_must_refute_stay_refuted() {
    for (name, line, col) in [
        ("must_refute_local_cell_callee", 32, 8),
        ("must_refute_local_ucell_callee", 41, 8),
        ("must_refute_local_cell_inline", 51, 8),
        ("must_refute_struct_cell_field", 60, 8),
        ("must_refute_cell_param", 77, 8),
        ("must_refute_ucell_param_inline", 87, 8),
        ("must_refute_cell_array", 96, 8),
        ("must_refute_cell_through_holder", 113, 8),
        ("must_refute_const_cell_transmute", 126, 4),
        ("must_refute_transmute_in_out_poke", 135, 4),
    ] {
        guard(name, line, col, Verdict::Failed);
    }
}

#[test]
fn real_mir_guards_plain_siblings_keep_proving() {
    for (name, line, col) in [
        ("control_struct_frozen_sibling", 69, 8),
        ("control_struct_plain_sibling", 151, 4),
        ("control_tuple_plain_sibling", 159, 4),
    ] {
        guard(name, line, col, Verdict::Proved);
    }
}
