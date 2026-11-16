//! INTERIOR-MUT-CHANNEL-2 (2026-10-16; found by the review of G2-OPTSTRING-1 and by the
//! `union-cell-realmir` fixtures): a shared borrow of a union's CELL field writes bytes
//! the union's other fields name.
//!
//! `union U { c: ManuallyDrop<Cell<usize>>, n: usize }`, an owned `u`, the guard
//! `u.n < s.len()`, then `poke(&u.c)` sets the cell to `usize::MAX` (defined behaviour),
//! then `s[u.n]`. G2's slot half named the cell place below `u.0` and not the union
//! cover the `&mut` channel carries since UNION-SIBLING-WRITE-2, and the name algebra
//! keeps `u.1` apart from `u.0`, so the guard survived the call. The same through
//! `&w.u.c` (a union field of a struct) and through a field holding a `Vec` whose
//! allocator holds a `Cell` (`&u.v`, read back through `u.n[k]`): there no name below
//! `u.v` denotes the cell bytes, but `u.n` does, so below a union the BYTE question
//! decides (`generate::shared_borrow_cell_places`). Behind `&` the overlap reaches a
//! discriminant with no call at all: for `r: &UT { e: Option<u32>, c:
//! ManuallyDrop<[Cell<u32>; 2]> }`, a raw store through a pointer cast from `&r.c` clears
//! `r.e`'s tag between two reads of it (`place_is_body_stable`'s union step; found by the
//! review of this fix).
//!
//! # Fixtures
//!
//! `tests/fixtures/union_cell_channel/<fn>_{o3,o0}_mir.json` are the compiler's own
//! extraction of the functions of `tests/data/union_cell_channel.rs`, UNEDITED, captured
//! with `trust-b58a105d`'s trustc (no trustd) by
//!
//! ```text
//! trustc --edition 2021 --crate-type lib --crate-name union_cell_channel \
//!        -C opt-level=<3|0> -Ztrust-verify=on -Ztrust-verify-profile=unix_hardened \
//!        -Ztrust-verify-level=2 -Ztrust-policy=advisory -Ztrust-verify-output=json \
//!        -Ztrust-dump=mir:<dir> union_cell_channel.rs
//! ```
//!
//! with every `span.file` rewritten to the crate-relative source path (and the toolchain
//! prefix of `core`'s `matches!` spans to `<home>/toolchains/`, which keeps
//! `sep_engine::is_trusted_std_file`'s answer). Each `must_refute_*` panics natively at -O0
//! and -O3 (`-C overflow-checks=on`) on the input in its comment; each control returns
//! for every input tried.
//!
//! # What main did, and the mutants (2026-10-16)
//!
//! Measured through this file's own entry (`tests/support/realmir_rows.rs`) on this tree
//! with one change at a time to `generate/path_defs.rs` and `lib.rs` (and, for main,
//! `local_defs.rs`):
//!
//! * origin/main `d512993d21` (before G2-OPTSTRING-1 and this rule; `2ff939074c` has the
//!   same trust-vcgen sources): the add row and the `s[..]` rows of the five
//!   borrow-below-a-union programs and of the two tag-reread programs, and their hardened
//!   twins, PROVED at both levels; the whole-union, behind-`&` and enum rows FAILED; the
//!   controls PROVED;
//! * G2-OPTSTRING-1 without this rule (the cover and the union step off): the same seven
//!   PROVED;
//! * the cover asked the NAMED question: the two `Vec`-field rows PROVED (the review's
//!   finding 2);
//! * `place_is_body_stable`'s union step off: the two tag-reread programs PROVED (the
//!   unit row `a_union_field_behind_a_shared_root_is_not_body_stable_when_the_union_holds_a_cell`
//!   pins the step too);
//! * G2-OPTSTRING-1's union rule off (the named walk keeps its question below a union):
//!   the whole-union and behind-`&` rows PROVED;
//! * the named question answering `false` for every enum (unsound on purpose): the
//!   enum-payload row PROVED.
//!
//! The three controls and every other row of these fixtures keep their verdicts under all
//! six.
#[path = "support/realmir_rows.rs"]
mod realmir_rows;

use realmir_rows::{PRIMARY_ADD, Row, TWIN_ADD, Verdict, expect, rows};

const SLICE: &str = "SliceBoundsCheck";
const TWIN: &str = "mir_assert::BoundsCheck";

/// The fixture of `name` at each optimization level it was captured at.
fn both_levels(name: &str) -> Vec<(&'static str, Vec<Row>)> {
    ["o3", "o0"]
        .into_iter()
        .map(|level| (level, rows("union_cell_channel/", &format!("{name}_{level}"), &[])))
        .collect()
}

/// The rows at `line`, column `col`, whose kind contains `needle`: at least one, all with
/// `want`.
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

/// The `s[..]` row and its hardened twin of each level of `name`, at `line`:`col`.
fn expect_index(name: &str, line: u32, col: u32, want: Verdict, why: &str) {
    for (level, rows) in both_levels(name) {
        let why = format!("{name} ({level}): {why}");
        expect_at_col(&rows, line, col, SLICE, want, &why);
        expect_at_col(&rows, line, col, TWIN, want, &why);
    }
}

// ─── INTERIOR-MUT-CHANNEL-2: a borrow of a union's cell field ─────────────────────

/// `poke_md_c32(&u.c)` sets the cell to `u32::MAX`, so `u.n + 1` overflows (`v = 1`).
/// Main PROVED the add row and its twin at both levels.
#[test]
fn must_refute_a_union_sibling_across_a_cell_field_borrow_add() {
    for (level, rows) in both_levels("must_refute_union_cell_field_add") {
        let why = format!("({level}) `poke(&u.c)` rewrites `u.n`");
        expect(&rows, 92, PRIMARY_ADD, 1, Verdict::Failed, &why);
        expect(&rows, 92, TWIN_ADD, 1, Verdict::Failed, &why);
    }
}

/// The same channel guarding an index: `s[u.n]` after `poke_md_c(&u.c)`, and through a
/// struct field (`&w.u.c`, whose cover is `w.u`). Main PROVED both rows at both levels.
#[test]
fn must_refute_a_union_sibling_across_a_cell_field_borrow_index() {
    expect_index("must_refute_union_cell_field_index", 103, 8, Verdict::Failed, "`poke(&u.c)`");
    expect_index(
        "must_refute_struct_union_cell_field_index",
        114,
        8,
        Verdict::Failed,
        "`poke(&w.u.c)` rewrites `w.u.n`",
    );
}

/// The review's finding 2: the borrowed field holds a `Vec` whose allocator holds a
/// `Cell`, so its only cell bytes are ones no name below `u.v` denotes, and `u.n[k]`
/// reads them. Below a union the byte question decides, also when the walk STARTS below
/// it. Main PROVED both; with the cover asked the NAMED question both stay PROVED.
#[test]
fn must_refute_a_union_sibling_across_a_vec_field_borrow() {
    expect_index("must_refute_union_vec_field_index", 125, 8, Verdict::Failed, "`poke(&u.v)`");
    expect_index(
        "must_refute_union_option_vec_field_index",
        136,
        8,
        Verdict::Failed,
        "`poke(&u.v)` over an `Option<Vec<u8, CA>>`",
    );
}

// ─── G2-OPTSTRING-1's own union and enum naming, at the verdict level ───────────

/// The whole union borrowed (`poke_uvo(&u)`): the walk passes through the union, whose
/// fields are asked the byte question (G2-OPTSTRING-1's union rule).
#[test]
fn must_refute_a_whole_union_over_a_vec_borrow() {
    expect_index(
        "must_refute_union_option_vec_whole_index",
        147,
        8,
        Verdict::Failed,
        "`poke_uvo(&u)` writes the allocator cell `u.n[k]` reads",
    );
}

/// The union behind `&` (`x: &UV`, `poke_uv(x)`): the POINTEE half's walk passes through
/// the union, whose fields are asked the byte question.
#[test]
fn must_refute_a_union_over_a_vec_behind_a_shared_reference() {
    expect_index(
        "must_refute_union_vec_behind_ref_index",
        199,
        8,
        Verdict::Failed,
        "`poke_uv(x)` writes the allocator cell `x.n[k]` reads",
    );
}

/// A `Vec` BESIDE a cell in an enum payload behind `&`: the enum is still named whole,
/// so the payload's `n` read by value after `poke_ovt(x)` is stale.
#[test]
fn must_refute_an_enum_with_a_vec_beside_a_cell() {
    expect_index(
        "must_refute_option_vec_beside_union_cell",
        170,
        40,
        Verdict::Failed,
        "`poke_ovt(x)` sets the union's cell",
    );
}

/// Precision control: a borrow of the union's `Freeze` field hands out no write channel,
/// so the guard holds across the call.
#[test]
fn control_a_borrow_of_a_union_freeze_field_keeps_the_guard() {
    expect_index(
        "control_union_freeze_field_borrow_index",
        184,
        8,
        Verdict::Proved,
        "`read_n(&u.n)` cannot write",
    );
}

// ─── The discriminant read through a union sibling behind `&` (no call) ──────────

/// The review of the fix (its b11 and b13): `r: &UT` with `UT { e: Option<u32>, c:
/// ManuallyDrop<[Cell<u32>; 2]> }`, two `matches!(&r.e, Some(_))` reads, and between them a
/// call-free raw store through `&r.c as *const _ as *mut [u32; 2]` that clears the tag, so
/// `s[b]` reads `s[5]`. Before the fix (`2ff939074c`) the discriminant CSE tied the second
/// read to the first; its pre-barrier guard is `place_is_body_stable`, whose union step
/// these rows pin (with the step off, both programs are PROVED at both levels).
#[test]
fn must_refute_a_tag_reread_across_a_raw_store_into_a_union_sibling() {
    expect_index(
        "must_refute_union_tag_reread_after_raw_store",
        241,
        4,
        Verdict::Failed,
        "the store through `&r.c` clears `r.e`'s tag",
    );
    expect_index(
        "must_refute_struct_union_tag_reread_after_raw_store",
        255,
        4,
        Verdict::Failed,
        "the store through `&h.u.c` clears `h.u.e`'s tag",
    );
}

/// Precision controls: the struct twin (its cells lie BESIDE the tag) and a store into
/// ANOTHER union keep the tie, so `s[1]` proves.
#[test]
fn control_a_tag_reread_keeps_its_tie_when_the_store_cannot_reach_the_tag() {
    expect_index(
        "control_struct_tag_reread_after_raw_store",
        269,
        4,
        Verdict::Proved,
        "the store through `&r.c` cannot reach `r.e`",
    );
    expect_index(
        "control_other_union_tag_reread_after_raw_store",
        285,
        4,
        Verdict::Proved,
        "the store goes to `w`, not `u`",
    );
}
