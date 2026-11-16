//! C-ROWS-PRECISION-1 (2026-10-19): the four class-(c) rows of the seal-6 / seal-7 reading
//! of aterm `6ac89ba10` that went PROVED (channel `trust-edbb3f30`) -> UNKNOWN with no
//! counterexample and no timeout. On seal-7 (`trust-41d79979`) `ay` still proves each of
//! them; what each lost is the evidence a published `#[trust(static)]` row needs
//! (`targo-trust/src/types.rs`: a solver proof "without attachable native or clean-kernel
//! proof evidence" is downgraded before publication):
//!
//! * `Parser::parse_and_dispatch_osc` (aterm-parser `dispatch.rs:718:62-71`,
//!   `&rest[m + 1..]`) and `goal_active` (aterm-phase `turn.rs:157:20-40`,
//!   `&rows[frame.bottom + 1..]`) lost their Clean-kernel certificate. Since
//!   RANGE-INDEX-RESULT-LEN-1 (`003dc1ce90`, TRUST-KI-1015-1) an earlier cut of the same
//!   function (`let rest = &data[k + 1..]`, `rows[from..frame.top]`) carries the definition
//!   `rest__slice_len == data__slice_len - (k + 1)` into every later VC, and the
//!   multi-variable Farkas lane of `trust_certify` (`multi_var_farkas_refutation`, the lane
//!   that certified both rows on the channel) had no `Sub` arm in `formula_linform`, which
//!   reads every atom of the pool: ONE such atom anywhere returned `None` for the whole
//!   pool, although the refutation (`m < rest.len()`, `m + 1 > rest.len()`) never uses it.
//!   Nor in `formula_to_normterm`, which reads the atoms a refutation uses. The fix gives
//!   both the arm (`nt_sub`: `Int.sub` is the kernel's reducible
//!   `λ m n => Int.add m (Int.neg n)`, and the kernel re-checks every term).
//! * `size_words` (aterm-messages `waits.rs:110:25-41`, `bytes + MB / 2`) and `lift_points`
//!   (aterm-messages `animate.rs:835:40-45`, `x - g`) lost the trust-mc PDR evidence of the
//!   direct typed CHC lane: the typed-CHC query the compiler emits for each is
//!   byte-identical on both seals, and seal-7's engine answers `Unknown` where the
//!   channel's answered `Proved`. That is below this crate: bisected with only the `ay` pin
//!   moved to ay `cc2c626b49` (CHC model validation; docs/KNOWN_HAZARDS.md
//!   C-ROWS-PRECISION-2). The rows here pin only what trust-vcgen owns for them: each stays
//!   PROVED, and its wrong twin stays FAILED.
//!
//! # Fixtures
//!
//! `tests/fixtures/c_rows_precision/<fn>_{o0,o3}_mir.json` are the compiler's own
//! extraction of the functions of `tests/data/c_rows_precision.rs` (each aterm body
//! verbatim, its crate-local helpers stubbed with their signatures), UNEDITED except as
//! said below, captured with `trust-41d79979`'s trustc (seal-7, no trustd), from the
//! repository root, by
//!
//! ```text
//! trustc --edition 2021 --crate-type lib --crate-name c_rows_precision \
//!        -C opt-level=<0 | 3 -C overflow-checks=on> -Ztrust-verify=on \
//!        -Ztrust-verify-profile=unix_hardened -Ztrust-verify-level=2 -Ztrust-policy=advisory \
//!        -Ztrust-verify-output=json -Ztrust-dump=mir:<dir> \
//!        crates/trust-vcgen/tests/data/c_rows_precision.rs
//! ```
//!
//! so every `span.file` of the source is the repository-relative path. The `format!` spans
//! of `size_words{,_twin}` name the toolchain's own `alloc/src/macros.rs`; its home prefix
//! is rewritten to `<home>/toolchains/` (as in `union_cell_channel_realmir.rs`), which keeps
//! `sep_engine::is_trusted_std_file`'s answer. Each `*_twin` panics natively at -O0 and
//! -O3 (`-C overflow-checks=on`) on the input in its comment; each real function returns on
//! every control tried.
//!
//! # What main did, and the mutants (2026-10-19)
//!
//! Measured through this file's own entry (`tests/support/realmir_rows.rs`) on origin/main
//! `c29da3e78b`: the two cut rows PROVED and NOT certified at both levels (and certified
//! on `edbb3f3009`, before `003dc1ce90`); with the fix they are certified. Mutants of
//! `trust-certify/src/lib.rs`, each restored byte for byte:
//!
//! ```text
//! mutant                                   tests that go red
//! both `Sub` arms removed (main's file)    r3_.., r4_.., a_sub_slice_length_..
//! the `formula_linform` arm removed        r3_.., r4_.., a_sub_slice_length_..
//! the `formula_to_normterm` arm removed    a_sub_slice_length_..
//! `nt_sub` folds `e1 + e2` (wrong sign)    a_sub_slice_length_..
//! ```
//!
//! R3 and R4 never use the definition, so only the pool has to parse; the
//! `formula_to_normterm` half is reached by a refutation that goes THROUGH `len - a`.
#[path = "support/realmir_rows.rs"]
mod realmir_rows;

use realmir_rows::{
    PRIMARY_ADD, PRIMARY_SUB, Row, TWIN_ADD, TWIN_SUB, Verdict, certified, expect_certified,
    load_path, rows, rows_of,
};

/// The fixture of `name` at each optimization level it was captured at.
fn both_levels(name: &str) -> Vec<(&'static str, Vec<Row>)> {
    ["o0", "o3"]
        .into_iter()
        .map(|level| (level, rows("c_rows_precision/", &format!("{name}_{level}"), &[])))
        .collect()
}

/// The rows at `line`, columns `cols`, whose kind contains `needle`: at least one, all
/// with `want`. Returns them.
fn expect_at<'a>(
    rows: &'a [Row],
    level: &str,
    line: u32,
    cols: (u32, u32),
    needle: &str,
    want: Verdict,
    why: &str,
) -> Vec<&'a Row> {
    let hits: Vec<&Row> = rows
        .iter()
        .filter(|r| {
            r.line == line
                && (r.vc.location.col_start, r.vc.location.col_end) == cols
                && r.kind.contains(needle)
        })
        .collect();
    assert!(
        !hits.is_empty(),
        "{level} line {line}:{}-{}: no `{needle}` row; all rows: {:#?}",
        cols.0,
        cols.1,
        rows.iter()
            .map(|r| (r.line, r.vc.location.col_start, r.vc.location.col_end, &r.kind, r.verdict))
            .collect::<Vec<_>>()
    );
    for row in &hits {
        assert_eq!(
            row.verdict, want,
            "{level} line {line}:{}-{} `{needle}`: {why}\nresult: {}\nformula: {:?}",
            cols.0, cols.1, row.result, row.vc.formula
        );
    }
    hits
}

/// [`expect_at`] `Proved`, and every such row certified by the Clean kernel.
fn expect_certified_at(rows: &[Row], level: &str, line: u32, cols: (u32, u32), why: &str) {
    for row in expect_at(rows, level, line, cols, "SliceBoundsCheck", Verdict::Proved, why) {
        assert!(
            certified(row),
            "{level} line {line}:{}-{}: the Clean kernel must certify the row: {why}\nformula: {:?}",
            cols.0,
            cols.1,
            row.vc.formula
        );
    }
}

/// R3, aterm-parser `dispatch.rs:718:62-71`: `m` is `rest.iter().position(..)`, below
/// `rest.len()`, so `&rest[m + 1..]` is in bounds. The pool carries `let rest =
/// &data[k + 1..]`'s length definition `rest.len() == data.len() - (k + 1)`.
#[test]
fn r3_parse_and_dispatch_osc_rest_cut_is_certified() {
    for (level, rows) in both_levels("parse_and_dispatch_osc") {
        expect_certified_at(
            &rows,
            level,
            144,
            (62, 71),
            "`m < rest.len()` closes `m + 1 > rest.len()`; the sub-slice length definition \
             beside it must not take the Farkas lane away",
        );
    }
}

/// R4, aterm-phase `turn.rs:157:20-40`: `rows[frame.bottom]` already checked
/// `frame.bottom < rows.len()`, so `&rows[frame.bottom + 1..]` is in bounds. The pool
/// carries `rows[from..frame.top]`'s length definition `len == frame.top - from`.
#[test]
fn r4_goal_active_rows_cut_is_certified() {
    for (level, rows) in both_levels("goal_active") {
        expect_certified_at(
            &rows,
            level,
            229,
            (20, 40),
            "the index check on `rows[frame.bottom]` closes the cut; the earlier cut's length \
             definition must not take the Farkas lane away",
        );
    }
}

/// The other half of the arm. In TRUST-KI-1015-1's own fixtures (`tests/fixtures/subslice_len/`,
/// `tests/data/subslice_len.rs`, `subslice_len_realmir.rs`), `rest.len() - 4` under
/// `input.len() >= 6` is refuted THROUGH the definition `rest.len() == input.len() - 2`, so
/// its certificate needs `formula_to_normterm`'s `Sub` arm as well as `formula_linform`'s
/// (R3 and R4 only need the pool to parse). These are the rows docs/TCB.md listed as
/// `[CERTIFY_MISS]` under RANGE_INDEX_RESULT_LEN.
#[test]
fn a_sub_slice_length_the_refutation_uses_is_certified() {
    for (name, line) in [("a15_subslice_ok", 14), ("b1_from_ok", 34), ("b12_reslice_ok", 246)] {
        let path =
            format!("{}/tests/fixtures/subslice_len/{name}.json", env!("CARGO_MANIFEST_DIR"));
        let rows = rows_of(load_path(&path), &[]);
        expect_certified(
            &rows,
            line,
            PRIMARY_SUB,
            1,
            true,
            "the parent's guard and the sub-slice's length definition close the underflow",
        );
    }
}

/// R1, aterm-messages `waits.rs:110:25-41`: the first branch took every
/// `bytes >= GB - MB / 2`, so `bytes + MB / 2` cannot overflow.
#[test]
fn r1_size_words_mb_branch_add_is_proved() {
    for (level, rows) in both_levels("size_words") {
        for needle in [PRIMARY_ADD, TWIN_ADD] {
            expect_at(&rows, level, 32, (25, 41), needle, Verdict::Proved, "guarded by the GB arm");
        }
    }
}

/// R2, aterm-messages `animate.rs:835:40-45`: `x` is `g + q` for the `q` the checked add
/// already took, so `x - g` is `q` and cannot overflow.
#[test]
fn r2_lift_points_offset_sub_is_proved() {
    for (level, rows) in both_levels("lift_points") {
        for needle in [PRIMARY_SUB, TWIN_SUB] {
            expect_at(&rows, level, 89, (40, 45), needle, Verdict::Proved, "`x - g == q`");
        }
    }
}

/// Each wrong twin panics natively on the input in its comment in
/// `tests/data/c_rows_precision.rs`; its row must stay FAILED.
#[test]
fn twins_stay_failed() {
    for (level, rows) in both_levels("size_words_twin") {
        for needle in [PRIMARY_ADD, TWIN_ADD] {
            expect_at(&rows, level, 54, (25, 41), needle, Verdict::Failed, "u64::MAX - MB/4 - 1");
        }
    }
    for (level, rows) in both_levels("lift_points_twin") {
        for needle in [PRIMARY_SUB, TWIN_SUB] {
            expect_at(&rows, level, 109, (40, 45), needle, Verdict::Failed, "a wrapped `x`");
        }
    }
    for (level, rows) in both_levels("parse_and_dispatch_osc_twin") {
        expect_at(&rows, level, 162, (62, 71), "SliceBoundsCheck", Verdict::Failed, "b\"a;b;\"");
    }
    for (level, rows) in both_levels("goal_active_twin") {
        expect_at(
            &rows,
            level,
            246,
            (20, 40),
            "SliceBoundsCheck",
            Verdict::Failed,
            "[\"─\", \"─\"]",
        );
    }
}
