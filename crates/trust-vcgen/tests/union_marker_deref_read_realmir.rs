//! UNION-MARKER-DEREF-READ-1 (2026-10-16; found by the review of the INTERIOR-MUT-CHANNEL-2
//! follow-ups): a read through a RECURSIVE union behind a reference was not seen as a
//! union read by `local_defs::deref_read_unwritten_at`.
//!
//! `union RU { n: usize, next: Option<&'static RU> }` held in `struct RH { k, u: RU }`,
//! then `for i in 0..h.u.n { h.u.next = None; t ^= h.u.n - i - 1 }`: the store writes the
//! null pointer over `h.u.n`, so `0 - 0 - 1` overflows at `i = 0`. The extractor spells a
//! recursive type as a by-name marker (`Ty::Datatype { name: "…::RU", variants: [] }`)
//! inside every other type and defines it once in the body's `datatype_defs`. The union
//! check asked `adt_kind == Some(Union)` of each step and lost the type at the marker
//! (`_ => ty = None`), so the store to `h.u.1` did not reach the read of `h.u.0` and the
//! range-end fact stayed live across it. The union write cover's walk
//! (`generate::union_write_cover_len`, over `field_base_may_overlap_siblings`) resolves the
//! marker through the table to the stamped union.
//!
//! # Fixtures
//!
//! `tests/fixtures/union_marker_deref_read/<fn>_{o3,o0}_mir.json` are the compiler's own
//! extraction of the functions of `tests/data/union_marker_deref_read.rs`, UNEDITED,
//! captured with `trust-b58a105d`'s trustc (no trustd), from the repository root, by
//!
//! ```text
//! trustc --edition 2021 --crate-type lib --crate-name union_marker_deref_read \
//!        -C opt-level=<3|0> -Ztrust-verify=on -Ztrust-verify-profile=unix_hardened \
//!        -Ztrust-verify-level=2 -Ztrust-policy=advisory -Ztrust-verify-output=json \
//!        -Ztrust-dump=mir:<dir> crates/trust-vcgen/tests/data/union_marker_deref_read.rs
//! ```
//!
//! so every `span.file` is already the repository-relative source path. Each
//! `must_refute_*` panics natively at -O0 and -O3 (`-C overflow-checks=on`) on the input in
//! its comment (and for every `n >= 1`); each control returns for every input tried.
//!
//! # What main did, and the mutant (2026-10-16)
//!
//! Measured through this file's own entry (`tests/support/realmir_rows.rs`): with
//! `local_defs.rs` as on origin/main `1cb40c0140` (the same blob as on `41d799797b` and
//! `2ff939074c`), both `-` rows of each must-refute line (`- i` and the panicking `- 1`)
//! and their hardened twins are PROVED at both levels (16 rows), and so with all of
//! `2ff939074c`'s `path_defs.rs`, `lib.rs` and `local_defs.rs`; the controls keep their
//! proofs under both. The installed toolchains agree for the review's twin programs: the
//! seal-7 candidate `trust-41d79979` PROVES the overflow row and its twin
//! (docs/KNOWN_HAZARDS.md, UNION-MARKER-DEREF-READ-1).
#[path = "support/realmir_rows.rs"]
mod realmir_rows;

use realmir_rows::{PRIMARY_SUB, Row, TWIN_SUB, Verdict, rows};

/// The fixture of `name` at each optimization level it was captured at.
fn both_levels(name: &str) -> Vec<(&'static str, Vec<Row>)> {
    ["o3", "o0"]
        .into_iter()
        .map(|level| (level, rows("union_marker_deref_read/", &format!("{name}_{level}"), &[])))
        .collect()
}

/// The rows at `line`, columns `cols`, whose kind contains `needle`: at least one, all
/// with `want`.
fn expect_at(rows: &[Row], line: u32, cols: (u32, u32), needle: &str, want: Verdict, why: &str) {
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
        "line {line}:{}-{}: no `{needle}` row; all rows: {:#?}",
        cols.0,
        cols.1,
        rows.iter()
            .map(|r| (r.line, r.vc.location.col_start, r.vc.location.col_end, &r.kind, r.verdict))
            .collect::<Vec<_>>()
    );
    for row in hits {
        assert_eq!(
            row.verdict, want,
            "line {line}:{}-{} `{needle}`: {why}\nresult: {}\nformula: {:?}",
            cols.0, cols.1, row.result, row.vc.formula
        );
    }
}

/// The `-` row and its hardened twin of each level of `name`, at `line`, columns `cols`.
fn expect_sub(name: &str, line: u32, cols: (u32, u32), want: Verdict, why: &str) {
    for (level, rows) in both_levels(name) {
        let why = format!("{name} ({level}): {why}");
        expect_at(&rows, line, cols, PRIMARY_SUB, want, &why);
        expect_at(&rows, line, cols, TWIN_SUB, want, &why);
    }
}

/// `h.u.next = None` writes 0 over `h.u.n`, so the `- 1` of `h.u.n - i - 1` overflows at
/// `i = 0`; the same through a loaded `&mut RH` (`w.h.u`). With `local_defs.rs` as on
/// main, both rows and their twins are PROVED at both levels.
#[test]
fn must_refute_a_read_through_a_recursive_union_after_a_sibling_store() {
    expect_sub(
        "must_refute_recursive_union_in_struct",
        49,
        (13, 37),
        Verdict::Failed,
        "`h.u.next = None` clears `h.u.n` (a by-name marker of a union)",
    );
    expect_sub(
        "must_refute_recursive_union_via_loaded_ref",
        59,
        (13, 39),
        Verdict::Failed,
        "`w.h.u.next = None` clears `w.h.u.n` (a by-name marker of a union)",
    );
}

/// Precision controls: the same shapes over a recursive STRUCT (a by-name marker the
/// table defines as a struct), whose `next` lies beside `n`, keep both `-` rows proved.
#[test]
fn control_a_read_through_a_recursive_struct_keeps_its_fact() {
    for (name, line, cols) in [
        ("control_recursive_struct_in_struct", 69, [(13, 22), (13, 26)]),
        ("control_recursive_struct_via_loaded_ref", 79, [(13, 24), (13, 28)]),
    ] {
        for c in cols {
            expect_sub(name, line, c, Verdict::Proved, "the store to `next` cannot reach `n`");
        }
    }
}
