//! REAL-MIR pins for slice patterns matched through a TUPLE of slices.
//!
//! `match (idx, ops) { ([w], [e]) => .. }` lowers to `_3 = (copy _1, copy _2)`,
//! a length test per field through a fresh copy (`_15 = copy (_3.0)`,
//! `_8 = PtrMetadata(&raw (*_15))`, `switchInt(_8 == 1)`), and in the arm a
//! SECOND fresh copy of the same field that the `ConstantIndex` reads through
//! (`_17 = copy (_3.0)`, `_10 = &(*_17)[0 of 1]`). The arm's length is the
//! tuple field's length; each copy carries it.
//!
//! Fixtures: `tests/fixtures/slice_tuple_*_mir.json` are the compiler's own
//! extraction of [`tests/data/slice_tuple_patterns.rs`], captured with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -Ztrust-verify-profile=unix_hardened \
//!        -Ztrust-policy=advisory -Ztrust-dump=mir:<dir> slice_tuple_patterns.rs
//! ```
//!
//! on Trust `main` stage 1 `f9e47e012` (2026-10-02). Before the fix that
//! compiler, and the installed seal `321aaeda7`, refuted every slice row of
//! `pair_of_slices`, `tuple_of_slices` and `indexed_app`.
//!
//! # Mutation ledger (2026-10-02; each mutant reverts one piece)
//!
//! ```text
//! mutant                                              tests that go red
//! index lane does not conjoin the same-block ties     a_pair_of_slices…, a_triple…, the_original…,
//!                                                     the_other_unchecked…, a_reseated…
//! tie filter "rename at point is a no-op" removed     (none — equivalent: establish versioning leaves
//!                                                      no bare name the block writes before the use)
//! ties versioned at the use point, not establish      (none — equivalent here: the extraction drops a
//!                                                      tie whose subject is reseated before the use)
//! relevance closure skipped                           (none — relevance prunes only true, unrelated ties)
//! ```
//!
//! Every row is produced through the entry the compiler calls (hardened profile
//! ON) and decided by the deterministic in-process `ay` router. Each positive
//! shape has a counter-program in the same file that is a real panic and must
//! keep refuting.
use std::collections::HashSet;

use trust_types::{BlockId, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

const SOLVER_STACK_BYTES: usize = 256 * 1024 * 1024;

fn load(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/fixtures/slice_tuple_{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Proved,
    Failed,
    Other,
}

#[derive(Debug, Clone)]
struct Row {
    kind: String,
    line: u32,
    verdict: Verdict,
    result: String,
}

fn rows(name: &str) -> Vec<Row> {
    let func = load(name);
    let ops: HashSet<(BlockId, usize)> = HashSet::new();
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let context = trust_vcgen::VcgenContext::for_function(func.def_path.clone());
            let db = trust_vcgen::SummaryDatabase::new();
            let (solver_vcs, preclassified) =
                trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
                    &func, &db, true, &context, &ops,
                );
            let router = test_router::deterministic_test_router();
            let decided = solver_vcs.into_iter().map(|vc| {
                let (_, result) = router
                    .verify_all(std::slice::from_ref(&vc))
                    .into_iter()
                    .next()
                    .expect("one verdict per VC");
                (vc, result)
            });
            preclassified
                .into_iter()
                .chain(decided)
                .map(|(vc, result)| Row {
                    kind: format!("{:?}", vc.kind),
                    line: vc.location.line_start,
                    verdict: match result {
                        VerificationResult::Proved { .. } => Verdict::Proved,
                        VerificationResult::Failed { .. } => Verdict::Failed,
                        _ => Verdict::Other,
                    },
                    result: format!("{result:?}"),
                })
                .collect()
        })
        .expect("spawn")
        .join()
        .expect("generation thread")
}

/// Exactly `count` rows at `line` whose kind contains `needle`, each with `want`.
fn expect(rows: &[Row], line: u32, needle: &str, count: usize, want: Verdict, why: &str) {
    let hits: Vec<&Row> =
        rows.iter().filter(|r| r.line == line && r.kind.contains(needle)).collect();
    assert_eq!(
        hits.len(),
        count,
        "line {line}: expected {count} `{needle}` row(s); all rows: {rows:#?}"
    );
    for row in hits {
        assert_eq!(
            row.verdict, want,
            "line {line} `{needle}`: {why}\nresult: {}\nrow: {row:#?}",
            row.result
        );
    }
}

const SLICE: &str = "SliceBoundsCheck";

/// `pair_of_slices` (line 6, `([w], [e]) => ..`): the two `ConstantIndex` reads
/// go through fresh arm-block copies `_17`/`_18` of `_3.0`/`_3.1`. Before the
/// fix both rows were refuted at `_17__slice_len = 0` beside
/// `_3.0__slice_len = 1`: the index lane never conjoined the arm block's own
/// copy ties.
#[test]
fn a_pair_of_slices_matched_as_a_tuple_keeps_each_length() {
    let rows = rows("pair_of_slices");
    expect(&rows, 6, SLICE, 2, Verdict::Proved, "the arm guarantees both lengths are 1");
}

/// `tuple_of_slices` (lines 13-15): a `&str` beside two slices, three arms with
/// one, two and three element reads.
#[test]
fn a_triple_with_two_slices_keeps_each_arms_lengths() {
    let rows = rows("tuple_of_slices");
    expect(&rows, 13, SLICE, 1, Verdict::Proved, "`[w]` guarantees idx.len() == 1");
    expect(&rows, 14, SLICE, 2, Verdict::Proved, "`[w]`, `[e]` guarantee both lengths");
    expect(&rows, 15, SLICE, 3, Verdict::Proved, "`[h, l]`, `[e]` guarantee both lengths");
}

/// COUNTER: the arm tests `a`'s length only. `*x` is safe; `b[0]` panics for
/// `b = &[]` and its row (and hardened twin) must stay refuted — the fix must
/// not let one field's length stand in for the other's.
#[test]
fn the_other_unchecked_field_still_refutes() {
    let rows = rows("other_field_unchecked");
    expect(&rows, 24, "mir_assert::BoundsCheck", 1, Verdict::Failed, "`b[0]` panics for `b = &[]`");
    let slice: Vec<&Row> = rows.iter().filter(|r| r.line == 24 && r.kind == SLICE).collect();
    assert_eq!(slice.len(), 2, "the `[x]` read of `a` and `b[0]`'s assert: {rows:#?}");
    assert_eq!(
        slice.iter().filter(|r| r.verdict == Verdict::Proved).count(),
        1,
        "only the `[x]` read of `a`, which the arm guarantees, may prove: {slice:#?}"
    );
    assert_eq!(
        slice.iter().filter(|r| r.verdict == Verdict::Failed).count(),
        1,
        "`b[0]` must stay refuted: {slice:#?}"
    );
}

/// COUNTER: `t.0` is reseated to `c` after the arm matched the old `t.0`, so
/// `t.0[0]` panics for `c = &[]`. Its MIR bounds assert (bb2, over a fresh copy
/// of the NEW `t.0`) must stay refuted on both twins. The load row after that
/// assert (bb3, `copy (*_14)[_8]`) IS dominated by the assert's success edge and
/// proves — that is the one proved row at this line, and only one.
#[test]
fn a_reseated_tuple_field_still_refutes() {
    let rows = rows("reseated_field");
    expect(
        &rows,
        36,
        "mir_assert::BoundsCheck",
        1,
        Verdict::Failed,
        "`t.0[0]` panics for `c = &[]`",
    );
    let slice: Vec<&Row> = rows.iter().filter(|r| r.line == 36 && r.kind == SLICE).collect();
    assert_eq!(slice.len(), 2, "the assert row and the post-assert load row: {rows:#?}");
    assert_eq!(
        slice.iter().filter(|r| r.verdict == Verdict::Failed).count(),
        1,
        "the assert's own row must stay refuted: {slice:#?}"
    );
    assert_eq!(
        slice.iter().filter(|r| r.verdict == Verdict::Proved).count(),
        1,
        "only the load dominated by the assert may prove: {slice:#?}"
    );
}

/// `indexed_app` (lines 52-59): the shape trust-mc-trust-vc-ingest's
/// `lower_indexed_app` had before trust-mc `ae2157707` rewrote it around this
/// gap — enum elements matched by variant, a `Vec::as_slice()` operand, a
/// match guard. On Trust `main` stage 1 `f9e47e012` all eight slice rows were
/// refuted.
#[test]
fn the_original_indexed_application_shape_proves() {
    let rows = rows("indexed_app");
    expect(&rows, 52, SLICE, 1, Verdict::Proved, "`[Index::Numeral(width)]` fixes the length");
    expect(&rows, 57, SLICE, 2, Verdict::Proved, "`[..]`, `[expr]` fix both lengths");
    expect(&rows, 58, SLICE, 2, Verdict::Proved, "`[..]`, `[expr]` fix both lengths");
    expect(&rows, 59, SLICE, 3, Verdict::Proved, "`[high, low]`, `[expr]` fix both lengths");
}
