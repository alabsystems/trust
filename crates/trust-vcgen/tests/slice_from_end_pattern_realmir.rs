//! REAL-MIR pins for slice patterns counted FROM THE END.
//!
//! `[.., x]` lowers to `_4 = &(*_1)[1 of 1 from end]`: a `ConstantIndex` with
//! `from_end: true`, which reads element `len - offset`. That element is in range
//! iff `1 <= offset <= len`, so the bounds violation is `len < offset`. The index
//! lane (`constant_index_projection_vc`, `src/rvalue_safety.rs`) used the
//! FROM-START violation `len <= offset` for both directions, so every `[.., x]`
//! read was refuted at `len == offset` — the one-element slice, whose last element
//! is real — with `verified_counterexample = true`.
//!
//! Fixtures: `tests/fixtures/slice_from_end_*_mir.json` are the compiler's own
//! extraction of [`tests/data/slice_from_end_patterns.rs`], captured with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -Ztrust-verify-profile=unix_hardened \
//!        -Ztrust-policy=advisory -Ztrust-dump=mir:<dir> slice_from_end_patterns.rs
//! ```
//!
//! on Trust `main` stage 1 `f9e47e012` (2026-10-02), which refuted `last_of`
//! (1/1), `second_last` (1/1) and `ends_of_pair` (2/2).
//!
//! The counters are the same fixtures with the length test removed or weakened,
//! so the from-end read is a real out-of-range access; they must keep refuting.
//! Safe Rust cannot write those: a slice pattern's own length test always guards
//! its reads.
//!
//! # Mutation ledger (2026-10-02)
//!
//! ```text
//! mutant                                              tests that go red
//! from-end violation back to `len <= offset`          last_of…, second_last…, ends_of_pair…
//! from-end violation `len < offset - 1` (off by one)  none here — every rustc from-end row has
//!                                                     `min_length >= offset`, whose `len < min_length`
//!                                                     disjunct alone refutes the counters; killed by
//!                                                     `rvalue_safety::constant_index_violation_tests`
//! from-end `offset == 0` arm dropped                  none here (rustc never emits it); killed by
//!                                                     `from_end_offset_zero_is_always_out_of_range`
//! ```
use std::collections::HashSet;

use trust_types::{
    BlockId, ConstValue, Operand, Rvalue, Statement, Terminator, VerifiableFunction,
    VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

const SOLVER_STACK_BYTES: usize = 256 * 1024 * 1024;

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/slice_from_end_{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
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
    rows_of(load(name))
}

fn rows_of(func: VerifiableFunction) -> Vec<Row> {
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

/// `last_of` (line 6, `[.., x] => *x`): `[1 of 1 from end]` under `len >= 1`.
#[test]
fn last_of_proves() {
    let rows = rows("last_of");
    expect(&rows, 6, SLICE, 1, Verdict::Proved, "`len >= 1` puts element `len - 1` in range");
}

/// `second_last` (line 13, `[.., x, _] => *x`): `[2 of 2 from end]` under `len >= 2`.
#[test]
fn second_last_proves() {
    let rows = rows("second_last");
    expect(&rows, 13, SLICE, 1, Verdict::Proved, "`len >= 2` puts element `len - 2` in range");
}

/// `ends_of_pair` (line 25, `([.., x], [y, _, ..])`): one from-end read and one
/// from-start read through a tuple of slices.
#[test]
fn ends_of_pair_proves() {
    let rows = rows("ends_of_pair");
    expect(&rows, 25, SLICE, 2, Verdict::Proved, "both arm lengths put both reads in range");
}

/// The single block-0 `Ge(len, k)` length test of a one-pattern fixture.
fn length_test(func: &mut VerifiableFunction) -> &mut ConstValue {
    let block = &mut func.body.blocks[0];
    block
        .stmts
        .iter_mut()
        .find_map(|stmt| match stmt {
            Statement::Assign {
                rvalue: Rvalue::BinaryOp(_, _, Operand::Constant(k @ ConstValue::Uint(..))),
                ..
            } => Some(k),
            _ => None,
        })
        .expect("the pattern's length test `len >= k`")
}

/// COUNTER: `last_of` with block 0 jumping straight to the arm, so
/// `&(*_1)[1 of 1 from end]` runs for `a = &[]` — element `-1`, a real
/// out-of-range read. It must refute.
#[test]
fn an_unguarded_from_end_read_still_refutes() {
    let mut func = load("last_of");
    let arm = match &func.body.blocks[0].terminator {
        Terminator::SwitchInt { otherwise, .. } => *otherwise,
        other => panic!("block 0 ends in the length switch, not {other:?}"),
    };
    assert_eq!(arm, BlockId(2), "the arm with the from-end read");
    func.body.blocks[0].terminator = Terminator::Goto(arm);
    let rows = rows_of(func);
    expect(&rows, 6, SLICE, 1, Verdict::Failed, "`a = &[]` reads element -1");
}

/// COUNTER: `second_last` with its `len >= 2` test weakened to `len >= 1`, so
/// `[2 of 2 from end]` runs for a one-element slice and reads element `-1`.
#[test]
fn a_weakened_guard_on_a_from_end_read_still_refutes() {
    let mut func = load("second_last");
    let k = length_test(&mut func);
    assert!(matches!(*k, ConstValue::Uint(2, 64)), "the fixture's own `len >= 2`: {k:?}");
    *k = ConstValue::Uint(1, 64);
    let rows = rows_of(func);
    expect(&rows, 13, SLICE, 1, Verdict::Failed, "`len == 1` reads element -1");
}

/// `subslice_rest` (line 36, `([_, rest @ ..], [y]) => rest[1] ^ *y`): the arm
/// guarantees `a.len() >= 1` and `b.len() == 1`, so the `rest = a[1..]`
/// subslice and the `[y]` read are in range, but `rest[1]` panics for
/// `a.len() == 2`. Its bounds assert must refute on both twins; the subslice
/// and `[y]` rows prove.
#[test]
fn a_subslice_is_in_range_and_an_index_past_it_still_refutes() {
    let rows = rows("subslice_rest");
    expect(
        &rows,
        36,
        "mir_assert::BoundsCheck",
        1,
        Verdict::Failed,
        "`rest[1]` panics for `a.len() == 2`",
    );
    let slice: Vec<&Row> = rows.iter().filter(|r| r.line == 36 && r.kind == SLICE).collect();
    assert_eq!(slice.len(), 3, "the subslice, `[y]` and `rest[1]`'s assert: {rows:#?}");
    assert_eq!(
        slice.iter().filter(|r| r.verdict == Verdict::Proved).count(),
        2,
        "the subslice `a[1..]` and `[y]` are in range: {slice:#?}"
    );
    assert_eq!(
        slice.iter().filter(|r| r.verdict == Verdict::Failed).count(),
        1,
        "`rest[1]` must stay refuted: {slice:#?}"
    );
}
