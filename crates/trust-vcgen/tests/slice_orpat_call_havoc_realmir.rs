//! REAL-MIR pins for SLICE-LEN-CALL-HAVOC-1: a slice pattern behind an
//! or-pattern of string literals keeps its length across the `str` compares.
//!
//! `match (name, args) { ("a" | "b", [x, y]) => .. }` lowers to
//!
//! ```text
//! bb0: _3 = (copy _1, copy _2); _13 = copy (_3.1);
//!      _6 = &raw const (*_13); _7 = PtrMetadata(move _6); _8 = Eq(_7, 2)
//!      switchInt(_8)
//! bb2: _5 = <str as PartialEq>::eq(_14, "a")      // a CALL
//! bb3: _4 = <str as PartialEq>::eq(_15, "b")      // a CALL
//! bb6: _16 = copy (_3.1); _9 = &(*_16)[0 of 2]; ..
//! ```
//!
//! `_6: *const [i64]` is a mutable-pointer local, so its BASE name `_6` is on
//! the whole-function havoc list, and the path-definition fixpoint judged that
//! list at the `eq` calls under the DESTINATION relation, which reads the base
//! `_6` as a write of `_6__slice_len` — the raw pointer's own length metadata,
//! which lives in `_6`'s slot and which no callee can write. The ties
//! `_6__slice_len == _13__slice_len` and `_7 == _6__slice_len` died at bb2, and
//! both `[x, y]` reads were refuted at `_16__slice_len = 0` beside
//! `_6__slice_len = 2` (tla-shapes-families `cvw.rs:474`, preview3). The single
//! literal arm, which reaches the index block without a call, proved.
//!
//! Fixtures: `tests/fixtures/slice_orpat_*_mir.json` are the compiler's own
//! extraction of [`tests/data/slice_orpat_call_havoc.rs`], captured with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib --crate-name fx \
//!        -Ztrust-verify-profile=unix_hardened -Ztrust-policy=advisory \
//!        -Ztrust-dump=mir:<dir> crates/trust-vcgen/tests/data/slice_orpat_call_havoc.rs
//! ```
//!
//! on Trust `main` stage 1 `ed578e1a5` (2026-10-09), which refutes `op_simple`'s
//! and `orpat_ok`'s two rows and `op`'s two line-9 rows.
//!
//! # Counters
//!
//! Each reseats the indexed slice's SLOT through one of the slot-write channels
//! (`&mut s`, `&raw mut s`, a `&mut &[i64]` parameter's pointee) between the
//! length test and the read, or indexes past the tested length. Their MIR
//! bounds assert and its hardened twin must stay refuted: the plain relation
//! keeps only the length of a pointer whose slot nothing can write.
//!
//! # Mutation ledger (2026-10-10)
//!
//! ```text
//! mutant                                                    tests that go red
//! fixpoint terminator kill back on `TerminatorKill::survives`  the_or_pattern_*, the_full_*,
//!                                                              the_same_shape_*
//! ```
use std::collections::HashSet;

use trust_types::{BlockId, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

const SOLVER_STACK_BYTES: usize = 256 * 1024 * 1024;

fn load(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/fixtures/slice_orpat_{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
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

const SLICE: &str = "SliceBoundsCheck";
const ASSERT_TWIN: &str = "mir_assert::BoundsCheck";

/// Exactly `count` `SliceBoundsCheck` rows at `line`, each proved.
fn expect_all_proved(rows: &[Row], line: u32, count: usize, why: &str) {
    let hits: Vec<&Row> = rows.iter().filter(|r| r.line == line && r.kind == SLICE).collect();
    assert_eq!(
        hits.len(),
        count,
        "line {line}: expected {count} slice row(s); all rows: {rows:#?}"
    );
    for row in hits {
        assert_eq!(row.verdict, Verdict::Proved, "line {line}: {why}\nresult: {}", row.result);
    }
}

/// A real out-of-bounds read at `line`: its MIR bounds assert's hardened twin
/// and at least one slice row are refuted, and no slice row other than the one
/// load the assert dominates may prove.
fn expect_refuted(rows: &[Row], line: u32, why: &str) {
    let twins: Vec<&Row> =
        rows.iter().filter(|r| r.line == line && r.kind.contains(ASSERT_TWIN)).collect();
    assert_eq!(twins.len(), 1, "line {line}: one hardened assert twin; all rows: {rows:#?}");
    assert_eq!(twins[0].verdict, Verdict::Failed, "line {line}: {why}\n{}", twins[0].result);
    let slice: Vec<&Row> = rows.iter().filter(|r| r.line == line && r.kind == SLICE).collect();
    assert!(
        slice.iter().any(|r| r.verdict == Verdict::Failed),
        "line {line}: the assert's own slice row must stay refuted ({why}): {slice:#?}"
    );
    assert!(
        slice.iter().filter(|r| r.verdict == Verdict::Proved).count() <= 1,
        "line {line}: only the load dominated by the assert may prove: {slice:#?}"
    );
}

// ---------------------------------------------------------------------------
// POSITIVE: the measured shapes.
// ---------------------------------------------------------------------------

/// `("set_union" | "set_diff", [left, right]) => f1(*left, *right)`: two
/// `[k of 2]` reads after two `str::eq` calls. Refuted before the fix.
#[test]
fn the_or_pattern_arm_keeps_the_tested_length_across_the_str_compares() {
    let rows = rows("op_simple");
    expect_all_proved(&rows, 17, 2, "the arm tested `args.len() == 2` before the calls");
}

/// The same function under another name (a second dump of the shape).
#[test]
fn the_same_shape_under_another_name_proves_too() {
    let rows = rows("orpat_ok");
    expect_all_proved(&rows, 91, 2, "the arm tested `args.len() == 2` before the calls");
}

/// `tla_shapes_families::cvw::probe_admits_op` in miniature: the single-literal
/// or-pattern arm (line 8) and the one-element arm (line 10) proved before; the
/// four-literal arm (line 9) did not.
#[test]
fn the_full_probe_admits_op_shape_proves_every_arm() {
    let rows = rows("op");
    expect_all_proved(&rows, 8, 4, "each alternative binds both elements of a length-2 slice");
    expect_all_proved(&rows, 9, 2, "the four-literal arm tested `args.len() == 2`");
    expect_all_proved(&rows, 10, 1, "`[sets]` tested `args.len() == 1`");
}

/// CONTROL: a `&mut [i64]` parameter handed to a callee keeps its own length
/// (the callee can write elements, never the caller's fat pointer).
#[test]
fn a_mut_slice_parameter_keeps_its_length_across_a_call_that_receives_it() {
    let rows = rows("mut_slice_param_call");
    expect_all_proved(&rows, 84, 1, "`s.len() == 2` and no slot-write channel to `s`");
}

// ---------------------------------------------------------------------------
// COUNTERS: real panics, which must stay refuted.
// ---------------------------------------------------------------------------

/// `("set_union" | "set_diff", [_, _]) => args[2]`: index 2 of a length-2 slice.
#[test]
fn an_index_past_the_tested_length_still_refutes() {
    let rows = rows("orpat_oob");
    expect_refuted(&rows, 25, "`args[2]` with `args.len() == 2` panics");
}

/// `reseat(&mut s)` after `s.len() == 2`: the callee writes `s`'s slot.
#[test]
fn a_reseat_through_mut_borrow_after_the_check_still_refutes() {
    let rows = rows("reseat_after_check");
    expect_refuted(&rows, 38, "`reseat` makes `s` empty");
}

/// The same reseat through `&raw mut s`, taken before the check.
#[test]
fn a_reseat_through_raw_mut_after_the_check_still_refutes() {
    let rows = rows("reseat_raw_after_check");
    expect_refuted(&rows, 52, "`reseat_raw` makes `s` empty");
}

/// `p: &mut &[i64]`: the callee reseats the pointee `*p`.
#[test]
fn a_reseat_of_a_mut_parameters_pointee_still_refutes() {
    let rows = rows("param_pointee_reseat");
    expect_refuted(&rows, 61, "`reseat(p)` makes `*p` empty");
}

/// The or-pattern arm itself, then `reseat(&mut s)` before `s[1]`.
#[test]
fn a_reseat_inside_the_or_pattern_arm_still_refutes() {
    let rows = rows("pat_then_reseat");
    expect_refuted(&rows, 72, "`reseat` makes `s` empty after the arm matched");
}
