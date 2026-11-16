//! REAL-MIR pins for TRUST-KI-1015-1, the loop-index shape: a correct `for i in
//! START..END` loop that reads `w[i - k]` was reported FAILED by its `unix_hardened`
//! twins while the per-statement rows of the same asserts PROVED. The same holds of
//! the two other sources of a loop-yield fact the twin now carries: an `enumerate`
//! index and an adapter closure's item under the `ADAPTER_YIELD` premise.
//!
//! # The defect (measured 2026-10-15)
//!
//! aterm-digest `Sha256::compress` runs `for i in 16..64 { .. w[i - 15] .. w[i - 2]
//! .. w[i - 16] .. }` over `w: [u32; 64]`. On the channel `b58a105dde` (raw `trustc`,
//! `-Ztrust-verify-profile=unix_hardened`) the `[bounds]` row of `w[i - 15]` and its
//! `mir_assert::BoundsCheck` twin were FAILED (ay-in-process, `i = 79`), and the
//! `mir_assert::Overflow(Sub)` twin of `i - 15` was FAILED (`i = 0`) while the plain
//! `[overflow:sub]` row of the SAME subtraction was PROVED: one assert both proved
//! and refuted. Neither counterexample is reachable: `i` ranges over `16..64`.
//!
//! The fact that makes these rows safe is the range-yield fact `16 <= i < 64`
//! (`generate::iterator_yield::build_range_yield_guard_map`). It was missing from the
//! refuting VCs in two places:
//!
//! * the per-statement `[bounds]` row: the map attached the fact only to blocks that
//!   NAME the payload `i`, and the bounds assert's block reads `i - 15`'s temp. Fixed
//!   on main by 3f8dddbe50 (`locals_derived_from`), which is not in `b58a105dde`;
//! * the hardened twins (`hardened::append_assert_panic_vcs`): the twin lane never
//!   conjoined the range or enumerate yield map, only skipped a `BoundsCheck` twin
//!   whose index IS the payload. `w[i - 15]`'s index is a temp, so its twin and the
//!   `Overflow(Sub)` twin of `i - 15` reached ay with `i` equal to the iterator's
//!   loop-head havoc and no bound. Still so on main `edbb3f3009`; fixed with this file
//!   (`generate::LoopYieldGuards`).
//!
//! # Fixtures
//!
//! `tests/fixtures/loop_index_yield_twins/<fn>.json` are the compiler's own extraction
//! of [`tests/data/loop_index_yield_twins.rs`], captured with the channel `trustc`
//! (`b58a105dde`); `<fn>_closure.json` is `<fn>::{closure#0}`:
//!
//! ```text
//! trustc --crate-type lib --crate-name repro --edition 2024 --emit=metadata -C debuginfo=2 \
//!        -Ztrust-verify-level=2 -Ztrust-policy=advisory -Ztrust-verify-profile=unix_hardened \
//!        -Ztrust-dump=mir:<dir> loop_index_yield_twins.rs
//! ```
//!
//! Only the `span.file` fields were rewritten to the repo-relative source path. The
//! `enum_*` and `for_each_*` fixtures come from a second capture of the extended data
//! file with the same command; it reproduced the ten earlier fixtures byte for byte.
//! Every row goes through the entry the compiler calls (hardened profile ON) and is
//! decided by the deterministic in-process `ay` router, the `ay-in-process` lane that
//! refuted them. A closure body is handed the `ADAPTER_YIELD` premise the compiler
//! hands it ([`for_each_premise`]); the channel `trustc` disclosed that premise on
//! each captured closure.
//!
//! # Falsification control (2026-10-15)
//!
//! With the twin's yield conjunction removed (`hardened.rs`, `loop_yield_guards
//! .facts_at`), `correct_loops_prove_on_both_twins` and
//! `the_safe_twin_of_a_wrong_program_is_not_refuted` go red and every
//! `..._stays_refuted` test stays green: before the fix the correct programs were
//! refuted, after it they prove, and the wrong ones are refuted either way.
//!
//! The same control for the enumerate and `ADAPTER_YIELD` tests:
//! `correct_enumerate_loops_prove_on_both_twins`,
//! `correct_for_each_closures_prove_on_both_twins` and
//! `the_safe_twin_of_a_wrong_enumerate_or_closure_is_not_refuted` go red, naming
//! every pinned twin (each pair's per-statement row stays PROVED), and
//! `wrong_enumerate_loops_stay_refuted` and `wrong_for_each_closures_stay_refuted`
//! stay green.
use std::collections::HashSet;

use trust_types::{BlockId, VerifiableFunction, VerificationResult};
use trust_vcgen::{AdapterYieldFact, ClosureAdapterPremise};

#[path = "support/test_router.rs"]
mod test_router;

/// Real extracted MIR carries deep recursive `Formula` walks.
const SOLVER_STACK_BYTES: usize = 256 * 1024 * 1024;

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/loop_index_yield_twins/{name}.json", env!("CARGO_MANIFEST_DIR"));
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
    /// `format!("{:?}", vc.kind)`: the kind and, for a hardened row, its callee label.
    kind: String,
    line: u32,
    col: u32,
    verdict: Verdict,
    result: String,
}

/// Every row of fixture `name`, hardened profile ON.
fn rows(name: &str) -> Vec<Row> {
    rows_in(name, Vec::new())
}

/// Every row of fixture `name`, hardened profile ON, with the compiler's
/// `ADAPTER_YIELD` `premises` installed for it (none for a free function).
fn rows_in(name: &str, premises: Vec<ClosureAdapterPremise>) -> Vec<Row> {
    let func = load(name);
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let context = trust_vcgen::VcgenContext::for_function(func.def_path.clone())
                .with_adapter_yield_premises(premises);
            let db = trust_vcgen::SummaryDatabase::new();
            let ops: HashSet<(BlockId, usize)> = HashSet::new();
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
                    col: vc.location.col_start,
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

const INDEX: &str = "IndexOutOfBounds";
const SLICE: &str = "SliceBoundsCheck";
const SUB: &str = "ArithmeticOverflow { op: Sub";
const TWIN_BOUNDS: &str = "mir_assert::BoundsCheck";
const TWIN_SUB: &str = "mir_assert::Overflow(Sub)";

/// Exactly one row at `line:col` matches `needle`, and it has `want`.
fn expect(rows: &[Row], at: (u32, u32), needle: &str, want: Verdict, why: &str) {
    let hits: Vec<&Row> =
        rows.iter().filter(|r| (r.line, r.col) == at && r.kind.contains(needle)).collect();
    assert_eq!(
        hits.len(),
        1,
        "{}:{}: expected one `{needle}` row; all rows: {rows:#?}",
        at.0,
        at.1
    );
    assert_eq!(
        hits[0].verdict, want,
        "{}:{} `{needle}`: {why}\nresult: {}\nrow: {:#?}",
        at.0, at.1, hits[0].result, hits[0]
    );
}

/// An index row (`bounds`), its `BoundsCheck` twin, the subtraction computing the
/// index (`sub`, one column right) and its `Overflow(Sub)` twin: `w[i - k]`.
struct IndexMinus {
    at: (u32, u32),
    bounds: &'static str,
}

impl IndexMinus {
    fn sub_at(&self) -> (u32, u32) {
        (self.at.0, self.at.1 + 2)
    }
}

// ─── correct programs: every row of `w[i - k]` proves, twins included ──────────

/// `sum_lag15` (`for i in 16..64 { w[i - 15] }`), `schedule` (the SHA-256 message
/// schedule of aterm-digest `Sha256::compress`) and `lag2_slice` (`for i in
/// 2..v.len() { v[i - 2] }`). Before the fix the per-statement rows proved and the
/// twins of the FIRST `w[i - k]` of each statement were refuted (`i = 0`, `i = 79`).
#[test]
fn correct_loops_prove_on_both_twins() {
    let cases: &[(&str, &[IndexMinus])] = &[
        ("sum_lag15", &[IndexMinus { at: (11, 31), bounds: INDEX }]),
        (
            "schedule",
            &[
                IndexMinus { at: (18, 17), bounds: INDEX },
                IndexMinus { at: (18, 46), bounds: INDEX },
                IndexMinus { at: (19, 17), bounds: INDEX },
                IndexMinus { at: (19, 46), bounds: INDEX },
                IndexMinus { at: (20, 15), bounds: INDEX },
                IndexMinus { at: (20, 55), bounds: INDEX },
            ],
        ),
        ("lag2_slice", &[IndexMinus { at: (27, 31), bounds: SLICE }]),
    ];
    for (name, sites) in cases {
        let rows = rows(name);
        for site in *sites {
            let why = "the index and the subtraction are in range for every i the loop yields";
            expect(&rows, site.at, site.bounds, Verdict::Proved, why);
            expect(&rows, site.at, TWIN_BOUNDS, Verdict::Proved, why);
            expect(&rows, site.sub_at(), SUB, Verdict::Proved, why);
            expect(&rows, site.sub_at(), TWIN_SUB, Verdict::Proved, why);
        }
        // No other row of a correct program is refuted either.
        let refuted: Vec<&Row> = rows.iter().filter(|r| r.verdict == Verdict::Failed).collect();
        assert!(refuted.is_empty(), "{name}: a correct program has a refuted row: {refuted:#?}");
    }
}

// ─── wrong programs: the panicking row stays refuted in BOTH lanes ─────────────

/// The real defect of each wrong program, on the per-statement row and on its twin.
fn expect_refuted_both(name: &str, at: (u32, u32), primary: &str, twin: &str, why: &str) {
    let rows = rows(name);
    expect(&rows, at, primary, Verdict::Failed, why);
    expect(&rows, at, twin, Verdict::Failed, why);
}

/// Off by one: `for i in 15..64 { w[i - 16] }` underflows at `i = 15`.
#[test]
fn an_off_by_one_subtraction_stays_refuted() {
    expect_refuted_both("off_by_one_sub", (38, 33), SUB, TWIN_SUB, "`i - 16` underflows at i = 15");
}

/// Wrong range: `for i in 0..64 { w[i - 15] }` underflows at `i = 0`.
#[test]
fn a_range_from_zero_stays_refuted() {
    expect_refuted_both("range_from_zero", (47, 33), SUB, TWIN_SUB, "`i - 15` underflows at i = 0");
}

/// Wrong end: `for i in 16..66 { w[i - 1] }` reads `w[64]` at `i = 65`.
#[test]
fn a_range_past_the_end_stays_refuted() {
    expect_refuted_both("range_past_end", (56, 31), INDEX, TWIN_BOUNDS, "i = 65 reads w[64]");
}

/// Wrong width: `for i in 16..64 { w[i - 15] }` over `[u32; 32]` reads `w[32]` at `i = 47`.
#[test]
fn a_narrower_array_stays_refuted() {
    expect_refuted_both("narrow_array", (65, 31), INDEX, TWIN_BOUNDS, "i = 47 reads w[32] of 32");
}

/// The guard removed: `for i in lo..64 { w[i - 15] }` underflows at `lo = 0`. The
/// yield fact is `lo <= i < 64` and says nothing about `lo`.
#[test]
fn a_callers_start_stays_refuted() {
    expect_refuted_both("caller_start", (74, 33), SUB, TWIN_SUB, "`i - 15` underflows at lo = 0");
}

/// `for mut i in 16..64 { i = n; w[i - 15] }`: the payload is rebound, so it carries
/// no yield fact (`payload_carries_global_fact`), and both defects stay refuted.
#[test]
fn a_rebound_payload_stays_refuted() {
    expect_refuted_both("rebound_payload", (84, 33), SUB, TWIN_SUB, "`n - 15` underflows at n = 0");
    expect_refuted_both("rebound_payload", (84, 31), INDEX, TWIN_BOUNDS, "n = 100 reads w[85]");
}

/// The slice twin of the off-by-one: `for i in 1..v.len() { v[i - 2] }` underflows at
/// `i = 1`.
#[test]
fn a_slice_off_by_one_stays_refuted() {
    expect_refuted_both(
        "lag2_slice_from_one",
        (93, 33),
        SUB,
        TWIN_SUB,
        "`i - 2` underflows at i = 1",
    );
}

/// In each wrong program, the twin of the assert that CANNOT fail is no longer
/// refuted: `w[i - 16]` once `i - 16` did not underflow, `w[i - 15]` under `0..64` or
/// `lo..64`, `i - 1` under `16..66`, `i - 15` under `16..64` over a narrow array,
/// `v[i - 2]` once `i - 2` did not underflow. Their per-statement rows already proved.
#[test]
fn the_safe_twin_of_a_wrong_program_is_not_refuted() {
    let cases: &[(&str, (u32, u32), &str, &str)] = &[
        ("off_by_one_sub", (38, 31), INDEX, TWIN_BOUNDS),
        ("range_from_zero", (47, 31), INDEX, TWIN_BOUNDS),
        ("range_past_end", (56, 33), SUB, TWIN_SUB),
        ("narrow_array", (65, 33), SUB, TWIN_SUB),
        ("caller_start", (74, 31), INDEX, TWIN_BOUNDS),
        ("lag2_slice_from_one", (93, 31), SLICE, TWIN_BOUNDS),
    ];
    for (name, at, primary, twin) in cases {
        let rows = rows(name);
        let why = "this assert cannot fail for any value the loop yields";
        expect(&rows, *at, primary, Verdict::Proved, why);
        expect(&rows, *at, twin, Verdict::Proved, why);
    }
}

// ─── the enumerate half and the ADAPTER_YIELD premise ──────────────────────────
//
// `LoopYieldGuards::facts_at` is the range map, then the enumerate map
// (`for (i, x) in s.iter().enumerate()` => `0 <= i < s.len()`); the range map also
// carries a closure body's `ADAPTER_YIELD` integer premise (`(16..64).for_each(|i|
// ..)` => `16 <= i < 64`). The tests above pin the range map on a `for` loop. These
// pin the other two sources, one row and its twin at a time.

/// A per-statement row and its `unix_hardened` twin on the same assert.
struct Pair {
    at: (u32, u32),
    primary: &'static str,
    twin: &'static str,
}

/// One line per row of `pair` (the row, then the twin) that is not `want`, or is
/// not exactly one row. Collected, not asserted one by one, so a red run names
/// every site that moved.
fn mismatches(name: &str, rows: &[Row], pair: &Pair, want: Verdict) -> Vec<String> {
    let mut out = Vec::new();
    for needle in [pair.primary, pair.twin] {
        let hits: Vec<&Row> =
            rows.iter().filter(|r| (r.line, r.col) == pair.at && r.kind.contains(needle)).collect();
        match hits.as_slice() {
            [row] if row.verdict == want => {}
            [row] => out.push(format!(
                "{name} {}:{} `{needle}`: {:?}, expected {want:?}: {}",
                pair.at.0, pair.at.1, row.verdict, row.result
            )),
            _ => out.push(format!(
                "{name} {}:{} `{needle}`: {} rows, expected one",
                pair.at.0,
                pair.at.1,
                hits.len()
            )),
        }
    }
    out
}

/// The premise the compiler hands `(START..END).for_each(|i| ..)`'s closure body
/// (`rustc_mir_transform::trust_verify::adapter_yield::derive_premise`: the item is
/// parameter `_2`, `_1` is the environment). The channel `trustc` disclosed exactly
/// this premise on every closure captured here (`modeled_facts`: "core
/// `Iterator::for_each` over `16..64` ... item parameter `_2` has value in [16, 64)").
fn for_each_premise(start: i128, end: i128) -> Vec<ClosureAdapterPremise> {
    vec![ClosureAdapterPremise {
        item_local: 2,
        item_deref: false,
        item_fields: Vec::new(),
        fact: AdapterYieldFact::IntHalfOpen { start, end },
        adapter: "Iterator::for_each".to_string(),
        receiver: format!("{start}..{end}"),
    }]
}

/// A fixture, the `ADAPTER_YIELD` premises the compiler hands it, and its pairs.
type Case<'a> = (&'a str, Vec<ClosureAdapterPremise>, &'a [Pair]);

/// Every pair of every case is `want`. With `correct`, no other row of the
/// function is refuted either.
fn expect_pairs(cases: &[Case<'_>], want: Verdict, correct: bool, why: &str) {
    let mut bad = Vec::new();
    for (name, premises, pairs) in cases {
        let rows = rows_in(name, premises.clone());
        for pair in *pairs {
            bad.extend(mismatches(name, &rows, pair, want));
        }
        if correct {
            bad.extend(rows.iter().filter(|r| r.verdict == Verdict::Failed).map(|r| {
                format!("{name} {}:{} `{}`: refuted: {}", r.line, r.col, r.kind, r.result)
            }));
        }
    }
    assert!(bad.is_empty(), "{why}:\n{}", bad.join("\n"));
}

/// `enum_lag3` (`for (i, x) in v.iter().enumerate() { if i >= 3 { v[i - 3] } }`),
/// `enum_lag15` (the same over `w: &[u32; 64]` with `w[i - 15]`) and `enum_mirror`
/// (`w[63 - i]`). Each pair's twin needs `i < len`, the enumerate fact; the
/// subtraction under `i >= k` is discharged by its dominating guard and is covered
/// by the no-refuted-row check.
#[test]
fn correct_enumerate_loops_prove_on_both_twins() {
    expect_pairs(
        &[
            ("enum_lag3", Vec::new(), &[Pair { at: (106, 35), primary: SLICE, twin: TWIN_BOUNDS }]),
            (
                "enum_lag15",
                Vec::new(),
                &[Pair { at: (116, 35), primary: INDEX, twin: TWIN_BOUNDS }],
            ),
            ("enum_mirror", Vec::new(), &[Pair { at: (125, 33), primary: SUB, twin: TWIN_SUB }]),
        ],
        Verdict::Proved,
        true,
        "the index is below the length the enumerate runs over",
    );
}

/// `(16..64).for_each(|i| acc += w[i - 15])` and `w[i - 16]`: the closure body's
/// rows prove only from the `ADAPTER_YIELD` premise `16 <= i < 64`, the twins too.
#[test]
fn correct_for_each_closures_prove_on_both_twins() {
    let sites = |line| {
        [
            Pair { at: (line, 31), primary: INDEX, twin: TWIN_BOUNDS },
            Pair { at: (line, 33), primary: SUB, twin: TWIN_SUB },
        ]
    };
    let (lag15, lag16) = (sites(178), sites(186));
    expect_pairs(
        &[
            ("for_each_lag15_closure", for_each_premise(16, 64), &lag15),
            ("for_each_lag16_closure", for_each_premise(16, 64), &lag16),
        ],
        Verdict::Proved,
        true,
        "`i - k` and `w[i - k]` are in range for every item `16..64` yields",
    );
}

/// The real defect of each wrong enumerate program stays FAILED on the row and on
/// its twin: a guard off by one (`i >= 2`, `v[i - 3]`: `i - 3` underflows at
/// `i = 2`), a wider array (`63 - i` underflows at `i = 64` of 65), the mirror off
/// by one (`w[64 - i]` reads `w[64]` at `i = 0`), and the wrong slice (`b[i - 3]`
/// past a shorter `b`).
#[test]
fn wrong_enumerate_loops_stay_refuted() {
    expect_pairs(
        &[
            (
                "enum_lag3_guard_off_by_one",
                Vec::new(),
                &[Pair { at: (137, 37), primary: SUB, twin: TWIN_SUB }],
            ),
            (
                "enum_mirror_wide",
                Vec::new(),
                &[Pair { at: (147, 33), primary: SUB, twin: TWIN_SUB }],
            ),
            (
                "enum_mirror_past",
                Vec::new(),
                &[Pair { at: (156, 31), primary: INDEX, twin: TWIN_BOUNDS }],
            ),
            (
                "enum_other_lag",
                Vec::new(),
                &[Pair { at: (166, 35), primary: SLICE, twin: TWIN_BOUNDS }],
            ),
        ],
        Verdict::Failed,
        false,
        "a reachable panic must stay refuted on the row and on its twin",
    );
}

/// The real defect of each wrong closure stays FAILED on the row and on its twin
/// under the compiler's premise: `w[i - 17]` underflows at `i = 16`; `16..66`
/// reads `w[64]` at `i = 65`; `[u32; 32]` is read at 32 when `i = 47`.
#[test]
fn wrong_for_each_closures_stay_refuted() {
    expect_pairs(
        &[
            (
                "for_each_lag17_closure",
                for_each_premise(16, 64),
                &[Pair { at: (197, 33), primary: SUB, twin: TWIN_SUB }],
            ),
            (
                "for_each_past_end_closure",
                for_each_premise(16, 66),
                &[Pair { at: (206, 31), primary: INDEX, twin: TWIN_BOUNDS }],
            ),
            (
                "for_each_narrow_closure",
                for_each_premise(16, 64),
                &[Pair { at: (215, 31), primary: INDEX, twin: TWIN_BOUNDS }],
            ),
        ],
        Verdict::Failed,
        false,
        "a reachable panic must stay refuted on the row and on its twin",
    );
}

/// In those wrong programs, the assert that CANNOT fail proves on its twin too:
/// `v[i - 3]` once `i - 3` did not underflow (`i < v.len()`), `64 - i` (`i < 64`),
/// `w[i - 17]` once `i - 17` did not underflow, `i - 1` under `16..66`, `i - 15`
/// under `16..64`.
#[test]
fn the_safe_twin_of_a_wrong_enumerate_or_closure_is_not_refuted() {
    let cases: &[Case<'_>] = &[
        (
            "enum_lag3_guard_off_by_one",
            Vec::new(),
            &[Pair { at: (137, 35), primary: SLICE, twin: TWIN_BOUNDS }],
        ),
        ("enum_mirror_past", Vec::new(), &[Pair { at: (156, 33), primary: SUB, twin: TWIN_SUB }]),
        (
            "for_each_lag17_closure",
            for_each_premise(16, 64),
            &[Pair { at: (197, 31), primary: INDEX, twin: TWIN_BOUNDS }],
        ),
        (
            "for_each_past_end_closure",
            for_each_premise(16, 66),
            &[Pair { at: (206, 33), primary: SUB, twin: TWIN_SUB }],
        ),
        (
            "for_each_narrow_closure",
            for_each_premise(16, 64),
            &[Pair { at: (215, 33), primary: SUB, twin: TWIN_SUB }],
        ),
    ];
    expect_pairs(
        cases,
        Verdict::Proved,
        false,
        "this assert cannot fail for any value the loop yields",
    );
}
