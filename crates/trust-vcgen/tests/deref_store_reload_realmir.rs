//! REAL-MIR pins for KILLED-ENTRY-EXISTS-1: the hardened twin of an assert in a
//! block that STORES through `&mut` and reloads the same place keeps its entry
//! facts about the pre-store value, existentially renamed, instead of dropping
//! them.
//!
//! # The defect (measured on Trust `main` 20665862d7 and stage 1 `ed578e1a5`)
//!
//! `*count += 1; *count - 1` lowers to
//!
//! ```text
//! bb0: _2 = CheckedAdd(copy (*_1), 1); assert(!move (_2.1), Overflow(Add)) -> bb1
//! bb1: (*_1) = move (_2.0); _3 = copy (*_1); _4 = CheckedSub(copy _3, 1);
//!      assert(!move (_4.1), Overflow(Sub)) -> bb2
//! ```
//!
//! The per-statement `[overflow:sub]` row PROVES. Its `unix_hardened` twin
//! `mir_assert::Overflow(Sub)` was REFUTED with the model `_2.0#s0_0 = 0,
//! count*#s1_0 = 0`: bb1's entry facts `_2.0 == count* + 1` and `0 <= count* <=
//! MAX` mention `count*`, which bb1 writes, and `block_entry_fact_kill` dropped
//! them whole, so the stored value `_2.0` floated free. The twin now keeps them
//! with `count*` renamed to a fresh name (`__trust_kx1_count*`), the value
//! `count*` held at bb1's entry — see `BlockEntryFactKill::survive_or_quantify`
//! for the soundness argument. Preview3 measured the shape on trust-ir-conformance
//! (`CharCarriers::of`, `count += 1; (id, count - 1)` through a closure's captured
//! `&mut`).
//!
//! Each counter-program below is a real defect and must stay refuted, with a
//! model that is an execution that really underflows: a fact about the pre-store
//! value must never reach the value read after a store.
//!
//! # Fixtures
//!
//! `tests/fixtures/deref_store_reload_*_mir.json` are the compiler's own
//! extraction of [`tests/data/deref_store_reload.rs`], captured with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -Ztrust-verify=on \
//!        -Ztrust-verify-profile=unix_hardened -Ztrust-verify-level=2 \
//!        -Ztrust-policy=advisory -Ztrust-dump=mir:<dir> deref_store_reload.rs
//! ```
//!
//! on Trust stage 1 `ed578e1a5` (2026-10-10); only the `span.file` fields were
//! rewritten to the repo-relative source path.
//!
//! # Mutation ledger (2026-10-10)
//!
//! ```text
//! mutant                                              tests that go red
//! hardened kill back to the drop (`survives` filter)  bump_reload_twin_proves
//! killed fact kept WITHOUT the rename (unsound)       guard_then_zero_still_refutes, bump_then_sub_two_still_refutes,
//!                                                     bump_reload_twin_proves (no fresh name in the formula)
//! ```
//!
//! Under the unsound mutant the twins of `guard_then_zero` and `bump_then_sub_two`
//! PROVE: the version rename re-spells the kept `count*` as the post-store token, so
//! a fact about the entry value constrains the value the block wrote.
//! `bump_then_overwrite` stays refuted under both mutants.
use std::collections::HashSet;

use trust_types::{
    BlockId, Counterexample, CounterexampleValue, VerifiableFunction, VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

/// Real extracted MIR carries deep recursive `Formula` walks.
const SOLVER_STACK_BYTES: usize = 256 * 1024 * 1024;

const PRIMARY_SUB: &str = "ArithmeticOverflow { op: Sub";
const TWIN_SUB: &str = "mir_assert::Overflow(Sub)";

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/deref_store_reload_{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

#[derive(Debug, Clone)]
struct Row {
    kind: String,
    line: u32,
    formula: String,
    result: VerificationResult,
}

/// Every row of fixture `name`, hardened profile ON, through the entry the
/// compiler calls, decided by the deterministic in-process `ay` router.
fn rows(name: &str) -> Vec<Row> {
    let func = load(name);
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let context = trust_vcgen::VcgenContext::for_function(func.def_path.clone());
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
                    formula: format!("{:?}", vc.formula),
                    result,
                })
                .collect()
        })
        .expect("spawn")
        .join()
        .expect("generation thread")
}

/// The single row at `line` whose kind contains `needle`.
fn one<'a>(rows: &'a [Row], line: u32, needle: &str) -> &'a Row {
    let hits: Vec<&Row> =
        rows.iter().filter(|r| r.line == line && r.kind.contains(needle)).collect();
    assert_eq!(hits.len(), 1, "line {line}: expected one `{needle}` row; all rows: {rows:#?}");
    hits[0]
}

fn int_named(cex: &Counterexample, name: &str) -> Option<i128> {
    cex.assignments.iter().find_map(|(n, value)| match value {
        CounterexampleValue::Int(v) if n == name => Some(*v),
        CounterexampleValue::Uint(v) if n == name => i128::try_from(*v).ok(),
        _ => None,
    })
}

/// `row` is refuted, and `real` accepts its model as an execution that underflows.
fn assert_refuted(row: &Row, real: impl Fn(&Counterexample) -> bool, why: &str) {
    match &row.result {
        VerificationResult::Failed { counterexample, .. } => {
            let cex = counterexample.as_ref().expect("a refutation must carry its model");
            assert!(
                real(cex),
                "{why}: the model must be a real underflow; got {cex:?}\nrow: {row:#?}"
            );
        }
        other => panic!("{why}: must stay REFUTED; got {other:?}\nrow: {row:#?}"),
    }
}

/// The model names the reloaded value `reload` (the Sub's minuend local) and it
/// is below `bound`, so the subtraction really underflows.
fn reload_below(reload: &'static str, bound: i128) -> impl Fn(&Counterexample) -> bool {
    move |cex| int_named(cex, reload).is_some_and(|v| v < bound)
}

#[test]
fn bump_reload_twin_proves() {
    let rows = rows("bump");
    let primary = one(&rows, 11, PRIMARY_SUB);
    assert!(
        matches!(primary.result, VerificationResult::Proved { .. }),
        "the per-statement row proves `old + 1 - 1`: {primary:#?}"
    );
    let twin = one(&rows, 11, TWIN_SUB);
    assert!(
        matches!(twin.result, VerificationResult::Proved { .. }),
        "the hardened twin states the same operation and must keep bb1's entry fact \
         `_2.0 == old + 1` (renamed, not dropped): {twin:#?}"
    );
    assert!(
        twin.formula.contains("__trust_kx1_count*"),
        "the twin carries the killed fact over the fresh entry name: {}",
        twin.formula
    );
}

#[test]
fn bump_then_sub_two_still_refutes() {
    let rows = rows("bump_then_sub_two");
    for needle in [PRIMARY_SUB, TWIN_SUB] {
        assert_refuted(
            one(&rows, 17, needle),
            reload_below("_3", 2),
            "`old + 1 - 2` underflows at old = 0",
        );
    }
}

#[test]
fn bump_then_overwrite_still_refutes() {
    let rows = rows("bump_then_overwrite");
    for needle in [PRIMARY_SUB, TWIN_SUB] {
        assert_refuted(
            one(&rows, 26, needle),
            reload_below("_4", 1),
            "the reload reads the second store `v`, which may be 0; a fact about `old + 1` \
             must not reach it",
        );
    }
}

#[test]
fn guard_then_zero_still_refutes() {
    let rows = rows("guard_then_zero");
    for needle in [PRIMARY_SUB, TWIN_SUB] {
        assert_refuted(
            one(&rows, 33, needle),
            reload_below("_4", 1),
            "the guard `*count > 0` tests the value before `*count = 0`; the reload is 0",
        );
    }
}
