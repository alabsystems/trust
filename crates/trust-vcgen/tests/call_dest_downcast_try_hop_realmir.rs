//! REAL-MIR pins for D5-A-DOWNCAST-1 and D5-A-TRY-HOP-1: the D5-A
//! same-crate call-destination screen sees an `Option`-returning helper's
//! result through its downcast payload, its discriminant carrier and the `?`
//! operator.
//!
//! # What was wrong
//!
//! astream-agent `fork.rs:93` / `:107` (preview3, stage 1 `ed578e1a5`):
//!
//! ```text
//! fn index_in(records: &[R], at: u64) -> Option<usize> {
//!     usize::try_from(at).ok().filter(|&i| i < records.len())
//! }
//! pub fn swap(records: &[R], at: u64, r: R) -> Vec<R> {
//!     let mut out = records.to_vec();
//!     if let Some(i) = index_in(records, at) { out[i] = r; }   // FAILED
//!     out
//! }
//! ```
//!
//! The index is in range — `index_in` returns `Some(i)` only for
//! `i < records.len()`, and `to_vec` keeps that length (the Vec-length lane
//! already models it: `swap_direct` proves). No summary models `index_in`'s
//! return, so ay chose `Some(0)` beside `records__slice_len = 0`: a model of
//! the formula, not a run. The D5-A screen exists to hold exactly that, and
//! `index_in` was in its census, but the query names the result only as
//! `_5@1.0` (the `Some` payload, a DOWNCAST) and `__trust_mir__discr__5` (its
//! discriminant carrier); the screen matched `_5`, `_5.k` and `_5[k]` only. In
//! `try_swap` the `?` re-wraps the result through core's `Try::branch`
//! (`_4 = branch(move _5)`) and the query names only `_4@0.0`; nothing ties `_4`
//! to `_5`, so even the widened match could not see the dependence.
//!
//! Both rows are held (a fail-closed Unknown), not proved: proving them needs a
//! summary of `index_in` through `Option::filter` and its closure, which no
//! lane derives. The crate can state `ensures` on `index_in`; Trust must not
//! report a counterexample `index_in` can never produce.
//!
//! Fixtures: `tests/fixtures/d5_downcast_*_mir.json` are the compiler's own
//! extraction of [`tests/data/d5_downcast_try_hop.rs`], captured with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib --crate-name fx \
//!        -Ztrust-verify-profile=unix_hardened -Ztrust-policy=advisory \
//!        -Ztrust-dump=mir:<dir> crates/trust-vcgen/tests/data/d5_downcast_try_hop.rs
//! ```
//!
//! on Trust `main` stage 1 `ed578e1a5` (2026-10-09).
//!
//! # Mutation ledger (2026-10-10)
//!
//! ```text
//! mutant                                               tests that go red
//! `names_value` without `@` / the discriminant carrier  the_if_let_payload_*, the_question_mark_*
//! no `Try::branch` hop                                  the_question_mark_*
//! ```
use trust_types::{Terminator, VerifiableFunction, VerificationResult};
use trust_vcgen::{
    GENERIC_REFUTATION_HELD_PREFIX, GenericRefutationScope, LocalCallDestScreen, SummaryDatabase,
    VcgenContext,
};

#[path = "support/test_router.rs"]
mod test_router;

const SOLVER_STACK_BYTES: usize = 256 * 1024 * 1024;

fn load(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/fixtures/d5_downcast_{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

/// The census key of every call in `func` whose callee path ends in `::{suffix}`.
fn keys_of(func: &VerifiableFunction, suffix: &str) -> Vec<(u64, u32)> {
    func.body
        .blocks
        .iter()
        .filter_map(|block| match &block.terminator {
            Terminator::Call { func: callee, callee_identity: Some(identity), .. }
                if callee.ends_with(&format!("::{suffix}")) =>
            {
                Some((identity.stable_crate_id, identity.def_index))
            }
            _ => None,
        })
        .collect()
}

#[derive(Debug)]
struct Row {
    kind: String,
    line: u32,
    proved: bool,
    failed: bool,
    held: Option<String>,
}

/// Every slice / bounds row with ay's verdict and the screen's answer, the
/// census naming `keys`.
fn rows(name: &str, keys: Vec<(u64, u32)>) -> Vec<Row> {
    let func = load(name);
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let db = SummaryDatabase::new();
            let context = VcgenContext::for_function(func.def_path.clone())
                .with_local_call_dest_screen(LocalCallDestScreen::new(keys, &db));
            let (solver_vcs, preclassified) =
                trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
                    &func,
                    &db,
                    true,
                    &context,
                    &std::collections::HashSet::new(),
                );
            let scope = GenericRefutationScope::for_function_with_call_dests(
                &func,
                &solver_vcs,
                &preclassified,
                &context,
            );
            let router = test_router::deterministic_test_router();
            solver_vcs
                .iter()
                .filter(|vc| {
                    let kind = format!("{:?}", vc.kind);
                    kind.contains("SliceBoundsCheck") || kind.contains("BoundsCheck")
                })
                .map(|vc| {
                    let result = router
                        .verify_all(std::slice::from_ref(vc))
                        .into_iter()
                        .next()
                        .expect("one verdict")
                        .1;
                    Row {
                        kind: format!("{:?}", vc.kind),
                        line: vc.location.line_start,
                        proved: matches!(result, VerificationResult::Proved { .. }),
                        failed: matches!(result, VerificationResult::Failed { .. }),
                        held: scope.rejection_reason(vc),
                    }
                })
                .collect()
        })
        .expect("spawn")
        .join()
        .expect("generation thread")
}

/// Every ay-refuted row at `line` is held, naming `index_in`; there is one.
fn assert_all_refuted_rows_held(rows: &[Row], line: u32) {
    let refuted: Vec<&Row> = rows.iter().filter(|r| r.line == line && r.failed).collect();
    assert!(
        !refuted.is_empty(),
        "line {line}: ay must still refute (the screen is what holds it): {rows:#?}"
    );
    for row in refuted {
        let reason = row.held.as_deref().unwrap_or_else(|| {
            panic!("line {line}: a model over `index_in`'s free return must be held: {row:#?}")
        });
        assert!(reason.starts_with(GENERIC_REFUTATION_HELD_PREFIX), "{reason}");
        assert!(reason.contains("fx::index_in"), "the reason names the callee: {reason}");
    }
}

/// `if let Some(i) = index_in(records, at) { out[i] = r }` (fork.rs:93): the
/// query names the result as `_5@1.0` and `__trust_mir__discr__5`.
#[test]
fn the_if_let_payload_of_an_unmodeled_helper_is_held() {
    let func = load("swap");
    let keys = keys_of(&func, "index_in");
    assert_eq!(keys.len(), 1, "one call to `index_in`");
    // Control: without the census nothing holds the row, and ay refutes it.
    let control = rows("swap", Vec::new());
    assert!(control.iter().any(|r| r.line == 14 && r.failed), "{control:#?}");
    assert!(control.iter().all(|r| r.held.is_none()), "{control:#?}");
    assert_all_refuted_rows_held(&rows("swap", keys), 14);
}

/// `let i = index_in(records, at)?; out[i] = r` (fork.rs:107): the query names
/// only `branch`'s result `_4`, which core's `Try::branch` derives from `_5`.
#[test]
fn the_question_mark_result_of_an_unmodeled_helper_is_held() {
    let func = load("try_swap");
    let keys = keys_of(&func, "index_in");
    assert_eq!(keys.len(), 1, "one call to `index_in`");
    let control = rows("try_swap", Vec::new());
    assert!(control.iter().any(|r| r.line == 22 && r.failed), "{control:#?}");
    assert!(control.iter().all(|r| r.held.is_none()), "{control:#?}");
    assert_all_refuted_rows_held(&rows("try_swap", keys), 22);
}

/// COUNTER: `out[i]` with a caller-chosen `i` really panics; no screened call is
/// involved, so even a census that names `index_in` holds nothing.
#[test]
fn an_unguarded_parameter_index_keeps_its_refutation() {
    let keys = keys_of(&load("swap"), "index_in");
    let rows = rows("swap_bad", keys);
    let at: Vec<&Row> = rows.iter().filter(|r| r.line == 38).collect();
    assert!(at.iter().any(|r| r.failed), "`swap_bad(&[], 0, r)` panics: {rows:#?}");
    assert!(at.iter().all(|r| r.held.is_none()), "a genuine refutation is never held: {rows:#?}");
}

/// CONTROL: the Vec-length half is already modeled — the same store under a
/// direct `i < records.len()` guard proves.
#[test]
fn the_to_vec_length_half_is_modeled() {
    let rows = rows("swap_direct", Vec::new());
    let at: Vec<&Row> =
        rows.iter().filter(|r| r.line == 30 && r.kind == "SliceBoundsCheck").collect();
    assert!(!at.is_empty(), "{rows:#?}");
    assert!(at.iter().all(|r| r.proved), "`to_vec` keeps `records.len()`: {rows:#?}");
}
