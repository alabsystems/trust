//! Regression gate for the referent-fold hang found by the aterm gate's Trust
//! advisory lane on 2026-09-27: `targo trust check -p aterm-census --lib`
//! (trustc trust-6606d3bd) spent >90 CPU-minutes in one `aterm-census` body
//! inside `trust_vcgen`'s referent fold (`resolve_referent_guarded` ->
//! `referent_fold::is_stable` -> `walk_states` -> `written_place_rebinds` ->
//! a nested `resolve_referent` -> ...), a VC-generation pass that polled no
//! budget, so the 120 s per-function budget never bounded it.
//!
//! # Fixtures — real compiler dumps, not synthetic MIR
//!
//! Both are the `VerifiableFunction` a real trustc extracted with
//! `-Ztrust-dump=mir:dump` at the aterm gate's dev-profile flags
//!
//! ```text
//! trustc --crate-type lib --edition 2024 --crate-name <crate> \
//!        -Ztrust-verify=on -Ztrust-policy=advisory \
//!        -C opt-level=2 -C debug-assertions=on -C overflow-checks=on \
//!        -C debuginfo=line-tables-only --cfg clean_islands \
//!        -Ztrust-dump=mir:dump src/lib.rs
//! ```
//!
//! whitespace-compacted (content identical to the dump), except one change.
//! `tarjan_sccs_o2da_t6606.json`'s sysroot span files were recorded under the
//! extracting machine's home directory. They are rewritten to `<home>/...`,
//! keeping the tail (`.../library/<crate>/src/...`), which is what
//! `scripts/check_fixture_span_paths.py` requires. The rewrite is one-to-one
//! and keeps the file strings' order. No verdict reads a span's path: trusted-std
//! provenance comes from `TrustedStdSourceFiles`, which this test does not
//! install, so the pins below are unchanged.
//!
//! The fixtures are NOT in `tests/fixtures/` itself on purpose: the fold's own unit tests
//! (`referent_fold::fold_cost_fix`) compare every fixture there against the
//! test-only reference walk, which is the pre-2026-09-30 computation and is
//! exponential on exactly these bodies.
//!
//! ## `census_fold/tarjan_sccs_o2da_t6606.json`
//!
//! `aterm_census::lock_order::tarjan_sccs` (aterm 1cc89e9380,
//! `crates/aterm-census/src/lock_order.rs`), extracted by trust-6606d3bd.
//!
//! At -O2 that trustc ran the MIR inliner under verification, so the body holds
//! `Vec::index_mut` inlined into `&mut (*slice_ptr)[v]` reborrows: `index[v]`,
//! `low[v]` and `on_stack[v]` stored through eight raw/reborrowed pointers in
//! one loop, each pointer's region storing through the others. (Trust main
//! since f7c8bd778f runs the -O0 MIR pipeline in a verifying session, which
//! hides this shape at the default flags; `-Zmir-opt-level=2` restores it, and
//! the fold is reachable from any body of this shape however it is spelled.)
//!
//! Measured 2026-09-30 on this exact dump with the release
//! `vcgen_budget_realmir` harness (`profile_env_dir`):
//!
//! * trust main 7eddcd160b's fold: still running at the 600 s cap; a `sample`
//!   of it is 100% referent fold (`resolve_referent_guarded` / `is_stable` /
//!   `walk_states` / `written_place_rebinds` / `guards_rebound_by_terminator`).
//!   Verifying `aterm-census` with trust main 07091c92c1 at the gate's flags
//!   plus `-Zmir-opt-level=2` sat in this one function from t=600 s to the
//!   3600 s cap.
//! * the fixed fold: 0.18 s for the whole generation — 23 walks, 2 472 walk
//!   steps, 16 830 statement visits, 0 nested resolutions, 151 certified
//!   memo hits, 400 outcome-enumeration runs deciding 287 stores, 1 index.
//!
//! ## `census_fold/inflater_pump_o2da_db18f1e.json`
//!
//! `aterm_codec::inflate::stream::Inflater::pump` (aterm 0b4c7f8e20,
//! `crates/aterm-codec/src/inflate/stream.rs:176`), extracted by trust main
//! db18f1ea11 itself — the -O0 MIR pipeline, i.e. the shape the gate's
//! DEFAULT flags still produce after f7c8bd778f: 129 blocks, 27 stores through
//! a pointer.
//!
//! Measured 2026-10-02:
//!
//! * trust main db18f1ea11 verifying `aterm-codec` at the gate's flags with the
//!   DEFAULT 120 s budget reached this body by t=900 s and was still in it at
//!   the 1500 s cap; `sample` at t=900/1200/1500 s put 3603/3604, 3557/3557 and
//!   3538/3538 of the rustc thread's samples in `resolve_referent_guarded` ->
//!   `referent_fold::walk_states`. The fold was live on main at the default
//!   flags, not only under `-Zmir-opt-level=2`.
//! * the fixed compiler verifies the whole crate in 806 s at the same flags
//!   and budget; on this dump the fixed fold generates in about 2 s (debug
//!   test build) — 11 walks, 1 411 walk steps, 6 439 statement visits, 0
//!   nested resolutions, 58 certified memo hits, 119 outcome-enumeration runs
//!   deciding 330 stores, 1 index.
//!
//! # What is pinned (per fixture)
//!
//! 1. **The compiler's own checkpoint.** Generation runs under the exact
//!    ambient budget `trust_verify.rs` installs per function (120 000 ms /
//!    64 000 000 steps — the `-Ztrust-verify-function-budget-*` defaults) and
//!    must leave `verify_budget::exhausted_readonly()` false, which is precisely
//!    the test `preprocessing_budget_exceeded` applies. The STEP half is
//!    deterministic: every fold poll charges one step, so a fold that went
//!    exponential again spends the 64M steps and fails here — it does not hang
//!    and it does not depend on the machine's load.
//! 2. **Deterministic fold work bounds** (`AnalysisMemoStats::fold_*`), with
//!    a wide margin over the measurements above and orders of magnitude under
//!    what the unfixed fold does on these bodies.
//! 3. **The obligation inventory** each body produces, so a "speedup" that
//!    drops or duplicates obligations is caught. The fold changes cost, never
//!    an answer (`fold_cost_fix::the_fold_shortcuts_and_memo_change_no_resolution`
//!    proves that against the reference walk on every fixture it can afford);
//!    a pin change caused by an unrelated VC-generation change is expected and
//!    is recorded here.
//!
//! The memo statistics and the budget are thread-local, so the two tests may
//! run in parallel.

use std::time::{Duration, Instant};

use trust_types::VerifiableFunction;
use trust_vcgen as vcgen;

/// `-Ztrust-verify-function-budget-ms` default (`options.rs`).
const COMPILER_BUDGET_MS: u64 = 120_000;
/// `-Ztrust-verify-function-budget-steps` default (`options.rs`).
const COMPILER_BUDGET_STEPS: u64 = 64_000_000;

fn load(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/fixtures/census_fold/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture deserializes as a VerifiableFunction")
}

/// `(blocks, statements, locals)` and the number of stores through a pointer:
/// the shape the hang needed, so the pins are not vacuous.
fn shape(func: &VerifiableFunction) -> ((u64, u64, u64), usize) {
    let blocks = func.body.blocks.len() as u64;
    let stmts: u64 = func.body.blocks.iter().map(|b| b.stmts.len() as u64).sum();
    let locals = func.body.locals.len() as u64;
    let deref_stores = func
        .body
        .blocks
        .iter()
        .flat_map(|b| &b.stmts)
        .filter(|s| {
            matches!(s, trust_types::Statement::Assign { place, .. }
                if matches!(place.projections.first(), Some(trust_types::Projection::Deref)))
        })
        .count();
    ((blocks, stmts, locals), deref_stores)
}

struct Generated {
    solver_vcs: usize,
    discharged: usize,
    /// `verify_budget::exhausted_readonly()`, read while the budget is installed.
    exhausted: bool,
    stats: vcgen::AnalysisMemoStats,
    /// A context string for every assertion message.
    ctx: String,
}

/// One VC generation of `func` the way `trust_verify.rs` runs it per function.
fn generate_under_compiler_budget(func: &VerifiableFunction) -> Generated {
    let deadline = Instant::now() + Duration::from_millis(COMPILER_BUDGET_MS);
    let _budget = trust_types::verify_budget::VerifyBudgetGuard::install(
        Some(deadline),
        COMPILER_BUDGET_STEPS,
    );
    vcgen::reset_analysis_memo_stats();
    let t0 = Instant::now();
    let summaries = vcgen::SummaryDatabase::new();
    let context = vcgen::VcgenContext::for_function(func.def_path.clone());
    let ops: std::collections::HashSet<(trust_types::BlockId, usize)> = Default::default();
    // The compiler's entry point with the compiler's arguments (`trust_verify.rs`):
    // an empty summary database, hardened off, a per-function context, no
    // box-deref operations — `vcgen_budget_realmir::generate`'s call.
    let (solver_vcs, discharged) =
        vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
            func, &summaries, false, &context, &ops,
        );
    let elapsed = t0.elapsed();
    let exhausted = trust_types::verify_budget::exhausted_readonly();
    let stats = vcgen::analysis_memo_stats();
    let ((blocks, stmts, locals), _) = shape(func);
    let ctx = format!(
        "{} (blocks={blocks} stmts={stmts} locals={locals}) took {elapsed:?}; \
         solver_vcs={} discharged={}; {stats:?}",
        func.def_path,
        solver_vcs.len(),
        discharged.len()
    );
    Generated { solver_vcs: solver_vcs.len(), discharged: discharged.len(), exhausted, stats, ctx }
}

/// Pins 1 and 2: the compiler's checkpoint, and deterministic fold work far
/// under what the unfixed fold spends on these bodies.
fn assert_within_budget_and_bounded(g: &Generated) {
    let (stats, ctx) = (&g.stats, &g.ctx);
    // 1. The compiler's checkpoint, verbatim.
    assert!(
        !g.exhausted,
        "VC generation exhausted the compiler's per-function budget \
         ({COMPILER_BUDGET_MS} ms / {COMPILER_BUDGET_STEPS} steps): {ctx}"
    );
    // 2. Deterministic fold work.
    assert_eq!(stats.fold_index_builds, 1, "one fold index per function in a scope: {ctx}");
    assert!(stats.fold_walks >= 1, "ANTI-VACUITY: the fold never walked: {ctx}");
    assert!(stats.fold_walks <= 64, "stability walks: {ctx}");
    assert!(stats.fold_walk_steps <= 20_000, "stability walk states: {ctx}");
    assert!(stats.fold_stmt_visits <= 100_000, "statements the walks examined: {ctx}");
    assert!(stats.fold_nested_resolutions <= 64, "nested referent resolutions: {ctx}");
    assert!(stats.fold_outcome_runs <= 4_000, "outcome-enumeration runs: {ctx}");
}

#[test]
fn census_tarjan_sccs_fold_generates_within_the_compiler_budget() {
    let func = load("tarjan_sccs_o2da_t6606");
    assert_eq!(func.def_path, "aterm_census::lock_order::tarjan_sccs");
    let (dims, deref_stores) = shape(&func);
    assert_eq!(dims, (83, 515, 200), "fixture shape");
    assert!(deref_stores >= 8, "only {deref_stores} stores through a pointer");

    let g = generate_under_compiler_budget(&func);
    // Measured fold work: 1 / 23 / 2 472 / 16 830 / 0 / 400.
    assert_within_budget_and_bounded(&g);
    // 3. The obligation inventory (trust main 07091c92c1 + this fix: 47 / 5).
    assert_eq!((g.solver_vcs, g.discharged), (47, 5), "obligation inventory: {}", g.ctx);
}

#[test]
fn codec_inflater_pump_fold_generates_within_the_compiler_budget() {
    let func = load("inflater_pump_o2da_db18f1e");
    assert_eq!(func.def_path, "aterm_codec::inflate::stream::Inflater::pump");
    let (dims, deref_stores) = shape(&func);
    assert_eq!(dims, (129, 471, 186), "fixture shape");
    assert!(deref_stores >= 27, "only {deref_stores} stores through a pointer");

    let g = generate_under_compiler_budget(&func);
    // Measured fold work: 1 / 11 / 1 411 / 6 439 / 0 / 119.
    assert_within_budget_and_bounded(&g);
    // 3. The obligation inventory (trust main db18f1ea11 + this fix: 12 / 2).
    assert_eq!((g.solver_vcs, g.discharged), (12, 2), "obligation inventory: {}", g.ctx);
}
