//! Regression gate for the VC-generation budget blowup found by the 2026-09
//! verifier-on census of `library/core` (trustc 1.99.0-dev acb08e761,
//! `-Ztrust-policy=advisory -Ztrust-verify-function-budget-ms=5000`): twenty
//! bodies — `fmt::num::imp::<impl u32>::_fmt_inner`, `num::imp::int_sqrt::
//! u64_stages`, `slice::ascii::is_ascii`, the grisu/dragon formatters, … —
//! failed with `trust_verify.rs`'s "exceeded its per-function budget (5000 ms /
//! 64000000 steps) during VC generation" (the `preprocessing_budget_exceeded`
//! checkpoint right after `generate_vcs_…_and_box_deref_ops` returns).
//!
//! # Fixtures — real compiler dumps, not synthetic MIR
//!
//! `tests/fixtures/census_budget_{fmt_inner_u32,u64_stages,is_ascii}.json` are
//! the `VerifiableFunction`s the installed trustc (1.99.0-dev acb08e761) itself
//! extracted from the verbatim transcription of those three `library/core`
//! bodies in `tests/ui/trust/vcgen_budget_census_bodies.rs`, via
//!
//! ```text
//! trustc --crate-type lib --edition 2021 -Ztrust-policy=advisory \
//!        -Ztrust-verify-function-budget-ms=1000 -Ztrust-dump=mir:dump src/lib.rs
//! ```
//!
//! which — with the pre-memo `trust-vcgen` compiled into that trustc — reports
//! the census error for `u64_stages`, `fmt_inner_u8`, `fmt_inner_u32` and
//! `fmt_inner_usize` ("during VC generation"), on a QUIET machine, at the
//! tighter 1000 ms budget (at 5000 ms the same compile squeaks under on an idle
//! host; the census ran under load, which is how a 2-4 s generation crosses
//! 5 s). The JSON is that dump whitespace-compacted; the bodies are byte-for-
//! byte the dump's (`-Ztrust-dump=mir-only:` is NOT usable here: it skips VC
//! generation along with dispatch, so it can never show the error).
//!
//! **The dumps are PRE-CARRIER, and the harness supplies no compiler evidence
//! (measured 2026-09-24).** acb08e761 predates the round-7 callee carriers, so
//! every `Terminator::Call` here deserializes with `callee_identity: None` and
//! `callee_key: None` — the documented pre-carrier meaning, which every keyed
//! recognizer and every keyed coverage gate must answer fail-closed. And
//! `generate` below installs no `with_compiler_unmodeled_call_blocks` set,
//! which only `rustc_mir_transform::trust_verify` can supply. The pinned
//! inventory is therefore the FAIL-CLOSED inventory of a keyless body with no
//! compiler rows beside it — not the one today's compiler produces for the
//! same source. That is the right thing to pin (it is what a lost or
//! duplicated obligation would move), but a pin change caused by either
//! carrier is expected and is recorded per test below.
//!
//! # What is pinned, and why these bounds
//!
//! The blowup was never non-termination: it was the same handful of whole-body
//! analyses (`place_to_var_name`, `block_entry_versions`, `writes_until`, the
//! Call-havoc name lists, `v2_array_version_prepass`, …) being re-derived from
//! scratch inside the obligation walk's inner loops — ~O(VCs × blocks × locals
//! × (locals + body)) per function (see `src/fn_memo.rs`). The fix memoizes each
//! of them once per function per VC-gen scope. Two things are therefore pinned:
//!
//! 1. **A deterministic work bound**, via `trust_vcgen::analysis_memo_stats`:
//!    each analysis is COMPUTED at most as many times as it has distinct
//!    arguments — `block_entry_versions` once, `writes_until` once per
//!    `(block, prefix)`, `place_to_var_name` once per place. A step count is
//!    deterministic where a wall clock is not, so this is the non-flaky half.
//!    Measured on these fixtures before the memo: `place_to_var_name` 976 786 /
//!    1 142 489 / 48 465 mints, `block_entry_versions` 90 / 109 / 22 fixpoints,
//!    `v2_array_version_prepass` 28 425 / 29 965 / 5 121 walks
//!    (`fmt_inner_u32` / `u64_stages` / `is_ascii`); after: 255 / 185 / 70,
//!    1 / 1 / 1, 1 / 1 / 1.
//! 2. **The compiler's own checkpoint**: generation runs under the exact
//!    ambient budget `trust_verify.rs` installs (5000 ms / 64 000 000 steps)
//!    and must leave `verify_budget::exhausted_readonly()` false, which is
//!    precisely the test `preprocessing_budget_exceeded` applies. Debug-build
//!    wall time on these fixtures is 0.67 s / 0.70 s / 0.10 s (36.8 s / 38.6 s /
//!    1.05 s before), so the clock half carries a >6× margin even unoptimized.
//!
//! And — because a faster verifier that emits a different obligation set is a
//! soundness bug, not a fix — `memo_is_verdict_identical_*` runs each fixture
//! with the memo DISABLED (`with_analysis_memo_disabled`, the seam that makes
//! every wrapper compute uncached) and requires the full `(solver_vcs,
//! discharged)` result to be identical. Those three are the slow tests in this
//! file (the uncached path is the bug); they run in parallel, ~40 s wall.
//!
//! `profile_env_dir` is the measurement harness the numbers above came from —
//! inert unless `TRUST_VCGEN_PROFILE_DIR` names a directory of dump JSON.

use std::time::{Duration, Instant};

use trust_types::{VerifiableFunction, VerificationCondition, VerificationResult};

/// `-Ztrust-verify-function-budget-ms` as the census ran it (and as
/// `preprocessing_budget_exceeded` reports it).
const COMPILER_BUDGET_MS: u64 = 5_000;
/// `-Ztrust-verify-function-budget-steps` default (`options.rs`).
const COMPILER_BUDGET_STEPS: u64 = 64_000_000;

type Generated = (Vec<VerificationCondition>, Vec<(VerificationCondition, VerificationResult)>);

fn load_fixture(name: &str) -> VerifiableFunction {
    let json = std::fs::read_to_string(format!("tests/fixtures/{name}.json"))
        .unwrap_or_else(|e| panic!("tests/fixtures/{name}.json: {e}"));
    serde_json::from_str(&json).expect("fixture deserializes as a VerifiableFunction")
}

/// The compiler's entry point with the compiler's arguments
/// (`trust_verify.rs`, the `generate_vcs_with_discharge_and_summaries_
/// configured_with_context_and_box_deref_ops` arm): an empty summary
/// database, hardened off, a per-function context, no box-deref operations.
fn generate(func: &VerifiableFunction) -> Generated {
    let summaries = trust_vcgen::SummaryDatabase::new();
    let context = trust_vcgen::VcgenContext::for_function(func.def_path.clone());
    let ops: std::collections::HashSet<(trust_types::BlockId, usize)> = Default::default();
    trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
        func, &summaries, false, &context, &ops,
    )
}

struct Shape {
    blocks: usize,
    stmts: usize,
    locals: usize,
}

fn shape(func: &VerifiableFunction) -> Shape {
    Shape {
        blocks: func.body.blocks.len(),
        stmts: func.body.blocks.iter().map(|b| b.stmts.len()).sum(),
        locals: func.body.locals.len(),
    }
}

/// Generate under the compiler's ambient budget and return the result, the
/// analysis computation counts, and the wall time.
fn generate_under_compiler_budget(
    func: &VerifiableFunction,
) -> (Generated, trust_vcgen::AnalysisMemoStats, Duration) {
    let deadline = Instant::now() + Duration::from_millis(COMPILER_BUDGET_MS);
    let _budget = trust_types::verify_budget::VerifyBudgetGuard::install(
        Some(deadline),
        COMPILER_BUDGET_STEPS,
    );
    trust_vcgen::reset_analysis_memo_stats();
    let t0 = Instant::now();
    let out = generate(func);
    let elapsed = t0.elapsed();
    let stats = trust_vcgen::analysis_memo_stats();
    // The compiler's checkpoint, verbatim: `preprocessing_budget_exceeded`
    // reads this (non-charging) right after generation returns.
    assert!(
        !trust_types::verify_budget::exhausted_readonly(),
        "{}: VC generation exhausted the compiler's per-function budget \
         ({COMPILER_BUDGET_MS} ms / {COMPILER_BUDGET_STEPS} steps); took {elapsed:?}; {stats:?}",
        func.def_path
    );
    (out, stats, elapsed)
}

/// The per-shape gate: generation completes under the compiler's budget, each
/// memoized analysis is computed at most once per distinct argument, and the
/// obligation inventory is the pinned one.
fn assert_within_budget(
    fixture: &str,
    expected_solver_vcs: usize,
    expected_discharged: usize,
) -> Generated {
    let func = load_fixture(fixture);
    let Shape { blocks, stmts, locals } = shape(&func);
    let ((solver_vcs, discharged), stats, elapsed) = generate_under_compiler_budget(&func);
    let (blocks_n, stmts_n, locals_n) = (blocks as u64, stmts as u64, locals as u64);
    let ctx = format!(
        "{fixture} (blocks={blocks} stmts={stmts} locals={locals}) took {elapsed:?}; {stats:?}"
    );

    // Deterministic work bounds — one computation per distinct argument.
    assert_eq!(stats.entry_versions_computed, 1, "statement-version oracle build: {ctx}");
    assert_eq!(stats.array_prepass_computed, 1, "v2_array_version_prepass: {ctx}");
    assert!(
        stats.havoc_lists_computed <= 2,
        "mutable_pointer/mutably_borrowed name lists (one each): {ctx}"
    );
    assert!(stats.base_index_computed <= 1, "whole-local base index table: {ctx}");
    // `writes_until` is keyed by `(block, stmt_idx)` with `stmt_idx` ranging over
    // `0..=stmts.len()` per block — `stmts + blocks` is the whole key space.
    assert!(
        stats.writes_until_computed <= stmts_n + blocks_n,
        "writes_until prefix extractions exceed the (block, prefix) key space: {ctx}"
    );
    assert!(stats.ssa_collapse_computed <= locals_n, "SSA-collapse decisions per local: {ctx}");
    assert!(stats.deref_opacity_computed <= locals_n, "deref-opacity decisions per local: {ctx}");
    // Places minted: every local once, plus the projected places the body and
    // the walk name (measured 255 / 185 / 70 against 176 / 147 / 59 locals).
    assert!(
        stats.place_names_computed <= 2 * locals_n,
        "place_to_var_name mints are not once-per-place: {ctx}"
    );

    // The obligation inventory this shape produces — unchanged by the memo
    // (the parity tests below prove that against the uncached path) and pinned
    // so a future "speedup" that drops or duplicates obligations is caught.
    assert_eq!(solver_vcs.len(), expected_solver_vcs, "solver VC count: {ctx}");
    assert_eq!(discharged.len(), expected_discharged, "discharged count: {ctx}");
    (solver_vcs, discharged)
}

#[test]
fn fmt_inner_u32_generates_within_the_compiler_budget() {
    // (45, 2) -> (44, 3) at the 2026-09-10 merge of `origin/main`: the same 47
    // obligations, one of which that branch's vcgen work now DISCHARGES instead
    // of sending to a solver. Not a memo effect — the parity test below proves
    // memo-on and memo-off agree field-for-field on this same fixture.
    // (44, 3) -> (38, 3) with the mint-side unsafe stand-in (2026-09-19,
    // `unsafe_verify::detection::decide_site`): the six dropped rows are the
    // `[unsafe] missing SAFETY comment` stand-ins of six `<*const T>::add`
    // call sites (L190/191/208/209/220/221), each of which carries the
    // separation engine's own `[unsafe:sep:offset]` row minted for that same
    // terminator — MEASURED by diffing the two inventories row for row; every
    // other row is unchanged.
    // CORRECTION (2026-09-24, re-measured on b8934ae308's own tree): those six
    // sites are `core::hint::assert_unchecked` calls (bb6/7/40/41/59/60), not
    // `<*const T>::add`, and neither this inventory nor `u64_stages`' carries
    // any `[unsafe:sep:*]` row at b8934ae308. What dropped them was the
    // `compiler_mints_unmodeled_call_row` PREDICTOR ("the compiler will mint
    // `[unsafe:unmodeled-call]` here").
    // (38, 3) -> (44, 3) at 5677b28b62 (2026-09-20, "`Covered` stops betting on
    // a row it cannot see"): that predictor is deleted, and `decide_site` now
    // covers a call only on POSITIVE evidence, the compiler's own row set
    // (`with_compiler_unmodeled_call_blocks`). This harness installs none, so
    // the six `[unsafe] missing SAFETY comment` stand-ins at
    // L190/191/208/209/220/221 are back: fail-closed, by design ("empty keeps
    // every stand-in"). MEASURED row for row on the 5677b28b62 tree against its
    // parent ce084f8b80: +6 stand-ins, every other row identical; and on HEAD,
    // installing the compiler's evidence for those six blocks (computed as
    // `synthetic_unmodeled_unsafe_call_vcs` does, via
    // `call_has_unsafe_model_keyed`) gives back exactly (38, 3).
    // (44, 3) -> (46, 1) with unwrap-from-facts (2026-10-03, DECISION_QUEUE
    // "UF-1"): the two `Result::<u32, TryFromIntError>::expect` calls (L189 bb4,
    // L195 bb10) have CALL-pinned receivers, so each gets the solvable
    // `Call::expect::panic-freedom` obligation (a free tag: unproved, published
    // `failed`) in place of its preclassified
    // `Call::expect::panic-freedom-unverified` row. MEASURED by dumping both
    // inventories on this fixture: those two rows moved, every other row is
    // identical.
    assert_within_budget("census_budget_fmt_inner_u32", 46, 1);
}

#[test]
fn u64_stages_generates_within_the_compiler_budget() {
    // (42, 3) -> (39, 3): the three `.add` stand-ins at L98/L128 dropped for
    // their own `[unsafe:sep:offset]` rows (see `fmt_inner_u32` above).
    // CORRECTION (2026-09-24): they are the stand-ins of three
    // `core::hint::assert_unchecked` calls (bb5 at L98, bb26/bb47 at L128),
    // dropped by the same predictor (see `fmt_inner_u32` above).
    // (39, 3) -> (42, 3) at 5677b28b62, for the same reason as `fmt_inner_u32`:
    // the three stand-ins are back (L98, L128 twice), every other row
    // identical; with the compiler's evidence installed, exactly (39, 3).
    // (42, 3) -> (39, 3) at SELF-GUARDED-LITERAL-OPERAND-2 (2026-10-13): the body
    // has three shifts by a signed LITERAL amount, each checked through the cast
    // temporary `_t = const N as uW`. The shift binder now binds that literal cast
    // source by value, so each shift's two rows stating one proposition (the assert
    // lane's generic `ArithmeticOverflow { op: Shl }` fall-through and the
    // self-guarded statement-lane `ShiftOverflow`) become the one bound
    // `ShiftOverflow` row. Row for row (the lane's census of every fixture body):
    // those three generic rows are gone, each shift's surviving `ShiftOverflow` row
    // is now the assert lane's, and every other row is identical.
    assert_within_budget("census_budget_u64_stages", 39, 3);
}

#[test]
fn is_ascii_generates_within_the_compiler_budget() {
    // (15, 0) -> (12, 0): the three `.add` stand-ins at L46/L61/L66 dropped for
    // their own `[unsafe:sep:offset]` rows; the `read_unaligned` site at L66
    // keeps its stand-in (no engine row, no compiler row: `ptr::read` is
    // modeled by name, so `[unsafe:unmodeled-call]` is not minted for it).
    // (12, 0) -> (11, 0) at 0f7edab5fe (2026-09-20, "the mint decides on the
    // key; the text lane becomes a mirror"): `is_ptr_offset_call` now decides
    // on `CalleeKey::sysroot_item`, and these calls carry no key (see the
    // fixture note at the top), so the engine no longer runs its offset
    // interpreter for them. Row for row, against c2485d7917, its nearest
    // ancestor that builds (eb11d60d1d and c9e180574f, which add the carrier
    // in between, do not build on their own): the four
    // `[unsafe:sep:offset]` rows are gone — L46:32 (bb17 `<*const u8>::add`),
    // L53:47 (bb27 `<*const u8>::wrapping_add`), L61:28 (bb35
    // `<*const usize>::add`), L66:30 (bb42 `<*const u8>::add`). The three
    // `add` sites get their `Bool(true)` stand-ins back, an obligation that can
    // never be discharged and so is STRONGER than the offset row it replaces.
    // `wrapping_add` is a safe fn, so it has no stand-in, and its row was the
    // engine's in-bounds check on a provenance step, not a safety obligation of
    // the call (no pointer it produces loses a row: every deref/read site keeps
    // the stand-in it had). Every other row is identical.
    // On HEAD, giving each call the key today's extractor mints for it
    // (`sysroot_item_for` over its owner and leaf) gives back the exact 12-row
    // inventory above.
    assert_within_budget("census_budget_is_ascii", 11, 0);
}

/// The soundness half: the memo may change nothing about WHAT is generated.
/// `Debug` is the comparison form — every `VerificationCondition` field
/// (kind, formula, span, contracts, provenance) and every `VerificationResult`
/// prints through it, so two results are equal here iff every obligation and
/// every discharge is spelled identically.
fn assert_memo_is_verdict_identical(fixture: &str) {
    let func = load_fixture(fixture);
    let (with_memo, _, memo_elapsed) = generate_under_compiler_budget(&func);
    trust_vcgen::reset_analysis_memo_stats();
    let t0 = Instant::now();
    let without_memo = trust_vcgen::with_analysis_memo_disabled(|| generate(&func));
    let uncached_elapsed = t0.elapsed();
    let uncached = trust_vcgen::analysis_memo_stats();
    eprintln!(
        "{fixture}: memo {memo_elapsed:?} vs uncached {uncached_elapsed:?}; uncached work {uncached:?}"
    );
    // The uncached path really did the whole-body work again (otherwise the
    // seam is not exercising what it claims to). Keyed on the analyses THIS
    // memo still owns after the 2026-09-10 merge: `with_analysis_memo_disabled`
    // does not switch off `place_memo`/`havoc_memo`, so `entry_versions` (now
    // `havoc_memo::version_oracle`) stays at 1 in both runs and is no longer a
    // witness that the seam fired. See `src/fn_memo.rs`.
    assert!(
        uncached.array_prepass_computed > 1 && uncached.ssa_collapse_computed > 1,
        "{fixture}: the disabled-memo run did not recompute the analyses: {uncached:?}"
    );
    assert_eq!(
        with_memo.0.len(),
        without_memo.0.len(),
        "{fixture}: solver VC count differs with the memo"
    );
    assert_eq!(
        with_memo.1.len(),
        without_memo.1.len(),
        "{fixture}: discharged count differs with the memo"
    );
    for (i, (a, b)) in with_memo.0.iter().zip(&without_memo.0).enumerate() {
        assert_eq!(format!("{a:?}"), format!("{b:?}"), "{fixture}: solver VC #{i} differs");
    }
    for (i, (a, b)) in with_memo.1.iter().zip(&without_memo.1).enumerate() {
        assert_eq!(format!("{a:?}"), format!("{b:?}"), "{fixture}: discharged #{i} differs");
    }
}

#[test]
fn memo_is_verdict_identical_on_fmt_inner_u32() {
    assert_memo_is_verdict_identical("census_budget_fmt_inner_u32");
}

#[test]
fn memo_is_verdict_identical_on_u64_stages() {
    assert_memo_is_verdict_identical("census_budget_u64_stages");
}

#[test]
fn memo_is_verdict_identical_on_is_ascii() {
    assert_memo_is_verdict_identical("census_budget_is_ascii");
}

/// Isolation: the memo is per-function per-scope. Generating for A and then B
/// on one thread must give B exactly what B gets on a fresh thread (a fresh
/// `thread_local!`) that never saw A — no entry of A's may serve B.
#[test]
fn memo_does_not_serve_one_function_to_another() {
    let a = load_fixture("census_budget_fmt_inner_u32");
    let b = load_fixture("census_budget_u64_stages");
    let (_, _, _) = generate_under_compiler_budget(&a);
    let (b_after_a, _, _) = generate_under_compiler_budget(&b);
    let b_alone = std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || generate_under_compiler_budget(&b).0)
        .expect("spawn")
        .join()
        .expect("join");
    assert_eq!(b_after_a.0.len(), b_alone.0.len());
    assert_eq!(b_after_a.1.len(), b_alone.1.len());
    for (x, y) in b_after_a.0.iter().zip(&b_alone.0) {
        assert_eq!(format!("{x:?}"), format!("{y:?}"), "solver VC differs after generating A");
    }
    for (x, y) in b_after_a.1.iter().zip(&b_alone.1) {
        assert_eq!(format!("{x:?}"), format!("{y:?}"), "discharge differs after generating A");
    }
}

/// Scope discipline: outside a VC-gen scope the memo is inert — a public
/// `place_to_var_name` caller gets the uncached mint every time (and nothing is
/// retained for a later scope to find).
#[test]
fn memo_is_inert_outside_a_vcgen_scope() {
    let func = load_fixture("census_budget_is_ascii");
    let place = trust_types::Place { local: 1, projections: Vec::new() };
    trust_vcgen::reset_analysis_memo_stats();
    let first = trust_vcgen::place_to_var_name(&func, &place);
    let second = trust_vcgen::place_to_var_name(&func, &place);
    assert_eq!(first, second);
    assert_eq!(
        trust_vcgen::analysis_memo_stats().place_names_computed,
        2,
        "outside a scope every mint must compute"
    );
}

/// Measurement harness (not a test of anything): set
/// `TRUST_VCGEN_PROFILE_DIR=<dir of -Ztrust-dump=mir: JSON>` to time every
/// function there through the compiler's entry point with the memo on and
/// (`TRUST_VCGEN_PROFILE_BASELINE=1`) off, printing the analysis computation
/// counts; `TRUST_VCGEN_PROFILE_ONLY=<substr>` filters by def_path.
/// `#[ignore]`d, and it panics without `TRUST_VCGEN_PROFILE_DIR`, so a bare
/// `--ignored` run cannot pass having profiled nothing.
#[test]
#[ignore = "measurement driver: set TRUST_VCGEN_PROFILE_DIR=<dir of -Ztrust-dump=mir JSON> \
            and run with --ignored --nocapture"]
fn profile_env_dir() {
    let Ok(dir) = std::env::var("TRUST_VCGEN_PROFILE_DIR") else {
        panic!(
            "profile_env_dir is a measurement driver and TRUST_VCGEN_PROFILE_DIR is unset, so \
             it profiled nothing. Run: TRUST_VCGEN_PROFILE_DIR=<dir of -Ztrust-dump=mir JSON> \
             [TRUST_VCGEN_PROFILE_ONLY=<substr>] [TRUST_VCGEN_PROFILE_BASELINE=1] \
             targo --unverified test --manifest-path crates/Cargo.toml -p trust-vcgen \
             --test vcgen_budget_realmir -- --ignored --exact profile_env_dir --nocapture"
        );
    };
    let only = std::env::var("TRUST_VCGEN_PROFILE_ONLY").ok();
    let baseline = std::env::var("TRUST_VCGEN_PROFILE_BASELINE").is_ok();
    let mut funcs: Vec<VerifiableFunction> = std::fs::read_dir(&dir)
        .expect("profile dir readable")
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("json"))
        .map(|p| {
            serde_json::from_str(&std::fs::read_to_string(&p).expect("dump readable"))
                .expect("dump deserializes")
        })
        .collect();
    funcs.sort_by(|a, b| a.def_path.cmp(&b.def_path));
    for func in funcs {
        if let Some(only) = &only
            && !func.def_path.contains(only.as_str())
        {
            continue;
        }
        let Shape { blocks, stmts, locals } = shape(&func);
        trust_vcgen::reset_analysis_memo_stats();
        let t0 = Instant::now();
        let (solver, discharged) = generate(&func);
        let dt = t0.elapsed();
        let stats = trust_vcgen::analysis_memo_stats();
        eprintln!(
            "{:<28} blocks={blocks:<3} stmts={stmts:<4} locals={locals:<4} solver_vcs={:<3} discharged={:<2} memo   {dt:?}\n    {stats:?}",
            func.def_path,
            solver.len(),
            discharged.len(),
        );
        if baseline {
            trust_vcgen::reset_analysis_memo_stats();
            let t0 = Instant::now();
            let (solver, discharged) = trust_vcgen::with_analysis_memo_disabled(|| generate(&func));
            let dt = t0.elapsed();
            let stats = trust_vcgen::analysis_memo_stats();
            eprintln!(
                "{:<28} solver_vcs={:<3} discharged={:<2} NO-MEMO {dt:?}\n    {stats:?}",
                func.def_path,
                solver.len(),
                discharged.len(),
            );
        }
    }
}

/// Measurement harness (not a test of anything), census-vcgen-hang 2026-10-02: set
/// `TRUST_VCGEN_REPLAY_DIR=<dir of -Ztrust-dump=mir: JSON>` to replay, for every
/// function there, the owned-`Vec` index row at each of its `Vec` `Index`/`IndexMut`
/// call sites — what the compiler's `Vec`-forwarder gate does per root site — once
/// unscoped (the gate before `row_replay_scope`) and once under one
/// `trust_vcgen::row_replay_scope`, printing time and oracle builds for both and
/// asserting the rows agree. `TRUST_VCGEN_REPLAY_ONLY=<substr>` filters by def_path;
/// `TRUST_VCGEN_REPLAY_SCOPED_ONLY=1` skips the unscoped pass. `#[ignore]`d, and
/// it panics without `TRUST_VCGEN_REPLAY_DIR`, so a bare `--ignored` run cannot
/// pass having replayed nothing.
#[test]
#[ignore = "measurement driver: set TRUST_VCGEN_REPLAY_DIR=<dir of -Ztrust-dump=mir JSON> \
            and run with --ignored --nocapture"]
fn replay_env_dir() {
    let Ok(dir) = std::env::var("TRUST_VCGEN_REPLAY_DIR") else {
        panic!(
            "replay_env_dir is a measurement driver and TRUST_VCGEN_REPLAY_DIR is unset, so \
             it replayed nothing. Run: TRUST_VCGEN_REPLAY_DIR=<dir of -Ztrust-dump=mir JSON> \
             [TRUST_VCGEN_REPLAY_ONLY=<substr>] [TRUST_VCGEN_REPLAY_SCOPED_ONLY=1] \
             targo --unverified test --manifest-path crates/Cargo.toml -p trust-vcgen \
             --test vcgen_budget_realmir -- --ignored --exact replay_env_dir --nocapture"
        );
    };
    let only = std::env::var("TRUST_VCGEN_REPLAY_ONLY").ok();
    let scoped_only = std::env::var("TRUST_VCGEN_REPLAY_SCOPED_ONLY").is_ok();
    let mut paths: Vec<_> = std::fs::read_dir(&dir)
        .expect("replay dir readable")
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("json"))
        .collect();
    paths.sort();
    for path in paths {
        let func: VerifiableFunction =
            serde_json::from_str(&std::fs::read_to_string(&path).expect("dump readable"))
                .expect("dump deserializes");
        if let Some(only) = &only
            && !func.def_path.contains(only.as_str())
        {
            continue;
        }
        let sites: Vec<trust_types::BlockId> = func
            .body
            .blocks
            .iter()
            .filter(|block| match &block.terminator {
                trust_types::Terminator::Call { func, .. } => {
                    func.contains("Vec<")
                        && (func.contains("Index<usize>>::index")
                            || func.contains("IndexMut<usize>>::index_mut"))
                }
                _ => false,
            })
            .map(|block| block.id)
            .collect();
        if sites.is_empty() {
            continue;
        }
        let replay = |func: &VerifiableFunction| {
            trust_vcgen::reset_analysis_memo_stats();
            let t0 = Instant::now();
            let rows: Vec<_> =
                sites.iter().map(|&b| trust_vcgen::owned_vec_scalar_index_row(func, b)).collect();
            (rows, t0.elapsed(), trust_vcgen::analysis_memo_stats().entry_versions_computed)
        };
        let (scoped, scoped_dt, scoped_builds) = {
            let _replay = trust_vcgen::row_replay_scope();
            replay(&func)
        };
        let some = scoped.iter().filter(|row| row.is_some()).count();
        eprintln!(
            "{:<60} blocks={:<5} sites={:<3} rows={some:<3} SCOPED   {scoped_dt:?} oracle_builds={scoped_builds}",
            func.def_path,
            func.body.blocks.len(),
            sites.len(),
        );
        if scoped_only {
            continue;
        }
        let (unscoped, unscoped_dt, unscoped_builds) = replay(&func);
        eprintln!(
            "{:<60} blocks={:<5} sites={:<3} rows={some:<3} UNSCOPED {unscoped_dt:?} oracle_builds={unscoped_builds}",
            func.def_path,
            func.body.blocks.len(),
            sites.len(),
        );
        assert_eq!(scoped, unscoped, "{}: the replay scope changed a row", func.def_path);
    }
}
