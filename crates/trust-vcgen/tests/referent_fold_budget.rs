//! Trust: 2026-10-02 — THE REFERENT FOLD MUST FINISH, AND FINISH WITH THE PROOFS
//! THE SEALED DRIVER GETS.
//!
//! `referent_fold::is_stable` (`src/lib.rs`, round A12, `0bbb2e326c`) decides whether
//! `*r` may be spelled by the place `r` borrows. Its walk asks, for every store `*q = v`
//! in `r`'s region, where `q` points — which RESOLVES `q`, which runs `q`'s own walk,
//! which resolves every pointer stored through in `q`'s region, and so on. Nothing
//! below the top level was memoized, every level re-armed a fresh resolver fuel, and
//! nothing polled the per-function budget, so `k` element borrows stored through in
//! one region cost `O(k!)` walks. MEASURED on `trustc` d36c551fa (the main toolchain
//! of the 2026-10-02 proof-loss gate), `-Ztrust-verify-function-budget-ms=120000`:
//!
//! | fixture | main (d36c551fa)                                    | sealed driver 321aaeda7 |
//! |---------|------------------------------------------------------|-------------------------|
//! | `k04`   | 20/20 proved                                         | 20/20 proved            |
//! | `k07`   | 0/35 proved: every row solver-favorable, none given an authority; the function's budget clock noted stopped | 35/35 proved |
//! | `k08`   | 292 s, VC generation over budget: one `unsupported_mir` row | 40/40 proved, 52 s |
//! | `k10`   | stopped at the 900 s cap, still in the walk          | 50/50 proved, 76 s      |
//! | `pump`  | stopped at its cap, no result (in aterm-codec the function collapsed to `unsupported_mir`) | 8/9 proved |
//!
//! (`k` = the number of element borrows; the sealed driver has no stability walk.)
//! The same recursion held aterm-core's verification for 45 minutes with the 120 s
//! function budget never firing (release blocker 2 of the 2026-10-02 gate).
//!
//! # Merged onto main's referent fold (2026-10-08)
//!
//! This file came with `fix/referent-fold-budget`, whose remedy was a per-function
//! attribution TABLE built by rounds. main fixed the same exponential walk
//! independently and first (`812ec72053` per-function `FoldIndex` and budget polls,
//! `e82299f547` outcome enumeration and the certified verdict memo, `c76576515a`;
//! `tests/referent_fold_census_realmir.rs`), so the merge keeps MAIN's mechanism and
//! drops the table, its pruning and its caches. What stays from the branch: these
//! fixtures and the verdicts they pin, and its D41a change (a store through another,
//! ATTRIBUTED pointer asks that pointer's provenance; `written_place_rebinds`), which
//! is now made on main's recursion. The branch's table-vs-recursion parity rows are
//! gone with the table; main's own `referent_fold::fold_cost_fix` compares its
//! shortcuts with its reference walk on every top-level `tests/fixtures` body, the
//! `adv_fold`, `order_*` and `alias_*` captures below included. The `kNN`, `kNNa`
//! and `pump` captures live in `tests/fixtures/referent_fold_budget/` because that
//! reference walk is the exponential recursion on exactly them.
//!
//! # Fixtures
//!
//! `tests/fixtures/referent_fold_budget_{k04,k06,k07,k08,k09,k10,pump}_mir.json` are
//! `-Ztrust-dump=mir-only` captures from that main toolchain (stage2 d36c551fa,
//! `--edition=2024 --crate-type lib -Ztrust-verify-level=2
//! -Ztrust-verify-profile=unix_hardened`) of the sources beside them in
//! `tests/fixtures/referent_fold_budget_src/` — the proof-loss gate's own reproducers,
//! `stall/kNN.rs` and `budget/pump.rs`. The dump root is rewritten to `<dump-root>/`
//! (`scripts/check_fixture_span_paths.py`) and the JSON is whitespace-compacted; the
//! bodies are byte-for-byte the dump's.
//!
//! `kNN` is `k` independent `&mut [u32; 8]` element borrows behind index temporaries,
//! stored through and read back:
//!
//! ```text
//! let i0 = (n >> 0) & 7; ...           // k index temporaries
//! let p0 = &mut a0[i0]; ...            // k element borrows
//! *p0 = 1; ...                         // k stores, each inside every other's region
//! s = s.wrapping_add(*p0); ...         // k reads
//! ```
//!
//! `pump` is aterm-codec's `Inflater::pump` shape: `let Self { .. } = self` splits
//! `&mut self` into seven `&mut` field locals, a `match` on one of them hands out
//! `&mut` payload fields, and a loop stores through all of them.
//!
//! # What is pinned
//!
//! 1. Generation under the compiler's own ambient budget (120 000 ms / 64 000 000
//!    steps, the `-Ztrust-verify-function-budget-*` defaults) completes, inside a
//!    wall bound a debug build meets with a wide margin on a loaded host, and leaves
//!    `exhausted_readonly()` false — the test `preprocessing_budget_exceeded` applies.
//!    The fold's work stays linear in `k` (`fold_walks`).
//! 2. The rows this crate decides keep the sealed driver's verdict: the `k` element
//!    bounds rows of `kNN` and the arithmetic rows of `pump` PROVE through this
//!    crate's `generate` + the deployed backend pair (interval, then the
//!    deterministic in-process `ay`), and no row is refuted. (The `kNN` shift rows
//!    are proved on the compiler's native full lane, which this crate does not run;
//!    `assert_k_chain` says why they are pinned only as not refuted.)
//! 3. The false proof the fold exists for (`sf_field_reseat_bug`, re-measured as
//!    `adv_fold.rs`) is pinned unproved at both levels, beside its proving control;
//!    the `order_*` re-review captures and the `alias_*` adversarial probes pin the
//!    provenance arm (every `_bug` unproved and uncertified, every `_ctl` proved).

use std::sync::mpsc;
use std::time::{Duration, Instant};

use trust_types::{VcKind, VerifiableFunction, VerificationCondition, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

/// `-Ztrust-verify-function-budget-ms` default (`rustc_session::options`).
const COMPILER_BUDGET_MS: u64 = 120_000;
/// `-Ztrust-verify-function-budget-steps` default.
const COMPILER_BUDGET_STEPS: u64 = 64_000_000;

/// The wall bound on one fixture's VC generation, in an UNOPTIMIZED test build on a
/// shared, loaded host. Measured after the fix (see the commit): well under a second
/// per fixture. Before it, `k08` did not finish in this bound and `k10` did not finish
/// at all.
const GENERATION_BOUND: Duration = Duration::from_secs(60);

type Generated = (Vec<VerificationCondition>, Vec<(VerificationCondition, VerificationResult)>);

fn fixture_path(name: &str) -> String {
    let dir = env!("CARGO_MANIFEST_DIR");
    let nested = format!("{dir}/tests/fixtures/referent_fold_budget/{name}_mir.json");
    if std::path::Path::new(&nested).exists() {
        return nested;
    }
    format!("{dir}/tests/fixtures/{name}_mir.json")
}

fn load(name: &str) -> VerifiableFunction {
    let path = fixture_path(name);
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).unwrap_or_else(|e| panic!("{path} must deserialize: {e}"))
}

/// The compiler's entry point with the compiler's arguments, as
/// `vcgen_budget_realmir.rs` calls it.
fn generate(func: &VerifiableFunction) -> Generated {
    let summaries = trust_vcgen::SummaryDatabase::new();
    let context = trust_vcgen::VcgenContext::for_function(func.def_path.clone());
    let ops: std::collections::HashSet<(trust_types::BlockId, usize)> = Default::default();
    trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
        func, &summaries, false, &context, &ops,
    )
}

/// What one generation under an ambient budget left behind.
struct Run {
    generated: Generated,
    elapsed: Duration,
    /// `verify_budget::exhausted_readonly()` right after generation — the
    /// compiler's `preprocessing_budget_exceeded` checkpoint.
    exhausted: bool,
    /// The analysis work counters of the generation (`fold_walks`,
    /// `fold_walk_steps`: the referent fold's deterministic work).
    stats: trust_vcgen::AnalysisMemoStats,
}

/// Generate `name` on a fresh 64 MiB-stack thread under the ambient budget
/// `(ms, steps)` and wait at most `bound` for it. A generation still running at the
/// bound fails the test (its thread is left behind; the harness exits under it).
fn generate_bounded(name: &str, ms: u64, steps: u64, bound: Duration) -> Run {
    let func = load(name);
    let (tx, rx) = mpsc::channel();
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            let deadline = Instant::now() + Duration::from_millis(ms);
            let _budget =
                trust_types::verify_budget::VerifyBudgetGuard::install(Some(deadline), steps);
            trust_vcgen::reset_analysis_memo_stats();
            let t0 = Instant::now();
            let generated = generate(&func);
            let elapsed = t0.elapsed();
            let exhausted = trust_types::verify_budget::exhausted_readonly();
            let stats = trust_vcgen::analysis_memo_stats();
            let _ = tx.send(Run { generated, elapsed, exhausted, stats });
        })
        .expect("spawn the generation thread");
    rx.recv_timeout(bound).unwrap_or_else(|_| {
        panic!(
            "{name}: VC generation did not finish within {bound:?} — the referent fold's \
             walk is unbounded again"
        )
    })
}

/// Generate under the compiler's budget and require the checkpoint to pass.
fn generate_within_compiler_budget(name: &str) -> Run {
    let run = generate_bounded(name, COMPILER_BUDGET_MS, COMPILER_BUDGET_STEPS, GENERATION_BOUND);
    println!(
        "  {name}: generated {} solver + {} discharged obligations in {:?}; {} fold walks, \
         {} walk steps",
        run.generated.0.len(),
        run.generated.1.len(),
        run.elapsed,
        run.stats.fold_walks,
        run.stats.fold_walk_steps,
    );
    assert!(
        !run.exhausted,
        "{name}: VC generation exhausted the compiler's per-function budget \
         ({COMPILER_BUDGET_MS} ms / {COMPILER_BUDGET_STEPS} steps) in {:?}",
        run.elapsed
    );
    run
}

/// Every obligation with its verdict: the solver rows through the deployed backend
/// pair in the compiler's order (the interval backend, then the deterministic
/// in-process `ay`), the discharged rows as generation decided them.
fn verdicts((solver, discharged): Generated) -> Vec<(VerificationCondition, VerificationResult)> {
    let mut rows = std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            let router = trust_router::Router::with_backends(vec![
                Box::new(trust_router::interval_backend::IntervalBackend),
                Box::new(test_router::test_ay_backend()),
            ]);
            router.verify_all(&solver)
        })
        .expect("spawn the solver thread")
        .join()
        .expect("the solver thread must not panic");
    rows.extend(discharged);
    rows
}

fn is_proved(r: &VerificationResult) -> bool {
    matches!(r, VerificationResult::Proved { .. })
}

/// Generation within the compiler's budget and a deterministic work bound on the
/// fold, then the obligations.
///
/// WHICH ROWS. The sealed driver proves `3k` rows of `kNN` besides its own
/// `hardened_panic_boundary` ones: the `k` element bounds checks (by the `interval`
/// backend) and the `k` `(n >> i)` shift asserts, each reported as one `overflow`
/// and one `shift:right` row — and THOSE `2k` it proves on the compiler's native
/// full lane (`trust-full-verifier`), which this crate does not run. Through this
/// crate's `generate` + the deployed backend pair the bounds rows are the ones the
/// same authority decides, so they are pinned PROVED; the shift rows are generated
/// before any borrow (no folded name appears in them) and from the sixth one on the
/// in-process `ay` answers `Unknown` on their accumulated path condition — no folded
/// name appears in them, so not something the fold decides. They are pinned NOT
/// REFUTED. The end-to-end
/// row ("every row the seal proves") is the `trustc` run on `stall/kNN.rs`.
fn assert_k_chain(k: usize) {
    let name = format!("referent_fold_budget_k{k:02}");
    let run = generate_within_compiler_budget(&name);
    // A linear number of walks and nothing nested (main's outcome enumeration
    // decides every store through another borrow: its only guards are the `Index`
    // temporary and the array parameter, bare locals nothing borrows).
    let walks = run.stats.fold_walks;
    assert!(
        walks <= 2 * k as u64,
        "{name}: {walks} fold walks for {k} element borrows — the walk is nesting again"
    );
    let rows = verdicts(run.generated);
    let census: Vec<(String, u32, bool)> = rows
        .iter()
        .map(|(vc, r)| (format!("{:?}", vc.kind), vc.location.line_start, is_proved(r)))
        .collect();
    let bounds: Vec<&(VerificationCondition, VerificationResult)> =
        rows.iter().filter(|(vc, _)| matches!(vc.kind, VcKind::IndexOutOfBounds)).collect();
    assert_eq!(bounds.len(), k, "{name}: one element bounds row per borrow; rows {census:?}");
    for (vc, verdict) in &bounds {
        assert!(
            is_proved(verdict),
            "{name}: the bounds row at {}:{} must PROVE, as it does on the sealed driver; \
             got {verdict:?}",
            vc.location.line_start,
            vc.location.col_start
        );
    }
    for (vc, verdict) in &rows {
        assert!(
            !matches!(verdict, VerificationResult::Failed { .. }),
            "{name}: {:?} at {}:{} is REFUTED on a program that cannot panic; got {verdict:?}",
            vc.kind,
            vc.location.line_start,
            vc.location.col_start
        );
    }
    let proved = rows.iter().filter(|(_, r)| is_proved(r)).count();
    println!("  {name}: {proved}/{} obligations proved, {k}/{k} bounds rows", rows.len());
}

#[test]
fn k04_generates_within_the_budget_and_proves() {
    assert_k_chain(4);
}

#[test]
fn k06_generates_within_the_budget_and_proves() {
    assert_k_chain(6);
}

#[test]
fn k07_generates_within_the_budget_and_proves() {
    assert_k_chain(7);
}

#[test]
fn k08_generates_within_the_budget_and_proves() {
    assert_k_chain(8);
}

#[test]
fn k09_generates_within_the_budget_and_proves() {
    assert_k_chain(9);
}

#[test]
fn k10_generates_within_the_budget_and_proves() {
    assert_k_chain(10);
}

/// `pump`: generation completes within the compiler's budget, and the arithmetic
/// rows the sealed driver proves — `steps += 1` (`Add`), the guarded `*warm -= 1`
/// (`Sub`, read through a `&mut` payload field of a `&mut` field of `self`) and the
/// `b >> 1` shift — prove here too.
#[test]
fn pump_generates_within_the_budget_and_proves_the_arithmetic_rows() {
    let name = "referent_fold_budget_pump";
    let run = generate_within_compiler_budget(name);
    let rows = verdicts(run.generated);
    let arithmetic: Vec<&(VerificationCondition, VerificationResult)> = rows
        .iter()
        .filter(|(vc, _)| {
            matches!(vc.kind, VcKind::ArithmeticOverflow { .. } | VcKind::ShiftOverflow { .. })
        })
        .collect();
    let census: Vec<(String, usize, bool)> = arithmetic
        .iter()
        .map(|(vc, r)| (format!("{:?}", vc.kind), vc.location.line_start as usize, is_proved(r)))
        .collect();
    println!("  {name}: arithmetic rows {census:?}");
    for line in [33usize, 40, 66] {
        let here: Vec<_> =
            arithmetic.iter().filter(|(vc, _)| vc.location.line_start as usize == line).collect();
        assert!(!here.is_empty(), "{name}: an arithmetic row at line {line}; rows {census:?}");
        for (vc, verdict) in here {
            assert!(
                is_proved(verdict),
                "{name}: {:?} at line {line} must PROVE, as it does on the sealed driver; \
                 got {verdict:?}",
                vc.kind
            );
        }
    }
}

/// THE ALIASED-GUARD K-CHAIN: every index temporary is also shared-borrowed
/// (`let k_i = &i_i;`, the borrow `println!("{}", i_i)` takes), so no store through
/// another element borrow is decided without its attribution: every walk needs every
/// other pointer's, which is the dependency the old recursion paid for
/// exponentially. Each walk here also refuses its OWN fold: its own store lands
/// behind a `Deref`, and an aliased guard is reachable by any such store. Pinned:
/// generation is bounded, the walks stay polynomial in `k`, the `k` bounds rows
/// prove and nothing is refuted.
fn assert_aliased_chain(k: usize) {
    let name = format!("referent_fold_budget_k{k:02}a");
    let run = generate_within_compiler_budget(&name);
    let stats = run.stats;
    println!(
        "  {name}: {} walks, {} walk steps, {} nested resolutions, {} memo hits, {} outcome \
         decisions",
        stats.fold_walks,
        stats.fold_walk_steps,
        stats.fold_nested_resolutions,
        stats.fold_memo_hits,
        stats.fold_outcome_decisions
    );
    let k = k as u64;
    assert!(
        stats.fold_walks <= 4 * k * (k + 1),
        "{name}: {} fold walks for {k} element borrows is not polynomial",
        stats.fold_walks
    );
    let rows = verdicts(run.generated);
    let bounds: Vec<&(VerificationCondition, VerificationResult)> =
        rows.iter().filter(|(vc, _)| matches!(vc.kind, VcKind::IndexOutOfBounds)).collect();
    assert_eq!(bounds.len() as u64, k, "{name}: one element bounds row per borrow");
    for (vc, verdict) in &bounds {
        assert!(
            is_proved(verdict),
            "{name}: the bounds row at {}:{} must PROVE; got {verdict:?}",
            vc.location.line_start,
            vc.location.col_start
        );
    }
    for (vc, verdict) in &rows {
        assert!(
            !matches!(verdict, VerificationResult::Failed { .. }),
            "{name}: {:?} at {}:{} is REFUTED on a program that cannot panic; got {verdict:?}",
            vc.kind,
            vc.location.line_start,
            vc.location.col_start
        );
    }
}

#[test]
fn aliased_k06_stays_polynomial_and_proves() {
    assert_aliased_chain(6);
}

#[test]
fn aliased_k10_stays_polynomial_and_proves() {
    assert_aliased_chain(10);
}

/// THE FALSE PROOF THE FOLD EXISTS FOR, as the 2026-10-02 verifier re-measured it
/// (`adv_fold.rs`): `let r = &mut p.a; p = o; *r = 3; t[p.a as usize]` stores
/// into the OLD `p`, so `p.a` after the reseat is `o.a`, arbitrary, and the read
/// panics. The sealed driver PROVES and kernel-certifies that row. It must stay
/// unproved and uncertified at both levels, and the control — no reseat — must keep
/// its proof.
#[test]
fn the_reseat_false_proof_stays_closed_and_its_control_proves() {
    for level in ["o0", "o1"] {
        let bug = format!("referent_fold_budget_adv_fold_bug_{level}");
        let run = generate_within_compiler_budget(&bug);
        let rows = verdicts(run.generated);
        let read: Vec<&(VerificationCondition, VerificationResult)> = rows
            .iter()
            .filter(|(vc, _)| {
                matches!(vc.kind, VcKind::IndexOutOfBounds) && vc.location.line_start == 11
            })
            .collect();
        assert!(!read.is_empty(), "{bug}: the `t[p.a]` bounds row must be generated");
        for (vc, verdict) in &read {
            assert!(
                !is_proved(verdict),
                "{bug}: the read after the reseat is PROVED on a program that panics; \
                 got {verdict:?}"
            );
            assert!(
                trust_certify::certify_vc(vc).is_none() || !is_proved(verdict),
                "{bug}: a false proof may never be kernel-certified"
            );
        }
        let ctl = format!("referent_fold_budget_adv_fold_ctl_{level}");
        let run = generate_within_compiler_budget(&ctl);
        let rows = verdicts(run.generated);
        let read: Vec<&(VerificationCondition, VerificationResult)> = rows
            .iter()
            .filter(|(vc, _)| {
                matches!(vc.kind, VcKind::IndexOutOfBounds) && vc.location.line_start == 16
            })
            .collect();
        assert!(!read.is_empty(), "{ctl}: the `t[p.a]` bounds row must be generated");
        for (_, verdict) in &read {
            assert!(is_proved(verdict), "{ctl}: the control's read must PROVE; got {verdict:?}");
        }
    }
}

// ---------------------------------------------------------------------------
// Trust: 2026-10-07 — THE ATTRIBUTED STORE ASKS ITS POINTER'S PROVENANCE (D41a of
// `fix/referent-fold-budget`, on main's recursion since the 2026-10-08 merge).
//
// `order_safe_ctl` (`referent_fold_budget_src/fc_order.rs`, captured by the
// re-review's confirmer with stage2 d36c551fa at -O0 and -O1) is a correct program
// with no `unsafe`; it never panics (`t[l[k]]` reads `t[2]`). The branch's attribution
// table REFUTED its `t[l[k]]` row: an attributed store `*y = 3`, whose target carries a
// `Deref`, asked the body-global "is `k` borrowed anywhere" (`rk = &k`) where the same
// store unattributed asked the narrower provenance question. main never built the
// table and proves it; the rows below pin it, its bug twin and its raw-pointer
// variants on main's recursion with the provenance arm.
// ---------------------------------------------------------------------------

/// The rows of `name` at `line:col` with the given kind, solved by the deployed
/// backend pair, each with whether `certify_vc` kernel-certifies its formula. Only
/// the selected rows are solved. ANTI-VACUITY: at least one row must be generated.
fn rows_at(
    name: &str,
    line: u32,
    col: u32,
) -> Vec<(VerificationCondition, VerificationResult, bool)> {
    let run = generate_within_compiler_budget(name);
    let at = |vc: &VerificationCondition| {
        matches!(vc.kind, VcKind::IndexOutOfBounds)
            && vc.location.line_start == line
            && vc.location.col_start == col
    };
    let (solver, discharged) = run.generated;
    let solver: Vec<VerificationCondition> = solver.into_iter().filter(|vc| at(vc)).collect();
    let discharged: Vec<(VerificationCondition, VerificationResult)> =
        discharged.into_iter().filter(|(vc, _)| at(vc)).collect();
    let rows: Vec<(VerificationCondition, VerificationResult, bool)> =
        verdicts((solver, discharged))
            .into_iter()
            .map(|(vc, r)| {
                let certified = trust_certify::certify_vc(&vc).is_some();
                (vc, r, certified)
            })
            .collect();
    assert!(!rows.is_empty(), "{name}: the {line}:{col} bounds row must be generated");
    rows
}

fn is_failed(r: &VerificationResult) -> bool {
    matches!(r, VerificationResult::Failed { .. })
}

/// A program that panics: its row is never PROVED and never kernel-certified.
fn assert_bug_row_unproved(name: &str, line: u32, col: u32) {
    for (_, verdict, certified) in rows_at(name, line, col) {
        assert!(
            !is_proved(&verdict),
            "{name}: {line}:{col} is PROVED on a program that panics there; got {verdict:?}"
        );
        assert!(!certified, "{name}: {line}:{col} is kernel-certified on a program that panics");
    }
}

/// A correct program: its row PROVES and its formula kernel-certifies.
fn assert_ctl_row_proved(name: &str, line: u32, col: u32) {
    for (_, verdict, certified) in rows_at(name, line, col) {
        assert!(is_proved(&verdict), "{name}: {line}:{col} must PROVE; got {verdict:?}");
        assert!(certified, "{name}: {line}:{col} must kernel-certify");
    }
}

/// The measured false refutation of the table: `order_safe_ctl`'s `t[l[k]]` row
/// PROVES and certifies at both levels.
#[test]
fn the_order_control_proves_where_the_table_refuted_it() {
    for level in ["o0", "o1"] {
        let name = format!("referent_fold_budget_order_safe_ctl_{level}");
        assert_ctl_row_proved(&name, 18, 4);
    }
}

/// The bug twin (`*z = 6` last) stays refuted, and the counterexample carries the
/// value the program really stores (`_13 = 6`, read back through `l[k]`); under the
/// table it was the 4 the opaque `z*` let the solver pick.
#[test]
fn the_order_bug_twin_is_refuted_with_the_store_it_makes() {
    for level in ["o0", "o1"] {
        let name = format!("referent_fold_budget_order_safe_bug_{level}");
        for (_, verdict, certified) in rows_at(&name, 31, 4) {
            assert!(!certified, "{name}: 31:4 is kernel-certified on a program that panics");
            let VerificationResult::Failed { counterexample: Some(cex), .. } = &verdict else {
                panic!("{name}: 31:4 must be REFUTED with a counterexample; got {verdict:?}");
            };
            let shown = format!("{:?}", cex.assignments);
            assert!(
                shown.contains("(\"_13\", Int(6))"),
                "{name}: the counterexample must read back the 6 stored through `z`; got {shown}"
            );
        }
    }
}

/// The raw-pointer variants: PROVED and certified at -O1, never refuted at -O0 (where
/// the in-process `ay` answers Unknown on main too) and still kernel-certified there.
#[test]
fn the_raw_pointer_order_controls_are_not_refuted() {
    for (fixture, line) in [("order_raw_ctl", 46), ("order2_ctl", 64), ("order3_ctl", 82)] {
        let o1 = format!("referent_fold_budget_{fixture}_o1");
        assert_ctl_row_proved(&o1, line, 4);
        let o0 = format!("referent_fold_budget_{fixture}_o0");
        for (_, verdict, certified) in rows_at(&o0, line, 4) {
            assert!(!is_failed(&verdict), "{o0}: {line}:4 is REFUTED on a correct program");
            assert!(certified, "{o0}: {line}:4 must kernel-certify");
        }
    }
}

/// THE ADVERSARIAL ALIASING PROBES for the change above (`referent_fold_budget_src/
/// fx_adv.rs`, stage2 d36c551fa captures at -O0 and -O1; every `_bug` panics natively
/// for every input tried, every `_ctl` never does). The change answers a store
/// through an ATTRIBUTED other pointer in pointer-reached memory by that pointer's
/// provenance, so each `_bug` routes a pointer to the index guard `k` through a `Box`,
/// a `Vec`, `split_at_mut` or a reborrow loop, stores through it after `z = &mut l[k]`
/// is taken, makes the VC's new `k` differ from the borrow-time one
/// (`if k == k0 { return }`) and reads `t[*z]`: a fold that survived that store would
/// spell `*z` as `l[k_new]` (1, in bounds) where the program reads the 9 it stored.
/// None may be proved or certified. Each `_ctl` stores through a `Box` field, a `Vec`
/// slice element, `split_at_mut` halves or a loop reborrow between two stores
/// through `z`, with `k` shared-borrowed — the shape whose fold the body-global
/// question used to refuse (main refuted all three without the provenance arm, with a
/// counterexample that read the store as 4) — and its `t[l[k]]` row must prove and
/// certify.
#[test]
fn aliasing_probes_keep_every_bug_unproved_and_prove_their_controls() {
    let bugs = [
        ("box_alias_bug", 31),
        ("box_field_bug", 62),
        ("vec_alias_bug", 80),
        ("split_alias_bug", 128),
        ("loop_reborrow_bug", 168),
        ("box_loop_bug", 192),
    ];
    let ctls = [
        ("box_field_ctl", 47),
        ("vec_slice_ctl", 95),
        ("split_ctl", 111),
        ("loop_reborrow_ctl", 147),
    ];
    for level in ["o0", "o1"] {
        for (probe, line) in bugs {
            let name = format!("referent_fold_budget_alias_{probe}_{level}");
            assert_bug_row_unproved(&name, line, 4);
        }
        for (probe, line) in ctls {
            let name = format!("referent_fold_budget_alias_{probe}_{level}");
            assert_ctl_row_proved(&name, line, 4);
        }
    }
}
