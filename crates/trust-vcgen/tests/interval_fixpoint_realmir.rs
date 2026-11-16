//! Measurement harness for the interval fixpoint on REAL compiler dumps
//! (trust-fixpoint-deadline, 2026-10-02). Inert unless `TRUST_VCGEN_INTERVAL_DIR`
//! names a directory of `-Ztrust-dump=mir:` JSON (`VerifiableFunction`s).
//!
//! Found by census-vcgen-hang: verifying aterm-census at the aterm gate's flags plus
//! `-Zmir-opt-level=2`, `lock_order::run_lock_order_census` (1044 blocks, 3603
//! locals, 358 call blocks) spent 346 s — 226 s past its 120 s per-function budget —
//! almost all of it in `abstract_interp::merged_interval_environment ->
//! fixpoint_configured`, whose `Call` havoc re-derived and string-scanned the havoc
//! set at every visit, and which polled no budget. The census body's dump is 57 MB,
//! too large to commit; the deterministic pins live in the crate's unit tests
//! (`abstract_interp::budget_tests`). This harness is how the before/after numbers
//! were measured, kept runnable rather than quoted. For each dump it reports:
//!
//! 1. `fixpoint_configured` with no budget installed: wall time and an FNV-1a digest
//!    of the canonical block states — the digest must be identical before and after
//!    a cost change (same answer);
//! 2. the same call under a deadline of `TRUST_VCGEN_INTERVAL_DEADLINE_MS` (default
//!    2000) and the compiler's 64M-step budget: when it returned, whether the budget
//!    tripped, and whether the answer is the refusal (every block Top and reachable);
//! 3. with `TRUST_VCGEN_INTERVAL_GENERATE` set, the compiler's generation entry point
//!    with no budget: wall time and a digest of the full `(solver_vcs, discharged)`
//!    inventory — identical before and after means identical obligations.
//!
//! Runs 1 and 2 each execute inside a fresh `trust_vcgen::row_replay_scope()`: the
//! per-function memos (`place_memo`, `havoc_memo`, `fn_memo`) are LIVE, as they are
//! for every fixpoint the compiler runs (always inside a VC-generation scope). Outside
//! a scope those memos are inert and the whole-function havoc list is re-derived per
//! query, which measures a cost production never pays (the first cut of this harness
//! did exactly that: 397 s on the census body, almost all of it re-deriving that list).
//!
//! `TRUST_VCGEN_INTERVAL_ONLY=<substring>` restricts the run to matching `def_path`s.
//!
//! ```text
//! TRUST_VCGEN_INTERVAL_DIR=<dumps> targo --unverified test --release -p trust-vcgen \
//!     --test interval_fixpoint_realmir -- --nocapture --test-threads 1
//! ```

use std::time::{Duration, Instant};

use trust_types::VerifiableFunction;
use trust_vcgen::{FixpointConfig, FixpointResult, fixpoint_configured, type_aware_initial_state};

/// `-Ztrust-verify-function-budget-steps` default (`options.rs`).
const COMPILER_BUDGET_STEPS: u64 = 64_000_000;

fn fnv1a(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in bytes {
        h ^= u64::from(*b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

/// The block states, canonically ordered, as text.
fn canonical(result: &FixpointResult) -> String {
    let mut ids: Vec<_> = result.block_states.keys().copied().collect();
    ids.sort_by_key(|id| id.0);
    let mut out = String::new();
    for id in ids {
        let s = &result.block_states[&id];
        out.push_str(&format!("bb{} unreachable={}", id.0, s.is_unreachable));
        for (k, v) in &s.vars {
            out.push_str(&format!(" {k}=[{},{}]", v.lo, v.hi));
        }
        out.push('\n');
    }
    out
}

fn refused(result: &FixpointResult) -> bool {
    result.block_states.values().all(|s| !s.is_unreachable && s.vars.is_empty())
}

fn run(func: &VerifiableFunction) -> FixpointResult {
    fixpoint_configured(func, type_aware_initial_state(func), &FixpointConfig::for_function(func))
}

#[test]
fn interval_env_dir() {
    let Ok(dir) = std::env::var("TRUST_VCGEN_INTERVAL_DIR") else {
        return;
    };
    let only = std::env::var("TRUST_VCGEN_INTERVAL_ONLY").ok();
    let deadline_ms: u64 = std::env::var("TRUST_VCGEN_INTERVAL_DEADLINE_MS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(2000);
    let generate = std::env::var("TRUST_VCGEN_INTERVAL_GENERATE").is_ok();
    let mut paths: Vec<_> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("{dir}: {e}"))
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "json"))
        .collect();
    paths.sort();
    for path in paths {
        let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path:?}: {e}"));
        let func: VerifiableFunction = serde_json::from_str(&json)
            .unwrap_or_else(|e| panic!("{path:?} is not a VerifiableFunction: {e}"));
        if only.as_deref().is_some_and(|o| !func.def_path.contains(o)) {
            continue;
        }
        let blocks = func.body.blocks.len();
        let stmts: usize = func.body.blocks.iter().map(|b| b.stmts.len()).sum();
        let calls = func
            .body
            .blocks
            .iter()
            .filter(|b| {
                matches!(
                    b.terminator,
                    trust_types::Terminator::Call { .. } | trust_types::Terminator::TailCall { .. }
                )
            })
            .count();
        println!(
            "INTERVAL {} blocks={blocks} stmts={stmts} locals={} calls={calls}",
            func.def_path,
            func.body.locals.len()
        );

        // 1. No budget: the answer and its cost.
        trust_vcgen::reset_analysis_memo_stats();
        let t0 = Instant::now();
        let fp = {
            let _memos = trust_vcgen::row_replay_scope();
            run(&func)
        };
        let elapsed = t0.elapsed();
        let text = canonical(&fp);
        println!(
            "  UNBUDGETED fixpoint {:.3}s digest={:016x} states={} refused={} stats={:?}",
            elapsed.as_secs_f64(),
            fnv1a(text.as_bytes()),
            fp.block_states.len(),
            refused(&fp),
            trust_vcgen::analysis_memo_stats()
        );

        // 2. Under a deadline.
        {
            let t0 = Instant::now();
            let _budget = trust_types::verify_budget::VerifyBudgetGuard::install(
                Some(t0 + Duration::from_millis(deadline_ms)),
                COMPILER_BUDGET_STEPS,
            );
            let fp = {
                let _memos = trust_vcgen::row_replay_scope();
                run(&func)
            };
            let elapsed = t0.elapsed();
            println!(
                "  DEADLINE {deadline_ms}ms: returned after {:.3}s tripped={} refused={} digest={:016x}",
                elapsed.as_secs_f64(),
                trust_types::verify_budget::exhausted_readonly(),
                refused(&fp),
                fnv1a(canonical(&fp).as_bytes())
            );
        }

        // 3. The whole generation, no budget: the obligation inventory.
        if generate {
            let summaries = trust_vcgen::SummaryDatabase::new();
            let context = trust_vcgen::VcgenContext::for_function(func.def_path.clone());
            let ops: std::collections::HashSet<(trust_types::BlockId, usize)> = Default::default();
            trust_vcgen::reset_analysis_memo_stats();
            let t0 = Instant::now();
            let (solver_vcs, discharged) =
                trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
                    &func, &summaries, false, &context, &ops,
                );
            let elapsed = t0.elapsed();
            let inventory = format!("{solver_vcs:?}\n{discharged:?}");
            println!(
                "  GENERATE {:.3}s solver_vcs={} discharged={} digest={:016x} stats={:?}",
                elapsed.as_secs_f64(),
                solver_vcs.len(),
                discharged.len(),
                fnv1a(inventory.as_bytes()),
                trust_vcgen::analysis_memo_stats()
            );
        }
    }
}
