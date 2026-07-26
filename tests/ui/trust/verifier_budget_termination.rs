//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-verify-function-budget-steps=1 --crate-type=lib
//! Regression gate for the verifier preprocessing-termination guarantee
//! (reports/2026-07-18-verifier-termination-hang.md).
//!
//! The verifier's synchronous preprocessing (extraction, VC generation, spec
//! inference) is bounded by a DEADLINE-INDEPENDENT per-function step budget:
//! every instrumented pre-dispatch loop calls `budget_exhausted()` once per
//! iteration, which strictly decrements a `nat` step counter, so each loop runs
//! at most `remaining` iterations (well-founded descent — the provable
//! termination bound). Reaching a phase checkpoint over budget is a hard,
//! located compiler error.
//!
//! Under a deliberately tiny step budget the loop-bearing function below trips
//! the counter and the build fails with that error — proving the guarantee
//! FIRES (halt with a hard error, never a 4h spin). A step count is
//! deterministic where a wall-clock millisecond is not, so this gate is
//! non-flaky. Reintroduce an unbudgeted preprocessing loop and it either trips
//! the counter (this error) or, escaping it, hangs past compiletest's timeout —
//! either way CI goes red.

pub fn stepped(mut n: u32) { //~ ERROR exceeded its per-function budget
    while n > 0 invariant n <= 100 {
        n -= 1;
    }
}
