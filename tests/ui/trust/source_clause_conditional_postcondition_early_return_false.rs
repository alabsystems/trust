//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@ check-fail
//@ dont-check-compiler-stderr
//! THE NEGATIVE TWIN of
//! `source_clause_conditional_postcondition_early_return.rs`, false on exactly
//! ONE of its three paths: the fall-through returns `0` while the clause
//! promises `result >= a` for every `a <= 1000000`, so `pick_ret_zero(5, 0)`
//! returns `0` with `0 >= 5` false.
//!
//! This is the control that says the one-row-per-path shape does not credit a
//! value the body never wrote — the shape both the early-return spelling and,
//! after the per-path split, the `if`-expression spelling emit.
//!
//! MEASURED 2026-09-18 on the managed `trustc 1.99.0-dev (d75f13f97 2026-09-15)`
//! and re-measured ROW FOR ROW on the stage1 built from the tree that landed the
//! split (identical: this body's `Return` predecessors each have one guard path,
//! so the split does not fire on it). On this exact source: exit 1,
//! "2 proved, 0 failed, 2 unknown, 0 timed out, 0 runtime-checked out of 4
//! obligation(s)", `-Ztrust-verify-output=both` row by row —
//!
//! ```text
//! obligation:…:postcondition:0  unknown  trust-exact-source-clause-discharge
//! vc:…:postcondition:0          proved   trust-full-verifier
//! vc:…:postcondition:1          proved   trust-full-verifier
//! vc:…:postcondition:2          UNKNOWN  trust-full-verifier   <- the false path
//! ```
//!
//! The two TRUE paths prove and the FALSE one does not — which is the whole
//! point: per-path rows discriminate per path. The marker stays pending, so the
//! build fails.
//!
//! DELIBERATELY NOT PINNED: whether the false row lands `FAILED` (a propagated
//! refutation) or `UNKNOWN` (the counterexample-withholding firewall demoting
//! one). Both are fail-closed; pinning the stronger verdict would make an
//! improvement in refutation reach look like a regression. What is pinned is
//! that it is not a pass.

pub fn pick_ret_zero(a: u32, b: u32) -> u32
    //~^ ERROR Trust strict verification failed for
    ensures a <= 1000000 ==> result >= a
{
    if a >= 1000000 {
        return 1000000;
    }
    if b >= a {
        return b;
    }
    0
}
