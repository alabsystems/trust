//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! BROADLY-FALSE NEGATIVE TWIN of
//! `source_clause_conditional_postcondition_frontier.rs`.
//!
//! Same clause SHAPE (an implication), same three-path body — but the
//! consequent is strengthened from `>=` to `>`, which makes the clause FALSE on
//! TWO of the three paths: `pick_strict(0, 0)` takes the `b >= a` path and
//! returns `0` (`0 > 0` is false), and `pick_strict(5, 0)` takes the else path
//! and returns `5` (`5 > 5` is false). In both, `a <= 1000000` holds.
//!
//! The build must therefore still FAIL. The lane that produced this fixture
//! only rewrites the `reason` text of a marker row the discharge pass had
//! already left `Unknown`; it mints no authority and promotes nothing. If this
//! file ever compiles, that invariant broke and a false conditional
//! postcondition is being accepted — which is strictly worse than the
//! frontier the sibling fixture pins.
//!
//! Deliberately NOT asserting whether the row lands `FAILED` (a refutation
//! propagated from a body row) or `UNKNOWN` (the pending marker): both are
//! fail-closed, and pinning one would make an improvement in refutation reach
//! look like a regression. What is pinned is that it is not a pass.
//!
//! WHAT THIS FIXTURE DOES **NOT** CONTROL, corrected after review. It was
//! offered as "the mutation control" for the source-clause COMPOSITION rule. It
//! is not. Measured on stage1 built from this branch at `8113b3a0a81`
//! (2026-09-17), this exact source gives exit 1, "0 proved, 0 failed, 3 unknown,
//! 0 timed out, 0 runtime-checked out of 3 obligation(s)" — the same counts the
//! managed `trustc d75f13f97` gave. EVERY row is unknown (the submitted ChcVc is
//! a loop-elided over-approximation, a separate and independently recorded gap;
//! `docs/KNOWN_HAZARDS.md`, battery blockers a5/a8), so this file would stay red
//! even if the composition rule were deleted outright. What it pins is
//! fail-closed-ness in general, which is worth having and is not the same claim.
//!
//! Its sibling `source_clause_conditional_postcondition_false_one_path.rs` is
//! false on exactly one path and lands on the frontier's own counts (1 proved,
//! 2 unknown), so it is the one that moves with any fix to the frontier.

pub fn pick_strict(a: u32, b: u32) -> u32
    //~^ ERROR Trust strict verification failed for
    ensures a <= 1000000 ==> result > a
{
    if a >= 1000000 {
        1000000
    } else if b >= a {
        b
    } else {
        a
    }
}
