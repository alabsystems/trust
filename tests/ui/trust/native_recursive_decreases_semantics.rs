//@ revisions: correct wrong_decrease
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Cstrip=none
//@[correct] build-pass
//@[wrong_decrease] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! End-to-end E5 gate for first-class function-signature `decreases`.
//! The positive revision has two distinct recursive call sites so source
//! admission requires the exact fresh per-call-site bijection; both calls
//! strictly decrease the authored unsigned measure. The negative revision
//! keeps the same native surface but passes the entry measure unchanged, which
//! must remain a visible unproved termination obligation. (Post ay-0.9.0, the
//! solver's refutation of the encoded VC carries no producer fidelity
//! attestation and is demoted, so the row reads UNKNOWN rather than FAILED.)
//!
//! 2026-09-14 (policy B as ruled): the correct revision built with a REPORTED
//! gap — its one runtime-checked arithmetic row (`n - 1`) was tolerated once
//! the PROVED termination rows (no runtime fallback) no longer denied the
//! tolerance, and the two warnings on the definition were that report.
//! LATER THE SAME DAY the gap itself closed: trust-mc models each direct
//! self-call by the inductive hypothesis (engine `23dd58a6c7`) instead of an
//! unconditional error rule, so the aggregate panic-freedom row PROVES, the
//! `n - 1` assert is statically discharged rather than retained, and there is
//! no reported gap left to warn about. Both warnings are therefore gone; they
//! are NOT in `dont-require-annotations`, so if either returns this test fails
//! loudly and the tolerance question is live again.

#[cfg(correct)]
pub fn two_calls(n: u32) //[correct]~ NOTE Trust verification: 5 proved
    decreases n
{
    if n > 0 {
        two_calls(n - 1);
        two_calls(n - 1);
    }
}

// Re-pinned 2026-09-14 (trust-mc `23dd58a6c7`): the Level 0 aggregate
// panic-freedom row over the self-call now PROVES under the inductive
// hypothesis (there is nothing else in the body that can panic), so the
// "Level 0 safety verification incomplete" WARN no longer fires; the
// termination row stays UNKNOWN and strict verification still fails on it.
#[cfg(wrong_decrease)]
pub fn no_descent(n: u32) //[wrong_decrease]~ NOTE Trust verification: 1 proved, 0 failed, 1 unknown
//[wrong_decrease]~| NOTE [termination] UNKNOWN
//[wrong_decrease]~| ERROR Trust strict verification failed for
    decreases n
{
    if n > 0 {
        no_descent(n);
    }
}

fn main() {}
