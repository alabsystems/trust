//@ revisions: valid bad_recursive_call
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Cstrip=none
//@[valid] build-pass
//@[bad_recursive_call] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! Source-to-verdict soundness gate for the fresh-context definition-entry
//! `requires` exemption. The function's own exact source-owned precondition is
//! available as an entry assumption, but a recursive call is a distinct
//! call-site proof request even though its callee name and predicate text match
//! the definition. The valid revision establishes that request. The bad
//! revision passes a concrete counterexample; it must remain visible and make
//! strict verification fail rather than borrowing the definition-entry skip.
//!
//! 2026-09-14 (policy B as ruled): the valid revision built with a REPORTED gap
//! — its one runtime-checked arithmetic row (`n - 1` keeps rustc's overflow
//! check) was tolerated once a PROVED no-fallback row (the call-site
//! precondition) no longer denied the tolerance. Two warnings were annotated on
//! the definition as that report.
//!
//! RE-MEASURED 2026-09-16: the valid revision now reports
//! `4 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked,
//! 1 assumed (requires) out of 5` and emits NO warning at all. Two independent
//! moves, both upward. The `n - 1` row is PROVED rather than runtime-checked, so
//! there is no gap left to report — which is why the two WARN annotations are
//! gone rather than re-worded; and the `requires n > 0` row is counted
//! `assumed (requires)` instead of `proved` (`688d2058fd`), which is what makes
//! the denominator 5 with 4 proved rather than 5 proved. `build-pass` is
//! unchanged and still carries the revision: a body that warns about nothing
//! must still BUILD, and a regression that re-opened the gap would fail the
//! missing WARN pins rather than pass quietly.
//!
//! The bad revision's counts moved for the same `requires` reason —
//! `2 proved, 1 failed` is now `1 proved, 1 failed, 0 unknown, 0 timed out,
//! 1 runtime-checked, 1 assumed (requires) out of 4`. Everything this file
//! exists to pin is byte-identical there: `[precond] FAILED` with its
//! counterexample, the L0 WARN, and the strict ERROR.

#[cfg(valid)]
pub fn recursive_requires(n: u32) //[valid]~ NOTE Trust verification: 4 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 assumed (requires) out of 5
    requires n > 0
{
    if n > 1 {
        recursive_requires(n - 1);
    }
}

#[cfg(bad_recursive_call)]
pub fn recursive_requires(n: u32) //[bad_recursive_call]~ WARN Trust Level 0 safety verification incomplete
//[bad_recursive_call]~| NOTE [precond] FAILED
//[bad_recursive_call]~| NOTE Trust verification: 1 proved, 1 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 assumed (requires) out of 4
//[bad_recursive_call]~| ERROR Trust strict verification failed for
    requires n > 0
{
    if n > 0 {
        recursive_requires(0);
    }
}

fn main() {}
