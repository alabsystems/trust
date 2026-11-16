//@ needs-trust-verify
//@ compile-flags: --test -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-verify-output=both
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//~? RAW Trust: NOT EXCLUDED [test-harness-synthesized] `test_harness_requires_not_excluded::vacuous::{closure#0}` (test-runner-closure)
//~? RAW Trust: EXCLUDED [test-harness-synthesized] 2 body/bodies rustc's libtest harness synthesized (1 test runner closure(s), 1 harness main(s))
//! Trust (CB4): the one user obligation the libtest runner closure holds is the
//! CALL-SITE precondition row of its test function's `requires` — MEASURED:
//! `#[test] fn vacuous() requires false {}` reports `precondition of
//! …::vacuous#1 FAILED` inside `vacuous::{closure#0}`. Excluding that closure
//! would drop the row, so a `requires`-bearing test keeps its closure VERIFIED,
//! and human output says why it was not excluded.
//!
//! What the rule guards is exactly that row: a `#[test]` fn takes no arguments
//! and a `requires` clause can name neither a static nor a call, so a
//! non-trivial `requires` on a test is unsatisfiable, and the test function's
//! own vacuity guard already refuses to assume it. (The refusal line goes on to
//! name the test function and "the test function carries a `requires` clause";
//! only its stable prefix is pinned, because one RAW line satisfies one pin.)
//!
//! `plain` has no `requires` and is excluded as usual; `main` is excluded too —
//! 2 exclusions, and `vacuous::{closure#0}` is not among them. Advisory policy
//! keeps the refutation nonfatal so the file pins the disposition alone.
//!
//! MEASURED on the Track B stage 1 (2026-09-28): passes as annotated.

#[test]
fn vacuous()
    requires false
{
}

#[test]
fn plain() {}
