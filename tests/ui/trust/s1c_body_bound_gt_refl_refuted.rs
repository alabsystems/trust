//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-fail
//! Task #23 Slice 1 REFUTATION BRANCH (load-bearing falsification): the FALSE
//! postcondition `result > x` on the identity body body-binds to
//! `let result = x in result > x`; the sibling let-inlines to `x > x` and
//! refutes it by the valuation-independent irreflexive-comparison rule (false
//! for EVERY input, including every u64 — no Int-vs-machine gap). The
//! trust-wp lane returns a definite Failed with a counterexample; the build
//! MUST fail. A passing compile here would be a catastrophic false proof.
pub fn gt_refl(x: u64) -> u64 ensures result > x { x }
//~^ ERROR strict verification failed
//~| NOTE typed predicate is false by native pure replay rule
//~| NOTE [postcond] FAILED
//~| NOTE native full verifier status: Failed
