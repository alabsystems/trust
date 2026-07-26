//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-fail
//! Task #29 (falsification), subtraction shape: `ensures result - 1 < result`
//! is an unbounded-Int tautology but FALSE at `result == 0` for u64
//! (`0u64 - 1` wraps to `u64::MAX`). trust-mc finds the genuine machine
//! counterexample and the row is FAILED — while, before the #29 gate, the
//! bare trust-wp lane simultaneously reported the SAME postcondition
//! "verified" on Int semantics at native-lane granularity. This fixture pins
//! that the bare-claim lowering now refuses the arithmetic predicate
//! (amendment 1), so the deductive lane can never contradict the model
//! checker's machine-semantics refutation: the build fails with the genuine
//! FAILED row and the trust-wp claim is not eligible.
pub fn arith_sub(x: u64) -> u64 ensures result - 1 < result { x }
//~^ ERROR strict verification failed
