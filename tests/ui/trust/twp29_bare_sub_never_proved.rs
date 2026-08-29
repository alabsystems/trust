//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-fail
//! Task #29 (falsification), subtraction shape: `ensures result - 1 < result`
//! is an unbounded-Int tautology but FALSE at `result == 0` for u64
//! (`0u64 - 1` wraps to `u64::MAX`). TrustMC finds the genuine machine
//! counterexample and the row is FAILED. Historical TrustWP compatibility data
//! cannot contradict or publish over that machine-semantics refutation.
pub fn arith_sub(x: u64) -> u64 ensures result - 1 < result { x }
//~^ ERROR strict verification failed
