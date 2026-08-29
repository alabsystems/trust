//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-fail
//! Task #29 falsification retained after TrustWP authority retirement.
//!
//! `ensures result + 1 > result` is provable over unbounded Int (the
//! expression is an unbounded-Int tautology but FALSE at `u64::MAX` under
//! Rust's wrapping machine semantics. The active machine-faithful owner must
//! not prove it, and historical TrustWP wire data cannot revive publication.
pub fn arith_add(x: u64) -> u64 ensures result + 1 > result { x }
//~^ ERROR strict verification failed
