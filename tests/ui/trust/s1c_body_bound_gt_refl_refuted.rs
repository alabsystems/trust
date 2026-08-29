//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-fail
//! Load-bearing falsification: the TrustMC-owned body-aware postcondition
//! `result > x` is false for the identity body on every input. The strict build
//! must fail without consulting or minting any historical TrustWP authority.
pub fn gt_refl(x: u64) -> u64 ensures result > x { x }
//~^ ERROR strict verification failed
