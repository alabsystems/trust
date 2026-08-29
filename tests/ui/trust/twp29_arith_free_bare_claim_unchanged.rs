//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-pass
//! Historical-wire regression guard: the arithmetic-free ground comparison
//! `0 <= 1` remains accepted by the active TrustMC/body-aware path. The retired
//! TrustWP compatibility decoder may still parse its old schema, but cannot
//! own or publish this obligation.
pub fn ground(x: u64) -> u64 ensures 0 <= 1 { x >> 1 }
