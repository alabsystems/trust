//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ check-pass
//! Requires-bearing control after TrustWP authority retirement. This function
//! verifies through the independent
//! conditional VC/kernel/source lane: the authored Requires is an exact entry
//! assumption and the body proves the Ensures under it. Passing therefore does
//! never implies that a historical TrustWP carrier was minted; the focused
//! zero-request unit test pins that separation directly.
pub fn req_ge(x: u64) -> u64 requires x >= 1 ensures result >= x { x }
