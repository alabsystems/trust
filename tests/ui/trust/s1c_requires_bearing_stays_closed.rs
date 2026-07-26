//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ check-pass
//! Task #23 Slice 1, amendment 3 (falsification): a requires-bearing function
//! must NOT body-bind its `ensures`. `finalize_trust_wp_body_bound_public_claims`
//! checks the mutable public bundle, an independent compiler reference, and
//! the raw `CompilerContractBundle` for ANY Requires row (including
//! unsupported ones), so deleting public transport cannot bypass the guard.
//!
//! This particular function nevertheless verifies through the independent
//! conditional VC/kernel/source lane: the authored Requires is an exact entry
//! assumption and the body proves the Ensures under it. Passing therefore does
//! not imply that a body-bound carrier was minted; the focused zero-carrier
//! unit test pins that separation directly.
pub fn req_ge(x: u64) -> u64 requires x >= 1 ensures result >= x { x }
