//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ check-pass
//! Acceptance control after TrustWP authority retirement: the exact fresh
//! body-aware postcondition VC is TrustMC-owned and its kernel/source authority
//! proves `result >= x` for the identity body. The compiler must not mint a
//! historical TrustWP request or receipt on this path.
pub fn ge_refl(x: u64) -> u64 ensures result >= x { x }
