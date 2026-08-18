//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! The foreign-body lane must PROVE or DECLINE — never assume.
//!
//! This is the guard for `native_trust_ir_monomorphic_foreign_callees`. That
//! lane bundles real std bodies so their callers' panic-freedom obligations are
//! discharged by proof; the standing temptation is to close the remaining gap
//! the cheap way, by declaring the leftover std callees total. A totality model
//! is a promise that a function cannot panic for ANY input, and a wrong entry
//! manufactures false proofs in every crate downstream — strictly worse than
//! leaving the obligation open.
//!
//! So the callees below are the ones the lane deliberately does NOT admit, and
//! each must still be a hard error under the fail-closed default:
//!
//!   * `str::find` bottoms out in pattern machinery and `core::panicking`;
//!   * `u32::leading_zeros` bottoms out in the `ctlz` INTRINSIC — no MIR body
//!     exists to lower, for any input, ever;
//!   * `u32::saturating_sub` bottoms out in `saturating_sub`, likewise an
//!     intrinsic.
//!
//! Intrinsics, drop glue, fn-trait shims and virtual dispatch have no source
//! body, so they are the irreducible floor no amount of body-lowering reaches.
//! Recording them as audited assumptions is a legitimate separate decision; what
//! this test forbids is that decision being made SILENTLY, by widening the
//! bundling lane until "unsupported" quietly starts meaning "assume true".
//!
//! If this fixture ever starts passing, some callee here became total without an
//! audited model behind it — read that as a soundness regression, not progress.

pub fn probe_find(s: &str) -> Option<usize> { //~ ERROR Trust strict verification failed
    s.find('x')
}

pub fn probe_leading_zeros(x: u32) -> u32 {
    x.leading_zeros()
}

pub fn probe_saturating_sub(a: u32, b: u32) -> u32 {
    a.saturating_sub(b)
}

fn main() {}
