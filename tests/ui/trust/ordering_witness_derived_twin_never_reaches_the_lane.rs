//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The control of `ordering_witness_inconsistent_partial_ord.rs`
//! (ORD-WITNESS-CONSISTENT-1): the same `pick` over a type whose `PartialEq`
//! and `PartialOrd` are builtin derives over a `u32`, the one shape the
//! compiler's order-consistent set (`trust_verify::order_consistent_adts`)
//! admits.
//!
//! It is refused BEFORE the fix as well, under both policies (the stage 1 of
//! `76a6ea45b2`, measured 2026-10-05: `unknown … SpecModelUngrounded`, exit 1):
//! the extractor rewrites a provably-total derived comparison to the total-call
//! sentinel (`apply_total_partial_ord_sentinel`), so `a <= b` is never a
//! witness call the lane could read. The admitted set gates a credit no current
//! extraction asks for. This file pins that state. If `pick_derived` starts to
//! prove, the sentinel has started to carry the comparison's identity: check
//! that the credit came through the order-consistency gate, then update the
//! annotations.
#![feature(contracts)]
#![allow(incomplete_features)]
use core::contracts::ensures;

#[derive(Clone, Copy, PartialEq, PartialOrd)]
pub struct Dv(pub u32);

#[ensures(|r: &Result<(Dv, Dv), u8>| !matches!(r, Ok((d, c)) if d > c))]
pub fn pick_derived(a: Dv, b: Dv) -> Result<(Dv, Dv), u8> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    if !(a <= b) {
        return Err(1);
    }
    Ok((a, b))
}
