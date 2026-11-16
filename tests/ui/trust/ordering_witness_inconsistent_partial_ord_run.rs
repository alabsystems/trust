//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off
//@ error-pattern: the proved postcondition of pick_odd is false
//@ ignore-emscripten no processes
//! The WITNESS for `ordering_witness_inconsistent_partial_ord.rs`
//! (ORD-WITNESS-CONSISTENT-1): `pick_odd`, whose
//! `!matches!(r, Ok((d, c)) if d > c)` that file's BEFORE compiler reported
//! proved under both policies. `Odd`'s `le` and `gt` both answer `true`, so the
//! guard `a <= b` passes and the returned pair has `d > c`. `main` evaluates the
//! exact postcondition on `pick_odd(Odd(1), Odd(2))` and panics when it is
//! false.
//!
//! Built with verification OFF, so it passes before and after the fix alike: it
//! pins that the postcondition really is false, not the verdict. Measured
//! 2026-10-05 on the stage 1 at `scratchpad/stage1-w14` (`76a6ea45b2`): built
//! `-Ztrust-verify=off` it exits 101 with the message above.
#![feature(contracts)]
#![allow(incomplete_features)]
use core::cmp::Ordering;
use core::contracts::ensures;

#[derive(Clone, Copy, PartialEq)]
pub struct Odd(pub u32);
impl PartialOrd for Odd {
    fn partial_cmp(&self, _o: &Odd) -> Option<Ordering> {
        None
    }
    fn le(&self, _o: &Odd) -> bool {
        true
    }
    fn gt(&self, _o: &Odd) -> bool {
        true
    }
}

#[ensures(|r: &Result<(Odd, Odd), u8>| !matches!(r, Ok((d, c)) if d > c))]
#[inline(never)]
pub fn pick_odd(a: Odd, b: Odd) -> Result<(Odd, Odd), u8> {
    if !(a <= b) {
        return Err(1);
    }
    Ok((a, b))
}

fn main() {
    let r = pick_odd(Odd(1), Odd(2));
    let post_holds = !matches!(r, Ok((d, c)) if d > c);
    assert!(post_holds, "the proved postcondition of pick_odd is false");
}
