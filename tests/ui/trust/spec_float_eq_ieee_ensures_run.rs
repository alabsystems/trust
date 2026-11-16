//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=on
//@ error-pattern: the postcondition `result == result` does not hold
//@ ignore-emscripten no processes
//! The WITNESS for the `ensures` revisions of `spec_float_eq_ieee.rs`
//! (SPEC-FLOAT-EQ-STRUCTURAL-1, docs/KNOWN_HAZARDS.md): `e` built with
//! verification OFF and its clause checked by hand at the return.
//!
//! Rust's `==` on `f64` is IEEE equality, so for `result = NaN` the clause
//! `result == result` is false. Verified BEFORE the fix (the stage 1 of the wave-19
//! integration `46e9afaf95` and of main `912bbdf300`, default policy and
//! `-Ztrust-policy=certify`), both postcondition rows of `n` were PROVED and the
//! crate built rc 0; the review's `wit/ens_bin.rs`, this program with
//! verification ON, built rc 0 and exited 3 because `r == r` was false for
//! `r = n(NaN)`. This program is what that verdict certified: it panics.

#[inline(never)]
fn n(x: f64) -> f64
    ensures result == result
{
    x
}

fn main() {
    let r = n(std::hint::black_box(f64::NAN));
    assert!(r == r, "the postcondition `result == result` does not hold for result = {r}");
}
