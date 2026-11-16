//@ run-fail
//@ needs-trust-verify
//@ aux-build:num_rational_evil.rs
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off
//@ error-pattern: evil Ratio drop
//@ ignore-emscripten no processes
//! The WITNESS for `ratio_drop_requires_no_drop_impl.rs` (RATIO-DROP-1): the `victim`
//! whose `drop(r)` that file's BEFORE compiler read as panic-free because the
//! dependency's crate and type were NAMED like `num_rational::Ratio`. The `Drop` of
//! `auxiliary/num_rational_evil.rs` panics.
//!
//! Built with verification OFF, so it passes before and after the fix alike: it
//! pins that the drop really panics, not the verdict. Measured 2026-10-04 on the
//! stage 1 of `38e6c69b1c` (`scratchpad/stage1-w11fix`): the aux built with its own
//! flags and this file built `-Ztrust-verify=off` exits 101 with the message above.

extern crate num_rational_evil;

#[inline(never)]
pub fn victim(r: num_rational_evil::Ratio) -> u8 {
    let v = r.x;
    drop(r);
    v
}

fn main() {
    println!("{}", victim(num_rational_evil::Ratio { x: 3 }));
}
