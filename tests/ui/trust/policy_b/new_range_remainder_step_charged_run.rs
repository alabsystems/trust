//@ revisions: char_max u8_max
//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=on
//@[char_max] error-pattern: overflow in `Step::forward`
//@[u8_max] error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//! The run twin of `new_range_remainder_step_charged.rs` (NEW-RANGE-REMAINDER-UNCHARGED-1):
//! the WITNESS that `RangeFromIter::remainder` panics on the caller's iterator state.
//! Built with verification OFF, each revision exhausts a `RangeFrom` iterator at `MAX`
//! (the `take(1)` adaptor yields `MAX` and sets `exhausted`) and asks its remainder,
//! which steps past `MAX` and exits 101 with core's own message. The fix does not move it.
//!
//! Measured 2026-10-12 on the stage 1 of `51eac007f3` (`scratchpad/stage1-w24`), this
//! file's flags plus `--cfg <revision>`: `char_max` exits 101 "overflow in
//! `Step::forward`", `u8_max` exits 101 "attempt to add with overflow"; the review's
//! stock-nightly oracle (`14cae6813`, run by path) gave the same exit codes and messages.

#![allow(unused)]
#![feature(new_range_remainder)]
use core::range::RangeFrom;
use std::hint::black_box;

#[inline(never)]
fn rem_char(c: char) -> RangeFrom<char> {
    let mut it = RangeFrom::from(c..).into_iter();
    it.by_ref().take(1).for_each(drop);
    it.remainder()
}

#[inline(never)]
fn rem_u8(x: u8) -> RangeFrom<u8> {
    let mut it = RangeFrom::from(x..).into_iter();
    it.by_ref().take(1).for_each(drop);
    it.remainder()
}

fn main() {
    #[cfg(char_max)]
    println!("{:?}", rem_char(black_box(char::MAX)));
    #[cfg(u8_max)]
    println!("{:?}", rem_u8(black_box(u8::MAX)));
}
