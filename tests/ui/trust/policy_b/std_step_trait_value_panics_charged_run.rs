//@ revisions: fwd_char bwd_char fwd_u8 bwd_i32 closure_fwd
//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=on
//@[fwd_char] error-pattern: overflow in `Step::forward`
//@[bwd_char] error-pattern: overflow in `Step::backward`
//@[fwd_u8] error-pattern: attempt to add with overflow
//@[bwd_i32] error-pattern: attempt to subtract with overflow
//@[closure_fwd] error-pattern: overflow in `Step::forward`
//@ ignore-emscripten no processes
//! The run twin of `std_step_trait_value_panics_charged.rs`
//! (STEP-TRAIT-DIRECT-UNCHARGED-1): the WITNESS that every function of that file's `step`
//! revision really panics on the caller's value. Built with verification OFF, each
//! revision calls one of them with the panicking value and exits 101 with core's own
//! message. The fix does not move it.
//!
//! Measured 2026-10-11 on the stage 1 of `1213387e6d` (`scratchpad/stage1-w24probe`), this
//! file's flags plus `--cfg <revision>`: `fwd_char(char::MAX, 1)` and
//! `closure_fwd(Some((char::MAX, 1)))` exit 101 at `library/core/src/iter/range.rs:93:45`
//! "overflow in `Step::forward`"; `bwd_char('\0', 1)` at `range.rs:163:46` "overflow in
//! `Step::backward`"; `fwd_u8(u8::MAX, 1)` and `bwd_i32(i32::MIN, 1)` at `range.rs:438:1`
//! "attempt to add with overflow" / "attempt to subtract with overflow". Stock nightly
//! rustc (`14cae6813`, run by path) gives the same exit codes and messages.

#![allow(unused)]
#![feature(step_trait)]
use std::hint::black_box;
use std::iter::Step;

#[inline(never)]
fn fwd_char(c: char, n: usize) -> char {
    Step::forward(c, n)
}

#[inline(never)]
fn bwd_char(c: char, n: usize) -> char {
    Step::backward(c, n)
}

#[inline(never)]
fn fwd_u8(x: u8, n: usize) -> u8 {
    Step::forward(x, n)
}

#[inline(never)]
fn bwd_i32(x: i32, n: usize) -> i32 {
    Step::backward(x, n)
}

#[inline(never)]
fn closure_fwd(o: Option<(char, usize)>) -> Option<char> {
    o.map(|(c, n)| Step::forward(c, n))
}

fn main() {
    #[cfg(fwd_char)]
    black_box(fwd_char(black_box(char::MAX), black_box(1)));
    #[cfg(bwd_char)]
    black_box(bwd_char(black_box('\0'), black_box(1)));
    #[cfg(fwd_u8)]
    black_box(fwd_u8(black_box(u8::MAX), black_box(1)));
    #[cfg(bwd_i32)]
    black_box(bwd_i32(black_box(i32::MIN), black_box(1)));
    #[cfg(closure_fwd)]
    black_box(closure_fwd(black_box(Some((char::MAX, 1)))));
}
