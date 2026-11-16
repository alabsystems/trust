//@ revisions: v4 v6 find newrange nz
//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=on
//@[v4] error-pattern: overflow in `Step::forward`
//@[v6] error-pattern: overflow in `Step::forward`
//@[find] error-pattern: overflow in `Step::forward`
//@[newrange] error-pattern: overflow in `Step::forward`
//@[nz] error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//! The run twin of `range_from_step_types_charged.rs` (STEP-ELEM-RANGEFROM-1): the
//! WITNESS that advancing an open `x..` range over a non-integer core `Step` type panics
//! on the caller's value. Built with verification OFF, each revision steps a `RangeFrom`
//! past its type's `MAX` and exits 101 with core's own message: `Ipv4Addr::BROADCAST`
//! and `Ipv6Addr` `u128::MAX` (core's default `Step::forward`, an `expect`), the
//! `find` consumer from `255.255.255.250`, the stable `core::range::RangeFrom` iterator,
//! and `NonZero::<u8>::MAX` (`u8::MAX + 1` under the inherited overflow check). The fix
//! does not move it.
//!
//! MEASURED 2026-10-13 with these flags plus `--cfg <revision>` on `scratchpad/stage1-w25f`
//! (the wave-25 stage 1, tree of `a971311ee2`) and on stock `rustup run stable rustc`
//! 1.97.1: every revision exits 101 with the pattern above, on both.

#![allow(unused)]
use std::hint::black_box;
use std::net::{Ipv4Addr, Ipv6Addr};
use std::num::NonZero;

#[inline(never)]
fn ipv4_next2(x: Ipv4Addr) -> Option<Ipv4Addr> {
    let mut it = x..;
    it.next();
    it.next()
}

#[inline(never)]
fn ipv6_next2(x: Ipv6Addr) -> Option<Ipv6Addr> {
    let mut it = x..;
    it.next();
    it.next()
}

#[inline(never)]
fn ipv4_find(x: Ipv4Addr) -> Option<Ipv4Addr> {
    (x..).find(|a| a.octets()[3] == 7)
}

#[inline(never)]
fn newrange_v4_next2(x: Ipv4Addr) -> Option<Ipv4Addr> {
    let mut it = core::range::RangeFrom::from(x..).into_iter();
    it.next();
    it.next()
}

#[inline(never)]
fn nonzero_next2(x: NonZero<u8>) -> Option<NonZero<u8>> {
    let mut it = x..;
    it.next();
    it.next()
}

fn main() {
    #[cfg(v4)]
    println!("{:?}", ipv4_next2(black_box(Ipv4Addr::BROADCAST)));
    #[cfg(v6)]
    println!("{:?}", ipv6_next2(black_box(Ipv6Addr::from(u128::MAX))));
    #[cfg(find)]
    println!("{:?}", ipv4_find(black_box(Ipv4Addr::new(255, 255, 255, 250))));
    #[cfg(newrange)]
    println!("{:?}", newrange_v4_next2(black_box(Ipv4Addr::BROADCAST)));
    #[cfg(nz)]
    println!("{:?}", nonzero_next2(black_box(NonZero::<u8>::MAX)));
}
