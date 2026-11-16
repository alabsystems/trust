//@ revisions: pointee union reference read asm
//@ needs-asm-support
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Spawn census (design §5.4 LAUNDER; §10 "Typed LAUNDER"; the P2m
//! follow-up's soundness review, probes l1, l2, l4, l5 and a2): `entropy`
//! launders `seed_source` (a `fn() -> u64` read as an integer), a value
//! LAUNDER, which names no callable (a LAUNDER of `Any` until value LAUNDERs
//! are keyed). `keep` reads `launch`'s fn pointer as an integer:
//!
//! * `pointee`: through a pointer to it cast to `*const usize`;
//! * `union`: through a union field;
//! * `reference`: through a transmute of `&fn()` to `&usize`;
//! * `read`: through `ptr::read` of a cast pointer;
//! * `asm`: through a comment-only `asm!` whose `inout` register changes type
//!   (itself a value LAUNDER, a transmute).
//!
//! Each `keep` route is itself a LAUNDER now, keyed by the zero-argument
//! shape it puts into data (`pun_with_no_launder_is_charged.rs` pins them in a
//! crate with no value LAUNDER). `hand` gives the integer to C, which may call
//! it back, and `launch` spawns, so `hand` is refused in every revision. A
//! census that let data hold only the callable a LAUNDER of a known fn item
//! laundered (`seed_source`), while puns were recorded nowhere, left `hand`
//! QUIET in all five.

#![allow(dead_code)]

#[cfg(asm)]
use std::arch::asm;

extern "C" {
    fn c_call_back(n: usize);
}

fn launch() { //~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

fn seed_source() -> u64 {
    7
}

pub fn entropy() -> usize {
    seed_source as usize
}

#[cfg(union)]
union Pun {
    f: fn(),
    n: usize,
}

pub fn keep() -> usize { //~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called
    let f: fn() = launch;
    #[cfg(pointee)]
    let n = unsafe { *(&f as *const fn() as *const usize) };
    #[cfg(union)]
    let n = unsafe { Pun { f }.n };
    #[cfg(reference)]
    let n = unsafe { *std::mem::transmute::<&fn(), &usize>(&f) };
    #[cfg(read)]
    let n = unsafe { std::ptr::read(&f as *const fn() as *const usize) };
    #[cfg(asm)]
    let n: usize;
    #[cfg(asm)]
    unsafe {
        asm!("/*{0}*/", inout(reg) f => n)
    };
    n
}

pub fn hand(n: usize) { //~ NOTE may spawn (indirect)
    unsafe { c_call_back(n) }
}
