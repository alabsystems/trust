//@ revisions: inout same lateout code
//@ needs-asm-support
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[same] forbid-output:may spawn (indirect):
//@[same] forbid-output:not enumerated (no spawn was found):
//! Spawn census (the P2m follow-up's soundness review, probes a1 and a2): an
//! `asm!` register can carry a fn pointer's bits into an integer, and C code
//! handed that integer may call it back. `launch` spawns; `hand` gives `keep`'s
//! integer to C.
//!
//! * `inout`: a comment-only `asm!` runs no instruction, but `inout(reg) f =>
//!   n` hands `f`'s bits to `n`: a transmute of a fn pointer to an integer, a
//!   LAUNDER. `hand` is refused, with no other LAUNDER in the crate.
//! * `same`: the same barrier on an integer (zmij's) changes no type: no
//!   LAUNDER, no sink, and `hand` stays quiet.
//! * `lateout`: a comment-only `asm!` with a `lateout` place, which may share
//!   `f`'s register: no longer an assembly that writes nothing, so it is the
//!   UNKNOWN sink it was before comment-only assembly stopped being one, and a
//!   LAUNDER.
//! * `code`: assembly that runs moves `f` into `n`: an UNKNOWN sink and a
//!   LAUNDER.

#![allow(dead_code)]

use std::arch::asm;

extern "C" {
    fn c_call_back(n: usize);
}

fn launch() { //~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

pub fn keep() -> usize { //~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called
    let f: fn() = launch;
    #[cfg(not(same))]
    let n: usize;
    #[cfg(inout)]
    unsafe {
        asm!("/*{0}*/", inout(reg) f => n)
    };
    #[cfg(same)]
    let n = {
        let _ = f;
        let mut x: usize = 7;
        unsafe { asm!("/*{0}*/", inout(reg) x) };
        x
    };
    #[cfg(lateout)]
    unsafe {
        asm!("/*{0} {1}*/", in(reg) f, lateout(reg) n)
    };
    #[cfg(code)]
    unsafe {
        asm!("mov {0}, {1}", out(reg) n, in(reg) f)
    };
    n
}

pub fn hand(n: usize) { //[inout,lateout,code]~ NOTE may spawn (indirect)
    unsafe { c_call_back(n) }
}
