//@ revisions: comment code sym
//@ needs-asm-support
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[comment] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census (P2m cost 5): inline assembly is an UNKNOWN sink, and any sink
//! leaves every pool unclosed, so every function that formats or panics is
//! UNKNOWN. An `asm!` whose template is only C block comments and whitespace,
//! with no `sym` or `label` operand, assembles to no instruction: zmij's value
//! barrier (serde_json's number formatter), `asm!("/*{0}*/", inout(reg) x)`,
//! calls nothing and mints nothing, so `comment` has no row at all. `code`
//! adds one instruction after the comment, and `sym` names a symbol inside
//! it: both stay UNKNOWN, and with them every formatting or panicking
//! function.

#![allow(dead_code)]

use std::arch::asm;

fn helper() {}

pub fn barrier(mut x: u64) -> u64 {
    //[code,sym]~^ NOTE not enumerated (no spawn was found)
    #[cfg(comment)]
    unsafe {
        asm!("/*{0}*/", inout(reg) x)
    };
    #[cfg(code)]
    unsafe {
        asm!("/*{0}*/ nop", inout(reg) x)
    };
    #[cfg(sym)]
    unsafe {
        asm!("/*{0} {1}*/", inout(reg) x, sym helper)
    };
    x
}

pub fn plain(n: u32) -> String { format!("{n}") } //[code,sym]~ NOTE not enumerated (no spawn was found)

pub fn idx(v: &[u32], i: usize) -> u32 { v[i] } //[code,sym]~ NOTE not enumerated (no spawn was found)
