//@ revisions: o0 o1 o2
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@[o0] compile-flags: -Copt-level=0
//@[o1] compile-flags: -Copt-level=1
//@[o2] compile-flags: -Copt-level=2
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Spawn census (design 2026-09-29-spawn-census-by-construction §5.2, §8, §13,
//! probe p07): rows are looked up from facts taken BEFORE optimization, so
//! they are identical at every opt level (T6: a proof session runs the -O0 MIR
//! pipeline at every `-Copt-level` and refuses `-Zmir-opt-level`). The census
//! reads the callee as `func.ty(body)`, so `let f = launch; f()` is a direct
//! call (S2), and so is its caller. Before, the rows came from a re-walk of the
//! optimized body: refused at MIR level 1/2, quiet at `0`, caller never refused.

#![allow(dead_code)]

pub fn launch() { //~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[inline(never)]
pub fn via_local() { //~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    let f = launch;
    f()
}

pub fn outer() { //~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    via_local()
}
