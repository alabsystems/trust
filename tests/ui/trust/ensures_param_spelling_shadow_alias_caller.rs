//@ revisions: dbg2 dbg0 dbg2certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[dbg2] compile-flags: -Cdebuginfo=2
//@[dbg0] compile-flags: -Cdebuginfo=0
//@[dbg2certify] compile-flags: -Cdebuginfo=2 -Ztrust-policy=certify -Cpanic=abort
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! VS-1 (2026-10-04), the caller consequence of
//! `ensures_param_spelling_shadow_alias.rs`. `pick`'s clause `result == x` is
//! FALSE (it returns `k`). At `-Cdebuginfo=2` it used to be proved, because the
//! clause's `x` bound the local CopyProp had given the shadow's row. A caller
//! assumes a proved postcondition by parameter POSITION (`x` is argument 0, so
//! `r == a`), and `a - r` then looked overflow-free: the `overflow:sub` row was
//! proved with clean-kernel evidence (KernelRechecked), also under
//! `-Ztrust-policy=certify`, and TrustVerify replaced `caller`'s overflow assert
//! with a `goto`. A verify-on build then printed `caller(4, 5) = 4294967295`,
//! where a verify-off build panics with `attempt to subtract with overflow`.
//!
//! Both functions must fail in every revision: `pick`'s postcondition, and
//! `caller`'s subtraction, which nothing makes safe.
#![allow(unused_variables)]

pub fn pick(x: u32, k: u32) -> u32
    //~^ ERROR strict verification failed for
    ensures result == x
{
    let y = x;
    let x = k;
    x
}

pub fn caller(a: u32, b: u32) -> u32 {
    //~^ ERROR strict verification failed for
    let r = pick(a, b);
    a - r
}
