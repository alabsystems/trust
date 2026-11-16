//@ revisions: dbg2 dbg0
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[dbg2] compile-flags: -Cdebuginfo=2
//@[dbg0] compile-flags: -Cdebuginfo=0
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! VS-1 (2026-10-04), the controls that must stay ACCEPTED.
//!
//! `pick` is the body of `ensures_param_spelling_shadow_alias.rs` with the TRUE
//! clause `result == k`. Before the fix it was UNKNOWN at `-Cdebuginfo=2` and
//! proved at `-Cdebuginfo=0`: the last-write-wins collapse gave `_2`'s name to
//! the shadow `x`, so the spelling `k` named nothing. A spelling that names two
//! locals now names neither, `_2` keeps `k`, and the clause proves at both
//! levels.
//!
//! `restated` is the assumption gate's forced parameter restatement:
//! copy-propagation names `_1` `x`, the `requires` is restated from `n` to `x`
//! and assumed, and `result >= 0` proves. `x` has rows on `_1` only, so the
//! collapse is unchanged there. `plain` is the shape with no body binding.
#![allow(unused_variables)]

pub fn pick(x: u32, k: u32) -> u32
    //~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2
    ensures result == k
{
    let y = x;
    let x = k;
    x
}

pub fn restated(n: i32) -> i32
    //~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 assumed (requires) out of 3
    requires n >= 0
    ensures result >= 0
{
    let x = n;
    x
}

pub fn plain(x: u32) -> u32
    //~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2
    ensures result == x
{
    x
}
