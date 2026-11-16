//@ revisions: pick_dbg2 pick_dbg0 flip_dbg2 flip_dbg0 call_dbg2 call_dbg0 noshadow_dbg2 noshadow_dbg0 noalias_dbg2 noalias_dbg0
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[pick_dbg2] compile-flags: -Cdebuginfo=2
//@[pick_dbg0] compile-flags: -Cdebuginfo=0
//@[flip_dbg2] compile-flags: -Cdebuginfo=2
//@[flip_dbg0] compile-flags: -Cdebuginfo=0
//@[call_dbg2] compile-flags: -Cdebuginfo=2
//@[call_dbg0] compile-flags: -Cdebuginfo=0
//@[noshadow_dbg2] compile-flags: -Cdebuginfo=2
//@[noshadow_dbg0] compile-flags: -Cdebuginfo=0
//@[noalias_dbg2] compile-flags: -Cdebuginfo=2
//@[noalias_dbg0] compile-flags: -Cdebuginfo=0
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! VS-1 (2026-10-04): an `ensures` clause names a PARAMETER, and the verifier
//! found it by the parameter's debug spelling. CopyProp moves a body binding's
//! `var_debug_info` row onto the local it was copied from. For `pick` below the
//! rows the verifier reads are
//!
//! ```text
//! debug x => _1; debug k => _2; debug y => _1; debug x => _2;
//! ```
//!
//! `build_debug_name_map` collapsed them last-write-wins to `{_1: y, _2: x}`,
//! so the clause's `x` bound `_2`, which is `k`, and `result == x` became
//! `_0 == k`: at `-Cdebuginfo=2` it was proved (one row kernel-certified),
//! exit 0, while `pick(4, 5) == 5 != 4`. `flip` is the twin in which the
//! shadow's row lands on the return place (`debug x => _0`), so the clause
//! became `_0 == _0`. At `-Cdebuginfo=0` the MIR of these two one-block
//! functions keeps only the parameters' rows, and both were refuted. `call` is
//! `pick` with a call in its body: a function that is not one block keeps the
//! body rows at `-Cdebuginfo=0` too, so the debuginfo level is not what
//! decides it.
//!
//! Every function here returns something other than `x` for some input, so
//! `result == x` is FALSE and each revision must fail. `noshadow`
//! (`let z = k; z`) and `noalias` (`let x = k; x`) are the measured controls:
//! refuted at both levels before the fix, and they must stay refuted. Each
//! revision compiles exactly one function, so one function's failure cannot
//! mask another's false proof.
#![allow(unused_variables)]

#[cfg(any(pick_dbg2, pick_dbg0))]
pub fn pick(x: u32, k: u32) -> u32
    //[pick_dbg2,pick_dbg0]~^ ERROR strict verification failed for
    ensures result == x
{
    let y = x;
    let x = k;
    x
}

#[cfg(any(flip_dbg2, flip_dbg0))]
pub fn flip(x: u32) -> u32
    //[flip_dbg2,flip_dbg0]~^ ERROR strict verification failed for
    ensures result == x
{
    let y = x;
    let x = y ^ 1;
    x
}

#[cfg(any(call_dbg2, call_dbg0))]
pub fn pick_call(x: u32, k: u32) -> u32
    //[call_dbg2,call_dbg0]~^ ERROR strict verification failed for
    ensures result == x
{
    let y = x;
    let x = k;
    core::hint::black_box(());
    x
}

#[cfg(any(noshadow_dbg2, noshadow_dbg0))]
pub fn pick_noshadow(x: u32, k: u32) -> u32
    //[noshadow_dbg2,noshadow_dbg0]~^ ERROR strict verification failed for
    ensures result == x
{
    let z = k;
    z
}

#[cfg(any(noalias_dbg2, noalias_dbg0))]
pub fn pick_noalias(x: u32, k: u32) -> u32
    //[noalias_dbg2,noalias_dbg0]~^ ERROR strict verification failed for
    ensures result == x
{
    let x = k;
    x
}
