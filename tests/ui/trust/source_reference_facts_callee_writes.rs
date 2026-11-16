//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-fail
//! Falsification twin of the C1 source reference facts (`docs/TCB.md`, "Source
//! reference facts"). Must stay NON-proved.
//!
//! Both `&mut u32` parameters are claimed and so is the load `*v` in `bump`
//! (stage-1, 2026-11-06: `claimed=3 parameters=2 loads=1`). A fact says the
//! loaded value is an INITIALIZED `u32`, never WHICH one, and never that memory
//! is unchanged across a call.
//!
//! * `bump`: `*v + 1` overflows for some initialized `u32` whatever the facts
//!   say, so it pins only that the claims cost nothing they should not.
//! * `bump_after_zero` is the discriminating one: `*v` is 0 before the call, so
//!   only a wrong "the entry value / memory survives the call" reading of the
//!   facts would prove `*v + 1`. The counterexample must have `*v` = `u32::MAX`
//!   after `set_max`.
//! * `div_ref`: the load through a claimed `&u32` is claimed, and the fact must
//!   imply no VALUE: `100 / *x` must still fail with `*x` = 0.

fn set_max(x: &mut u32) {
    *x = u32::MAX;
}

pub fn bump(v: &mut u32) -> u32 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    //~| NOTE [overflow:add] FAILED
    //~| ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    set_max(v);
    *v + 1
}

pub fn bump_after_zero(v: &mut u32) -> u32 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    //~| NOTE [overflow:add] FAILED
    //~| ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    *v = 0;
    set_max(v);
    *v + 1
}

pub fn div_ref(x: &u32) -> u32 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    //~| NOTE [divzero] FAILED
    //~| ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    100 / *x
}
