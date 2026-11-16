//~ NOTE "proved":0,"failed":0,"unknown":2,"timed_out":0,"skipped":2,"runtime_checked":0,"cached":0,"total":2}
//~| NOTE "proved":1,"failed":0,"unknown":1,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":2}
//@ revisions: advisory strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-pass
//@[certify] check-fail
//! OD-1 phase 1: an instance that is still generic PROPAGATES. `g<U>` calls `f::<U>`;
//! `f` carries an instance hypothesis, and the instance `f::<U>` is not concrete, so
//! `g` publishes `f`'s hypothesis as its own `assumption:instance-hypothesis` row (line
//! 1, first pin: that row, the global-alloc row, and `g`'s unchanged
//! `runtime_checked` row for the unbundled generic call). `h` names `g::<Good>`, which
//! discharges `f`'s site THROUGH `g` at `Good` (second pin: a `proved` discharge row
//! for `f::<Good>` beside `h`'s whole-function row, counted `skipped`: it carries no
//! proof credit of its own).
//!
//! Amended 2026-10-04 (OD-1 open shapes, DECISION_QUEUE "OD-1" item 14): `f`'s own rows
//! prove everything but its hypothesis (the instance-RELATIVE evidence bar), so `g`'s
//! call `f::<U>` is now LOWERED under the propagated hypothesis: the first pin is `g`'s
//! hypothesis row and the global-alloc row, with NO `runtime_checked` absent-callee row
//! (it was `"runtime_checked":1,"total":3` before), and strict passes CONDITIONALLY.
//! Certify still refuses both carriers.
pub trait Tr {
    fn m(&self) -> u32;
}

pub struct Good;

impl Tr for Good {
    fn m(&self) -> u32 {
        1
    }
}

pub fn f<T: Tr>(t: &T) -> u32 {
    //[certify]~^ ERROR Trust certify verification failed for `still_generic_instance_propagates::f`: 1 instance hypothesis row(s)
    t.m()
}

pub fn g<U: Tr>(u: &U) -> u32 {
    //[advisory]~^ WARN `still_generic_instance_propagates::g`: 1 instance hypothesis row(s)
    //[strict]~^^ WARN `still_generic_instance_propagates::g`: 1 instance hypothesis row(s)
    //[certify]~^^^ ERROR Trust certify verification failed for `still_generic_instance_propagates::g`: 1 instance hypothesis row(s)
    f(u)
}

pub fn h() -> u32 {
    g(&Good)
}
