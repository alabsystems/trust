//~ NOTE [trust-instance-hypothesis] call to `<F as core::ops::function::Fn<(u32,)>>::call` in `closure_captured_callable_admitted::shared::{closure#0}`
//~| NOTE [trust-instance-hypothesis] call to `<P as core::ops::function::FnMut<(&str,)>>::call_mut` in `closure_captured_callable_admitted::paths_of::{closure#0}`
//~| NOTE [trust-instance-hypothesis] call to `<F as core::ops::function::Fn<()>>::call` in `closure_captured_callable_admitted::cell_control::{closure#0}`
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
//@[strict] check-fail
//@[certify] check-fail
//! OD-1 item 20 (T6, 2026-10-10; docs/DECISION_QUEUE.md "OD-1-T6-CALLABLE"): a call on
//! a CAPTURED callable inside a plain closure of a generic `fn` is the root's own open
//! dispatch and is ADMITTED like the same call in the `fn` body (OD-1 item 14(a)), with
//! a per-instance discharge where the root's instance reaches the closure. Preview3
//! (stage 1 `ed578e1a5`) measured the shape on clean-cake's
//! `build_signature::{closure#0}` (`|m| paths(m)` with `paths: impl FnMut(&str) -> ..`):
//! `failed`, "call to absent callee `<impl FnMut .. as FnMut<..>>::call_mut`", because a
//! closure body admitted nothing (its sites were class (c) of "L0 refutation rows").
//!
//! * `shared::{closure#0}` calls a captured `&F`: one hypothesis row, no `failed` row;
//!   `shared` calls the closure at its own parameters (an admitted propagated call), so
//!   it carries the hypothesis too and passes strict CONDITIONALLY;
//! * `use_good` names `shared::<{closure}>` at a panic-free callable: the discharge of
//!   the closure's site at that instance is `proved` (no credit);
//! * `use_bad` names it at a callable that panics: that discharge is `failed`, an error
//!   on strict and certify (and `Bad`'s own body is refused for its own panic);
//! * `paths_of` is the measured clean-cake shape (the closure is handed to `Iterator::map`
//!   and the parent `collect`s it): the closure's site is a hypothesis row, and the
//!   parent's `collect` over a hypothesis-carrying closure is not credited (a
//!   `runtime_checked` row, which strict refuses), never proved;
//! * `cell_control`: admitting the closure's site havocs only what the call's own
//!   arguments reach; a `Cell` the callable may also hold is NOT assumed unchanged
//!   across the call, so the guarded `panic!` stays unproved (no false proof).
//! Certify refuses every hypothesis row.

use std::cell::Cell;

pub fn shared<F: Fn(u32) -> u32>(f: &F, x: u32) -> u32 {
    //[certify]~^ ERROR Trust certify verification failed for `closure_captured_callable_admitted::shared`: 1 instance hypothesis row(s)
    let g = || f(x);
    //[certify]~^ ERROR Trust certify verification failed for `closure_captured_callable_admitted::shared::{closure#0}`: termination is not established
    //[certify]~| ERROR Trust certify verification failed for `closure_captured_callable_admitted::shared::{closure#0}`: 1 instance hypothesis row(s)
    g()
}

pub fn use_good() -> u32 {
    //[strict]~^ ERROR Trust strict verification failed for `closure_captured_callable_admitted::use_good`
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete for `closure_captured_callable_admitted::use_good`
    //[certify]~| ERROR Trust strict verification failed for `closure_captured_callable_admitted::use_good`
    shared(&|v: u32| v / 2, 7)
}

pub fn use_bad() -> u32 {
    //[strict]~^ ERROR Trust instance discharge not established for `closure_captured_callable_admitted::use_bad`: 1 instance(s)
    //[strict]~| ERROR Trust strict verification failed for `closure_captured_callable_admitted::use_bad`
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `closure_captured_callable_admitted::use_bad`
    //[certify]~| ERROR Trust instance discharge not established for `closure_captured_callable_admitted::use_bad`: 1 instance(s)
    //[certify]~| ERROR Trust strict verification failed for `closure_captured_callable_admitted::use_bad`
    shared(
        &|v: u32| -> u32 {
            //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `closure_captured_callable_admitted::use_bad::{closure#0}`
            //[strict]~| ERROR Trust strict verification failed for `closure_captured_callable_admitted::use_bad::{closure#0}`
            //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `closure_captured_callable_admitted::use_bad::{closure#0}`
            //[certify]~| ERROR Trust strict verification failed for `closure_captured_callable_admitted::use_bad::{closure#0}`
            if v > 3 {
                panic!("bad");
            }
            v
        },
        7,
    )
}

pub fn paths_of<P: FnMut(&str) -> u32>(modules: &[String], mut paths: P) -> Vec<u32> {
    //[strict]~^ ERROR Trust strict verification failed for `closure_captured_callable_admitted::paths_of`
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete for `closure_captured_callable_admitted::paths_of`
    //[certify]~| ERROR Trust strict verification failed for `closure_captured_callable_admitted::paths_of`
    modules.iter().map(|m| paths(m)).collect()
    //[certify]~^ ERROR Trust certify verification failed for `closure_captured_callable_admitted::paths_of::{closure#0}`: termination is not established
    //[certify]~| ERROR Trust certify verification failed for `closure_captured_callable_admitted::paths_of::{closure#0}`: 1 instance hypothesis row(s)
}

pub fn cell_control<F: Fn()>(c: &Cell<u32>, f: &F) -> u32 {
    //[strict]~^ ERROR Trust strict verification failed for `closure_captured_callable_admitted::cell_control`
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete for `closure_captured_callable_admitted::cell_control`
    //[certify]~| ERROR Trust certify verification failed for `closure_captured_callable_admitted::cell_control`: 1 instance hypothesis row(s)
    //[certify]~| ERROR Trust strict verification failed for `closure_captured_callable_admitted::cell_control`
    let g = || {
        //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `closure_captured_callable_admitted::cell_control::{closure#0}`
        //[strict]~| ERROR Trust strict verification failed for `closure_captured_callable_admitted::cell_control::{closure#0}`
        //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `closure_captured_callable_admitted::cell_control::{closure#0}`
        //[certify]~| ERROR Trust certify verification failed for `closure_captured_callable_admitted::cell_control::{closure#0}`: termination is not established
        //[certify]~| ERROR Trust certify verification failed for `closure_captured_callable_admitted::cell_control::{closure#0}`: 1 instance hypothesis row(s)
        //[certify]~| ERROR Trust strict verification failed for `closure_captured_callable_admitted::cell_control::{closure#0}`
        let a = c.get();
        f();
        if a != c.get() {
            panic!("changed");
        }
        a
    };
    g()
}
