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
//! OD-1 item 20 (T6, 2026-10-10; docs/DECISION_QUEUE.md "OD-1-T6-CALLABLE"): the
//! instances of an admitted closure site are discharged where its root's instance is
//! reached, including when the closure body is verified AFTER the body that names the
//! root's instance:
//!
//! * `use_paths_bad` / `use_paths_good` are declared before `paths_of`, whose closure
//!   is handed to `Iterator::map` (no direct call edge from `paths_of` to it): the
//!   instance `paths_of::<{closure}>` reaches `paths_of::{closure#0}` through the root's
//!   glue walk (`local_bodies_in_args`), and the closure is verified first when it is
//!   not yet (`glue::discharge_reached`); the discharge is `failed` at the panicking
//!   callable (an error on strict and certify) and `proved` at the panic-free one;
//! * `use_make_bad` calls the closure a generic `make::<{closure}>` returned: a
//!   concrete call of a local closure, discharged at its instance (`failed`).
//!   Its own native lowering takes the `Fn` shim into the closure as an ABSENT callee
//!   (CLOSURE-ABSENT-CALLEE, `22532b0200`): one fail-closed `PanicFreedom` row, so the
//!   strict refusal is "strict verification failed" (certify adds "Level 0 safety
//!   verification incomplete"); before that commit the whole lowering failed ("full
//!   verification failed").

pub fn use_paths_bad(ms: &[String]) -> Vec<u32> {
    //[strict]~^ ERROR Trust instance discharge not established for `closure_discharge_through_root_instance::use_paths_bad`: 1 instance(s)
    //[strict]~| ERROR Trust strict verification failed for `closure_discharge_through_root_instance::use_paths_bad`
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `closure_discharge_through_root_instance::use_paths_bad`
    //[certify]~| ERROR Trust instance discharge not established for `closure_discharge_through_root_instance::use_paths_bad`: 1 instance(s)
    //[certify]~| ERROR Trust strict verification failed for `closure_discharge_through_root_instance::use_paths_bad`
    paths_of(ms, |s: &str| -> u32 {
        //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `closure_discharge_through_root_instance::use_paths_bad::{closure#0}`
        //[strict]~| ERROR Trust strict verification failed for `closure_discharge_through_root_instance::use_paths_bad::{closure#0}`
        //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `closure_discharge_through_root_instance::use_paths_bad::{closure#0}`
        //[certify]~| ERROR Trust strict verification failed for `closure_discharge_through_root_instance::use_paths_bad::{closure#0}`
        if s.is_empty() {
            panic!("bad");
        }
        1
    })
}

pub fn use_paths_good(ms: &[String]) -> Vec<u32> {
    //[certify]~^ ERROR Trust Level 0 safety verification incomplete for `closure_discharge_through_root_instance::use_paths_good`
    //[certify]~| ERROR Trust strict verification failed for `closure_discharge_through_root_instance::use_paths_good`
    paths_of(ms, |_s: &str| -> u32 { 1 })
}

pub fn paths_of<P: FnMut(&str) -> u32>(modules: &[String], mut paths: P) -> Vec<u32> {
    //[strict]~^ ERROR Trust strict verification failed for `closure_discharge_through_root_instance::paths_of`
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete for `closure_discharge_through_root_instance::paths_of`
    //[certify]~| ERROR Trust strict verification failed for `closure_discharge_through_root_instance::paths_of`
    modules.iter().map(|m| paths(m)).collect()
    //[certify]~^ ERROR Trust certify verification failed for `closure_discharge_through_root_instance::paths_of::{closure#0}`: termination is not established
    //[certify]~| ERROR Trust certify verification failed for `closure_discharge_through_root_instance::paths_of::{closure#0}`: 1 instance hypothesis row(s)
}

pub fn make<F: Fn(u32) -> u32>(f: F) -> impl Fn(u32) -> u32 {
    move |x| f(x)
    //[certify]~^ ERROR Trust certify verification failed for `closure_discharge_through_root_instance::make::{closure#0}`: termination is not established
    //[certify]~| ERROR Trust certify verification failed for `closure_discharge_through_root_instance::make::{closure#0}`: 1 instance hypothesis row(s)
}

pub fn use_make_bad() -> u32 {
    //[strict]~^ ERROR Trust instance discharge not established for `closure_discharge_through_root_instance::use_make_bad`: 1 instance(s)
    //[strict]~| ERROR Trust strict verification failed for `closure_discharge_through_root_instance::use_make_bad`
    //[certify]~^^^ ERROR Trust instance discharge not established for `closure_discharge_through_root_instance::use_make_bad`: 1 instance(s)
    //[certify]~| ERROR Trust Level 0 safety verification incomplete for `closure_discharge_through_root_instance::use_make_bad`
    //[certify]~| ERROR Trust strict verification failed for `closure_discharge_through_root_instance::use_make_bad`
    let g = make(|v: u32| -> u32 {
        //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `closure_discharge_through_root_instance::use_make_bad::{closure#0}`
        //[strict]~| ERROR Trust strict verification failed for `closure_discharge_through_root_instance::use_make_bad::{closure#0}`
        //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `closure_discharge_through_root_instance::use_make_bad::{closure#0}`
        //[certify]~| ERROR Trust strict verification failed for `closure_discharge_through_root_instance::use_make_bad::{closure#0}`
        if v > 1 {
            panic!("bad");
        }
        v
    });
    g(3)
}
