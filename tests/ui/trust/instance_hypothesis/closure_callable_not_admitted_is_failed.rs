//~ NOTE indirect call `<F as core::ops::function::FnMut<(&mut u32,)>>::call_mut` through an untypeable callable receiver
//~| NOTE "outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked:trust-full-verifier"
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
//! controls. Admitting plain closure bodies changes no other admission conjunct, so
//! each of these callable shapes stays NOT admitted and keeps its fail-closed row:
//!
//! * `bump_in_closure`: the rust-call argument tuple `(&mut u32,)` hands the callee a
//!   `&mut` by value, which the one-level havoc does not cover (item 14(a)'s
//!   non-admitted shape, now inside a closure): class (c), `failed`;
//! * `visit_mut`: a closure capturing `&mut u32` handed BY VALUE to an open dispatch
//!   (`<V as Visit>::visit`): an adversarial `Visit` impl may call it, and it writes
//!   through the capture, which the havoc does not reach ("a by-value argument that
//!   holds a `&mut`"): class (c), `failed` — a closure capturing `&mut` stays refused
//!   as an argument;
//! The body-level controls (an unsafe closure body, a coroutine) are in
//! `closure_body_fences_not_admitted.rs`: compiletest keeps only the first 512 KiB of a
//! compile's stderr, and the JSON rows of these four bodies cross it.

pub fn bump_in_closure<F: FnMut(&mut u32)>(mut f: F, x: &mut u32) {
    //[strict]~^ ERROR Trust strict verification failed for `closure_callable_not_admitted_is_failed::bump_in_closure`
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete for `closure_callable_not_admitted_is_failed::bump_in_closure`
    //[certify]~| ERROR Trust strict verification failed for `closure_callable_not_admitted_is_failed::bump_in_closure`
    let mut g = |v: &mut u32| f(v);
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `closure_callable_not_admitted_is_failed::bump_in_closure::{closure#0}`
    //[strict]~| ERROR Trust strict verification failed for `closure_callable_not_admitted_is_failed::bump_in_closure::{closure#0}`
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `closure_callable_not_admitted_is_failed::bump_in_closure::{closure#0}`
    //[certify]~| ERROR Trust certify verification failed for `closure_callable_not_admitted_is_failed::bump_in_closure::{closure#0}`: termination is not established
    //[certify]~| ERROR Trust strict verification failed for `closure_callable_not_admitted_is_failed::bump_in_closure::{closure#0}`
    g(x)
}

pub trait Visit {
    fn visit<G: FnMut(u32)>(&self, g: G);
}

pub fn visit_mut<V: Visit>(v: &V, acc: &mut u32) {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `closure_callable_not_admitted_is_failed::visit_mut`
    //[strict]~| ERROR Trust strict verification failed for `closure_callable_not_admitted_is_failed::visit_mut`
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `closure_callable_not_admitted_is_failed::visit_mut`
    //[certify]~| ERROR Trust strict verification failed for `closure_callable_not_admitted_is_failed::visit_mut`
    v.visit(|x| *acc = x)
}
