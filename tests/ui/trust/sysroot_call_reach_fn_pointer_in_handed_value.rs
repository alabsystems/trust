//@ revisions: wake_by_ref wake wake_by_ref_certify context_wake_by_ref waker_in_vec waker_in_option
//@ revisions: arguments_handed arguments_handed_certify local_key_handed noop_waker_cost
//@ revisions: waker_clone_pin waker_drop_pin will_wake poll_with_handed_context
//@ revisions: context_from_handed_waker waker_data format_local format_local_certify
//@ revisions: format_str_param format_str_param_certify format_vec_param println_local
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[wake_by_ref_certify] compile-flags: -Ztrust-policy=certify
//@[arguments_handed_certify] compile-flags: -Ztrust-policy=certify
//@[format_local_certify] compile-flags: -Ztrust-policy=certify
//@[format_str_param_certify] compile-flags: -Ztrust-policy=certify
//@[wake_by_ref] check-fail
//@[wake] check-fail
//@[wake_by_ref_certify] check-fail
//@[context_wake_by_ref] check-fail
//@[waker_in_vec] check-fail
//@[waker_in_option] check-fail
//@[arguments_handed] check-fail
//@[arguments_handed_certify] check-fail
//@[local_key_handed] check-fail
//@[noop_waker_cost] check-fail
//@[waker_clone_pin] check-fail
//@[waker_drop_pin] check-fail
//@[will_wake] check-pass
//@[poll_with_handed_context] check-pass
//@[context_from_handed_waker] check-pass
//@[waker_data] check-pass
//@[format_local] check-pass
//@[format_local_certify] check-pass
//@[format_str_param] check-pass
//@[format_str_param_certify] check-pass
//@[format_vec_param] check-pass
//@[println_local] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! CALL-REACH-1 D7 (2026-10-13, docs/DECISION_QUEUE.md CALL-REACH-1-D7): a `fn`
//! pointer stored in a FIELD of a std value the verified body was HANDED, and called
//! inside the sysroot call it is passed to.
//!
//! D2 made a call through a `fn` pointer a leaf of the call walk ("a pointer the
//! instance was handed was built where the value was made"); D6 turned that leaf off
//! while the call hands the instance a `fn` pointer TYPE. A `Waker`'s
//! `RawWakerVTable` is not a type argument: `w.wake_by_ref()` on a handed `&Waker`
//! runs the vtable function the caller's caller chose. BEFORE (stage 1 of main
//! `3ed8b09dad`): `closed(walk)`, then exit 0 under the default policy with one
//! runtime-checked row (certify refused) for `wake_by_ref`, `wake`,
//! `context_wake_by_ref`, `waker_in_vec`, `waker_in_option`, `arguments_handed` (a
//! handed `fmt::Arguments`, whose `rt::Argument` formatters the caller chose) and
//! `local_key_handed` (a handed `LocalKey`'s `inner` accessor, KNOWN_HAZARDS' D6
//! review entry); `noop_waker_cost` too.
//!
//! AFTER: an argument whose type holds a `fn` pointer in a field and whose VALUE is not
//! shown built in the calling body (a parameter, a value read from one, any call result
//! but a `format_args!` builder's) turns D2's leaf off as D6 does, so the walk opens and
//! the bridge withdraws the callee into a counted fail-closed absent-callee row.
//!
//! The controls pin what must not move: a handed waker or context passed to a call
//! that makes no pointer call (`will_wake`, `Pending::poll`, `Context::from_waker`,
//! `Waker::data`) stays `closed(walk)`, and every `format_args!` the body builds
//! itself (`format!`, `println!`), over a handed `&str` or `&Vec<u32>` too, keeps
//! D2's leaf, under certify where it was accepted there. `noop_waker_cost` is the cost
//! row: `Waker::noop()` is a sysroot call result, which D7 does not tell apart from a
//! handed waker. `waker_clone_pin` and `waker_drop_pin` were already refused (the
//! clone's and the destructor's own lanes) and stay refused.

#![allow(dead_code)]

use std::fmt;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};

#[cfg(any(wake_by_ref, wake_by_ref_certify))]
pub fn f(w: &Waker) {
    //[wake_by_ref]~^ ERROR Trust strict verification failed for `sysroot_call_reach_fn_pointer_in_handed_value::f`
    w.wake_by_ref()
}

#[cfg(wake)]
pub fn f(w: Waker) {
    //[wake]~^ ERROR Trust strict verification failed for `sysroot_call_reach_fn_pointer_in_handed_value::f`
    w.wake()
}

#[cfg(context_wake_by_ref)]
pub fn f(cx: &mut Context<'_>) {
    //[context_wake_by_ref]~^ ERROR Trust strict verification failed for `sysroot_call_reach_fn_pointer_in_handed_value::f`
    cx.waker().wake_by_ref()
}

#[cfg(waker_in_vec)]
pub fn f(v: &Vec<Waker>) {
    //[waker_in_vec]~^ ERROR Trust strict verification failed for `sysroot_call_reach_fn_pointer_in_handed_value::f`
    for w in v {
        w.wake_by_ref()
    }
}

#[cfg(waker_in_option)]
pub fn f(o: Option<Waker>) {
    //[waker_in_option]~^ ERROR Trust strict verification failed for `sysroot_call_reach_fn_pointer_in_handed_value::f`
    if let Some(w) = o {
        w.wake()
    }
}

#[cfg(any(arguments_handed, arguments_handed_certify))]
pub fn f(a: fmt::Arguments<'_>) -> String {
    //[arguments_handed]~^ ERROR Trust strict verification failed for `sysroot_call_reach_fn_pointer_in_handed_value::f`
    std::fmt::format(a)
}

#[cfg(local_key_handed)]
pub fn f(k: &'static std::thread::LocalKey<std::cell::Cell<u32>>) -> u32 {
    //[local_key_handed]~^ ERROR Trust strict verification failed for `sysroot_call_reach_fn_pointer_in_handed_value::f`
    k.with(|c| c.get())
}

#[cfg(noop_waker_cost)]
pub fn f() {
    //[noop_waker_cost]~^ ERROR Trust strict verification failed for `sysroot_call_reach_fn_pointer_in_handed_value::f`
    Waker::noop().wake_by_ref()
}

#[cfg(waker_clone_pin)]
pub fn f(w: &Waker) -> Waker {
    w.clone()
}

#[cfg(waker_drop_pin)]
pub fn f(w: Waker) {
    drop(w)
}

#[cfg(will_wake)]
pub fn f(a: &Waker, b: &Waker) -> bool {
    a.will_wake(b)
}

#[cfg(poll_with_handed_context)]
pub fn f(cx: &mut Context<'_>) -> Poll<()> {
    let mut r = std::future::pending::<()>();
    Pin::new(&mut r).poll(cx)
}

#[cfg(context_from_handed_waker)]
pub fn f(w: &Waker) -> Poll<()> {
    let mut cx = Context::from_waker(w);
    let mut r = std::future::pending::<()>();
    Pin::new(&mut r).poll(&mut cx)
}

#[cfg(waker_data)]
pub fn f(w: &Waker) -> *const () {
    w.data()
}

#[cfg(any(format_local, format_local_certify))]
pub fn f(x: u32) -> String {
    format!("{}", x)
}

#[cfg(any(format_str_param, format_str_param_certify))]
pub fn f(s: &str) -> String {
    format!("{s}!")
}

#[cfg(format_vec_param)]
pub fn f(v: &Vec<u32>) -> String {
    format!("{:?}", v)
}

#[cfg(println_local)]
pub fn f(x: u32) {
    println!("{x}")
}
