//@ revisions: advisory strict certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=human --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-fail
//@[certify] check-fail
//! OD-1 item 20 (T6, 2026-10-10; docs/DECISION_QUEUE.md "OD-1-T6-CALLABLE"): the body
//! conjuncts still refuse a closure body the way they refuse a `fn` body. Admitting a
//! PLAIN closure of a plain `fn` (`instance_hypothesis::is_plain_closure_of_fn`) leaves
//! every other body conjunct in force:
//!
//! * `in_unsafe_closure`: a closure body with an unsafe operation (D33's census) admits
//!   no site; its callable call keeps its class (c) `failed` row (the closure's summary
//!   pins 4 failed: that row and the unsafe dereference's three). GLR-1 (2026-10-26,
//!   docs/DECISION_QUEUE.md): the indirect-call gate refuses that same call, so the
//!   closure also publishes the gate's `unknown` `native-verification-gap` row on every
//!   revision (3 unknown of 10, was 2 of 9), a second disclosure beside the `failed` row;
//! * `in_async_block`: a coroutine is no plain closure and admits nothing.

pub fn in_unsafe_closure<F: Fn(u32) -> u32>(f: F, p: *const u32) -> u32 {
    //[strict]~^ ERROR Trust strict verification failed for `closure_body_fences_not_admitted::in_unsafe_closure`
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete for `closure_body_fences_not_admitted::in_unsafe_closure`
    //[certify]~| ERROR Trust strict verification failed for `closure_body_fences_not_admitted::in_unsafe_closure`
    let g = || f(unsafe { *p });
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `closure_body_fences_not_admitted::in_unsafe_closure::{closure#0}`
    //[strict]~| ERROR Trust strict verification failed for `closure_body_fences_not_admitted::in_unsafe_closure::{closure#0}`
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `closure_body_fences_not_admitted::in_unsafe_closure::{closure#0}`
    //[certify]~| ERROR Trust certify verification failed for `closure_body_fences_not_admitted::in_unsafe_closure::{closure#0}`: termination is not established
    //[certify]~| ERROR Trust strict verification failed for `closure_body_fences_not_admitted::in_unsafe_closure::{closure#0}`
    //~^^^^^^ NOTE Trust verification: 1 proved, 4 failed, 3 unknown, 0 timed out, 0 runtime-checked, 2 skipped out of 10 obligation(s)
    g()
}

pub fn in_async_block<F: Fn(u32) -> u32>(f: F) -> impl core::future::Future<Output = u32> {
    async move { f(1) }
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `closure_body_fences_not_admitted::in_async_block::{closure#0}`
    //[strict]~| ERROR Trust strict verification failed for `closure_body_fences_not_admitted::in_async_block::{closure#0}`: coroutine executor-protocol premise is unproved
    //[strict]~| ERROR Trust strict verification failed for `closure_body_fences_not_admitted::in_async_block::{closure#0}`: 1 obligation(s)
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `closure_body_fences_not_admitted::in_async_block::{closure#0}`
    //[certify]~| ERROR Trust strict verification failed for `closure_body_fences_not_admitted::in_async_block::{closure#0}`: coroutine executor-protocol premise is unproved
    //[certify]~| ERROR Trust strict verification failed for `closure_body_fences_not_admitted::in_async_block::{closure#0}`: 1 obligation(s)
}
