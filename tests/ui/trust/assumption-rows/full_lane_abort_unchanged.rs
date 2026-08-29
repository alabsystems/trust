// Trust (assumption ledger, Stage 1): the explicit crate-under-check strict lane
// stays fail-closed on a coroutine — a hard build error. The abort is the explicit
// executor-protocol rejection emitted by `abort_on_coroutine_protocol_assumption`
// (compiler/rustc_mir_transform/src/trust_verify.rs) on the coroutine DEFINITION.
//
// RE-PINNED 2026-08-22 for D2 (0e9090f03b), which closed a false Certified PROVE on the
// coroutine resume premise and thereby reverted `ca53846043`'s routing: the premise is
// published as an ASSUMPTION row again and the strict lane rejects the DEFINITION —
// exactly the abort this file was written to pin. The 2026-08-19 retarget onto a
// caller-side charge is WITHDRAWN, not weakened: its expectations described a routing
// this binary no longer has, and the guard they replaced is back.
//
// MEASURED on stage2 ec4783d80 with this file's own flags. Nothing in that run is
// attributed to any item other than `tick`, and this is all of it (the pins below are the
// three errors and the raw row; the `note:` summary is quoted, not pinned):
//
//     Trust: ASSUMPTION [coroutine] `full_lane_abort_unchanged::tick::{closure#0}`
//     note: Trust verification: 1 conditionally discharged (NOT proved), 2 failed,
//         0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 5 obligation(s)
//     error: Trust Level 0 safety verification incomplete for `...`: 3 obligation(s)
//         were not proved
//     error: Trust strict verification failed for `...`: coroutine executor-protocol
//         premise is unproved
//     error: Trust strict verification failed for `...`: 3 obligation(s) were not fully
//         verified
//
// `resumes`/`does_not_resume` are kept as the resume vs. no-resume pair, but they carry
// NO expectations, because in THIS lane they produce no Trust diagnostic at all: the run
// emits exactly what is listed above and nothing else. Under `-Ztrust-policy=advisory`
// with otherwise identical
// flags the same two bodies do report, "4 obligation(s) were not proved" and "2
// obligation(s) were not proved"; the two extra rows on `resumes` are its `[assert]` and
// `[unreach]` rows, both runtime-checked. Also measured on that advisory run: the string
// `[trust-coroutine-resume-precondition]` appears NOWHERE in the output, so the
// caller-side charge `ca53846043` added is not what fails this crate. The definition-side
// rejection is, and it is what is pinned. Do not re-add caller-count expectations without
// measuring them in THIS lane.
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ edition: 2021
//@ compile-flags: --crate-type=lib
//@ check-fail
//@ dont-check-compiler-stderr
use std::future::Future;
use std::mem::ManuallyDrop;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};

pub async fn tick(x: u32) -> u32 { x }
//~^ ERROR Trust Level 0 safety verification incomplete
//~| ERROR coroutine executor-protocol premise is unproved
//~| ERROR obligation(s) were not fully verified

// The resume site: a direct in-bundle call to `tick::{closure#0}`.
pub fn resumes(x: u32) -> u32 {
    let mut fut = ManuallyDrop::new(tick(x));
    let pinned = unsafe { Pin::new_unchecked(&mut *fut) };
    let waker = Waker::noop();
    let mut cx = Context::from_waker(waker);
    match pinned.poll(&mut cx) {
        Poll::Ready(v) => v,
        Poll::Pending => 0,
    }
}

// The control: same construction, same unsafe block, no resume.
pub fn does_not_resume(x: u32) -> u32 {
    let mut fut = ManuallyDrop::new(tick(x));
    let pinned = unsafe { Pin::new_unchecked(&mut *fut) };
    let waker = Waker::noop();
    let cx = Context::from_waker(waker);
    let _ = (&pinned, &cx);
    x
}
//~? RAW Trust: ASSUMPTION [coroutine] `full_lane_abort_unchanged::tick::{closure#0}`
