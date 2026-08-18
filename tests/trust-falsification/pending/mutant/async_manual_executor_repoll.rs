#![crate_type = "lib"]
// PENDING adversarial fixture for the coroutine resume-state CONTRACT lane
// (piece #13 step-3; sibling of proved/async_zero_await_widen.rs).
//
// A hand-rolled IN-CRATE executor that polls the zero-await future AGAIN after
// it returned `Poll::Ready` — the exact executor-protocol violation
// (`Future::poll` after completion may panic: rustc's coroutine lowers the
// second resume onto the `ResumedAfterReturn` sentinel) that the coroutine
// body's exported `contract:coroutine-resume-state` precondition (resume state
// ∈ {0}) forbids. This crate MUST NOT verify clean (exit != 0): the coroutine
// body's sentinel proofs are conditional on every caller establishing the
// resume state, and this caller violates it.
//
// EXPECTED verdict (post-rebuild): rc 1, honest INCOMPLETE — the bridge mints
// an unprovable caller-side `[trust-coroutine-resume-precondition]`
// Precondition obligation at every in-bundle poll/resume callsite (no
// caller-side discharge lane exists yet), and the std `Waker`/`Context`/`Pin`
// plumbing additionally keeps absent-callee rows red. It sits in pending/, NOT
// mutant/: the gate's mutant lane requires an explicit REFUTATION verdict
// ('Level 0 summary: N failed'), and honestly refuting a re-poll needs the
// follow-on caller-side discharge lane (prove the FIRST poll's precondition,
// refute the SECOND). PROMOTE to mutant/ when that lane can refute; the
// soundness bar meanwhile is only "never rc 0".
//
// SOUNDNESS PIN: if this crate EVER verifies clean (rc 0), the contract lane
// has silently swallowed a callsite obligation — a P0 fail-open, exactly the
// class the plan's constraint "NEVER swallow callsite obligations" names.
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

async fn f(x: u8) -> u16 {
    (x as u16) + 1
}

fn noop_raw_waker() -> RawWaker {
    const VTABLE: RawWakerVTable =
        RawWakerVTable::new(|_| noop_raw_waker(), |_| {}, |_| {}, |_| {});
    RawWaker::new(std::ptr::null(), &VTABLE)
}

pub fn poll_after_ready(x: u8) -> u16 {
    let mut fut = f(x);
    // SAFETY: `fut` lives on this frame for the whole call and is never moved
    // after being pinned; the pin is dropped before the frame unwinds.
    let mut fut = unsafe { Pin::new_unchecked(&mut fut) };
    // SAFETY: the vtable is a no-op waker over a null data pointer; every
    // vtable entry ignores the pointer, so no dereference ever occurs.
    let waker = unsafe { Waker::from_raw(noop_raw_waker()) };
    let mut cx = Context::from_waker(&waker);
    let first = fut.as_mut().poll(&mut cx);
    // EXECUTOR-PROTOCOL VIOLATION: the zero-await future completed on the
    // first poll; polling again resumes a RETURNED coroutine (state 1, outside
    // the exported live set {0}) and hits the ResumedAfterReturn panic.
    let second = fut.as_mut().poll(&mut cx);
    match (first, second) {
        (Poll::Ready(v), _) => v,
        _ => 0,
    }
}
