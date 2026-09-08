//@ edition: 2021
//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-AWC): a PURE-VALUE awaitee joins the opaque-carrier binding.
//!
//! The `!is_pure_value_shape` tooth on that admission was written by wave-GI
//! for the FOR lane, where its premise holds: a `Range<usize>` iterator IS
//! modelable and wave-FR implements `Iterator::next` on it, so opaquing it
//! would erase a model the producer actually has.
//!
//! For an AWAITEE the premise is false. The state advance lives entirely inside
//! `Future::poll` — an arbitrary user trait method with no lang-level semantics
//! this producer could ever implement — so the opaque carrier IS the value
//! model, for a pure-value awaitee exactly as much as for a pointer-bearing
//! one. The conjunct was inherited only because B5 stage 3a shared the arm
//! verbatim.
//!
//! The tooth is NOT weakened: the lane adds an affirmative disjunct that
//! requires TWO independent witnesses a user-written `match` cannot supply —
//! rustc's own `MatchSource::AwaitDesugar` stamp (threaded as a parameter with
//! no `Default`, so a forgetful caller is a compile error) AND a one-argument
//! call of the `into_future` lang item.

use core::future::{Future, Ready, ready};
use core::pin::Pin;
use core::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

pub async fn awaits_pure() -> i32 {
    let a: Ready<i32> = ready(7);
    a.await
}

fn noop_waker() -> Waker {
    fn n(_: *const ()) {}
    fn c(_: *const ()) -> RawWaker {
        RawWaker::new(core::ptr::null(), &V)
    }
    static V: RawWakerVTable = RawWakerVTable::new(c, n, n, n);
    unsafe { Waker::from_raw(RawWaker::new(core::ptr::null(), &V)) }
}

fn block_on<F: Future>(mut f: F) -> F::Output {
    let w = noop_waker();
    let mut cx = Context::from_waker(&w);
    loop {
        // SAFETY: `f` is not moved after this point.
        let p = unsafe { Pin::new_unchecked(&mut f) };
        if let Poll::Ready(v) = p.poll(&mut cx) {
            return v;
        }
    }
}

fn main() {
    assert_eq!(block_on(awaits_pure()), 7);
}
