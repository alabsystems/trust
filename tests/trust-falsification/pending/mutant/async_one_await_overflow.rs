#![crate_type = "lib"]
// MUTANT sibling of pending/proved/async_one_await_widen.rs. The widen is
// dropped on the resumed value: `x + y` on u8 OVERFLOWS (x = 249, y = 7 wraps;
// both operands are havoc'd u8 to the solver, so any model with x + y > 255
// refutes). MUST fail closed (exit 1) with a genuine overflow REFUTATION on
// the coroutine body's data obligation.
//
// SOUNDNESS PIN (validation (3b) of the contract-lane plan): the one-await
// entry contract `state ∈ {0, 3}` constrains ONLY the resume-state selector.
// If this mutant ever verifies, the contract leaked a data fact — e.g.
// constrained an across-await saved local or the captured `x` — which is the
// "NEVER constrain captured data / frame fields" violation. Pending/ for the
// same reason as its proved sibling (in-crate executor plumbing rows); the
// refutation itself is expected to hold already.
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

pub struct YieldOnce(bool);

impl Future for YieldOnce {
    type Output = u8;
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<u8> {
        if self.0 {
            Poll::Ready(7)
        } else {
            self.0 = true;
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    }
}

pub async fn g(x: u8) -> u8 {
    let y = YieldOnce(false).await;
    x + y
}
