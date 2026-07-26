// Regression test for rust-lang#63818 / tRust#915
//
// Async functions capture their parameters into the coroutine state struct.
// After the async transform, the future holds both the parameter value and
// references to it. LLVM's noalias attribute on these parameters incorrectly
// assumes they don't alias the coroutine state, causing miscompilation.
//
// This test verifies that the pattern compiles and runs correctly — i.e.,
// that noalias is NOT applied to coroutine parameters that may become
// self-referential after the async transform.

//@ edition: 2021
//@ run-pass

async fn takes_ref(x: &i32) -> i32 {
    // Yield point — forces x to be captured into the coroutine state.
    // After the async transform, the future struct holds both the captured
    // reference and the data it points to, creating potential self-aliasing.
    tokio_yield().await;
    *x
}

async fn self_referential_pattern() -> i32 {
    let val = 42;
    // The reference &val is passed to takes_ref. In the coroutine state,
    // both `val` and the reference to it coexist — self-referential.
    takes_ref(&val).await
}

// Minimal yield implementation without external dependencies
async fn tokio_yield() {
    use std::future::Future;
    use std::pin::Pin;
    use std::task::{Context, Poll};

    struct YieldOnce(bool);

    impl Future for YieldOnce {
        type Output = ();
        fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
            if self.0 {
                Poll::Ready(())
            } else {
                self.0 = true;
                cx.waker().wake_by_ref();
                Poll::Pending
            }
        }
    }

    YieldOnce(false).await
}

fn main() {
    // Drive the future to completion using a minimal executor
    use std::future::Future;
    use std::pin::pin;
    use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

    fn noop_raw_waker() -> RawWaker {
        fn no_op(_: *const ()) {}
        fn clone(p: *const ()) -> RawWaker {
            RawWaker::new(p, &VTABLE)
        }
        const VTABLE: RawWakerVTable = RawWakerVTable::new(clone, no_op, no_op, no_op);
        RawWaker::new(std::ptr::null(), &VTABLE)
    }

    let waker = unsafe { Waker::from_raw(noop_raw_waker()) };
    let mut cx = Context::from_waker(&waker);

    let mut fut = pin!(self_referential_pattern());

    loop {
        match fut.as_mut().poll(&mut cx) {
            Poll::Ready(val) => {
                assert_eq!(val, 42);
                break;
            }
            Poll::Pending => continue,
        }
    }
}
