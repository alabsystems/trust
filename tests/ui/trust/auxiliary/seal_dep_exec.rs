//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_async_trust.rs` and its `_holds`
//! twin: a minimal executor that polls a future to completion. Safe, and
//! sound.
#![forbid(unsafe_code)]

use std::future::Future;
use std::sync::Arc;
use std::task::{Context, Poll, Wake, Waker};

struct Noop;
impl Wake for Noop {
    fn wake(self: Arc<Self>) {}
}

pub fn block_on<F: Future>(f: F) -> F::Output {
    let mut f = Box::pin(f);
    let w = Waker::from(Arc::new(Noop));
    let mut cx = Context::from_waker(&w);
    loop {
        if let Poll::Ready(v) = f.as_mut().poll(&mut cx) {
            return v;
        }
    }
}
