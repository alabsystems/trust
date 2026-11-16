//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_lowering.rs` (crate A): runs the
//! `async` closure it is handed, once. Safe, and sound.
#![forbid(unsafe_code)]

use std::future::Future;
use std::task::{Context, Poll, Waker};

pub fn block_on<F: Future>(f: F) -> F::Output {
    let mut f = std::pin::pin!(f);
    let mut cx = Context::from_waker(Waker::noop());
    loop {
        if let Poll::Ready(v) = f.as_mut().poll(&mut cx) {
            return v;
        }
    }
}

pub fn run<F: AsyncFnOnce()>(f: F) {
    block_on(f())
}
