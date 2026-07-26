// tRust compatibility guard for rust-lang#49682-shaped code.
//
// Current upstream-compatible Rust accepts this pattern. If tRust later adds a
// verifier-only rejection for cross-thread coroutine use, that check must stay
// out of vanilla upstream compatibility mode.
//@ check-pass

#![feature(coroutines, coroutine_trait, stmt_expr_attributes, thread_local)]

use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;

#[thread_local]
static TLS_VALUE: u32 = 42;

fn main() {
    let mut gen = #[coroutine] || {
        let r = &TLS_VALUE;
        yield;
        let _ = *r;
    };
}
