//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//@ edition: 2024
#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]
//! Trust (B5 stage 2): a SINGLE-SUSPEND, capture-free coroutine lowers to a
//! real state machine — no new IR, `Inst::CoroSuspend` has been wired in
//! trust-ir (interpreter, validator, wire format, Lean semantics) since it
//! was introduced.
//!
//!   entry:  %st = load i64 frame[0]      ; frame = param 0 (a POINTER)
//!           switch %st { default => k0, 1 => k1(%resume) }
//!   k0:     coro_suspend frame, slot 0, next 1, value %y
//!   k1(%r): <after the yield; %r IS the resumed value>
//!
//! The signature change (param 0 by-value coroutine -> frame pointer) is why
//! `splice_ok` refuses these bodies: a caller lowered elsewhere still passes
//! the coroutine by value. The dominance gate is the soundness argument —
//! the continuation is entered from the DISPATCH too, so nothing bound
//! before the suspend may be read after it (frame-resident live locals are
//! stage 2b).

use std::ops::Coroutine;
use std::pin::Pin;

fn make() -> impl Coroutine<Yield = u32, Return = u32> {
    #[coroutine]
    || {
        yield 7;
        42
    }
}

fn main() {
    let mut c = make();
    match Pin::new(&mut c).resume(()) {
        std::ops::CoroutineState::Yielded(v) => assert_eq!(v, 7),
        _ => unreachable!(),
    }
    match Pin::new(&mut c).resume(()) {
        std::ops::CoroutineState::Complete(v) => assert_eq!(v, 42),
        _ => unreachable!(),
    }
    let mut u = unit_yield_with_live_local();
    match Pin::new(&mut u).resume(()) {
        std::ops::CoroutineState::Yielded(()) => {}
        _ => unreachable!(),
    }
    match Pin::new(&mut u).resume(()) {
        std::ops::CoroutineState::Complete(v) => assert_eq!(v, 6),
        _ => unreachable!(),
    }
}

// Trust (B5 stage 2b): a bare `yield;` (unit operand — value-less by the
// wave-UV invariant, so it is synthesized, not demanded) and a local LIVE
// ACROSS the suspend (havoc'd in the continuation rather than refused: the
// frame is caller-owned and its layout is unavailable pre-transform, so
// inventing slots would write past memory the caller may not have).
fn unit_yield_with_live_local() -> impl Coroutine<Yield = (), Return = u32> {
    #[coroutine]
    || {
        let keep = 5u32;
        yield;
        keep + 1
    }
}
