//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// B5 stage 3a: the CALLER half of the coroutine frame protocol.
// `let mut a = #[coroutine] || { .. yield .. };` mints a caller-owned frame
// (`Alloca I64`, state seeded 0) ONLY under the whole-body witness — every
// `VarRef` of the var in the THIR arena is consumed by a recognized
// `Pin::new(&mut a).resume(())` peel — and each resume lowers as a force-havoc
// declaration call `@coroutine(frame)` followed by the DONE-sentinel read:
// `load i64 frame; icmp eq COROUTINE_DONE_STATE; condbr` into the two
// `CoroutineState` variant constants merged through a join param. Fences (v1):
// plain local coroutine, resume/yield/return all unit, `CoroutineState` the
// lang-item enum registered with two single-unit-payload variants, the resume
// argument a trivial `()`. An ESCAPED var (any use outside the recognized
// peel) never mints a frame and each resume refuses with
// `CoroutineResume(unframed receiver)` — see `escaped` below, which must keep
// its refusal (the exclusivity proof is what makes the frame the var's single
// home). Design of record:
// docs/design/2026-08-31-b5-stage3-resume-driving-entry.md.
#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]

use std::ops::Coroutine;
use std::pin::Pin;

// The single-resume discard shape (live-upvar-across-yield's `main`).
pub fn drive() -> i64 {
    let mut a = #[coroutine]
    || {
        yield;
    };
    Pin::new(&mut a).resume(());
    7
}

// Two sequential resumes on ONE frame (conditional-drop's `t1`/`t2` shape):
// the ledger row is per-var, so both calls pass the same slot and the second
// resume observes whatever state the first call's callee stored.
pub fn drive_twice() -> i64 {
    let mut g = #[coroutine]
    || {
        yield;
        yield;
    };
    Pin::new(&mut g).resume(());
    Pin::new(&mut g).resume(());
    3
}

// A CAPTURING coroutine still frames: the frame is `[state]` only and the
// produced callee (stage 2d) HAVOCs every upvar read, so no capture payload is
// ever dereferenced through the frame pointer.
pub fn drive_capturing(seed: i64) -> i64 {
    let mut c = #[coroutine]
    move || {
        let _s = seed;
        yield;
    };
    Pin::new(&mut c).resume(());
    seed
}

// The let-bound result: a `CoroutineState<(), ()>` enum value flows into an
// ordinary binding (the join param IS the value; nothing else consumes it).
pub fn drive_bound() -> i64 {
    let mut a = #[coroutine]
    || {
        yield;
    };
    let _st = Pin::new(&mut a).resume(());
    11
}

// NEGATIVE — the escape witness: `e` is also passed by reference to an opaque
// sink, so the whole-body witness fails, no frame exists, and the resume call
// keeps a fail-closed refusal (`CoroutineResume(unframed receiver)`). This fn
// must NOT lower; it pins the exclusivity proof.
pub fn sink<T>(_: &mut T) {}
pub fn escaped() -> i64 {
    let mut e = #[coroutine]
    || {
        yield;
    };
    sink(&mut e);
    Pin::new(&mut e).resume(());
    9
}
