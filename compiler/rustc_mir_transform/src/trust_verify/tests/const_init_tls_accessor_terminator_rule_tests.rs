//! R16 FRONT A — mutation pins on the ONE rule that separates a
//! CONST-INITIALIZED thread-local accessor from every other storage shape.
//!
//! `library/std/src/sys/thread_local/native/mod.rs` emits four accessors:
//!
//! ```text
//!   const + !Drop  ->  |_| { #[thread_local] static VAL: T = INIT; &VAL }   // NO calls
//!   const +  Drop  ->  |_| EagerStorage::<T>::get(&VAL)                     // one Call
//!   lazy  + !Drop  ->  |i| LazyStorage::<T, !>::get_or_init(&VAL, i, __rust_std_internal_init_fn)
//!   lazy  +  Drop  ->  |i| LazyStorage::<T, ()>::get_or_init(&VAL, i, __rust_std_internal_init_fn)
//! ```
//!
//! Measured on the deployed driver sha256:c1aa6ca629447701 (probe crate `P`,
//! `-Ztrust-dump=mir`): `P::CONSTP::{constant#0}::{closure#1}` has the single
//! terminator `Return`, while `P::LAZYP::{constant#0}::{closure#0}` and
//! `{closure#1}` each carry
//! `Call std::sys::thread_local::native::lazy::Storage::<Cell<bool>, _>::get_or_init::<fn() -> Cell<bool> {P::LAZYP::__rust_std_internal_init_fn}>`.
//! So "zero `Call` terminators" is the positive const-init discriminator, and
//! tolerating even ONE `Call` here re-opens false proof #13's exact hole: the
//! caller of a key whose USER-WRITTEN initializer panics would be admitted.
//!
//! THE MUTANT (campaign lesson 7): widen
//! `tls_accessor_terminator_cannot_call_or_panic` to also accept
//! `TerminatorKind::Call { .. }` — the naive "the accessor is just a getter"
//! move — and `a_call_terminator_is_the_lazy_accessor_and_must_decline` goes
//! RED. Widening it to accept `Assert` turns
//! `a_panicking_terminator_must_decline` RED. The green cases below stay green
//! under both mutants, so these pins DISCRIMINATE rather than pass vacuously.

use rustc_middle::mir::{
    BasicBlock, CallSource, Local, Operand, Place, SwitchTargets, TerminatorKind, UnwindAction,
};
use rustc_span::DUMMY_SP;

use super::super::tls_accessor_terminator_cannot_call_or_panic;

fn place() -> Place<'static> {
    Place::from(Local::from_u32(1))
}

#[test]
fn the_const_init_accessor_shape_is_admitted() {
    // `|_| { #[thread_local] static VAL: T = INIT; &VAL }` lowers to a
    // ThreadLocalRef statement plus `Return`. Nothing else is needed, and the
    // three remaining control-flow-only kinds must stay admitted so a
    // slightly different (still call-free, still panic-free) lowering does not
    // silently make the whole lane inert.
    assert!(tls_accessor_terminator_cannot_call_or_panic(&TerminatorKind::Return));
    assert!(tls_accessor_terminator_cannot_call_or_panic(&TerminatorKind::Unreachable));
    assert!(tls_accessor_terminator_cannot_call_or_panic(&TerminatorKind::Goto {
        target: BasicBlock::from_u32(0),
        loop_hint_attrs: Default::default()
    }));
    assert!(tls_accessor_terminator_cannot_call_or_panic(&TerminatorKind::SwitchInt {
        discr: Operand::Copy(place()),
        targets: SwitchTargets::new(std::iter::empty(), BasicBlock::from_u32(0)),
    }));
}

#[test]
fn a_call_terminator_is_the_lazy_accessor_and_must_decline() {
    // THE pin. A lazy `thread_local!`'s accessor differs from the const-init
    // one ONLY by this call, whose third argument is the user's
    // `__rust_std_internal_init_fn`. Admitting `Call` here would admit
    // `LAZYP` — the R15 witness whose initializer is `panic!("init boom")` —
    // and stamp its caller statically panic-free.
    assert!(!tls_accessor_terminator_cannot_call_or_panic(&TerminatorKind::Call {
        func: Operand::Copy(place()),
        args: Box::new([]),
        destination: place(),
        target: None,
        unwind: UnwindAction::Continue,
        call_source: CallSource::Misc,
        fn_span: DUMMY_SP,
    }));
    assert!(!tls_accessor_terminator_cannot_call_or_panic(&TerminatorKind::TailCall {
        func: Operand::Copy(place()),
        args: Box::new([]),
        fn_span: DUMMY_SP,
    }));
}

#[test]
fn a_panicking_terminator_must_decline() {
    // The other two ways a body with no calls could still panic: an `Assert`
    // (bounds/overflow/division) and drop glue.
    assert!(!tls_accessor_terminator_cannot_call_or_panic(&TerminatorKind::Assert {
        cond: Operand::Copy(place()),
        expected: true,
        msg: Box::new(rustc_middle::mir::AssertKind::OverflowNeg(Operand::Copy(place()))),
        target: BasicBlock::from_u32(0),
        unwind: UnwindAction::Continue,
    }));
    assert!(!tls_accessor_terminator_cannot_call_or_panic(&TerminatorKind::Drop {
        place: place(),
        target: BasicBlock::from_u32(0),
        unwind: UnwindAction::Continue,
        replace: false,
        drop: None,
    }));
}

#[test]
fn unwind_and_coroutine_terminators_decline() {
    // Not panic SOURCES, but nothing in the const-init accessor shape
    // produces them either; keeping them out preserves the "this body is
    // exactly the eager `&VAL` read" claim rather than a weaker one.
    assert!(!tls_accessor_terminator_cannot_call_or_panic(&TerminatorKind::UnwindResume));
    assert!(!tls_accessor_terminator_cannot_call_or_panic(&TerminatorKind::UnwindTerminate(
        rustc_middle::mir::UnwindTerminateReason::Abi
    )));
    assert!(!tls_accessor_terminator_cannot_call_or_panic(&TerminatorKind::CoroutineDrop));
}
