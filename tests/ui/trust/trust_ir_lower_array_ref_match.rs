//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//@ edition: 2021
//! Trust (wave-ADP): `match v { … }` on `v: &[T; N]` -- the reference peel with no `Borrow` node
//! to peel.
//!
//! The producer refused this shape for one reason only: there was no THIR `Deref` to route on.
//! `match *v { … }` is ALREADY CLEAN and rustc's MIR for the two spellings is byte-identical
//! (both `switchInt(copy (*_1)[j of N])` chains), and wave-MRB already peels exactly this shape
//! when the scrutinee is a WRITTEN `&e` -- so `match &[97u8, 10u8] { b"a\n" => 1, _ => 2 }` was
//! clean while the same match through a ref-typed variable was refused. The missing operation is
//! a single `Inst::Load` of the pointee, which the `Deref` arm already emits under an allow-list
//! that explicitly contains both mapped array spellings.
//!
//! THE FREEZE GATE IS THE SOUNDNESS ARGUMENT, and the lane looks obviously safe until you check
//! one thing. The lane replaces rustc's per-arm re-read of `(*_1)[j]` with ONE up-front load,
//! and `lower_tuple_match` ADMITS GUARDED ARMS -- measured: `match *v { [97, 10] if v[0] == 97
//! => 1, _ => 2 }` compiles clean -- so user code genuinely runs between arm tests. One snapshot
//! is equivalent only if nothing can change the referent in between, and shared-`&` plus a
//! FROZEN pointee is exactly that: with no `UnsafeCell` in the referent no safe code can mutate
//! through a shared reference, and borrowck freezes it against `&mut` for the whole match. The
//! attack is LIVE rather than hypothetical -- `&[Cell<u8>; 1]` refuses today with this very tag,
//! so a lane without the gate would have claimed it and a mutating guard would then read a stale
//! snapshot: a WRONG VALUE, not a coverage gap. The gate is on the POINTEE and not on the guard,
//! because a guard mutating an unrelated `Cell` is fine.
//!
//! BOTH mapped array spellings are admitted, and that is load-bearing: an in-file comment
//! asserts `map_ty` gives `[T; N>0]` a `Ty::Tuple`, but read at the source it is `Ty::Array` for
//! a scalar element and `Ty::Tuple` only for an aggregate element. Every measured body is `u8`,
//! i.e. the `Ty::Array` half, so admitting one spelling would have dropped the whole class.
//!
//! Not under `=strict`: the negative pins below must keep their tags.

#![allow(dead_code)]

use std::cell::Cell;

// THE LANE: the corpus shape.
pub fn byte_string(v: &[u8; 2]) -> i32 {
    match v {
        b"a\n" => 1,
        _ => 2,
    }
}

// The ALREADY-CLEAN twin, whose MIR is byte-identical. It is the semantic evidence for the lane
// and must stay clean.
pub fn peeled(v: &[u8; 2]) -> i32 {
    match *v {
        [97u8, 10u8] => 1,
        _ => 2,
    }
}

// The wave-MRB twin: a WRITTEN `&e`, clean before this wave via the borrow peel.
pub fn written_ref() -> i32 {
    match &[97u8, 10u8] {
        b"a\n" => 1,
        _ => 2,
    }
}

// A GUARDED arm through the peel -- admitted, because `[u8; 2]` is frozen.
pub fn guarded(v: &[u8; 2]) -> i32 {
    match v {
        [97, 10] if v[0] == 97 => 1,
        _ => 2,
    }
}

// FAIL-CLOSED: a NON-FROZEN pointee. This is the live attack, and if it ever lowers clean the
// lane has a wrong value waiting for someone to write the mutating guard.
pub fn interior_mutable(v: &[Cell<u8>; 1]) -> i32 {
    match v {
        [_] => 1,
    }
}

// FAIL-CLOSED: `&mut` -- the write channel is unmodeled and the referent is not frozen.
pub fn mutable_ref(v: &mut [u8; 2]) -> i32 {
    match v {
        [97, 10] => 1,
        _ => 2,
    }
}

// FAIL-CLOSED: a zero-length array has no element to test.
pub fn empty(v: &[u8; 0]) -> i32 {
    match v {
        [] => 1,
    }
}

// FAIL-CLOSED: a CONST-GENERIC length is not a known usize, and the body stays symbolic.
pub fn generic_len<const N: usize>(v: &[u8; N]) -> i32 {
    match v {
        _ => 1,
    }
}

// FAIL-CLOSED: a top-level BINDING would bind the REFERENCE, and this lane materializes no
// pointer -- so the arm does not peel and the whole plan is refused before anything is emitted.
pub fn binds_the_reference(v: &[u8; 2]) -> i32 {
    match v {
        r => r[0] as i32,
    }
}

fn main() {}
