//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-OPA): the opaque-carrier gate's head test becomes a MENTIONS
//! test.
//!
//! An `AliasTyKind::Opaque` head sets HAS_TY_OPAQUE on itself, so the shipped
//! `matches!(a.kind, Opaque)` implies `ty.has_opaque_types()` — every type
//! admitted today is still admitted, byte-identically, at the same carrier.
//! What it adds is the case where the unrevealed opaque is NESTED in a
//! Projection's args rather than being the head, which the disjunction below
//! would otherwise fail closed on its own `has_opaque_types()` disjunct. Every
//! new admission is a strict SUBSET of what the arm refuses today.
//!
//! Nothing is revealed either way: the carrier is NAMED, so the E0391
//! reentrancy hazard of asking for a hidden type inside `mir_built` is
//! untouched, and the differential's `mir.has_opaque_types()` gate answers
//! NotRun before any signature check — coverage, never Agreed.

pub trait Pair {
    type Out;
    fn out(self) -> Self::Out;
}

impl Pair for u32 {
    type Out = u32;
    fn out(self) -> u32 {
        self + 1
    }
}

pub fn mk() -> impl Pair<Out = u32> {
    5u32
}

pub fn nested_projection_over_opaque() -> u32 {
    mk().out()
}

fn main() {
    assert_eq!(nested_projection_over_opaque(), 6);
}
