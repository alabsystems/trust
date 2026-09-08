//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//@ edition: 2021
//! Trust (wave-VVM): the VACUOUS match, generalized off wave-VRM's shared-ref shape to EVERY
//! scrutinee type `lower_match`'s scrutinee-kind catch-all refuses. A single unguarded arm whose
//! pattern tests nothing and binds nothing is not a dispatch at all: rustc's own MIR for it is a
//! `goto` into the arm body, so the lane emits the body and nothing else.
//!
//! PLACEMENT IS THE SOUNDNESS ARGUMENT, and it is why this is not wave-VRM widened in place.
//! wave-VRM runs BEFORE the scrutinee-kind split, so generalizing it there would have claimed
//! INTEGER scrutinees too — bodies that lower clean today through the `Switch` path, whose IR
//! would silently change shape and whose derived-MIR channel would then have to re-agree. This
//! lane sits inside the arm that is about to push a refusal, so every body reaching it is
//! already dirty: became-dirty is zero by construction and the histogram can only move down.
//! Same argument wave-MRB and wave-VRM each made for their own placement.
//!
//! The SCRUTINEE IS NOT LOWERED, so it must be PROVEN effect-free — `effect_free_closure_receiver`'s
//! allow-list (`Scope`/`Use`/`Borrow` wrappers, built-in `&T` derefs, non-union field
//! projections, bottoming out at a pure `VarRef`/`UpvarRef` place read or a capture-effect-free
//! closure literal). Nothing is moved and nothing is dropped either: a pattern the vacuity
//! predicate admits contains no `Binding`, so the scrutinee place is not moved out of and the
//! match introduces no drop obligation.
//!
//! Not under `=strict`: several of these bodies are confined for OTHER reasons (the union ones
//! by wave-UVL's `union_lane`), so the derived-MIR channel has nothing to compare for them.

#![allow(dead_code, unused_variables)]

#[repr(C)]
union U {
    a: u32,
    b: f32,
}

struct S {
    x: u32,
    y: u32,
}

// The corpus shape (`tests/ui/union/union_wild_or_wild.rs`): a UNION scrutinee whose pattern is
// a `Leaf` over an `Or` of two `Wild`s. Both halves of the vacuity predicate are exercised —
// `Leaf`'s all-fields recursion and `Or`'s all-alternatives recursion.
pub fn union_wild_or_wild(v: u32) -> u32 {
    let u = U { a: v };
    match u {
        U { a: _ | _ } => {}
    }
    v + 1
}

// A FLOAT scrutinee. Float pattern equality is a semantics decision the producer refuses to
// make (`Match(float scrutinee)`) — but a pattern that never compares anything asks nothing of
// that decision, which is exactly why the lane is keyed on the PATTERN and not on the type.
pub fn float_wild(f: f64, k: u32) -> u32 {
    match f {
        _ => k + 1,
    }
}

// An ARRAY scrutinee under a `Leaf`-free bare `_`.
pub fn array_wild(a: [u32; 4], k: u32) -> u32 {
    match a {
        _ => k + 2,
    }
}

// A STRUCT scrutinee destructured with all-wildcard fields: `Leaf` with a non-empty subpattern
// list, the case wave-VRM's `subpatterns.is_empty()` terminal could not reach.
pub fn struct_all_wild(s: S, k: u32) -> u32 {
    match s {
        S { x: _, y: _ } => k + 3,
    }
}

// The scrutinee is a FIELD read of a local — a pure place projection on
// `effect_free_closure_receiver`'s allow-list, so the lane still fires.
pub fn field_scrutinee(s: S, k: u32) -> u32 {
    match s.x {
        _ => k + 4,
    }
}

// FAIL-CLOSED, and each of these keeps its existing precise tag rather than taking the lane.

// A BINDING is not vacuous: it binds, and this lane materializes no place.
pub fn binding_declines(f: f64, k: u32) -> u32 {
    match f {
        _v => k + 5,
    }
}

// A GUARD is a user-visible computation; the arm no longer always matches.
pub fn guard_declines(f: f64, k: u32) -> u32 {
    match f {
        _ if k > 0 => k + 6,
        _ => k + 7,
    }
}

// TWO arms: narrower than soundness needs (an irrefutable first arm makes the rest dead), but
// one arm removes every question about which arm rustc's MIR would have selected — the same
// conservatism wave-VRM chose.
pub fn two_arms_decline(f: f64, k: u32) -> u32 {
    match f {
        0.0 => k + 8,
        _ => k + 11,
    }
}

// A CONSTANT pattern tests, so it is not vacuous even though the scrutinee type is one this
// arm refuses.
pub fn constant_pattern_declines(f: f64, k: u32) -> u32 {
    match f {
        1.0 => k + 9,
        _ => k + 10,
    }
}

fn main() {}
