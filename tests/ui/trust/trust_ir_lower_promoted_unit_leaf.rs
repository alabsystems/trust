//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//@ edition: 2021
//! Trust (wave-UPL): a promotable aggregate whose leaf is `()`.
//!
//! `eval_promotable_aggregate`'s arity match already admits a ZERO-ARITY aggregate --
//! `Ty::Struct(sid)` with no fields gives `expected == 0 == consts.len()`. So `&G(Inner)` on a
//! zero-field `Inner` is admitted TODAY and grades `mode=Agreed equal=true` against the MIR
//! oracle, while `&G(())` -- the same zero-payload leaf, one spelling over -- was refused.
//! The match's own comment claimed the excluded case has no promotable-field walk to arrive
//! from; that is false of `()`, whose walk reaches the site exactly as `Inner`'s does. The
//! refusal was an omission from a match arm, not an argument.
//!
//! THE SPELLING IS TAKEN, NOT INVENTED. `Constant::PhantomData` is the producer's own
//! `seed_lane_ty` answer at `Ty::Unit` and the only pairing trust-ir's `shape_matches_ty` accepts
//! there; `Aggregate(vec![])` would be a fabricated spelling no consumer names.
//!
//! THE LANE MAKES THE PRODUCER AGREE WITH RUSTC, which is the opposite direction from a
//! borrow-ledger widening. Today `&G(())` builds a stack `Alloca` snapshot, and GIVEN that
//! artifact the downstream refusal is CORRECT -- rustc genuinely promotes the referent to
//! `'static`, so `fn f<'a>() -> S<'a>` legally returns the aggregate and admitting the snapshot
//! would ship a dangling pointer. This arm does not admit the snapshot: it removes the reason the
//! snapshot was built, so the value reaching the field is a `GlobalAddr` into a module global and
//! the outlives fact holds as a FACT rather than as a concession.
//!
//! The `is_freeze` gate is upstream and untouched, so interior mutability still cannot enter --
//! `&Cell::new(32)` is an `ExprKind::Call` and never reaches this walk anyway.

#![allow(dead_code)]

pub struct Inner;
pub struct G0(pub Inner);
pub struct G1(pub ());

// The CONTROL, clean before this wave: a zero-FIELD struct leaf.
pub fn zero_field_leaf() -> &'static G0 {
    &G0(Inner)
}

// THE LANE: the same zero-payload leaf spelled `()`.
pub fn unit_leaf() -> &'static G1 {
    &G1(())
}

// A UNIT leaf beside a real scalar, so the arm is exercised at a non-sole lane index.
pub struct Mixed(pub (), pub u32);

pub fn mixed_leaf() -> &'static Mixed {
    &Mixed((), 7)
}

// A bare unit tuple, the degenerate spelling.
pub fn bare_unit() -> &'static () {
    &()
}

fn main() {}
