//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//@ edition: 2021
//! Trust (wave-GRB): the `#![feature(reborrow)]` GENERIC REBORROW of a user ADT. The producer had
//! no arm for `ExprKind::Reborrow` at all -- the variant's only other occurrence in the crate was
//! the naming table -- so every one of these bodies fell to `lower_expr_walk`'s terminal
//! catch-all.
//!
//! THE CLASS IS A HARD DICHOTOMY, and rustc's own coercion code draws the line.
//! `coerce_reborrow` emits `GenericReborrow(Mut)` only when the two ADT defs are the SAME and
//! then UNIFIES the types, so a `Mut` reborrow's target IS its source modulo regions.
//! `coerce_shared_reborrow` emits `GenericReborrow(Not)` only after refusing same-def outright,
//! so a `Not` target is ALWAYS a structurally different ADT -- rustc guarantees only that the two
//! "currently have the same memory layout" and declares no field correspondence at all. This lane
//! admits the first half and refuses the second, and checks BOTH conjuncts rather than assuming
//! their equivalence: if upstream implements its `CoerceShared check goes here` FIXME
//! differently, the gate refuses instead of guessing.
//!
//! THE VALUE CLAIM IS DEFINITIONAL. `Rvalue::Reborrow(t, Mut, place)` is documented as a bitwise
//! copy of the place at the same type, and both MIR builders confirm it -- one takes
//! `as_temp(source)` then copies, the other takes `as_place(source)` then pushes the assign.
//! Neither moves out and neither deinitializes. So the value IS the source place's value, which
//! is what `lower_expr(source)` produces: the same `&*r == r` identity the thin shared and `&mut`
//! reborrow lanes already ship for the BUILTIN reborrow, one spelling over.
//!
//! The node's residual content is a borrowck OUTLIVES fact -- the source is unusable while the
//! reborrow lives. The producer models values, not aliasing, and this lane leans on that fact in
//! NO direction: the copy is the right value whether or not borrowck accepts the program, so the
//! pre-borrowck position of `mir_built` is irrelevant here.
//!
//! THE ORACLE ALREADY ADMITS IT WITH THIS EXACT GATE: `mir_lower`'s scalar path forwards a
//! `Rvalue::Reborrow` place value and errors when the source and target trust-ir types differ,
//! and its aggregate path validates equal layout before copying "so a future rustc relaxation
//! fails loud". `trust-mir-extract` refuses it, but for a PROOF-side reason its own comment
//! concedes -- the reborrow-trait aliasing semantics -- not a value-side one.
//!
//! BOUNDED AND HONEST: `feature(reborrow)` is unstable, so every occurrence lives in its own
//! feature-test directory. This is +2, and the whole class is 5 bodies corpus-wide. Nobody
//! should size a follow-on off it until the feature stabilizes.
//!
//! Not under `=strict`: the CoerceShared negatives must keep their tags.

#![feature(reborrow)]
#![allow(dead_code, unused_variables)]

use std::marker::{CoerceShared, PhantomData, Reborrow};

// THE LANE: a `Mut` generic reborrow, same ADT def on both sides.
struct CustomMarker<'a>(PhantomData<&'a ()>);
impl<'a> Reborrow for CustomMarker<'a> {}

fn method<'a>(_a: CustomMarker<'a>) -> &'a () {
    &()
}

pub fn identity_reborrow() {
    let a = CustomMarker(PhantomData);
    let _ = method(a);
    let _ = method(a);
}

// THE LANE, with a real PAYLOAD: the forwarded value carries a scalar field, so this is not
// vacuous over a ZST.
struct P<'a> {
    n: u32,
    m: PhantomData<&'a ()>,
}
impl<'a> Reborrow for P<'a> {}

fn take<'a>(p: P<'a>) -> u32 {
    p.n
}

pub fn payload_reborrow() -> u32 {
    let p = P { n: 7, m: PhantomData };
    take(p) + take(p)
}

// The COPY TWIN, clean before this wave and after. It is the semantic control: the same program
// with the reborrow node removed lowers to the same forwarded value.
#[derive(Clone, Copy)]
struct Q {
    n: u32,
}

fn take_q(q: Q) -> u32 {
    q.n
}

pub fn copy_twin() -> u32 {
    let q = Q { n: 7 };
    take_q(q) + take_q(q)
}

// FAIL-CLOSED: a `Not` / CoerceShared reborrow. Its target is a DIFFERENT ADT with a different
// field list, and rustc declares no field correspondence -- only that the layouts "currently"
// match. Forwarding the source value under the target's sort would be a claim rustc does not
// make.
pub struct MyMut<'a>(&'a u32);
impl Reborrow for MyMut<'_> {}

#[derive(Clone, Copy)]
pub struct MyRef<'a>(&'a u32);
impl<'a> CoerceShared<MyRef<'a>> for MyMut<'a> {}

fn take_ref(r: MyRef<'_>) -> u32 {
    *r.0
}

pub fn coerce_shared_declines() -> u32 {
    let v = 3u32;
    take_ref(MyMut(&v))
}

fn main() {}
