//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//@ edition: 2021
//! Trust (wave-BLB): `&mut <box-rooted chain>.f` where the LEAF field is a thin `Box<T>`.
//!
//! `Box` is a `ty::Adt::is_struct()`, so its leaf maps to `Ty::Struct(sid)` -- neither
//! `is_scalar_ty` nor the `Ty::Ptr` that F1 Increment A admitted on the mut path -- and that is
//! the ONLY thing that refused this shape. Everything else already works: the `Box<Struct>`
//! chain base is accepted, the data pointer is supplied, the offsets pass, drop glue is handled.
//! `control_scalar_leaf` below borrows field 1 of the SAME Drop-bearing struct through the SAME
//! Box base and is clean TODAY, which means the offset agreement already passes against a
//! registered table that types field 0 as `Ty::Struct(Box)`; field 0 at offset 0 agrees
//! trivially.
//!
//! It is an ASYMMETRY, not a missing model. The deref-accessor lane admits exactly this leaf
//! class off a `&mut` REF base -- `fn ref_base(a: &mut A) -> &mut Box<isize> { &mut a.x }` is
//! clean today -- but it requires the base pointer to be in `ref_param_ptrs`, which a box DATA
//! pointer can never satisfy, so the box-rooted spelling had no lane at all.
//!
//! `base_box.is_some()` IS THE CONTAINMENT and is the one conjunct that must not be dropped:
//! without it a REF-based Box leaf would be served by this lane instead of the accessor lane,
//! re-routing measured-clean bodies off a lowering that emits a projection WITNESS onto a bare
//! GEP. `ref_base` below is the anti-re-route pin.
//!
//! WHAT IT RESTS ON, corrected by adversarial review before landing. The obvious backstop --
//! "every consumer of a non-scalar pointee fails closed, so even a wrong address could not become
//! a wrong VALUE" -- is FALSE here, and false TODAY. `Box` is precisely the ONE non-scalar
//! pointee the producer has a full read/write model for: `**p` is not a generic non-scalar deref,
//! because the inner `*p` yields a place of type `Box<isize>` and the outer deref is the
//! specifically-modelled box deref. Measured on the ref-param twin the accessor lane already
//! mints today, all zero-tag clean: `*p = Box::new(9)`, `**p = 7`, `let v = **p`, `&mut **p`.
//! `consumers_are_live` below pins that, so a future widening that changes it is visible.
//!
//! So this lane extends a LIVE write channel, and the containment is the gate list -- box-rooted
//! base, no dynamic index, the affirmative box test, the layout evidence -- with nothing
//! downstream behind it. The address rests on one leg and it is a real one: the interior-offset
//! check reduces to `declared_struct_field_offset(sid, field) == emitted`, an equality against
//! the DECLARED trust-ir table that the leaf level goes through like every other level, so rustc
//! field REORDERING is gated rather than argued.
//!
//! DISCLOSED: both instruments are structurally blind to this population -- the oracle refuses
//! `Deref` on `Box`, so the interpretation differential is `NotRun`, and the derived-MIR channel
//! refuses a load through a `&mut` param. The clean-rate this buys carries ZERO value evidence on
//! either channel, which is the posture the waves it extends already ship.
//!
//! Not under `=strict`: the negative pins must keep their tags.

#![allow(dead_code, unused_variables)]

struct A {
    x: Box<isize>,
    y: isize,
}

fn use_mut<T>(_: &mut T) {}

// THE LANE (`borrowck-box-sensitivity` shape): a Box LEAF through a Box-rooted base.
pub fn box_leaf() {
    let mut a: Box<A> = Box::new(A { x: Box::new(0), y: 1 });
    let p = &mut a.x;
    use_mut(p);
}

// CONTROL, clean before this wave: same struct, same Box base, SCALAR leaf at offset 8. It is
// what proves the offset table already types field 0 as a Box.
pub fn control_scalar_leaf() {
    let mut a: Box<A> = Box::new(A { x: Box::new(0), y: 1 });
    let p = &mut a.y;
    use_mut(p);
}

// CONTROL, clean before this wave: a raw-pointer leaf, the `Ty::Ptr` half Increment A admitted.
struct A2 {
    x: *mut isize,
    y: isize,
}

pub fn control_ptr_leaf() {
    let mut a: Box<A2> = Box::new(A2 { x: std::ptr::null_mut(), y: 1 });
    let p = &mut a.x;
    use_mut(p);
}

// THE ANTI-RE-ROUTE PIN. This is served by the deref-accessor lane, which emits a projection
// witness rather than a bare GEP. It was clean before this wave and must stay on that lane --
// the `base_box.is_some()` conjunct is what keeps it there.
pub fn ref_base(a: &mut A) -> &mut Box<isize> {
    &mut a.x
}

// FAIL-CLOSED: an UNSIZED pointee. `box_data_ptr_at_offset_zero` refuses these, and they are
// measured dirty today.
struct S1 {
    x: Box<[u8]>,
    y: isize,
}

pub fn unsized_slice_leaf() {
    let mut a: Box<S1> = Box::new(S1 { x: Box::new([0u8; 2]), y: 1 });
    let p = &mut a.x;
    use_mut(p);
}

struct S2 {
    x: Box<dyn Send>,
    y: isize,
}

pub fn unsized_dyn_leaf() {
    let mut a: Box<S2> = Box::new(S2 { x: Box::new(0u8), y: 1 });
    let p = &mut a.x;
    use_mut(p);
}

// FAIL-CLOSED: the SHARED borrow of the same place stays byte-identical (the lane is mut-only,
// because widening the shared side would re-route its already-clean off==0 population).
pub fn shared_stays() {
    let a: Box<A> = Box::new(A { x: Box::new(0), y: 1 });
    let p = &a.x;
    let _ = p;
}

// FAIL-CLOSED: PLACE MODE. An assign-lhs would `Store` a `Ty::Struct`, which this lane models no
// channel for -- the `!place_mode` conjunct.
pub fn place_mode_stays() {
    let mut a: Box<A> = Box::new(A { x: Box::new(0), y: 1 });
    (*a).x = Box::new(5);
}

// THE CONSUMERS ARE LIVE, and this pin says so rather than asserting a decline that does not
// happen. A draft of this lane claimed `**p` would keep `Deref(non-scalar pointee)` and
// `*p = Box::new(..)` would keep `Assign(*r= non-scalar)`; measured on the ref-param twin the
// accessor lane already mints, both lower CLEAN with zero tags, because `Box` is the one
// non-scalar pointee with a full read/write model. Written as a decline these fixtures would
// have failed on their first run, and the live risk was that they would then be "fixed" by
// relaxing the assertion -- at which point the containment the draft offered would be gone with
// nobody noticing. They are written as what actually happens, so a future widening that changes
// it is a diff.
pub fn consumers_are_live() -> isize {
    let mut a: Box<A> = Box::new(A { x: Box::new(0), y: 1 });
    let p = &mut a.x;
    *p = Box::new(9);
    **p = 7;
    let v = **p;
    use_mut(&mut **p);
    v
}

fn main() {}
