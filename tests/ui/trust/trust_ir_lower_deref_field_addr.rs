//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-DPW): the wave-DP interior-field address lane is not special to
//! `Deref`/`DerefMut` impls.
//!
//! THE LANE'S SHAPE, stated precisely because getting it wrong cost three
//! misdiagnoses: it requires a STRUCT-TYPED LEAF
//! (`if !matches!(leaf_ty, Ty::Struct(_)) { return None; }`). `&mut o.i` where
//! `i: Inner` is in scope; `&mut s.b` where `b: i32` is NOT, and never was —
//! a scalar leaf keeps its own refusal. Every fixture here therefore projects a
//! struct field, at a NON-ZERO offset, through a `&mut` PARAM, outside any
//! `Deref` impl.
//!
//! Every tooth of wave-DP is retained: the base must be a `&mut` ref PARAM
//! (`ref_param_ptrs` + `is_mut_borrow_ptr`, i.e. caller memory that outlives the
//! call, which is what makes the derived GEP legitimately `interior_ptrs` rather
//! than the `frame_interior_ptrs` wave-FIL created for frame bases); the target
//! must be a THIN `&mut T`; and the byte offset must pass
//! `struct_interior_offset_admissible` against the registered `StructId`. The
//! accessor gate was a scoping decision from when the ledger discipline was less
//! settled, not a premise of it.
//!
//! MEASURED: control 0 of 2 clean, subject 2 of 2. On the pinned corpus the wave
//! is +0 — not because it is inert, but because the corpus contains no body of
//! this shape. This file is what witnesses it.
//!
//! `run-pass` is deliberate: the fixtures WRITE through the returned address, so
//! a wrong byte offset is caught by execution rather than by a coverage count.

pub struct Inner {
    pub x: i32,
    pub y: i32,
}
pub struct Outer {
    pub n: i32,
    pub i: Inner,
}

/// The sugared spelling, struct leaf at a non-zero offset.
pub fn field_addr(o: &mut Outer) -> &mut Inner {
    &mut o.i
}

/// The explicit deref spelling of the same place.
pub fn field_addr_deref(o: &mut Outer) -> &mut Inner {
    &mut (*o).i
}

/// Written through, so a wrong offset is a wrong VALUE, not a wrong count.
pub fn bump(o: &mut Outer) -> i32 {
    let r = &mut o.i;
    r.x += 10;
    o.i.x
}

fn main() {
    let mut o = Outer { n: 1, i: Inner { x: 2, y: 3 } };
    field_addr(&mut o).x = 7;
    assert_eq!(o.i.x, 7);
    field_addr_deref(&mut o).y = 8;
    assert_eq!(o.i.y, 8);
    assert_eq!(bump(&mut o), 17);
    assert_eq!(o.n, 1);
}
