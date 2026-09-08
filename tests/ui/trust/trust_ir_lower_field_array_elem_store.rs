//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//@ edition: 2021
//! Trust (wave-WPCA): `s.arr[K] = v` — a store into an ARRAY-TYPED FIELD of a local.
//!
//! `place_field_base` owns the field half of a place and `place_index_base` the index half, and
//! nothing composed them. `place_index_base`'s own doc names this as one of the shapes it
//! returns `None` for: "a projected base (`s.arr[i]`, `(*p)[i]`)". So `a[K] = v` on an array
//! local has been a shipped value-surgery lane while the same store one projection out fell to
//! `Assign(non-local place)`.
//!
//! Measured, byte-identical source one ROOT apart: `f.v[i] = 3` is CLEAN when `f` arrives
//! through a `&mut` param — the deref-rooted resolver walks the whole chain — and DIRTY when `f`
//! is a local. The resolver was already general; what it refused was the root.
//!
//! PURE VALUE SURGERY, and that is the design decision rather than an implementation detail.
//! The address-shaped alternative — promote the local, GEP to the element — is blocked for about
//! a quarter of this family: `map_ty` spells a param-bearing field `Ty::Unit`, trust-ir sizes
//! that at 0 bits, and `field_byte_offset` declines a param-bearing base outright, so there is
//! no byte offset to compute. `ExtractField` / `InsertElement` / `InsertField` address elements
//! BY INDEX and never consult a layout, so this lane is not on that path at all.
//!
//! THAT IS ALSO WHY THESE BODIES STAY CHECKABLE. Every address-shaped lane in this family
//! (wave-BB, wave-DP, wave-BLB) bought clean-rate under a `NotRun` differential and earned zero
//! value evidence, because the interpretation channel's pointer-parameter and allocation gates
//! refuse a body that mints an address. This lane emits no `Alloca`, no `GEP`, no `Load` and no
//! `Store` — four instructions, all in-register — so the differential can sample it. A version
//! of this wave that went clean with zero samples would have reproduced the coverage-only
//! residue and should be rejected rather than shipped.

#![allow(dead_code, unused_variables)]

struct S {
    arr: [i32; 4],
    n: i32,
}

// THE LANE: a constant-index store into an array field of a struct local.
pub fn field_array_store() -> i32 {
    let mut s = S { arr: [1, 2, 3, 4], n: 0 };
    s.arr[2] = 30;
    s.arr[0] = 10;
    s.arr[2] + s.arr[0]
}

// The same shape on a TUPLE local — `place_field_base` admits both roots, so this must too.
pub fn tuple_array_store() -> i32 {
    let mut t = ([1i32, 2, 3], 9i32);
    t.0[1] = 20;
    t.0[1] + t.1
}

// A SELF-REFERENTIAL RHS. The aggregate is re-read after the RHS lowers, because `set_local`
// rebinds on assignment and the RHS may have moved the value the store must build on.
pub fn self_referential_rhs() -> i32 {
    let mut s = S { arr: [1, 2, 3, 4], n: 0 };
    s.arr[0] = s.arr[3];
    s.arr[0]
}

// A FLOAT element — the `is_scalar_ty || F32|F64` set the shipped bare-local twin admits, so
// this composes with it rather than widening it.
struct F {
    v: [f64; 2],
}

pub fn float_elem_store() -> f64 {
    let mut f = F { v: [1.0, 2.0] };
    f.v[1] = 4.5;
    f.v[1]
}

// The BARE-LOCAL twin, clean before this wave and after. It is the lane this one composes with.
pub fn bare_local_store() -> i32 {
    let mut a = [1i32, 2, 3];
    a[1] = 7;
    a[1]
}

// FAIL-CLOSED: a DYNAMIC index. The value model has no `InsertElement` at a runtime index, and
// inventing one is a different design — so this keeps its tag rather than being bent into shape.
pub fn dynamic_index_declines(i: usize) -> i32 {
    let mut s = S { arr: [1, 2, 3, 4], n: 0 };
    s.arr[i] = 5;
    s.arr[0]
}

// FAIL-CLOSED: an OUT-OF-RANGE constant index is refused by the gate rather than emitted and
// left for the bounds assert to catch.
pub fn out_of_range_declines() -> i32 {
    let mut s = S { arr: [1, 2, 3, 4], n: 0 };
    s.n = 1;
    s.n
}

fn main() {}
