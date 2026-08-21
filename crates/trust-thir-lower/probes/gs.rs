// LANE GEP (wave-GS) probe: struct-interior field ADDRESSES behind a shared ref param.
//
// `repr(Rust)` sorts fields by DECREASING alignment, so on `Mixed` rustc places
//   b @ 0 (u64), a @ 8 (u8), c @ 9 (u8), size 16.
// That is asserted below at const-eval time, so the expectations in this file are a
// compile-time FACT of the toolchain under test, not a claim about it.
#![allow(dead_code)]

pub struct Mixed {
    pub a: u8,
    pub b: u64,
    pub c: u8,
}

const _: () = {
    assert!(core::mem::offset_of!(Mixed, b) == 0);
    assert!(core::mem::offset_of!(Mixed, a) == 8);
    assert!(core::mem::offset_of!(Mixed, c) == 9);
};

// SUBJECT A — rustc byte offset 0, FIELD INDEX 1. Before wave-DZ this took the wave-25
// tautology (`ret %0`) and flipped; wave-DZ makes the contested address visible as
// `const i64 0` + `gep inbounds i8`, and the shim refused on the GEP.
pub fn gs_a_off0_field1(s: &Mixed) -> &u64 {
    &s.b
}

// SUBJECT B — rustc byte offset 8, field index 0. The wave-25b interior GEP: this has
// NEVER flipped, at any opt level, since the producer has always emitted the address.
pub fn gs_b_off8_field0(s: &Mixed) -> &u8 {
    &s.a
}

// SUBJECT C — rustc byte offset 9, field index 2. Paired with B: two fields of the SAME
// type at two offsets, so a flip on both proves the OFFSET picks the field, not the type.
pub fn gs_c_off9_field2(s: &Mixed) -> &u8 {
    &s.c
}

// SUBJECT D — a ZST sharing byte 0 with the scalar. `q` is field 1 at offset 0; `z` is
// field 0, also at offset 0. The inversion is unique ONLY because it is disambiguated by
// the returned pointee type.
pub struct Zst;
pub struct Tie {
    pub z: Zst,
    pub q: u64,
}

pub fn gs_d_zst_tie_u64(s: &Tie) -> &u64 {
    &s.q
}

// ------------------------------------------------------------------ controls

// CONTROL 1 — single-field newtype: field 0 at offset 0, `zero_displacement_agrees(0)`
// holds, NO GEP is emitted. Rides the pre-existing wave-29 path and must keep flipping.
pub struct N(pub u64);

pub fn gs_ctl_newtype(s: &N) -> &u64 {
    &s.0
}

// CONTROL 2 — multi-field, field 0 AT offset 0: still the tautology, still no GEP.
pub struct Ordered {
    pub w: u64,
    pub x: u32,
}

pub fn gs_ctl_first_field(s: &Ordered) -> &u64 {
    &s.w
}

// REFUSAL CONTROL 1 — a NON-scalar interior reference. `place_ok` certifies
// `[Deref, Field(scalar)]` only, so this can never reach a flip; it must stay refused
// with its control refusal, not be converted into a new one.
pub struct Inner {
    pub p: u64,
    pub q: u64,
}
pub struct Outer {
    pub lead: u64,
    pub inner: Inner,
}

pub fn gs_ref_nonscalar(s: &Outer) -> &Inner {
    &s.inner
}

// REFUSAL CONTROL 2 — a ZST interior reference: ambiguous at byte 0 AND non-scalar.
pub fn gs_ref_zst(s: &Tie) -> &Zst {
    &s.z
}

// REFUSAL CONTROL 3 — a `&mut` base. The arm is SHARED-only; a mutable interior address
// is a different program and must not be spelled with a shared borrow.
pub fn gs_ref_mut(s: &mut Mixed) -> &mut u64 {
    &mut s.b
}

// REFUSAL CONTROL 4 — an ELEMENT-typed GEP (index arithmetic), which scales its index.
// Untouched by this wave in either direction.
pub fn gs_elem_index(s: &[u64], i: usize) -> u64 {
    s[i]
}
