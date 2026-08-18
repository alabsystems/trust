// LANE MF-R10 (eighth review) — REPRESENTATION AND LAYOUT.
//
// Every corpus written for this gate so far (rounds 1-7, 35 files, 1,213 body names) is built out
// of plain `#[derive(Clone, Copy)]` structs and bare tuples. Not one of them carries a `#[repr]`
// attribute, a zero-sized field, a `PhantomData`, a unit struct or a transparent newtype — I
// checked by grep across all 35 files: `grep -l "repr(" probes/*.rs` is EMPTY.
//
// That matters here because the marker plan is a claim about which operands built sends through
// `as_operand` -> `as_temp`, and layout is exactly what decides whether a field read is a place
// projection, an unaligned copy, or nothing at all. A ZST field takes no operand temp; a packed
// field is not a plain place; a transparent newtype is a one-field aggregate whose field is the
// whole value.
//
// No body name in this file appears in any of the 35 probe files rounds 1-7 wrote.

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::let_and_return, clippy::needless_return, clippy::precedence)]
#![allow(clippy::nonminimal_bool, clippy::needless_bool, clippy::redundant_field_names)]
#![allow(unused_unsafe, clippy::unnecessary_cast)]

use core::marker::PhantomData;

#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct Tw(pub u32);

#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct Tw8(pub u8);

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Cs {
    pub a: u32,
    pub b: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Cw {
    pub n: u8,
    pub w: u64,
    pub m: u16,
}

#[repr(align(16))]
#[derive(Clone, Copy)]
pub struct Al {
    pub a: u32,
    pub b: u32,
}

#[derive(Clone, Copy)]
pub struct Zu;

#[derive(Clone, Copy)]
pub struct Ph {
    pub a: u32,
    pub p: PhantomData<u8>,
}

#[derive(Clone, Copy)]
pub struct Unit2 {
    pub a: u32,
    pub u: (),
}

// --- A: TRANSPARENT NEWTYPES. One-field aggregates whose field IS the value. -----------------

#[inline(never)]
pub fn w01_transparent_ctor(a: u32, b: u32) -> Tw {
    Tw(a ^ b)
}

#[inline(never)]
pub fn w02_transparent_read(t: Tw) -> u32 {
    t.0
}

#[inline(never)]
pub fn w03_transparent_eq_zero(t: Tw) -> bool {
    t.0 == 0
}

#[inline(never)]
pub fn w04_transparent_ctor_const() -> Tw {
    Tw(41)
}

#[inline(never)]
pub fn w05_transparent_ctor_param(a: u32) -> Tw {
    Tw(a)
}

#[inline(never)]
pub fn w06_transparent_narrow(t: Tw) -> Tw8 {
    Tw8(t.0 as u8)
}

#[inline(never)]
pub fn w07_transparent_pair_cmp(t: Tw, u: Tw) -> bool {
    t.0 == u.0
}

#[inline(never)]
pub fn w08_transparent_xor_then_cmp(t: Tw, a: u32) -> bool {
    (t.0 ^ a) == 0
}

// --- B: repr(C) AND repr(align). Field order and padding the derive-only corpora never saw. --

#[inline(never)]
pub fn w09_repr_c_ctor(a: u32, b: u32) -> Cs {
    Cs { a: a ^ b, b: a & b }
}

#[inline(never)]
pub fn w10_repr_c_swap(s: Cs) -> Cs {
    Cs { a: s.b, b: s.a }
}

#[inline(never)]
pub fn w11_repr_c_wide_ctor(n: u8, w: u64, m: u16) -> Cw {
    Cw { n: n, w: w, m: m }
}

#[inline(never)]
pub fn w12_repr_c_wide_read(c: &Cw) -> u64 {
    c.w
}

#[inline(never)]
pub fn w13_repr_c_wide_mix(c: Cw) -> bool {
    (c.n as u64) == c.w
}

#[inline(never)]
pub fn w14_align_ctor(a: u32, b: u32) -> Al {
    Al { a: a & b, b: a | b }
}

#[inline(never)]
pub fn w15_align_read_xor(x: &Al) -> u32 {
    x.a ^ x.b
}

#[inline(never)]
pub fn w16_align_read_cmp(x: Al) -> bool {
    x.a == x.b
}

// --- C: ZERO-SIZED TERRITORY. A field that takes no operand temp at all. ---------------------

#[inline(never)]
pub fn w17_unit_struct_ctor() -> Zu {
    Zu
}

#[inline(never)]
pub fn w18_phantom_ctor(a: u32) -> Ph {
    Ph { a: a, p: PhantomData }
}

#[inline(never)]
pub fn w19_phantom_ctor_expr(a: u32, b: u32) -> Ph {
    Ph { a: a ^ b, p: PhantomData }
}

#[inline(never)]
pub fn w20_phantom_read(p: Ph) -> u32 {
    p.a
}

#[inline(never)]
pub fn w21_unit_field_ctor(a: u32) -> Unit2 {
    Unit2 { a: a, u: () }
}

#[inline(never)]
pub fn w22_unit_field_expr(a: u32, b: u32) -> Unit2 {
    Unit2 { a: a | b, u: () }
}

// --- D: TUPLE ARITY AND MIXED WIDTHS, as a repr question rather than a permutation one. ------

#[inline(never)]
pub fn w23_tuple_mixed_widths(a: u8, b: u64, c: bool) -> (u8, u64, bool) {
    (a, b, c)
}

#[inline(never)]
pub fn w24_tuple_five_scalars(a: u8, b: u16, c: u32, d: u64, e: i8) -> (u8, u16, u32, u64, i8) {
    (a, b, c, d, e)
}

#[inline(never)]
pub fn w25_tuple_of_transparent(a: u32, b: u32) -> (Tw, Tw) {
    (Tw(a), Tw(b))
}

#[inline(never)]
pub fn w26_tuple_expr_and_place(a: u32, b: u32, c: u32) -> (u32, u32) {
    (a ^ b, c)
}

// --- E: WRITES AND BORROWS THROUGH A LAYOUT-ANNOTATED PLACE. --------------------------------

#[inline(never)]
pub fn w27_write_transparent(w: &mut Tw, v: u32) {
    w.0 = v;
}

#[inline(never)]
pub fn w28_write_repr_c(w: &mut Cs, v: u32) {
    w.a = v;
}

#[inline(never)]
pub fn w29_write_repr_c_from_field(w: &mut Cs, s: Cs) {
    w.b = s.a;
}

#[inline(never)]
pub fn w30_write_align_wide(w: &mut Cw, v: u64) {
    w.w = v;
}

#[inline(never)]
pub fn w31_borrow_transparent(t: &Tw) -> &u32 {
    &t.0
}

#[inline(never)]
pub fn w32_borrow_repr_c_second(c: &Cs) -> &u32 {
    &c.b
}

#[inline(never)]
pub fn w33_borrow_align(x: &Al) -> &u32 {
    &x.a
}
