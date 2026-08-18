// LANE MF-R4 (round-3 REVIEW, 2026-08-13) — A WRITE PLUS ONE OTHER MARKER-MINTING CONSTRUCT.
//
// The round-3 grammar is a claim about the WHOLE body: "the body's field writes are the only
// constructs in it that mint a marker on either side". A grammar-shaped claim is refuted by a
// body that satisfies every stated clause and still carries a second minting construct. This
// file pairs a write with each candidate: an aggregate literal, a destructuring bind, a borrow,
// a nested item, an inner block, a discarded expression, a `_ =` assignment, a compound
// assignment, a struct update, an interior borrow returned, and a second body-level tail.
//
// It also sweeps the INTERIOR-BORROW plan's neighbourhood, which round 3 gated pre-emptively and
// which therefore has no adversarial corpus at all.
//
// No name here appears in any of the 18 existing probe files.
//
//   trustc --edition 2021 --crate-type=lib --crate-name=p_mfr4_mix \
//     -Ztrust-ir-lower=on -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Ztrust-dump=ir:IR probes/mfr4_mix.rs --out-dir OUT

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::needless_late_init, clippy::let_and_return, clippy::no_effect)]
#![allow(clippy::field_reassign_with_default, clippy::assign_op_pattern)]

#[derive(Clone, Copy, Default)]
pub struct M4 {
    pub a: u32,
    pub b: u32,
    pub c: u64,
}

#[derive(Clone, Copy)]
pub struct Two {
    pub p: u32,
    pub q: u32,
}

// --- A: WRITE + AGGREGATE in the same body ----------------------------------------------------

#[inline(never)]
pub fn x01_write_then_agg_tail(w: &mut M4, v: u32) -> M4 {
    w.a = v;
    M4 { a: v, b: 0, c: 0 }
}

#[inline(never)]
pub fn x02_agg_written_into_field(w: &mut M4, v: u32, u: u32) {
    w.a = v;
    w.b = u;
}

#[inline(never)]
pub fn x03_write_then_tuple_tail(w: &mut M4, v: u32) -> (u32, u32) {
    w.a = v;
    (v, v)
}

#[inline(never)]
pub fn x04_write_then_array_tail(w: &mut M4, v: u32) -> [u32; 2] {
    w.a = v;
    [v, v]
}

#[inline(never)]
pub fn x05_agg_then_write_from_it(w: &mut M4, v: u32) {
    let s = Two { p: v, q: v };
    w.a = s.p;
}

#[inline(never)]
pub fn x06_struct_update_then_write(w: &mut M4, s: M4, v: u32) {
    *w = M4 { a: v, ..s };
    w.b = v;
}

// --- B: WRITE + DESTRUCTURING BIND ------------------------------------------------------------

#[inline(never)]
pub fn x07_destructure_param_then_write(Two { p, q }: Two, w: &mut M4) {
    w.a = p;
}

#[inline(never)]
pub fn x08_destructure_let_then_write(s: Two, w: &mut M4) {
    let Two { p, q } = s;
    w.a = p;
}

#[inline(never)]
pub fn x09_tuple_let_then_write(t: (u32, u32), w: &mut M4) {
    let (p, q) = t;
    w.a = p;
}

#[inline(never)]
pub fn x10_ref_pattern_param_then_write(&v: &u32, w: &mut M4) {
    w.a = v;
}

#[inline(never)]
pub fn x11_mut_binding_param_then_write(mut v: u32, w: &mut M4) {
    w.a = v;
}

#[inline(never)]
pub fn x12_wild_param_then_write(_: u32, w: &mut M4, v: u32) {
    w.a = v;
}

// --- C: WRITE + BORROW ------------------------------------------------------------------------

#[inline(never)]
pub fn x13_write_then_borrow_tail(w: &mut M4, v: u32) -> u32 {
    w.a = v;
    w.b
}

#[inline(never)]
pub fn x14_write_through_reborrow(w: &mut M4, v: u32) {
    let r = &mut *w;
    r.a = v;
}

#[inline(never)]
pub fn x15_borrow_field_then_write(w: &mut M4, v: u32) {
    let r = &w.b;
    w.a = v;
}

// --- D: THE INTERIOR-BORROW PLAN'S NEIGHBOURHOOD ----------------------------------------------

#[inline(never)]
pub fn x16_borrow_field_tail(s: &M4) -> &u32 {
    &s.a
}

#[inline(never)]
pub fn x17_borrow_nested_field_tail(s: &Two) -> &u32 {
    &s.q
}

#[inline(never)]
pub fn x18_borrow_whole_tail(s: &M4) -> &M4 {
    &*s
}

#[inline(never)]
pub fn x19_borrow_field_mut_tail(s: &mut M4) -> &mut u32 {
    &mut s.a
}

#[inline(never)]
pub fn x20_borrow_after_item(s: &M4) -> &u32 {
    struct Nested;
    &s.a
}

#[inline(never)]
pub fn x21_borrow_in_if(c: bool, s: &M4) -> &u32 {
    if c { &s.a } else { &s.b }
}

#[inline(never)]
pub fn x22_borrow_of_deref_param<'a>(p: &'a &'a M4) -> &'a u32 {
    &p.a
}

#[inline(never)]
pub fn x23_borrow_second_field_offset(s: &M4) -> &u64 {
    &s.c
}

// --- E: WRITE + A CONSTRUCT THE GRAMMAR CLASSIFIES BY STATEMENT KIND ---------------------------

#[inline(never)]
pub fn x24_write_then_nested_item(w: &mut M4, v: u32) {
    fn helper() -> u32 {
        1
    }
    w.a = v;
}

#[inline(never)]
pub fn x25_write_inside_inner_block(w: &mut M4, v: u32) {
    {
        w.a = v;
    }
}

#[inline(never)]
pub fn x26_write_then_inner_block_write(w: &mut M4, v: u32, u: u32) {
    w.a = v;
    {
        w.b = u;
    }
}

#[inline(never)]
pub fn x27_write_then_discarded_expr(w: &mut M4, v: u32, a: u32, b: u32) {
    w.a = v;
    let _ = a == b;
}

#[inline(never)]
pub fn x28_underscore_assign_then_write(w: &mut M4, v: u32, a: u32, b: u32) {
    _ = a == b;
    w.a = v;
}

#[inline(never)]
pub fn x29_compound_assign_field(w: &mut M4, v: u32) {
    w.a += v;
}

#[inline(never)]
pub fn x30_compound_then_plain_write(w: &mut M4, v: u32, u: u32) {
    w.a += v;
    w.b = u;
}

#[inline(never)]
pub fn x31_write_then_unsafe_block(w: &mut M4, v: u32) {
    w.a = v;
    unsafe {}
}

#[inline(never)]
pub fn x32_unsafe_body_write(w: &mut M4, v: u32) {
    unsafe {
        w.a = v;
    }
}

#[inline(never)]
pub fn x33_write_tail_no_semi(w: &mut M4, v: u32) {
    w.a = v
}

#[inline(never)]
pub fn x34_two_writes_tail_no_semi(w: &mut M4, v: u32, u: u32) {
    w.a = v;
    w.b = u
}

#[inline(never)]
pub fn x35_const_write_tail_no_semi(w: &mut M4) {
    w.a = 1
}

// --- F: WRITE + A SECOND BODY-LEVEL EXPRESSION THAT MINTS ------------------------------------

#[inline(never)]
pub fn x36_write_then_cmp_tail(w: &mut M4, v: u32, a: u32, b: u32) -> bool {
    w.a = v;
    a == b
}

#[inline(never)]
pub fn x37_write_then_place_tail(w: &mut M4, v: u32, a: u32) -> u32 {
    w.a = v;
    a
}

#[inline(never)]
pub fn x38_write_then_const_tail(w: &mut M4, v: u32) -> u32 {
    w.a = v;
    9
}

#[inline(never)]
pub fn x39_write_then_deref_tail(w: &mut M4, v: u32, p: &u32) -> u32 {
    w.a = v;
    *p
}

#[inline(never)]
pub fn x40_write_then_field_tail(w: &mut M4, v: u32, s: Two) -> u32 {
    w.a = v;
    s.p
}

#[inline(never)]
pub fn x41_write_then_call_tail(w: &mut M4, v: u32) -> u32 {
    w.a = v;
    callee(v)
}

#[inline(never)]
pub fn callee(v: u32) -> u32 {
    v
}

#[inline(never)]
pub fn x42_write_then_borrow_ref_tail(w: &mut M4, v: u32) -> &u32 {
    w.a = v;
    &w.b
}
