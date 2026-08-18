// LANE MF-R5 (round-4-fix REVIEW, 2026-08-14) — THE ADMITTED POPULATION.
//
// Every previous corpus in this lane was aimed at bodies the marker plans REFUSE: round 3's
// residual was a story about emissions nothing had sanctioned, so the interesting bodies were
// the ones outside every plan. Round 4's invariant is a claim about the bodies plans ADMIT —
// "the shim emitted a marker" and "a plan sanctioned it" are the same statement — and the way
// to refute a claim about admitted bodies is to write admitted bodies.
//
// This file is therefore the operand-temp plan's own class, written densely: statement-free
// single-block expression bodies where built materialises SOME temps and not others, so the
// difference between "this body is planned" (what `mf_gate::mint::lease` asks) and "this VALUE
// is planned" (what `mf_plan` actually says) is observable in the marker channel.
//
// Written without reading any prior lane's classifier. No body name here appears in any of the
// 22 existing probe files.
//
//   trustc --edition 2021 --crate-type=lib --crate-name=p_mfr5_plan \
//     -Ztrust-ir-lower=on -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Ztrust-dump=ir:IR probes/mfr5_plan.rs --out-dir OUT

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::let_and_return, clippy::needless_return, clippy::bool_comparison)]

#[derive(Clone, Copy)]
pub struct G5 {
    pub p: u32,
    pub q: u32,
    pub r: u64,
    pub s: u8,
    pub t: bool,
}

#[derive(Clone, Copy)]
pub struct Duo {
    pub lo: u32,
    pub hi: u32,
}

// --- A: ONE marked temp, nothing else. The minimal admitted body. --------------------------

#[inline(never)]
pub fn g01_eq_two_params(a: u32, b: u32) -> bool {
    a == b
}

#[inline(never)]
pub fn g02_ne_two_params(a: u64, b: u64) -> bool {
    a != b
}

#[inline(never)]
pub fn g03_lt_two_params(a: i32, b: i32) -> bool {
    a < b
}

#[inline(never)]
pub fn g04_ge_mixed_width(a: u8, b: u8) -> bool {
    a >= b
}

#[inline(never)]
pub fn g05_eq_param_const(a: u32) -> bool {
    a == 7
}

#[inline(never)]
pub fn g06_eq_const_param(a: u32) -> bool {
    9 == a
}

// --- B: a NESTED tree — built lives the inner result temp, and the plan names exactly that
//        value. The outer result is not in the plan, which is where a per-body lease and a
//        per-value plan come apart. --------------------------------------------------------

#[inline(never)]
pub fn g07_and_then_eq(a: u8, b: u8) -> bool {
    (a & b) == b
}

#[inline(never)]
pub fn g08_or_then_ne(a: u8, b: u8) -> bool {
    (a | b) != b
}

#[inline(never)]
pub fn g09_xor_then_eq_const(a: u32, b: u32) -> bool {
    (a ^ b) == 0
}

#[inline(never)]
pub fn g10_shift_then_eq(a: u32) -> bool {
    (a >> 3) == 1
}

#[inline(never)]
pub fn g11_two_nested_ands(a: u8, b: u8, c: u8) -> bool {
    (a & b) == (b & c)
}

#[inline(never)]
pub fn g12_three_deep_and(a: u32, b: u32, c: u32) -> bool {
    ((a & b) & c) == c
}

#[inline(never)]
pub fn g13_right_nested_and(a: u32, b: u32, c: u32) -> bool {
    a == (b & c)
}

// --- C: a FIELD read in operand position. `s.k` is `Category::Place`, so built copies it into
//        a marked temp — one more marked value per operand. -------------------------------

#[inline(never)]
pub fn g14_field_eq_const(g: G5) -> bool {
    g.p == 0
}

#[inline(never)]
pub fn g15_field_eq_field(g: G5) -> bool {
    g.p == g.q
}

#[inline(never)]
pub fn g16_field_eq_param(g: G5, a: u32) -> bool {
    g.q == a
}

#[inline(never)]
pub fn g17_two_fields_anded(g: G5) -> bool {
    (g.p & g.q) == g.q
}

#[inline(never)]
pub fn g18_field_bool_direct(g: G5) -> bool {
    g.t
}

#[inline(never)]
pub fn g19_duo_fields_ne(d: Duo) -> bool {
    d.lo != d.hi
}

// --- D: ARITHMETIC under `-Coverflow-checks=on` — the Overflow+Assert idiom, which splits the
//        block and therefore moves every marker's rendered position. ------------------------

#[inline(never)]
pub fn g20_add_then_eq(a: u32, b: u32) -> bool {
    (a + b) == 0
}

#[inline(never)]
pub fn g21_sub_then_lt(a: u32, b: u32) -> bool {
    (a - b) < 4
}

#[inline(never)]
pub fn g22_mul_then_eq_param(a: u32, b: u32, c: u32) -> bool {
    (a * b) == c
}

#[inline(never)]
pub fn g23_add_field_field(g: G5) -> u32 {
    g.p + g.q
}

#[inline(never)]
pub fn g24_wrapping_add_eq(a: u32, b: u32) -> bool {
    a.wrapping_add(b) == 0
}

// --- E: bodies with NO marked value at all — the plan admits and names nothing, so any marker
//        the shim emits is one no plan asked for, and the body-end census cannot tell. -------

#[inline(never)]
pub fn g25_return_param(a: u32) -> u32 {
    a
}

#[inline(never)]
pub fn g26_return_const() -> u32 {
    11
}

#[inline(never)]
pub fn g27_return_field(g: G5) -> u32 {
    g.p
}

#[inline(never)]
pub fn g28_not_bool(a: bool) -> bool {
    !a
}

#[inline(never)]
pub fn g29_neg_int(a: i32) -> i32 {
    -a
}

#[inline(never)]
pub fn g30_cast_widen(a: u8) -> u32 {
    a as u32
}

#[inline(never)]
pub fn g31_cast_narrow(a: u64) -> u8 {
    a as u8
}

// --- F: comparison chains whose operands are themselves comparisons — several marked values in
//        one body, so an over-issue shows up as a LATER line rather than a first-line diff. --

#[inline(never)]
pub fn g32_eq_of_eqs(a: u32, b: u32, c: u32, d: u32) -> bool {
    (a == b) == (c == d)
}

#[inline(never)]
pub fn g33_and_of_eqs(a: u32, b: u32, c: u32, d: u32) -> bool {
    (a == b) & (c == d)
}

#[inline(never)]
pub fn g34_or_of_lts(a: i32, b: i32, c: i32, d: i32) -> bool {
    (a < b) | (c < d)
}

#[inline(never)]
pub fn g35_xor_of_ges(a: u8, b: u8, c: u8, d: u8) -> bool {
    (a >= b) ^ (c >= d)
}

#[inline(never)]
pub fn g36_eq_of_field_eqs(g: G5, h: G5) -> bool {
    (g.p == h.p) == (g.q == h.q)
}
