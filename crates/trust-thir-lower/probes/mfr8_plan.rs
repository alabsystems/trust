// LANE MF-R10 (eighth review) — THE PLAN'S OWN BOUNDARY, POPULATED ON BOTH SIDES.
//
// `plan_operand_marker_temps` carries two ordering rules, and both are stated in the source as
// closing bodies that were ONCE ADMITTED-AND-WRONG:
//
//   rule (1) "a marked result may not take a marked operand"    — closes `W8((a & b) | c)`,
//            `Two { x: a & b, y: (c ^ d) | e }`, `Inner(*p as u32)`, `((a & b) | c) == 0`
//   rule (2) "a marked operand may not be preceded by a place"  — closes `a == (b & c)`,
//            `self.0 == (b & c)`, `a | (b & c)`, `a == *p`
//
// Those rules live on the PREDICTED side and on the EMITTER side at once: `MfPlans::seal` is one
// call and `MfPlans::predict` reads the very set the arms read. So this file populates BOTH SIDES
// of each rule — the refused shape and its admitted twin — at widths and in constructs the
// rounds-1-7 corpus never used, so that a driver which widens the plan by one line has somewhere
// to land and a driver which does not is visibly unchanged.
//
// No body name in this file appears in any of the 35 probe files rounds 1-7 wrote.

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::let_and_return, clippy::needless_return, clippy::precedence)]
#![allow(clippy::nonminimal_bool, clippy::needless_bool, clippy::unnecessary_cast)]

#[derive(Clone, Copy)]
pub struct P2 {
    pub x: u64,
    pub y: u64,
}

#[derive(Clone, Copy)]
pub struct P3 {
    pub a: i32,
    pub b: i32,
    pub c: i32,
}

#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct Pn(pub u16);

// --- A: RULE (1) VIOLATIONS — a marked result taking a marked operand. ----------------------

#[inline(never)]
pub fn p01_deep_xor_cmp_u64(a: u64, b: u64, c: u64) -> bool {
    ((a ^ b) ^ c) == 0
}

#[inline(never)]
pub fn p02_deep_and_or_cmp_i32(a: i32, b: i32, c: i32) -> bool {
    ((a & b) | c) == 0
}

#[inline(never)]
pub fn p03_deep_u128_cmp(a: u128, b: u128, c: u128) -> bool {
    ((a & b) ^ c) == 0
}

#[inline(never)]
pub fn p04_deep_usize_cmp(a: usize, b: usize, c: usize) -> bool {
    ((a | b) & c) == 0
}

#[inline(never)]
pub fn p05_ctor_from_deep_u64(a: u64, b: u64, c: u64) -> P2 {
    P2 { x: (a ^ b) | c, y: b }
}

#[inline(never)]
pub fn p06_ctor_two_deep_i32(a: i32, b: i32, c: i32, d: i32, e: i32) -> P3 {
    P3 { a: a & b, b: (c ^ d) | e, c: e }
}

#[inline(never)]
pub fn p07_cast_over_binop_u16(a: u16, b: u16) -> Pn {
    Pn((a ^ b) as u16)
}

#[inline(never)]
pub fn p08_cast_over_load(p: &u16) -> Pn {
    Pn(*p as u16)
}

#[inline(never)]
pub fn p09_cast_over_cast(a: u8) -> bool {
    ((a as u16) as u32) == 0
}

#[inline(never)]
pub fn p10_not_over_binop(a: u64, b: u64) -> bool {
    !(a & b) == 0
}

// --- B: THE ADMITTED TWINS of A — same depth, but the outer result is RETURNED. -------------

#[inline(never)]
pub fn p11_deep_xor_returned_u64(a: u64, b: u64, c: u64) -> u64 {
    (a ^ b) ^ c
}

#[inline(never)]
pub fn p12_deep_and_or_returned_i32(a: i32, b: i32, c: i32) -> i32 {
    (a & b) | c
}

#[inline(never)]
pub fn p13_deep_u128_returned(a: u128, b: u128, c: u128) -> u128 {
    (a & b) ^ c
}

#[inline(never)]
pub fn p14_deep_usize_returned(a: usize, b: usize, c: usize) -> usize {
    (a | b) & c
}

#[inline(never)]
pub fn p15_cast_returned_u16(a: u16, b: u16) -> u32 {
    (a ^ b) as u32
}

// --- C: RULE (2) VIOLATIONS — a PLACE operand preceding a marked one. -----------------------

#[inline(never)]
pub fn p16_right_nested_u64(a: u64, b: u64, c: u64) -> bool {
    a == (b & c)
}

#[inline(never)]
pub fn p17_right_nested_i32(a: i32, b: i32, c: i32) -> i32 {
    a | (b & c)
}

#[inline(never)]
pub fn p18_right_nested_u128(a: u128, b: u128, c: u128) -> bool {
    a == (b ^ c)
}

#[inline(never)]
pub fn p19_right_nested_field(s: P2, b: u64, c: u64) -> bool {
    s.x == (b & c)
}

#[inline(never)]
pub fn p20_place_then_load(a: u16, p: &u16) -> bool {
    a == *p
}

#[inline(never)]
pub fn p21_right_nested_char(a: char, b: u32, c: u32) -> bool {
    (a as u32) == (b & c)
}

#[inline(never)]
pub fn p22_right_nested_ctor(a: u64, b: u64, c: u64) -> P2 {
    P2 { x: a, y: b & c }
}

// --- D: THE ADMITTED TWINS of C — the marked operand comes FIRST. ---------------------------

#[inline(never)]
pub fn p23_left_nested_u64(a: u64, b: u64, c: u64) -> bool {
    (b & c) == a
}

#[inline(never)]
pub fn p24_left_nested_i32(a: i32, b: i32, c: i32) -> i32 {
    (b & c) | a
}

#[inline(never)]
pub fn p25_left_nested_u128(a: u128, b: u128, c: u128) -> bool {
    (b ^ c) == a
}

#[inline(never)]
pub fn p26_const_then_nested_u64(b: u64, c: u64) -> bool {
    0 == (b & c)
}

#[inline(never)]
pub fn p27_load_alone(p: &u16) -> bool {
    *p == 0
}

#[inline(never)]
pub fn p28_two_loads(p: &u16, q: &u16) -> bool {
    (*p ^ *q) == 0
}

// --- E: MULTI-BLOCK (lane K) IN THE SAME NEW TYPES, so the block index is exercised too. ----

#[inline(never)]
pub fn p29_branch_u128(a: u128, b: u128, c: u128) -> u128 {
    if (a & b) == 0 { c ^ 1 } else { c ^ 2 }
}

#[inline(never)]
pub fn p30_branch_isize(a: isize, b: isize) -> isize {
    if a < b { a | 1 } else { b | 2 }
}

#[inline(never)]
pub fn p31_branch_char(a: char, b: char) -> u32 {
    if a == b { 1 } else { 2 }
}

#[inline(never)]
pub fn p32_branch_field_u64(s: P2) -> u64 {
    if s.x == s.y { s.x ^ 3 } else { s.y ^ 4 }
}

#[inline(never)]
pub fn p33_branch_f64(a: f64, b: f64) -> u32 {
    if a < b { 5 } else { 6 }
}
