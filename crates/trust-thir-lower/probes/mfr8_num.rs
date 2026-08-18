// LANE MF-R10 (eighth review) — THE SCALAR SET, ALL SIXTEEN OF IT.
//
// `SCALAR_CANDS` in `to_mir.rs` admits sixteen trust-ir scalars. The rounds-1-7 corpus is written
// almost entirely in `u32`/`u64`/`u8`/`bool`: `i128`/`u128` appear in ZERO of the 35 files,
// `isize`/`usize` in a handful of index positions, `char` in four, `f32`/`f64` in three and never
// as an operand-temp shape.
//
// The marker plan is a per-VALUE claim, and the one component of the oracle's marker line the
// predicted side admits it cannot render is the DECLARED TYPE (`s{alpha}:{ty}`). So a corpus whose
// bodies all mint `u32` temps cannot distinguish a temp minted at the right type from one minted
// at the wrong one. This file mints temps at every width and every signedness the fragment
// admits, deliberately including bodies where two temps of DIFFERENT types are live at once.
//
// No body name in this file appears in any of the 35 probe files rounds 1-7 wrote.

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::let_and_return, clippy::needless_return, clippy::precedence)]
#![allow(clippy::nonminimal_bool, clippy::needless_bool, clippy::unnecessary_cast)]
#![allow(clippy::float_cmp, clippy::cast_lossless, clippy::char_lit_as_u8)]

#[derive(Clone, Copy)]
pub struct Wide {
    pub s: i128,
    pub u: u128,
}

#[derive(Clone, Copy)]
pub struct Sized2 {
    pub i: isize,
    pub u: usize,
}

#[derive(Clone, Copy)]
pub struct Fl {
    pub f: f32,
    pub d: f64,
}

#[derive(Clone, Copy)]
pub struct Ch {
    pub c: char,
    pub b: bool,
}

// --- A: 128-BIT. Never written before, at either signedness. ---------------------------------

#[inline(never)]
pub fn n01_u128_xor(a: u128, b: u128) -> u128 {
    a ^ b
}

#[inline(never)]
pub fn n02_u128_eq_zero(a: u128, b: u128) -> bool {
    (a & b) == 0
}

#[inline(never)]
pub fn n03_i128_or(a: i128, b: i128) -> i128 {
    a | b
}

#[inline(never)]
pub fn n04_i128_lt(a: i128, b: i128) -> bool {
    a < b
}

#[inline(never)]
pub fn n05_u128_ctor(a: u128, b: u128) -> Wide {
    Wide { s: 0, u: a ^ b }
}

#[inline(never)]
pub fn n06_wide_read_pair(w: Wide) -> bool {
    w.u == 0
}

#[inline(never)]
pub fn n07_u128_narrow_cast(a: u128) -> u32 {
    a as u32
}

#[inline(never)]
pub fn n08_u32_widen_cast(a: u32) -> u128 {
    a as u128
}

// --- B: isize/usize AS VALUES, not as indices. ----------------------------------------------

#[inline(never)]
pub fn n09_usize_and(a: usize, b: usize) -> usize {
    a & b
}

#[inline(never)]
pub fn n10_isize_ge(a: isize, b: isize) -> bool {
    a >= b
}

#[inline(never)]
pub fn n11_sized_ctor(i: isize, u: usize) -> Sized2 {
    Sized2 { i: i, u: u }
}

#[inline(never)]
pub fn n12_sized_cross_cast(s: Sized2) -> bool {
    (s.i as usize) == s.u
}

#[inline(never)]
pub fn n13_usize_to_u64(a: usize) -> u64 {
    a as u64
}

// --- C: FLOATS. No overflow check, no bitwise ops — a different rvalue population entirely. ---

#[inline(never)]
pub fn n14_f32_add(a: f32, b: f32) -> f32 {
    a + b
}

#[inline(never)]
pub fn n15_f64_mul(a: f64, b: f64) -> f64 {
    a * b
}

#[inline(never)]
pub fn n16_f64_lt(a: f64, b: f64) -> bool {
    a < b
}

#[inline(never)]
pub fn n17_f32_eq_self(a: f32) -> bool {
    a == a
}

#[inline(never)]
pub fn n18_fl_ctor(a: f32, b: f64) -> Fl {
    Fl { f: a, d: b }
}

#[inline(never)]
pub fn n19_fl_read_cmp(x: Fl) -> bool {
    (x.f as f64) < x.d
}

#[inline(never)]
pub fn n20_f64_to_i32(a: f64) -> i32 {
    a as i32
}

#[inline(never)]
pub fn n21_i32_to_f64(a: i32) -> f64 {
    a as f64
}

// --- D: char AND bool AS FIRST-CLASS SCALARS. ------------------------------------------------

#[inline(never)]
pub fn n22_char_eq(a: char, b: char) -> bool {
    a == b
}

#[inline(never)]
pub fn n23_char_to_u32(a: char) -> u32 {
    a as u32
}

#[inline(never)]
pub fn n24_char_cmp_const(a: char) -> bool {
    a < 'z'
}

#[inline(never)]
pub fn n25_ch_ctor(c: char, b: bool) -> Ch {
    Ch { c: c, b: b }
}

#[inline(never)]
pub fn n26_ch_read_and(x: Ch) -> bool {
    x.b & (x.c == 'a')
}

#[inline(never)]
pub fn n27_bool_xor(a: bool, b: bool) -> bool {
    a ^ b
}

#[inline(never)]
pub fn n28_bool_not(a: bool) -> bool {
    !a
}

#[inline(never)]
pub fn n29_bool_to_u8(a: bool) -> u8 {
    a as u8
}

// --- E: MIXED-WIDTH TEMPS LIVE AT ONCE. Two marked slots of DIFFERENT declared types. --------

#[inline(never)]
pub fn n30_u8_and_u64_live(a: u8, b: u64) -> bool {
    (a as u64) == (b & 255)
}

#[inline(never)]
pub fn n31_i8_and_i64_live(a: i8, b: i64) -> bool {
    (a as i64) == (b | 1)
}

#[inline(never)]
pub fn n32_cast_chain_up(a: u8) -> u64 {
    a as u16 as u32 as u64
}

#[inline(never)]
pub fn n33_cast_chain_down(a: u64) -> u8 {
    a as u32 as u16 as u8
}

#[inline(never)]
pub fn n34_sign_flip_chain(a: u32) -> i64 {
    a as i32 as i64
}

#[inline(never)]
pub fn n35_char_u32_u64(a: char) -> u64 {
    a as u32 as u64
}
