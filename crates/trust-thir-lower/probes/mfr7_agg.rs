// LANE MF-R8 (seventh review) — THE AGGREGATE SEAM, WHERE THE SHARED LIST STILL IS.
//
// The sixth review's residual is one body: `P2 { l: a & b, r: a & b }`, whose two fields are two
// DIFFERENT trust-ir values that compute the same thing, so a local reversed copy of the field
// list leaves the value channel green and moves only the marker slots. Round 6 answered the
// MUTABLE spelling (`agg_chains` is bound immutably now) and the ORDER spelling (a reversed walk
// leaves the retirement run in increasing operand position and is refused). Neither answer is a
// second DERIVATION: `MfPlans::predict` is still handed the very `agg_chains` the `Return` arm
// routed, and both readers still come from one call to `agg_return_chains`.
//
// This file widens the class the residual lives in: aggregates whose fields are semantically
// equal, aggregates whose fields are equal only at one width, aggregates mixing marked temps with
// fresh operand temps, tuples of every arity the fragment admits, and aggregates with assignment
// traffic after the constructor so a moved retirement run is legible.
//
// No body name in this file appears in any of the 32 probe files rounds 1-6 wrote.

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::let_and_return, clippy::needless_return, clippy::precedence)]
#![allow(clippy::nonminimal_bool, clippy::needless_bool)]

#[derive(Clone, Copy)]
pub struct G2 {
    pub l: u32,
    pub r: u32,
}

#[derive(Clone, Copy)]
pub struct G3 {
    pub x: u32,
    pub y: u32,
    pub z: u32,
}

#[derive(Clone, Copy)]
pub struct G4 {
    pub a: u32,
    pub b: u32,
    pub c: u32,
    pub d: u32,
}

#[derive(Clone, Copy)]
pub struct GW {
    pub n: u32,
    pub w: u64,
}

// --- A: SEMANTICALLY EQUAL FIELDS. The residual class, widened. -----------------------------

#[inline(never)]
pub fn g01_two_equal_xor(a: u32, b: u32) -> G2 {
    G2 { l: a ^ b, r: a ^ b }
}

#[inline(never)]
pub fn g02_two_equal_and(a: u32, b: u32) -> G2 {
    G2 { l: a & b, r: a & b }
}

#[inline(never)]
pub fn g03_two_equal_params(a: u32) -> G2 {
    G2 { l: a, r: a }
}

#[inline(never)]
pub fn g04_two_equal_consts() -> G2 {
    G2 { l: 7, r: 7 }
}

#[inline(never)]
pub fn g05_three_equal_xor(a: u32, b: u32) -> G3 {
    G3 { x: a ^ b, y: a ^ b, z: a ^ b }
}

#[inline(never)]
pub fn g06_three_equal_params(a: u32) -> G3 {
    G3 { x: a, y: a, z: a }
}

#[inline(never)]
pub fn g07_four_equal_params(a: u32) -> G4 {
    G4 { a, b: a, c: a, d: a }
}

#[inline(never)]
pub fn g08_outer_equal_inner_differ(a: u32, b: u32) -> G3 {
    G3 { x: a ^ b, y: b ^ a, z: a ^ b }
}

// --- B: EQUAL PAIRS INSIDE A LARGER AGGREGATE — a reversal confined to two of four slots. ----

#[inline(never)]
pub fn g09_four_middle_pair_equal(a: u32, b: u32, c: u32) -> G4 {
    G4 { a: c, b: a ^ b, c: a ^ b, d: c }
}

#[inline(never)]
pub fn g10_four_outer_pair_equal(a: u32, b: u32, c: u32) -> G4 {
    G4 { a: a ^ b, b: c, c: c, d: a ^ b }
}

#[inline(never)]
pub fn g11_four_all_params(a: u32, b: u32, c: u32, d: u32) -> G4 {
    G4 { a, b, c, d }
}

#[inline(never)]
pub fn g12_four_reversed_params(a: u32, b: u32, c: u32, d: u32) -> G4 {
    G4 { a: d, b: c, c: b, d: a }
}

// --- C: MIXED MARKED TEMPS AND FRESH OPERAND TEMPS in one constructor -----------------------

#[inline(never)]
pub fn g13_temp_then_param(a: u32, b: u32, c: u32) -> G2 {
    G2 { l: a ^ b, r: c }
}

#[inline(never)]
pub fn g14_param_then_temp(a: u32, b: u32, c: u32) -> G2 {
    G2 { l: c, r: a ^ b }
}

#[inline(never)]
pub fn g15_const_then_temp(a: u32, b: u32) -> G2 {
    G2 { l: 3, r: a ^ b }
}

#[inline(never)]
pub fn g16_temp_then_const(a: u32, b: u32) -> G2 {
    G2 { l: a ^ b, r: 3 }
}

#[inline(never)]
pub fn g17_three_mixed(a: u32, b: u32, c: u32) -> G3 {
    G3 { x: a, y: b ^ c, z: 11 }
}

#[inline(never)]
pub fn g18_three_mixed_other_order(a: u32, b: u32, c: u32) -> G3 {
    G3 { x: 11, y: a, z: b ^ c }
}

// --- D: TUPLE RETURNS, every arity the fragment admits --------------------------------------

#[inline(never)]
pub fn g19_tuple_two_equal(a: u32, b: u32) -> (u32, u32) {
    (a ^ b, a ^ b)
}

#[inline(never)]
pub fn g20_tuple_two_params(a: u32, b: u32) -> (u32, u32) {
    (a, b)
}

#[inline(never)]
pub fn g21_tuple_two_swapped(a: u32, b: u32) -> (u32, u32) {
    (b, a)
}

#[inline(never)]
pub fn g22_tuple_three_equal(a: u32) -> (u32, u32, u32) {
    (a, a, a)
}

#[inline(never)]
pub fn g23_tuple_three_mixed(a: u32, b: u32) -> (u32, u32, u32) {
    (a, a ^ b, b)
}

#[inline(never)]
pub fn g24_tuple_four_params(a: u32, b: u32, c: u32, d: u32) -> (u32, u32, u32, u32) {
    (a, b, c, d)
}

#[inline(never)]
pub fn g25_tuple_bool_pair(a: u32, b: u32) -> (bool, bool) {
    (a == b, a == b)
}

// --- E: MIXED WIDTHS — equal at one width, different at another ----------------------------

#[inline(never)]
pub fn g26_widths_narrow_then_wide(a: u32, b: u64) -> GW {
    GW { n: a, w: b }
}

#[inline(never)]
pub fn g27_widths_cast_field(a: u32) -> GW {
    GW { n: a, w: a as u64 }
}

#[inline(never)]
pub fn g28_widths_both_computed(a: u32, b: u32) -> GW {
    GW { n: a ^ b, w: (a as u64) ^ (b as u64) }
}

// --- F: TRAFFIC AROUND THE CONSTRUCTOR — the aggregate's retirement run with assigns after it.

#[inline(never)]
pub fn g29_compute_then_construct(a: u32, b: u32, c: u32) -> G2 {
    let t = a ^ b;
    G2 { l: t, r: t ^ c }
}

#[inline(never)]
pub fn g30_construct_from_shadowed(a: u32, b: u32) -> G2 {
    let t = a ^ b;
    let t = t ^ a;
    G2 { l: t, r: t }
}

#[inline(never)]
pub fn g31_branch_then_construct(c: bool, a: u32, b: u32) -> G2 {
    let t = if c { a } else { b };
    G2 { l: t, r: t }
}

#[inline(never)]
pub fn g32_construct_in_both_arms(c: bool, a: u32, b: u32) -> G2 {
    if c { G2 { l: a ^ b, r: a ^ b } } else { G2 { l: b ^ a, r: b ^ a } }
}

// --- G: FIELD READS FEEDING A CONSTRUCTOR — the input aggregate and the output aggregate. ----

#[inline(never)]
pub fn g33_copy_fields_straight(p: &G2) -> G2 {
    G2 { l: p.l, r: p.r }
}

#[inline(never)]
pub fn g34_copy_fields_swapped(p: &G2) -> G2 {
    G2 { l: p.r, r: p.l }
}

#[inline(never)]
pub fn g35_copy_same_field_twice(p: &G2) -> G2 {
    G2 { l: p.l, r: p.l }
}

#[inline(never)]
pub fn g36_fields_combined_equal(p: &G2) -> G2 {
    G2 { l: p.l ^ p.r, r: p.l ^ p.r }
}
