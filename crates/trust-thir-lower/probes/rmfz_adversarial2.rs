// REVIEW LANE (rmfz, 2026-08-13) — ADVERSARIAL CORPUS, PART 2.
//
// Part 1 exposed a blind spot in part 1 itself: `canon_markers` renames locals by FIRST APPEARANCE
// and carries only the TYPE, so a permutation of same-typed fields is INVISIBLE to the marker
// channel (`T3 { c: z, a: x, b: y }` with three `u32` fields compares equal to `T3 { a: x, b: y,
// c: z }`). Every ordering question here is therefore asked over a struct whose three fields have
// THREE DIFFERENT WIDTHS, so a swap moves a type in the canonical sequence.
//
// Also here: the MULTI-BLOCK plan (`plan_branch_markers`), which the subject newly gates behind the
// source-form gate — a change that can only REMOVE derived markers, and therefore can only lose
// flips. And the constant-field-write EMISSION change, in the shapes the lane's group E did not
// use.

#![allow(clippy::eq_op, clippy::identity_op, dead_code)]

/// Three DIFFERENT widths, so a permutation is visible in the canonical marker sequence.
#[derive(Clone, Copy)]
pub struct W3 {
    pub a: u8,
    pub b: u32,
    pub c: u64,
}

#[derive(Clone, Copy)]
pub struct W2 {
    pub a: u8,
    pub b: u64,
}

#[derive(Clone, Copy)]
pub struct Slot {
    pub f: bool,
    pub g: u8,
    pub h: u64,
}

// =================================================================================================
// GROUP W — FRU AND FIELD PERMUTATION OVER A MIXED-WIDTH THREE-FIELD STRUCT.
// All 8 FRU spellings (7 non-empty explicit subsets + the empty one), all 6 written orders of the
// fully-written PARAM form, all 6 written orders of the fully-written SAME-INDEX-READ form, and
// the partial twins in every position.
// =================================================================================================

// --- FRU spellings ---
#[inline(never)]
pub fn w01_fru_none(p: W3) -> W3 {
    W3 { ..p }
}
#[inline(never)]
pub fn w02_fru_a(p: W3, x: u8) -> W3 {
    W3 { a: x, ..p }
}
#[inline(never)]
pub fn w03_fru_b(p: W3, y: u32) -> W3 {
    W3 { b: y, ..p }
}
#[inline(never)]
pub fn w04_fru_c(p: W3, z: u64) -> W3 {
    W3 { c: z, ..p }
}
#[inline(never)]
pub fn w05_fru_ab(p: W3, x: u8, y: u32) -> W3 {
    W3 { a: x, b: y, ..p }
}
#[inline(never)]
pub fn w06_fru_ac(p: W3, x: u8, z: u64) -> W3 {
    W3 { a: x, c: z, ..p }
}
#[inline(never)]
pub fn w07_fru_bc(p: W3, y: u32, z: u64) -> W3 {
    W3 { b: y, c: z, ..p }
}
#[inline(never)]
pub fn w08_fru_ca_written_reversed(p: W3, x: u8, z: u64) -> W3 {
    W3 { c: z, a: x, ..p }
}

// --- fully written, PARAM values, all six source orders ---
#[inline(never)]
pub fn w09_abc(x: u8, y: u32, z: u64) -> W3 {
    W3 { a: x, b: y, c: z }
}
#[inline(never)]
pub fn w10_acb(x: u8, y: u32, z: u64) -> W3 {
    W3 { a: x, c: z, b: y }
}
#[inline(never)]
pub fn w11_bac(x: u8, y: u32, z: u64) -> W3 {
    W3 { b: y, a: x, c: z }
}
#[inline(never)]
pub fn w12_bca(x: u8, y: u32, z: u64) -> W3 {
    W3 { b: y, c: z, a: x }
}
#[inline(never)]
pub fn w13_cab(x: u8, y: u32, z: u64) -> W3 {
    W3 { c: z, a: x, b: y }
}
#[inline(never)]
pub fn w14_cba(x: u8, y: u32, z: u64) -> W3 {
    W3 { c: z, b: y, a: x }
}

// --- fully written, SAME-INDEX BASE READS (the written-out twin of `W3 { ..p }`), six orders ---
#[inline(never)]
pub fn w15_reads_abc(p: W3) -> W3 {
    W3 { a: p.a, b: p.b, c: p.c }
}
#[inline(never)]
pub fn w16_reads_acb(p: W3) -> W3 {
    W3 { a: p.a, c: p.c, b: p.b }
}
#[inline(never)]
pub fn w17_reads_bac(p: W3) -> W3 {
    W3 { b: p.b, a: p.a, c: p.c }
}
#[inline(never)]
pub fn w18_reads_bca(p: W3) -> W3 {
    W3 { b: p.b, c: p.c, a: p.a }
}
#[inline(never)]
pub fn w19_reads_cab(p: W3) -> W3 {
    W3 { c: p.c, a: p.a, b: p.b }
}
#[inline(never)]
pub fn w20_reads_cba(p: W3) -> W3 {
    W3 { c: p.c, b: p.b, a: p.a }
}

// --- partial written-out twins: one explicit param, two same-index reads, every position ---
#[inline(never)]
pub fn w21_twin_a(p: W3, x: u8) -> W3 {
    W3 { a: x, b: p.b, c: p.c }
}
#[inline(never)]
pub fn w22_twin_b(p: W3, y: u32) -> W3 {
    W3 { a: p.a, b: y, c: p.c }
}
#[inline(never)]
pub fn w23_twin_c(p: W3, z: u64) -> W3 {
    W3 { a: p.a, b: p.b, c: z }
}

// --- partial twins written OUT of field order ---
#[inline(never)]
pub fn w24_twin_a_written_last(p: W3, x: u8) -> W3 {
    W3 { b: p.b, c: p.c, a: x }
}
#[inline(never)]
pub fn w25_twin_c_written_first(p: W3, z: u64) -> W3 {
    W3 { c: z, a: p.a, b: p.b }
}

// --- reads that CROSS indices (no FRU spelling exists) — in field order and out of it ---
#[inline(never)]
pub fn w26_cross_in_order(p: W3, q: W3) -> W3 {
    W3 { a: q.a, b: p.b, c: q.c }
}
#[inline(never)]
pub fn w27_cross_out_of_order(p: W3, q: W3) -> W3 {
    W3 { c: q.c, b: p.b, a: q.a }
}

// --- an INSTRUCTION field plus same-index reads, in every position ---
#[inline(never)]
pub fn w28_instr_first(p: W3, x: u8, y: u8) -> W3 {
    W3 { a: x & y, b: p.b, c: p.c }
}
#[inline(never)]
pub fn w29_instr_middle(p: W3, x: u32, y: u32) -> W3 {
    W3 { a: p.a, b: x & y, c: p.c }
}
#[inline(never)]
pub fn w30_instr_last(p: W3, x: u64, y: u64) -> W3 {
    W3 { a: p.a, b: p.b, c: x & y }
}

// --- an instruction field written LAST but declared FIRST ---
#[inline(never)]
pub fn w31_instr_first_written_last(p: W3, x: u8, y: u8) -> W3 {
    W3 { b: p.b, c: p.c, a: x & y }
}

// --- two same-index reads and one CONSTANT, out of written order ---
#[inline(never)]
pub fn w32_const_and_reads_out_of_order(p: W3) -> W3 {
    W3 { c: p.c, a: 1, b: p.b }
}

// --- a two-field mixed-width struct, both spellings ---
#[inline(never)]
pub fn w33_w2_in_order(x: u8, y: u64) -> W2 {
    W2 { a: x, b: y }
}
#[inline(never)]
pub fn w34_w2_out_of_order(x: u8, y: u64) -> W2 {
    W2 { b: y, a: x }
}
#[inline(never)]
pub fn w35_w2_reads_out_of_order(p: W2) -> W2 {
    W2 { b: p.b, a: p.a }
}
#[inline(never)]
pub fn w36_w2_fru(p: W2, x: u8) -> W2 {
    W2 { a: x, ..p }
}
#[inline(never)]
pub fn w37_w2_fru_b(p: W2, y: u64) -> W2 {
    W2 { b: y, ..p }
}

// =================================================================================================
// GROUP K — MULTI-BLOCK BODIES. `plan_branch_markers` is newly gated behind the source-form gate,
// which can only REMOVE derived markers. Every shape here is a body the multi-block plan could
// admit; the ones with a destructuring parameter, a statement, or an out-of-order struct literal
// are the ones the new gate withdraws.
// =================================================================================================

#[inline(never)]
pub fn k01_if_simple(a: u64, b: u64) -> u64 {
    if a == 0 { b } else { a }
}

#[inline(never)]
pub fn k02_if_marked_cond(a: u64, b: u64, c: u64) -> u64 {
    if (a & b) == 0 { c } else { a }
}

#[inline(never)]
pub fn k03_if_destructured_param(&a: &u64, b: u64) -> u64 {
    if a == 0 { b } else { a }
}

#[inline(never)]
pub fn k04_if_wild_param(_: u64, a: u64, b: u64) -> u64 {
    if a == 0 { b } else { a }
}

#[inline(never)]
pub fn k05_if_mut_param(mut a: u64, b: u64) -> u64 {
    if a == 0 { b } else { a }
}

#[inline(never)]
pub fn k06_shortcircuit_or(a: u64, b: u64) -> bool {
    a == 0 || b == 0
}

#[inline(never)]
pub fn k07_shortcircuit_and(a: u64, b: u64) -> bool {
    a == 0 && b == 0
}

#[inline(never)]
pub fn k08_if_struct_in_order(p: W3, a: u64, x: u8, y: u32, z: u64) -> W3 {
    if a == 0 { W3 { a: x, b: y, c: z } } else { p }
}

#[inline(never)]
pub fn k09_if_struct_out_of_order(p: W3, a: u64, x: u8, y: u32, z: u64) -> W3 {
    if a == 0 { W3 { c: z, a: x, b: y } } else { p }
}

#[inline(never)]
pub fn k10_if_field_cond(s: W3, b: u64) -> u64 {
    if s.a == 0 { b } else { s.c }
}

#[inline(never)]
pub fn k11_nested_if(a: u64, b: u64, c: u64) -> u64 {
    if a == 0 { if b == 0 { c } else { b } } else { a }
}

#[inline(never)]
pub fn k12_if_right_nested_cond(a: u64, b: u64, c: u64) -> u64 {
    if a == (b & c) { b } else { c }
}

// =================================================================================================
// GROUP E2 — THE CONSTANT-FIELD-WRITE EMISSION CHANGE, in shapes the lane's group E did not use.
// The change is NOT gated by the source-form gate, so it reaches every body.
// =================================================================================================

#[inline(never)]
pub fn e2_01_write_bool_true(s: &mut Slot) {
    s.f = true;
}
#[inline(never)]
pub fn e2_02_write_bool_false(s: &mut Slot) {
    s.f = false;
}
#[inline(never)]
pub fn e2_03_write_u8_const(s: &mut Slot) {
    s.g = 200;
}
#[inline(never)]
pub fn e2_04_write_u64_const(s: &mut Slot) {
    s.h = 0xDEAD_BEEF_CAFE_0000;
}
#[inline(never)]
pub fn e2_05_write_zero(s: &mut Slot) {
    s.h = 0;
}
#[inline(never)]
pub fn e2_06_write_named_const(s: &mut Slot) {
    const K: u64 = 77;
    s.h = K;
}
#[inline(never)]
pub fn e2_07_write_const_then_read(s: &mut Slot) -> u64 {
    s.h = 5;
    s.h
}
#[inline(never)]
pub fn e2_08_write_place_then_const(s: &mut Slot, v: u64) {
    s.h = v;
    s.g = 1;
}
#[inline(never)]
pub fn e2_09_write_three_consts(s: &mut Slot) {
    s.f = true;
    s.g = 2;
    s.h = 3;
}
#[inline(never)]
pub fn e2_10_write_through_ref(s: &mut &mut Slot) {
    s.h = 9;
}
#[inline(never)]
pub fn e2_11_write_cast_const(s: &mut Slot, _v: u8) {
    s.h = 4u32 as u64;
}
#[inline(never)]
pub fn e2_12_write_neg_const(s: &mut Slot) {
    s.g = !0u8;
}

// =================================================================================================
// GROUP X — remaining operand-position questions at MIXED WIDTHS, where the canonical sequence
// cannot hide a swap.
// =================================================================================================

// A marked CAST (u8 -> u64) as operand 0 and a place (u64) as operand 1.
#[inline(never)]
pub fn x01_cast_then_place_mixed(a: u8, b: u64) -> u64 {
    (a as u64) & b
}
// The mirror, refused by rule (2).
#[inline(never)]
pub fn x02_place_then_cast_mixed(a: u8, b: u64) -> u64 {
    b & (a as u64)
}
// A marked cast on BOTH sides, different source widths.
#[inline(never)]
pub fn x03_two_casts_mixed(a: u8, b: u16) -> bool {
    (a as u64) == (b as u64)
}
// The same, source widths swapped, to catch a sequence that is order-blind.
#[inline(never)]
pub fn x04_two_casts_mixed_swapped(a: u8, b: u16) -> bool {
    (b as u64) == (a as u64)
}
// A marked load (u64) and a marked cast (u8 -> u64).
#[inline(never)]
pub fn x05_load_and_cast(p: &u64, a: u8) -> bool {
    *p == (a as u64)
}
// The mirror.
#[inline(never)]
pub fn x06_cast_and_load(p: &u64, a: u8) -> bool {
    (a as u64) == *p
}
// A marked binop whose operands are a field read (u8) and a constant, compared to a wider field.
#[inline(never)]
pub fn x07_field_binop_then_field(s: W3) -> bool {
    ((s.a & 1) as u64) == s.c
}
// A field read of a NARROW field as the place operand after a marked WIDE binop.
#[inline(never)]
pub fn x08_wide_marked_then_narrow_place(s: W3, y: u64) -> bool {
    (s.c & y) == s.c
}
