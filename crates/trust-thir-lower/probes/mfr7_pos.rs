// LANE MF-R8 (seventh review) — MARKER POSITION, NOT MARKER COUNT.
//
// Everything the marker gate checks today is a COUNT (`observe` vs `MfPlans::predict`), three
// IDENTITY rules (live-twice / dead-twice-in-one-block / live-never-retired) and, since round 6,
// ONE ORDER rule (`mf_gate::retirement_order`: within a run of `StorageDead`s the locals that are
// operands of one assignment must appear in strictly decreasing operand position).
//
// None of those reads a marker's POSITION RELATIVE TO THE ASSIGNMENTS AROUND IT — which is
// exactly what the oracle's marker channel renders (`mk b{fine}.{assigns_seen}:{live|dead}`).
// This file is built so that position is LEGIBLE: every body has at least one marked temp with
// real assignment traffic both before and after it, so a marker moved by one statement changes
// the rendered line and nothing else. A body with a single assign and its markers at the two ends
// cannot distinguish "immediately after the consuming assign" from "at the end of the block", and
// most of the 1,280 bodies rounds 1-6 wrote are that shape.
//
// No body name in this file appears in any of the 32 probe files rounds 1-6 wrote.

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::let_and_return, clippy::needless_return, clippy::bool_comparison)]
#![allow(clippy::if_same_then_else, clippy::needless_bool, clippy::precedence)]
#![allow(clippy::nonminimal_bool, clippy::comparison_chain, clippy::collapsible_else_if)]

#[derive(Clone, Copy)]
pub struct Pos {
    pub u: u32,
    pub v: u32,
    pub w: u64,
}

// --- A: TRAFFIC AFTER THE RETIREMENT RUN. The consuming assign is followed by more assigns, so
//        "retire here" and "retire at the end of the block" render differently. ----------------

#[inline(never)]
pub fn q01_cmp_then_two_more_ops(a: u32, b: u32, c: u32) -> u32 {
    let t = (a ^ b) ^ c;
    t ^ a
}

#[inline(never)]
pub fn q02_pair_then_pair(a: u32, b: u32, c: u32, d: u32) -> u32 {
    (a ^ b) ^ (c ^ d)
}

#[inline(never)]
pub fn q03_three_sequential_pairs(a: u32, b: u32, c: u32) -> u32 {
    ((a ^ b) ^ (b ^ c)) ^ (c ^ a)
}

#[inline(never)]
pub fn q04_deep_left_five(a: u32, b: u32, c: u32, d: u32, e: u32) -> u32 {
    ((((a ^ b) ^ c) ^ d) ^ e)
}

#[inline(never)]
pub fn q05_deep_right_five(a: u32, b: u32, c: u32, d: u32, e: u32) -> u32 {
    a ^ (b ^ (c ^ (d ^ e)))
}

#[inline(never)]
pub fn q06_and_or_and(a: u32, b: u32, c: u32, d: u32) -> u32 {
    (a & b) | (c & d)
}

#[inline(never)]
pub fn q07_shift_then_mask(a: u32, b: u32) -> u32 {
    (a >> 3) & b
}

#[inline(never)]
pub fn q08_mask_then_shift(a: u32, b: u32) -> u32 {
    (a & b) >> 3
}

// --- B: A MARKED TEMP WHOSE LIVE AND DEAD STRADDLE OTHER TRAFFIC ------------------------------

#[inline(never)]
pub fn q09_first_pair_dies_late(a: u32, b: u32, c: u32, d: u32) -> u32 {
    let p = a ^ b;
    let q = c ^ d;
    p ^ q
}

#[inline(never)]
pub fn q10_first_pair_dies_later_still(a: u32, b: u32, c: u32, d: u32, e: u32) -> u32 {
    let p = a ^ b;
    let q = c ^ d;
    let r = d ^ e;
    (p ^ q) ^ r
}

#[inline(never)]
pub fn q11_reuse_one_operand_twice(a: u32, b: u32) -> u32 {
    (a ^ b) ^ (a ^ b)
}

#[inline(never)]
pub fn q12_reuse_one_operand_thrice(a: u32, b: u32) -> u32 {
    ((a ^ b) ^ a) ^ b
}

// --- C: COMPARISONS FOLLOWED BY ARITHMETIC (the ICmp arm with traffic after it) ----------------

#[inline(never)]
pub fn q13_cmp_then_arith(a: u32, b: u32, c: u32) -> u32 {
    if a == b { c ^ 1 } else { c ^ 2 }
}

#[inline(never)]
pub fn q14_cmp_of_sums(a: u32, b: u32, c: u32, d: u32) -> bool {
    (a ^ b) == (c ^ d)
}

#[inline(never)]
pub fn q15_two_cmps_anded(a: u32, b: u32, c: u32) -> bool {
    (a == b) & (b == c)
}

#[inline(never)]
pub fn q16_two_cmps_ored(a: u32, b: u32, c: u32) -> bool {
    (a == b) | (b == c)
}

#[inline(never)]
pub fn q17_cmp_lt_then_cmp_gt(a: u32, b: u32) -> bool {
    (a < b) & (b > a)
}

#[inline(never)]
pub fn q18_cmp_chain_three(a: u32, b: u32, c: u32, d: u32) -> bool {
    ((a == b) & (b == c)) | (c == d)
}

// --- D: BRANCH CONDITIONS WITH TRAFFIC IN BOTH ARMS. Lane K defers the condition's operand
//        temps onto BOTH arm entries at assign position 0; a run moved to the arm's END renders
//        differently only if the arm HAS assigns. --------------------------------------------

#[inline(never)]
pub fn q19_branch_arms_both_work(a: u32, b: u32, c: u32) -> u32 {
    if a == b { c ^ a } else { c ^ b }
}

#[inline(never)]
pub fn q20_branch_arms_both_two_ops(a: u32, b: u32, c: u32, d: u32) -> u32 {
    if a == b { (c ^ a) ^ d } else { (c ^ b) ^ d }
}

#[inline(never)]
pub fn q21_branch_cond_from_pair(a: u32, b: u32, c: u32, d: u32) -> u32 {
    if (a ^ b) == c { d ^ 1 } else { d ^ 2 }
}

#[inline(never)]
pub fn q22_branch_then_join_work(a: u32, b: u32, c: u32) -> u32 {
    let t = if a == b { c } else { a };
    t ^ b
}

#[inline(never)]
pub fn q23_branch_join_two_ops(a: u32, b: u32, c: u32, d: u32) -> u32 {
    let t = if a == b { c } else { a };
    (t ^ b) ^ d
}

#[inline(never)]
pub fn q24_nested_branch_arms_work(a: u32, b: u32, c: u32, d: u32) -> u32 {
    if a == b {
        if c == d { a ^ c } else { b ^ d }
    } else {
        c ^ d
    }
}

// --- E: FIELD READS AS OPERANDS, with traffic after ---------------------------------------

#[inline(never)]
pub fn q25_two_fields_then_op(p: &Pos, a: u32) -> u32 {
    (p.u ^ p.v) ^ a
}

#[inline(never)]
pub fn q26_field_then_two_ops(p: &Pos, a: u32, b: u32) -> u32 {
    ((p.u ^ a) ^ b) ^ p.v
}

#[inline(never)]
pub fn q27_field_cmp_then_arith(p: &Pos, a: u32) -> u32 {
    if p.u == p.v { a ^ 1 } else { a ^ 2 }
}

#[inline(never)]
pub fn q28_field_wide_then_narrow(p: &Pos, a: u64) -> u64 {
    (p.w ^ a) ^ (p.u as u64)
}

// --- F: CASTS AND UNARY, with traffic after ----------------------------------------------

#[inline(never)]
pub fn q29_cast_then_two_ops(a: u32, b: u64, c: u64) -> u64 {
    ((a as u64) ^ b) ^ c
}

#[inline(never)]
pub fn q30_two_casts_then_op(a: u32, b: u16, c: u64) -> u64 {
    ((a as u64) ^ (b as u64)) ^ c
}

#[inline(never)]
pub fn q31_not_then_two_ops(a: u32, b: u32, c: u32) -> u32 {
    ((!a) ^ b) ^ c
}

#[inline(never)]
pub fn q32_neg_then_op(a: i32, b: i32) -> i32 {
    (-a) ^ b
}

// --- G: SINGLE-OPERAND RUNS. The order rule is VACUOUS on a run of one constrained local, so
//        these bodies measure whether anything else sees a moved marker. --------------------

#[inline(never)]
pub fn q33_one_const_operand_then_work(a: u32, b: u32) -> u32 {
    (a ^ 7) ^ b
}

#[inline(never)]
pub fn q34_both_const_operands_then_work(a: u32) -> u32 {
    (5u32 ^ 7u32) ^ a
}

#[inline(never)]
pub fn q35_const_then_field(p: &Pos) -> u32 {
    (p.u ^ 9) ^ p.v
}

#[inline(never)]
pub fn q36_unary_only_then_work(a: u32, b: u32) -> u32 {
    let n = !a;
    n ^ b
}
