// LANE MF-R5 — RETIREMENT DENSITY.
//
// `MfSite::Retire` is the site the fourth review's attack chose, and round 4's answer is an
// identity ledger: a `StorageDead` must retire a local some site marked live. A ledger that is
// WRITTEN on every live and only READ on every dead never consumes anything, so this file makes
// retirement dense — many operand temps per instruction, chained instructions, and the same
// local reachable from several operand positions — to make the difference between "retires a
// local that was marked" and "retires it once" measurable.
//
// No body name here appears in any of the 22 existing probe files.
//
//   trustc --edition 2021 --crate-type=lib --crate-name=p_mfr5_pair \
//     -Ztrust-ir-lower=on -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Ztrust-dump=ir:IR probes/mfr5_pair.rs --out-dir OUT

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::let_and_return, clippy::needless_return, clippy::bool_comparison)]
#![allow(clippy::nonminimal_bool, clippy::double_comparisons)]

#[derive(Clone, Copy)]
pub struct Quad {
    pub w: u32,
    pub x: u32,
    pub y: u32,
    pub z: u32,
}

// --- A: WIDE — one instruction, both operands needing a temp. -----------------------------

#[inline(never)]
pub fn h01_two_field_operands(q: Quad) -> bool {
    q.w == q.x
}

#[inline(never)]
pub fn h02_three_field_and(q: Quad) -> bool {
    (q.w & q.x) == q.y
}

#[inline(never)]
pub fn h03_four_field_and(q: Quad) -> bool {
    (q.w & q.x) == (q.y & q.z)
}

#[inline(never)]
pub fn h04_four_field_or(q: Quad) -> bool {
    (q.w | q.x) != (q.y | q.z)
}

// --- B: DEEP — left-spine chains, so the retirements nest. ---------------------------------

#[inline(never)]
pub fn h05_left_spine_3(a: u32, b: u32, c: u32) -> u32 {
    (a & b) & c
}

#[inline(never)]
pub fn h06_left_spine_4(a: u32, b: u32, c: u32, d: u32) -> u32 {
    ((a & b) & c) & d
}

#[inline(never)]
pub fn h07_left_spine_5(a: u32, b: u32, c: u32, d: u32, e: u32) -> u32 {
    (((a & b) & c) & d) & e
}

#[inline(never)]
pub fn h08_right_spine_4(a: u32, b: u32, c: u32, d: u32) -> u32 {
    a | (b | (c | d))
}

#[inline(never)]
pub fn h09_balanced_4(a: u32, b: u32, c: u32, d: u32) -> u32 {
    (a & b) | (c & d)
}

#[inline(never)]
pub fn h10_balanced_8(a: u32, b: u32, c: u32, d: u32, e: u32, f: u32, g: u32, i: u32) -> u32 {
    ((a & b) | (c & d)) ^ ((e & f) | (g & i))
}

// --- C: the SAME parameter in several operand positions — one source local, several temps. --

#[inline(never)]
pub fn h11_same_param_twice(a: u32) -> bool {
    a == a
}

#[inline(never)]
pub fn h12_same_param_thrice(a: u32) -> u32 {
    (a & a) & a
}

#[inline(never)]
pub fn h13_same_field_twice(q: Quad) -> bool {
    q.y == q.y
}

#[inline(never)]
pub fn h14_same_field_in_both_arms(q: Quad) -> u32 {
    (q.z & q.z) | (q.z & q.z)
}

// --- D: mixed constant / place operands, so exactly one side takes a temp. ------------------

#[inline(never)]
pub fn h15_const_left_field_right(q: Quad) -> bool {
    3 == q.w
}

#[inline(never)]
pub fn h16_field_left_const_right(q: Quad) -> bool {
    q.x == 3
}

#[inline(never)]
pub fn h17_const_folded_chain(a: u32) -> u32 {
    (a & 0xff) | 0x100
}

#[inline(never)]
pub fn h18_two_consts_one_place(a: u32) -> bool {
    ((a & 1) ^ 2) == 3
}

// --- E: shifts and casts inside operand trees — different widths on the two sides. ---------

#[inline(never)]
pub fn h19_shift_pair(a: u32, b: u32) -> bool {
    (a >> 1) == (b >> 2)
}

#[inline(never)]
pub fn h20_cast_pair(a: u8, b: u16) -> bool {
    (a as u32) == (b as u32)
}

#[inline(never)]
pub fn h21_cast_of_field(q: Quad) -> u64 {
    q.w as u64
}

#[inline(never)]
pub fn h22_widened_and(a: u8, b: u8) -> u32 {
    (a as u32) & (b as u32)
}
