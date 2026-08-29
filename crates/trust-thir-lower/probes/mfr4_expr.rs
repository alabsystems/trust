// LANE MF-R4 (round-3 REVIEW, 2026-08-13) — THE STATEMENT-FREE SURFACE.
//
// `source_form_admits` refuses any block carrying a non-item statement, so the wave-MF operand
// plan and lane K's branch plan only ever see EXPRESSION BODIES. That is the marker surface with
// the most emitting sites (`ResultTemp`, `OperandTemp`, `Retire`) and the least adversarial
// coverage: rounds 1-3 all converged on the field-write arm and left this one alone. Round 3's
// chokepoint routes all three of those sites through a single `mf_plan.is_some()` test, so if the
// operand plan is wrong about a body, the chokepoint hands it a lease anyway.
//
// Every body here is statement-free (or one construct away from it, as a control), and each adds
// exactly one nesting or ordering twist to the operand/branch plans: operand order under
// permutation, deep operator trees, right-nesting, mixed widths, comparison chains feeding
// branches, branch conditions that are themselves branches, and joins with unequal arm shapes.
//
// No name here appears in any of the 18 existing probe files.
//
//   trustc --edition 2021 --crate-type=lib --crate-name=p_mfr4_expr \
//     -Ztrust-ir-lower=on -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Ztrust-dump=ir:IR probes/mfr4_expr.rs --out-dir OUT

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::needless_bool, clippy::nonminimal_bool, clippy::precedence)]

#[derive(Clone, Copy)]
pub struct E4 {
    pub a: u32,
    pub b: u32,
    pub c: u64,
    pub d: u16,
}

// --- A: OPERAND TREES, left- and right-nested, with mixed categories --------------------------

#[inline(never)]
pub fn e01_left_nested_three(a: u32, b: u32, c: u32) -> u32 {
    (a ^ b) ^ c
}

#[inline(never)]
pub fn e02_right_nested_three(a: u32, b: u32, c: u32) -> u32 {
    a ^ (b ^ c)
}

#[inline(never)]
pub fn e03_right_nested_four(a: u32, b: u32, c: u32, d: u32) -> u32 {
    a ^ (b ^ (c ^ d))
}

#[inline(never)]
pub fn e04_balanced_four(a: u32, b: u32, c: u32, d: u32) -> u32 {
    (a ^ b) ^ (c ^ d)
}

#[inline(never)]
pub fn e05_const_left_place_right(a: u32) -> u32 {
    7 ^ a
}

#[inline(never)]
pub fn e06_place_left_const_right(a: u32) -> u32 {
    a ^ 7
}

#[inline(never)]
pub fn e07_field_operands(s: E4) -> u32 {
    s.a ^ s.b
}

#[inline(never)]
pub fn e08_field_and_deref(s: E4, p: &u32) -> u32 {
    s.a ^ *p
}

#[inline(never)]
pub fn e09_two_derefs(p: &u32, q: &u32) -> u32 {
    *p ^ *q
}

#[inline(never)]
pub fn e10_deref_field(p: &E4) -> u32 {
    p.a ^ p.b
}

#[inline(never)]
pub fn e11_mixed_width_cast(a: u16, b: u32) -> u32 {
    (a as u32) ^ b
}

#[inline(never)]
pub fn e12_u64_operands(a: u64, b: u64) -> u64 {
    a ^ b
}

// --- B: COMPARISONS feeding branches ----------------------------------------------------------

#[inline(never)]
pub fn e13_if_cmp_two_places(a: u32, b: u32) -> u32 {
    if a == b { a } else { b }
}

#[inline(never)]
pub fn e14_if_cmp_place_const(a: u32, b: u32) -> u32 {
    if a == 0 { b } else { a }
}

#[inline(never)]
pub fn e15_if_cmp_of_binop(a: u32, b: u32, c: u32) -> u32 {
    if (a ^ b) == c { a } else { c }
}

#[inline(never)]
pub fn e16_if_nested_cond(a: u32, b: u32, c: u32) -> u32 {
    if if a == b { true } else { false } { c } else { a }
}

#[inline(never)]
pub fn e17_if_arms_are_ifs(a: u32, b: u32, c: u32) -> u32 {
    if a == b { if b == c { a } else { b } } else { if a == c { c } else { a } }
}

#[inline(never)]
pub fn e18_if_arm_const_other_binop(a: u32, b: u32) -> u32 {
    if a == b { 0 } else { a ^ b }
}

#[inline(never)]
pub fn e19_if_arm_binop_other_const(a: u32, b: u32) -> u32 {
    if a == b { a ^ b } else { 0 }
}

#[inline(never)]
pub fn e20_if_both_arms_binop(a: u32, b: u32) -> u32 {
    if a == b { a ^ b } else { b ^ a }
}

#[inline(never)]
pub fn e21_if_cond_field(s: E4) -> u32 {
    if s.a == s.b { s.a } else { s.b }
}

#[inline(never)]
pub fn e22_if_cond_deref(p: &u32, a: u32) -> u32 {
    if *p == a { a } else { *p }
}

// --- C: MATCH as an expression ----------------------------------------------------------------

#[inline(never)]
pub fn e23_match_bool_expr(c: bool, a: u32, b: u32) -> u32 {
    match c {
        true => a,
        false => b,
    }
}

#[inline(never)]
pub fn e24_match_int_three_arms(a: u32, b: u32) -> u32 {
    match a {
        0 => b,
        1 => a,
        _ => 0,
    }
}

#[inline(never)]
pub fn e25_match_on_binop(a: u32, b: u32) -> u32 {
    match a ^ b {
        0 => a,
        _ => b,
    }
}

#[inline(never)]
pub fn e26_match_arms_binop(a: u32, b: u32) -> u32 {
    match a {
        0 => a ^ b,
        _ => b ^ a,
    }
}

#[inline(never)]
pub fn e27_match_nested_in_arm(a: u32, b: u32, c: u32) -> u32 {
    match a {
        0 => match b {
            0 => c,
            _ => b,
        },
        _ => a,
    }
}

// --- D: SHORT-CIRCUIT trees (branches with implicit joins) -------------------------------------

#[inline(never)]
pub fn e28_and_of_two_cmps(a: u32, b: u32, c: u32) -> bool {
    a == b && b == c
}

#[inline(never)]
pub fn e29_or_of_two_cmps(a: u32, b: u32, c: u32) -> bool {
    a == b || b == c
}

#[inline(never)]
pub fn e30_and_or_mixed(a: u32, b: u32, c: bool) -> bool {
    (a == b && c) || a == 0
}

#[inline(never)]
pub fn e31_not_of_and(a: u32, b: u32, c: bool) -> bool {
    !(a == b && c)
}

#[inline(never)]
pub fn e32_if_of_and(a: u32, b: u32, c: bool, d: u32) -> u32 {
    if a == b && c { d } else { a }
}

// --- E: UNARY / cast / bit chains -------------------------------------------------------------

#[inline(never)]
pub fn e33_not_place(a: u32) -> u32 {
    !a
}

#[inline(never)]
pub fn e34_not_of_binop(a: u32, b: u32) -> u32 {
    !(a ^ b)
}

#[inline(never)]
pub fn e35_cast_chain(a: u8) -> u64 {
    a as u32 as u64
}

#[inline(never)]
pub fn e36_cast_of_binop(a: u32, b: u32) -> u64 {
    (a ^ b) as u64
}

#[inline(never)]
pub fn e37_shift_by_place(a: u32, s: u32) -> u32 {
    a << s
}

#[inline(never)]
pub fn e38_shift_by_const(a: u32) -> u32 {
    a << 3
}

#[inline(never)]
pub fn e39_shift_of_shift(a: u32, s: u32, t: u32) -> u32 {
    (a << s) >> t
}

// --- F: STRUCT LITERAL tails, and permutation-relevant field orders ---------------------------

#[inline(never)]
pub fn e40_agg_in_order(a: u32, b: u32, c: u64, d: u16) -> E4 {
    E4 { a, b, c, d }
}

#[inline(never)]
pub fn e41_agg_out_of_order(a: u32, b: u32, c: u64, d: u16) -> E4 {
    E4 { d, c, b, a }
}

#[inline(never)]
pub fn e42_agg_mixed_const(a: u32, c: u64) -> E4 {
    E4 { b: 1, a, d: 2, c }
}

#[inline(never)]
pub fn e43_agg_from_derefs(p: &u32, q: &u32, r: &u64, s: &u16) -> E4 {
    E4 { a: *p, b: *q, c: *r, d: *s }
}

#[inline(never)]
pub fn e44_agg_of_binops(a: u32, b: u32, c: u64) -> E4 {
    E4 { a: a ^ b, b: b ^ a, c, d: 0 }
}

#[inline(never)]
pub fn e45_agg_same_field_twice_order(a: u32, c: u64) -> E4 {
    E4 { c, a, b: a, d: 0 }
}

#[inline(never)]
pub fn e46_agg_inside_if(c: bool, a: u32, b: u32) -> E4 {
    if c { E4 { a, b, c: 0, d: 0 } } else { E4 { a: b, b: a, c: 0, d: 0 } }
}

// --- G: CONTROLS — the same shape with one statement, to pin what the statement costs ---------

#[inline(never)]
pub fn e47_control_let_then_binop(a: u32, b: u32) -> u32 {
    let t = a ^ b;
    t
}

#[inline(never)]
pub fn e48_control_semi_then_binop(a: u32, b: u32) -> u32 {
    ();
    a ^ b
}

#[inline(never)]
pub fn e49_control_item_then_binop(a: u32, b: u32) -> u32 {
    const Z: u32 = 0;
    a ^ b ^ Z
}
