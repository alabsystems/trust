// LANE MF-R5 — THE MULTI-BLOCK PLAN (lane K).
//
// `mf_plan` for a multi-block body comes from `plan_branch_markers`, and lane K's discipline
// retires the condition's operand temps at the ENTRY OF BOTH ARMS — one list, emitted twice.
// That is the one place in the shim where `dead` legitimately exceeds `live`, and it is exactly
// the arithmetic the body-end ledger has to leave loose. This file populates it: conditions of
// every operand shape, arms of every marker-mintiness, and joins that do and do not add work.
//
// No body name here appears in any of the 22 existing probe files.
//
//   trustc --edition 2021 --crate-type=lib --crate-name=p_mfr5_branch \
//     -Ztrust-ir-lower=on -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Ztrust-dump=ir:IR probes/mfr5_branch.rs --out-dir OUT

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::let_and_return, clippy::needless_return, clippy::bool_comparison)]
#![allow(clippy::if_same_then_else, clippy::needless_bool)]

#[derive(Clone, Copy)]
pub struct Sel {
    pub k: u32,
    pub m: u32,
    pub f: bool,
}

// --- A: condition is a bare place — no operand temp to retire at the arms. -----------------

#[inline(never)]
pub fn k01_if_param_bool(c: bool, a: u32, b: u32) -> u32 {
    if c { a } else { b }
}

#[inline(never)]
pub fn k02_if_field_bool(s: Sel, a: u32, b: u32) -> u32 {
    if s.f { a } else { b }
}

#[inline(never)]
pub fn k03_if_not_param(c: bool, a: u32, b: u32) -> u32 {
    if !c { a } else { b }
}

// --- B: condition is a comparison — two operand temps, retired at BOTH arm entries. --------

#[inline(never)]
pub fn k04_if_eq_params(a: u32, b: u32) -> u32 {
    if a == b { a } else { b }
}

#[inline(never)]
pub fn k05_if_lt_params(a: i32, b: i32) -> i32 {
    if a < b { a } else { b }
}

#[inline(never)]
pub fn k06_if_eq_fields(s: Sel) -> u32 {
    if s.k == s.m { s.k } else { s.m }
}

#[inline(never)]
pub fn k07_if_eq_field_const(s: Sel) -> u32 {
    if s.k == 0 { 1 } else { s.m }
}

#[inline(never)]
pub fn k08_if_nested_and_cond(a: u32, b: u32, c: u32) -> u32 {
    if (a & b) == c { a } else { c }
}

// --- C: arms that themselves mint markers — the join is where a per-body lease stops being
//        the same statement as a per-value plan. ---------------------------------------------

#[inline(never)]
pub fn k09_arms_compare(c: bool, a: u32, b: u32) -> bool {
    if c { a == b } else { b == a }
}

#[inline(never)]
pub fn k10_arms_and(c: bool, a: u32, b: u32) -> u32 {
    if c { a & b } else { b & a }
}

#[inline(never)]
pub fn k11_cond_and_arms_both(a: u32, b: u32) -> u32 {
    if a == b { a & b } else { a | b }
}

#[inline(never)]
pub fn k12_nested_if(a: u32, b: u32, c: u32) -> u32 {
    if a == b {
        if b == c { a } else { b }
    } else {
        c
    }
}

// --- D: short-circuit joins — two `CondBr`s and a join block that mints its own value. -----

#[inline(never)]
pub fn k13_and_and(a: u32, b: u32, c: u32) -> bool {
    a == b && b == c
}

#[inline(never)]
pub fn k14_or_or(a: u32, b: u32, c: u32) -> bool {
    a == b || b == c
}

#[inline(never)]
pub fn k15_and_or_mix(a: u32, b: u32, c: u32, d: u32) -> bool {
    (a == b) && (c == d || a == d)
}

#[inline(never)]
pub fn k16_not_of_and(a: u32, b: u32, c: u32) -> bool {
    !(a == b && b == c)
}

// --- E: match as a branch — a `SwitchInt` whose discriminant is a bool or a small int. -----

#[inline(never)]
pub fn k17_match_bool(c: bool, a: u32, b: u32) -> u32 {
    match c {
        true => a,
        false => b,
    }
}

#[inline(never)]
pub fn k18_match_bool_of_cmp(a: u32, b: u32) -> u32 {
    match a == b {
        true => a,
        false => b,
    }
}

#[inline(never)]
pub fn k19_if_else_if(a: u32, b: u32) -> u32 {
    if a == b {
        0
    } else if a < b {
        1
    } else {
        2
    }
}

#[inline(never)]
pub fn k20_cond_field_arms_field(s: Sel) -> u32 {
    if s.f { s.k & s.m } else { s.k | s.m }
}
