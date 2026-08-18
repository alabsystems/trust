// LANE MF-R6 (sixth review) — THE `match` FAMILY, which is where round 5's residual lived.
//
// `k18_match_bool_of_cmp` was admitted-and-wrong in every driver back to the control: built ends a
// MATCH SCRUTINEE's temporary scope AT the scrutinee (retiring the comparison's operand temps in
// the HEAD block) while an `if` CONDITION's scope ends on each outgoing edge (retiring them at both
// arm entries). The two spellings lower to byte-identical trust-ir. Round 5 refuses a `match` whose
// scrutinee is not `hir_tail_is_marker_free`; new-main refuses ANY `match`. This file is the family
// that decides whether either refusal is the right width — every scrutinee shape that mints a temp,
// every scrutinee shape that does not, and the `if` sibling of each so the two can be compared row
// by row.
//
// No body name in this file appears in any of the 27 probe files rounds 1-5 wrote.
//
//   trustc --edition 2021 --crate-type=lib --crate-name=p_mfr6_match \
//     -Ztrust-ir-lower=on -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Ztrust-dump=ir:IR probes/mfr6_match.rs --out-dir OUT

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::let_and_return, clippy::needless_return, clippy::bool_comparison)]
#![allow(clippy::if_same_then_else, clippy::needless_bool, clippy::match_like_matches_macro)]
#![allow(clippy::comparison_chain, clippy::needless_match)]

#[derive(Clone, Copy)]
pub struct Pair {
    pub a: u32,
    pub b: u32,
    pub f: bool,
}

// --- A: scrutinee is a BARE PLACE — mints no temp on either side. The admitted sibling. --------

#[inline(never)]
pub fn q01_match_param_bool(c: bool, x: u32, y: u32) -> u32 {
    match c {
        true => x,
        false => y,
    }
}

#[inline(never)]
pub fn q02_match_field_bool(p: Pair, x: u32, y: u32) -> u32 {
    match p.f {
        true => x,
        false => y,
    }
}

#[inline(never)]
pub fn q03_match_param_bool_wild(c: bool, x: u32, y: u32) -> u32 {
    match c {
        true => x,
        _ => y,
    }
}

// --- B: scrutinee is a COMPARISON — k18's exact family, one row per comparison operator. -------

#[inline(never)]
pub fn q04_match_eq_params(a: u32, b: u32) -> u32 {
    match a == b {
        true => a,
        false => b,
    }
}

#[inline(never)]
pub fn q05_match_ne_params(a: u32, b: u32) -> u32 {
    match a != b {
        true => a,
        false => b,
    }
}

#[inline(never)]
pub fn q06_match_lt_params(a: i32, b: i32) -> i32 {
    match a < b {
        true => a,
        false => b,
    }
}

#[inline(never)]
pub fn q07_match_ge_params(a: i32, b: i32) -> i32 {
    match a >= b {
        true => a,
        false => b,
    }
}

#[inline(never)]
pub fn q08_match_eq_fields(p: Pair) -> u32 {
    match p.a == p.b {
        true => p.a,
        false => p.b,
    }
}

#[inline(never)]
pub fn q09_match_eq_field_const(p: Pair) -> u32 {
    match p.a == 0 {
        true => 1,
        false => p.b,
    }
}

// The `if` sibling of q04 — same program, different scope rule. Stays admitted in both designs.
#[inline(never)]
pub fn q10_if_eq_params_sibling(a: u32, b: u32) -> u32 {
    if a == b { a } else { b }
}

// --- C: scrutinee is a BOOLEAN OPERATOR result — a temp built retires at the scrutinee. --------

#[inline(never)]
pub fn q11_match_and_of_cmps(a: u32, b: u32, c: u32) -> u32 {
    match (a == b) & (b == c) {
        true => a,
        false => c,
    }
}

#[inline(never)]
pub fn q12_match_xor_params(x: bool, y: bool, a: u32, b: u32) -> u32 {
    match x ^ y {
        true => a,
        false => b,
    }
}

#[inline(never)]
pub fn q13_match_not_param(c: bool, a: u32, b: u32) -> u32 {
    match !c {
        true => a,
        false => b,
    }
}

#[inline(never)]
pub fn q14_match_bitand_eq(a: u32, b: u32, c: u32) -> u32 {
    match (a & b) == c {
        true => a,
        false => c,
    }
}

// --- D: scrutinee is a CAST — a temp on the built side, no `Inst::ICmp` on ours. ----------------

#[inline(never)]
pub fn q15_match_cast_eq(a: u8, b: u32) -> u32 {
    match (a as u32) == b {
        true => b,
        false => 0,
    }
}

// --- E: NON-BOOL scrutinees — an integer switch, which is a different SwitchInt shape. ---------

#[inline(never)]
pub fn q16_match_u32_literals(k: u32, a: u32, b: u32) -> u32 {
    match k {
        0 => a,
        1 => b,
        _ => 0,
    }
}

#[inline(never)]
pub fn q17_match_u32_binding_arm(k: u32, a: u32) -> u32 {
    match k {
        0 => a,
        n => n,
    }
}

#[inline(never)]
pub fn q18_match_field_u32_literals(p: Pair) -> u32 {
    match p.a {
        0 => p.b,
        _ => p.a,
    }
}

// A scrutinee that is itself an ARITHMETIC result: the temp is not a comparison temp.
#[inline(never)]
pub fn q19_match_sum_literals(a: u32, b: u32) -> u32 {
    match a & b {
        0 => a,
        _ => b,
    }
}

// --- F: arms that MINT — the join is where the marked-result set and the branch plan meet. -----

#[inline(never)]
pub fn q20_match_param_arms_compare(c: bool, a: u32, b: u32) -> bool {
    match c {
        true => a == b,
        false => b == a,
    }
}

#[inline(never)]
pub fn q21_match_param_arms_and(c: bool, a: u32, b: u32) -> u32 {
    match c {
        true => a & b,
        false => b | a,
    }
}

#[inline(never)]
pub fn q22_match_cmp_arms_compare(a: u32, b: u32) -> bool {
    match a == b {
        true => a == 0,
        false => b == 0,
    }
}

// --- G: `matches!` — a macro-expanded match whose arms are constants. --------------------------

#[inline(never)]
pub fn q23_matches_macro_param(k: u32) -> bool {
    matches!(k, 0)
}

#[inline(never)]
pub fn q24_matches_macro_cmp(a: u32, b: u32) -> bool {
    matches!(a == b, true)
}

// --- H: the same shapes with a `return` rather than a tail, so the plan sees a different HIR. --

#[inline(never)]
pub fn q25_match_eq_return(a: u32, b: u32) -> u32 {
    return match a == b {
        true => a,
        false => b,
    };
}

#[inline(never)]
pub fn q26_match_param_return(c: bool, a: u32, b: u32) -> u32 {
    return match c {
        true => a,
        false => b,
    };
}
