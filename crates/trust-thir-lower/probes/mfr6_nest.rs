// LANE MF-R6 (sixth review) — NESTED CONTROL, GUARDS THAT BIND TEMPS, AND TAIL-POSITION MATCHES.
//
// Round 5's `SourceFormGate` clause looks at EVERY `Match` node in the body and asks whether its
// SCRUTINEE is marker-free. That is a per-node question asked by a whole-body walk, so this file
// pushes on the seam: a `match` nested inside an arm of another `match`, a `match` nested inside an
// `if`, an `if` nested inside a `match` arm, a guard (which built lowers as its own scope with its
// own temps and its own `StorageDead` placement, and which the trust-ir renders as one more
// `CondBr`), and the tail-vs-statement position of each.
//
// A guard is the interesting case for the LAW rather than for the gate: `a == b` in a guard is a
// second comparison whose operand temps built retires on the guard's own edges, and the trust-ir
// `CondBr` it produces is indistinguishable from an `if`'s. If `plan_branch_markers` admits the
// body and `predict` counts the guard's operands with `mult = 2`, but built retires them once,
// the counts still agree and the SEQUENCE does not.
//
// No body name in this file appears in any of the 27 probe files rounds 1-5 wrote.

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::let_and_return, clippy::needless_return, clippy::bool_comparison)]
#![allow(clippy::if_same_then_else, clippy::needless_bool, clippy::match_like_matches_macro)]
#![allow(clippy::comparison_chain, clippy::needless_match, clippy::collapsible_else_if)]

#[derive(Clone, Copy)]
pub struct Trio {
    pub x: u32,
    pub y: u32,
    pub z: u32,
}

// --- A: MATCH INSIDE MATCH. The outer scrutinee is marker-free, the inner is not. --------------

#[inline(never)]
pub fn n01_match_in_arm_cmp_inner(c: bool, a: u32, b: u32) -> u32 {
    match c {
        true => match a == b {
            true => a,
            false => b,
        },
        false => b,
    }
}

#[inline(never)]
pub fn n02_match_in_arm_bare_inner(c: bool, d: bool, a: u32, b: u32) -> u32 {
    match c {
        true => match d {
            true => a,
            false => b,
        },
        false => b,
    }
}

// Both scrutinees mint: the outer's temps and the inner's temps are live at once.
#[inline(never)]
pub fn n03_match_in_arm_both_cmp(a: u32, b: u32, c: u32) -> u32 {
    match a == b {
        true => match b == c {
            true => a,
            false => b,
        },
        false => c,
    }
}

// --- B: MATCH INSIDE IF and IF INSIDE MATCH — the gate walks both, the plan sees one CFG. ------

#[inline(never)]
pub fn n04_match_inside_if(c: bool, a: u32, b: u32) -> u32 {
    if c {
        match a == b {
            true => a,
            false => b,
        }
    } else {
        b
    }
}

#[inline(never)]
pub fn n05_if_inside_match_arm(c: bool, a: u32, b: u32) -> u32 {
    match c {
        true => {
            if a == b {
                a
            } else {
                b
            }
        }
        false => b,
    }
}

#[inline(never)]
pub fn n06_if_inside_if(a: u32, b: u32, c: u32) -> u32 {
    if a == b { if b == c { a } else { b } } else { c }
}

// --- C: GUARDS. A guard is a second `CondBr` whose operands built scopes differently. ----------

#[inline(never)]
pub fn n07_guard_cmp_params(k: u32, a: u32, b: u32) -> u32 {
    match k {
        _ if a == b => a,
        _ => b,
    }
}

#[inline(never)]
pub fn n08_guard_bare_bool(k: u32, c: bool, a: u32, b: u32) -> u32 {
    match k {
        _ if c => a,
        _ => b,
    }
}

#[inline(never)]
pub fn n09_guard_binds_temp(k: u32, b: u32) -> u32 {
    match k {
        n if n == b => n,
        n => n & b,
    }
}

#[inline(never)]
pub fn n10_guard_on_literal_arm(k: u32, a: u32, b: u32) -> u32 {
    match k {
        0 if a == b => a,
        0 => b,
        _ => k,
    }
}

#[inline(never)]
pub fn n11_guard_and_of_cmps(k: u32, a: u32, b: u32, c: u32) -> u32 {
    match k {
        _ if (a == b) & (b == c) => a,
        _ => c,
    }
}

// --- D: TAIL POSITION vs STATEMENT POSITION of the same match. --------------------------------

#[inline(never)]
pub fn n12_match_tail_after_nothing(a: u32, b: u32) -> u32 {
    match a == b {
        true => a,
        false => b,
    }
}

#[inline(never)]
pub fn n13_match_tail_in_block(a: u32, b: u32) -> u32 {
    {
        match a == b {
            true => a,
            false => b,
        }
    }
}

#[inline(never)]
pub fn n14_match_tail_unsafe_block(a: u32, b: u32) -> u32 {
    unsafe {
        match a == b {
            true => a,
            false => b,
        }
    }
}

// --- E: THREE-WAY and DEEPER CFGs — more joins than either plan has been measured against. -----

#[inline(never)]
pub fn n15_three_way_match(k: u32, a: u32, b: u32, c: u32) -> u32 {
    match k {
        0 => a,
        1 => b,
        2 => c,
        _ => 0,
    }
}

#[inline(never)]
pub fn n16_chain_if_else_if(a: u32, b: u32, c: u32) -> u32 {
    if a == b {
        a
    } else if b == c {
        b
    } else {
        c
    }
}

#[inline(never)]
pub fn n17_match_three_arms_minting(k: u32, a: u32, b: u32) -> u32 {
    match k {
        0 => a & b,
        1 => a | b,
        _ => a ^ b,
    }
}

#[inline(never)]
pub fn n18_deep_nest_three(t: Trio) -> u32 {
    if t.x == t.y { if t.y == t.z { t.x } else { t.y } } else { t.z }
}

// --- F: SHORT-CIRCUIT `&&`/`||`, which lower to nested `CondBr` chains, not to a `BinOp`. ------

#[inline(never)]
pub fn n19_and_and_params(a: u32, b: u32, c: u32) -> u32 {
    if (a == b) && (b == c) { a } else { c }
}

#[inline(never)]
pub fn n20_or_or_params(a: u32, b: u32, c: u32) -> u32 {
    if (a == b) || (b == c) { a } else { c }
}

#[inline(never)]
pub fn n21_match_on_and_and(a: u32, b: u32, c: u32) -> u32 {
    match (a == b) && (b == c) {
        true => a,
        false => c,
    }
}
