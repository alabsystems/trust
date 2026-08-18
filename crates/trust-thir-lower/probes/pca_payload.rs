// Trust (LANE PCA, plan-clause audit, 2026-08-17) — the ENUM-PAYLOAD-READ (wave-EP) clause corpus.
//
// The wave-EP plan was written for exactly TWO shipped bodies (`Reducibility::height`,
// `SimpPriority::value`) and its review corpus is `probes/ep_review_corpus_{a,b,c}.rs`. Its clauses
// are a four-block grammar; a clause of a four-block grammar can only be witnessed by bodies that
// are three, four and five blocks, with the payload arm first and second, with joins that do and do
// not compute, and so on. That population is here.
#![allow(dead_code, clippy::match_like_matches_macro, clippy::needless_match)]
#![allow(unused_variables, clippy::manual_map)]

// -------------------------------------------------------------------------------------------------
// The shipped shape and its immediate neighbourhood.
// -------------------------------------------------------------------------------------------------

pub enum P1 {
    Zero,
    Reg(u32),
}

/// The `Reducibility::height` shape verbatim: payload arm SECOND in source, const arm first.
pub fn ep_ok_payload_second(p: &P1) -> u32 {
    match p {
        P1::Zero => 0,
        P1::Reg(k) => *k,
    }
}

/// The `SimpPriority::value` shape: payload arm FIRST in source.
pub fn ep_ok_payload_first(p: &P1) -> u32 {
    match p {
        P1::Reg(k) => *k,
        P1::Zero => 0,
    }
}

/// The same two arms written with `if let`.
pub fn ep_ok_if_let(p: &P1) -> u32 {
    if let P1::Reg(k) = p { *k } else { 0 }
}

/// A by-VALUE receiver rather than `&P1` — a different discriminant read.
pub fn ep_byvalue(p: P1) -> u32 {
    match p {
        P1::Zero => 0,
        P1::Reg(k) => k,
    }
}

// -------------------------------------------------------------------------------------------------
// E2 — exactly four blocks. Three-arm and five-arm matches are the population on the other side.
// -------------------------------------------------------------------------------------------------

pub enum P3 {
    A,
    B,
    C(u32),
}

/// Three arms, one payload: rustc mints TWO chained `falseEdge` blocks.
pub fn ep_e2_three_arms(p: &P3) -> u32 {
    match p {
        P3::A => 0,
        P3::B => 1,
        P3::C(k) => *k,
    }
}

/// Three arms with the payload FIRST.
pub fn ep_e2_three_arms_first(p: &P3) -> u32 {
    match p {
        P3::C(k) => *k,
        P3::A => 0,
        P3::B => 1,
    }
}

pub enum P4 {
    A,
    B,
    C,
    D(u32),
}

/// Four arms, one payload.
pub fn ep_e2_four_arms(p: &P4) -> u32 {
    match p {
        P4::A => 0,
        P4::B => 1,
        P4::C => 2,
        P4::D(k) => *k,
    }
}

/// A two-arm match with a WILDCARD default rather than a named variant.
pub fn ep_e2_wildcard(p: &P3) -> u32 {
    match p {
        P3::C(k) => *k,
        _ => 0,
    }
}

// -------------------------------------------------------------------------------------------------
// E10 / E11 — the arm shapes. One arm is exactly the payload triple + `Br(join,[payload])`; the
// other is exactly `Const ; Br(join,[const])`.
// -------------------------------------------------------------------------------------------------

/// The const arm COMPUTES instead of folding: `1 + 1` is still folded by the producer, so this
/// probes whether the plan's "exactly two nodes" arm shape survives a computed constant.
pub fn ep_e11_const_arm_computes(p: &P1) -> u32 {
    match p {
        P1::Zero => 1 + 1,
        P1::Reg(k) => *k,
    }
}

/// The const arm reads a NAMED constant.
pub const EPK: u32 = 7;
pub fn ep_e11_const_arm_named(p: &P1) -> u32 {
    match p {
        P1::Zero => EPK,
        P1::Reg(k) => *k,
    }
}

/// The payload arm ADDS to the payload: the triple's result is no longer the sole `Br` argument.
pub fn ep_e10_payload_arm_computes(p: &P1) -> u32 {
    match p {
        P1::Zero => 0,
        P1::Reg(k) => *k + 1,
    }
}

/// The payload arm CASTS the payload.
pub fn ep_e10_payload_arm_casts(p: &P1) -> u64 {
    match p {
        P1::Zero => 0,
        P1::Reg(k) => *k as u64,
    }
}

/// The payload is read TWICE in its arm.
pub fn ep_e10_payload_twice(p: &P1) -> u32 {
    match p {
        P1::Zero => 0,
        P1::Reg(k) => *k + *k,
    }
}

/// Both arms carry a payload — no const arm at all.
pub enum P2B {
    L(u32),
    R(u32),
}
pub fn ep_e11_both_payload(p: &P2B) -> u32 {
    match p {
        P2B::L(k) => *k,
        P2B::R(k) => *k,
    }
}

/// The payload is BORROWED out rather than read.
pub fn ep_e10_payload_borrowed(p: &P1) -> &u32 {
    match p {
        P1::Zero => &0,
        P1::Reg(k) => k,
    }
}

// -------------------------------------------------------------------------------------------------
// E13 / E14 / E15 — the join takes exactly one parameter and immediately returns it.
// -------------------------------------------------------------------------------------------------

/// The join COMPUTES: the match value is added to before it is returned.
pub fn ep_e14_join_computes(p: &P1) -> u32 {
    (match p {
        P1::Zero => 0,
        P1::Reg(k) => *k,
    }) + 1
}

/// The join COMPARES: the match value feeds a `==`.
pub fn ep_e14_join_compares(p: &P1) -> bool {
    (match p {
        P1::Zero => 0,
        P1::Reg(k) => *k,
    }) == 7
}

/// The match value is the CONDITION of an outer `if`: the join is a branch head.
pub fn ep_e14_join_is_head(p: &P1, q: u32) -> u32 {
    if (match p {
        P1::Zero => 0,
        P1::Reg(k) => *k,
    }) == 0
    {
        q
    } else {
        0
    }
}

/// The match value is CAST in the join.
pub fn ep_e14_join_casts(p: &P1) -> u64 {
    (match p {
        P1::Zero => 0,
        P1::Reg(k) => *k,
    }) as u64
}

// -------------------------------------------------------------------------------------------------
// E5 / E6 / E7 / E8 — the head: `Load(enum) ; ExtractField 0 ; Switch` with one case and a default.
// -------------------------------------------------------------------------------------------------

/// A match on a `bool` — no enum load at all.
pub fn ep_e5_bool_match(c: bool, a: u32, b: u32) -> u32 {
    match c {
        true => a,
        false => b,
    }
}

/// A match on an INTEGER with two arms — a switch, but the scrutinee is not an enum.
pub fn ep_e5_int_match(n: u32, a: u32) -> u32 {
    match n {
        0 => a,
        _ => 1,
    }
}

/// A payload read from a variant whose payload is at field 1 of a MULTI-field variant.
pub enum P5 {
    N,
    T(u32, u32),
}
pub fn ep_e6_second_field(p: &P5) -> u32 {
    match p {
        P5::N => 0,
        P5::T(_, b) => *b,
    }
}

/// A payload read of the FIRST field of a multi-field variant.
pub fn ep_e6_first_field(p: &P5) -> u32 {
    match p {
        P5::N => 0,
        P5::T(a, _) => *a,
    }
}

/// A STRUCT-variant payload read by field name.
pub enum P6 {
    N,
    S { k: u32 },
}
pub fn ep_e6_struct_variant(p: &P6) -> u32 {
    match p {
        P6::N => 0,
        P6::S { k } => *k,
    }
}

/// A payload of a NON-u32 scalar type.
pub enum P7 {
    N,
    B(bool),
}
pub fn ep_e5_bool_payload(p: &P7) -> bool {
    match p {
        P7::N => false,
        P7::B(b) => *b,
    }
}

pub enum P8 {
    N,
    W(u64),
}
pub fn ep_e5_u64_payload(p: &P8) -> u64 {
    match p {
        P8::N => 0,
        P8::W(w) => *w,
    }
}

pub enum P9 {
    N,
    I(i32),
}
pub fn ep_e5_i32_payload(p: &P9) -> i32 {
    match p {
        P9::N => 0,
        P9::I(i) => *i,
    }
}

/// An explicit-discriminant enum — the switch case value is not the variant index.
#[repr(u8)]
pub enum PD {
    A = 3,
    B = 9,
}
pub fn ep_e7_explicit_disc(p: &PD) -> u32 {
    match p {
        PD::A => 0,
        PD::B => 1,
    }
}

// -------------------------------------------------------------------------------------------------
// E1 — the wave-MF firewall, on this grammar.
// -------------------------------------------------------------------------------------------------

/// The payload arm binds through a `let`: the producer opens a lexical scope.
pub fn ep_e1_let_arm(p: &P1) -> u32 {
    match p {
        P1::Zero => 0,
        P1::Reg(k) => {
            let v = *k;
            v
        }
    }
}

/// The whole match is bound to a `let` before it is returned.
pub fn ep_e1_let_whole(p: &P1) -> u32 {
    let v = match p {
        P1::Zero => 0,
        P1::Reg(k) => *k,
    };
    v
}

// -------------------------------------------------------------------------------------------------
// E9 — the two arm blocks ARE the switch's two edges. A guard puts a third block between them.
// -------------------------------------------------------------------------------------------------

/// A MATCH GUARD on the payload arm.
pub fn ep_e9_guard(p: &P1) -> u32 {
    match p {
        P1::Reg(k) if *k > 3 => *k,
        _ => 0,
    }
}

/// An OR-pattern arm.
pub fn ep_e9_or_pattern(p: &P3) -> u32 {
    match p {
        P3::A | P3::B => 0,
        P3::C(k) => *k,
    }
}
