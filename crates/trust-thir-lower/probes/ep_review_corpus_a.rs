// Trust (wave-EP REVIEW, 2026-08-17) — ADVERSARIAL CORPUS A of three: arities, field indices,
// scalar widths, arm orders, arm counts.
//
// WHY THIS EXISTS. Wave-EP shipped the enum-payload-READ marker plan with its whole measured
// population being TWO clean-kernel bodies. Nothing in this file was written by that wave. 75
// hand-written bodies across the three `ep_review_corpus_*.rs` files sit within one step of
// `plan_payload_markers`' four-block grammar; a body that flips here that the grammar was not
// measured for is a widening nobody priced.
//
// MEASURED, sealed control (`41b5835841`) vs sealed subject (`e7171a5daf`), both opt levels:
// 25 bodies GAINED a codegen flip at -O3, 0 lost at either level, `derived_mir: agreed` 64 -> 64,
// lineage moved on 0. Every deliberate control below refused. The class generalizes correctly —
// it is not overfitted to the two shipped bodies.

#![allow(dead_code)]

// ---------------------------------------------------------------------------------------------
// A1..A6 — PAYLOAD ARITY. The shipped pair is arity 1, field 0. Built binds the OTHER fields the
// same way; the plan's `recognize_ref_payload_read` triple is field-index-blind, so a 2-field
// variant read at field 1 is the first place the emitted `gep` offset can be wrong.
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Copy)]
pub enum A2 {
    V(u32, u32),
    N,
}

impl A2 {
    /// A1 — arity 2, read field 0.
    pub fn f0(&self) -> u32 {
        match self {
            A2::V(a, _) => *a,
            _ => 0,
        }
    }
    /// A2 — arity 2, read field 1. The offset the shipped pair never exercises.
    pub fn f1(&self) -> u32 {
        match self {
            A2::V(_, b) => *b,
            _ => 0,
        }
    }
}

#[derive(Clone, Copy)]
pub enum A3 {
    V(u8, u32, u64),
    N,
}

impl A3 {
    /// A3 — arity 3, read field 0 (a `u8` before two wider fields: alignment padding in the gep).
    pub fn g0(&self) -> u8 {
        match self {
            A3::V(a, _, _) => *a,
            _ => 0,
        }
    }
    /// A4 — arity 3, read field 1.
    pub fn g1(&self) -> u32 {
        match self {
            A3::V(_, b, _) => *b,
            _ => 0,
        }
    }
    /// A5 — arity 3, read field 2 (the widest, last).
    pub fn g2(&self) -> u64 {
        match self {
            A3::V(_, _, c) => *c,
            _ => 0,
        }
    }
}

/// A6 — NAMED fields rather than positional. Same MIR `Field(0)`, different HIR.
#[derive(Clone, Copy)]
pub enum ANamed {
    V { h: u32 },
    N,
}

impl ANamed {
    pub fn h(&self) -> u32 {
        match self {
            ANamed::V { h } => *h,
            _ => 0,
        }
    }
}

// ---------------------------------------------------------------------------------------------
// A7..A12 — ARM ORDER AND ARM COUNT. The plan hardcodes `tramp: arm_a.id` = `func.blocks[1]`.
// Everything here moves the payload arm around that assumption.
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Copy)]
pub enum T3 {
    A(u32),
    B,
    C,
}

impl T3 {
    /// A7 — THREE variants, ONE payload arm, TWO explicit const arms (no wildcard). Built chains
    /// TWO `falseEdge` blocks; the plan mints one. Must not flip.
    pub fn three_explicit(&self) -> u32 {
        match self {
            T3::A(x) => *x,
            T3::B => 1,
            T3::C => 2,
        }
    }
    /// A8 — three variants, payload arm LAST before a wildcard.
    pub fn three_last(&self) -> u32 {
        match self {
            T3::B => 1,
            T3::C => 2,
            T3::A(x) => *x,
        }
    }
}

#[derive(Clone, Copy)]
pub enum TwoPay {
    A(u32),
    B(u32),
}

impl TwoPay {
    /// A9 — BOTH arms read a payload. Two payload triples; the plan admits exactly one.
    pub fn both(&self) -> u32 {
        match self {
            TwoPay::A(x) => *x,
            TwoPay::B(y) => *y,
        }
    }
    /// A10 — both arms payload, but one is discarded for a constant. One triple only.
    pub fn one_of_two(&self) -> u32 {
        match self {
            TwoPay::A(x) => *x,
            TwoPay::B(_) => 7,
        }
    }
}

#[derive(Clone, Copy, Default)]
pub enum Four {
    #[default]
    P,
    Q(u32),
    R,
    S,
}

impl Four {
    /// A11 — the shipped `Reducibility` shape EXACTLY, payload arm FIRST, wildcard tail, four
    /// variants. This is the positive control inside my own corpus: it must flip on the subject
    /// and not on the control, or my harness is not measuring the wave.
    pub fn first(&self) -> u32 {
        match self {
            Four::Q(h) => *h,
            _ => 0,
        }
    }
    /// A12 — the same four variants with the payload arm SECOND (the `SimpPriority` order) but
    /// with a NON-exhaustive tail, so no `Unreachable` fold.
    pub fn second(&self) -> u32 {
        match self {
            Four::P => 1000,
            Four::Q(h) => *h,
            _ => 0,
        }
    }
}

// ---------------------------------------------------------------------------------------------
// A13..A18 — SCALAR WIDTH AND KIND. `scalar_ok` admits bool/int/float/char; the shipped pair is
// `u32` only. Each of these declares a DIFFERENT `&S` temp type, which is the type column the
// marker channel compares as `MfTy::Opaque` — the one thing that class does NOT discriminate.
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Copy)]
pub enum W8 {
    V(u8),
    N,
}
impl W8 {
    pub fn v(&self) -> u8 {
        match self {
            W8::V(x) => *x,
            _ => 0,
        }
    }
}

#[derive(Clone, Copy)]
pub enum W64 {
    V(i64),
    N,
}
impl W64 {
    pub fn v(&self) -> i64 {
        match self {
            W64::V(x) => *x,
            _ => 0,
        }
    }
}

#[derive(Clone, Copy)]
pub enum W128 {
    V(u128),
    N,
}
impl W128 {
    pub fn v(&self) -> u128 {
        match self {
            W128::V(x) => *x,
            _ => 0,
        }
    }
}

#[derive(Clone, Copy)]
pub enum WBool {
    V(bool),
    N,
}
impl WBool {
    pub fn v(&self) -> bool {
        match self {
            WBool::V(x) => *x,
            _ => false,
        }
    }
}

#[derive(Clone, Copy)]
pub enum WChar {
    V(char),
    N,
}
impl WChar {
    pub fn v(&self) -> char {
        match self {
            WChar::V(x) => *x,
            _ => 'z',
        }
    }
}

#[derive(Clone, Copy)]
pub enum WF64 {
    V(f64),
    N,
}
impl WF64 {
    pub fn v(&self) -> f64 {
        match self {
            WF64::V(x) => *x,
            _ => 0.0,
        }
    }
}

#[derive(Clone, Copy)]
pub enum WUsize {
    V(usize),
    N,
}
impl WUsize {
    pub fn v(&self) -> usize {
        match self {
            WUsize::V(x) => *x,
            _ => 0,
        }
    }
}
