// Trust (wave-EP REVIEW, 2026-08-17) — ADVERSARIAL CORPUS C of three: layout and repr, the
// TRAMPOLINE's own assumption, surface forms, and interference with the four PRE-EXISTING plans.
//
// PRE-EXISTING FINDING, NOT WAVE-EP, FILED FOR A SEPARATE LANE. `Ordered::v` below is a
// `derived_mir: mismatch` on the CONTROL and the SUBJECT alike:
//
//   line 3: built   b0: switch(disc(u32,deref(a1)))[900->b1,1->b2,else->b3]
//           derived b0: switch(disc(u32,deref(a1)))[1->b1,900->b2,else->b3]
//
// The wave-YM ascending-discriminant sort MISALIGNS when built keeps ARM order. The comparator
// catches it and nothing flips, but `mismatch` is a gated shrink axis and clean-kernel carries
// none — this is the first body written that produces one. Its mirror `Ordered2::v` (source order
// and discriminant order agreeing) flips clean, which is what isolates the cause.

#![allow(dead_code)]

// ---------------------------------------------------------------------------------------------
// C1..C6 — REPR AND DISCRIMINANT LAYOUT. The plan's head clause demands
// `Load(enum) ; ExtractField 0 ; Switch` with ONE case and a default. An explicit-discriminant or
// `repr` enum changes the tag VALUE the switch tests, which is the `enum-disc-index` seam.
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Copy)]
#[repr(u8)]
pub enum R8 {
    A = 10,
    B(u32) = 20,
    C = 30,
}
impl R8 {
    pub fn v(&self) -> u32 {
        match self {
            R8::B(x) => *x,
            _ => 0,
        }
    }
}

#[derive(Clone, Copy)]
#[repr(C)]
pub enum RC {
    A,
    B(u32),
}
impl RC {
    pub fn v(&self) -> u32 {
        match self {
            RC::B(x) => *x,
            _ => 0,
        }
    }
}

#[derive(Clone, Copy)]
#[repr(i64)]
pub enum RI64 {
    A = -5,
    B(u32) = 7,
}
impl RI64 {
    pub fn v(&self) -> u32 {
        match self {
            RI64::B(x) => *x,
            _ => 0,
        }
    }
}

/// C4 — a TWO-variant enum where the payload variant is index 0 (the shipped pair both have the
/// payload at a nonzero variant index).
#[derive(Clone, Copy)]
pub enum PayFirst {
    V(u32),
    N,
}
impl PayFirst {
    pub fn v(&self) -> u32 {
        match self {
            PayFirst::V(x) => *x,
            PayFirst::N => 0,
        }
    }
}

/// C5 — the same, EXHAUSTIVE (so the shim's wave-V reshape mints an `Unreachable` otherwise-block
/// on top of the trampoline). This is the `SimpPriority` fold with the arms swapped.
#[derive(Clone, Copy)]
pub enum PayFirstExh {
    V(u32),
    N,
}
impl PayFirstExh {
    pub fn v(&self) -> u32 {
        match self {
            PayFirstExh::V(x) => *x,
            PayFirstExh::N => 1000,
        }
    }
}

/// C6 — FIVE variants, wildcard tail, payload arm first. More `falseEdge` blocks in built than
/// the plan's four-block grammar can be describing.
#[derive(Clone, Copy)]
pub enum Five {
    A(u32),
    B,
    C,
    D,
    E,
}
impl Five {
    pub fn v(&self) -> u32 {
        match self {
            Five::A(x) => *x,
            _ => 0,
        }
    }
}

// ---------------------------------------------------------------------------------------------
// C7..C12 — INTERFERENCE WITH THE OTHER FOUR PLANS. `MfPlans::seal` resolves the payload plan
// against `write`, `borrow` and the source-form lane. Each of these body carries a second
// marker-relevant construct alongside the payload read.
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Copy)]
pub enum E {
    V(u32),
    N,
}

pub struct Cell {
    pub k: u32,
}

/// C7 — a FIELD WRITE through a ref param in the same body as a payload read. `plan_field_write_
/// markers` and `plan_payload_markers` must not both hold.
pub fn write_and_read(c: &mut Cell, e: &E) {
    c.k = match e {
        E::V(h) => *h,
        _ => 0,
    };
}

/// C8 — an INTERIOR BORROW (`&c.k`) forwarded to a call, plus a payload read.
pub fn borrow_and_read(c: &Cell, e: &E) -> u32 {
    let a = sink(&c.k);
    let b = match e {
        E::V(h) => *h,
        _ => 0,
    };
    a + b
}

#[inline(never)]
pub fn sink(x: &u32) -> u32 {
    *x
}

/// C9 — TWO payload matches in ONE body. Two triples, seven blocks; the plan's four-block clause
/// must refuse, and if it did not, `mf_payload_dead` would be overwritten.
pub fn two_matches(a: &E, b: &E) -> u32 {
    let x = match a {
        E::V(h) => *h,
        _ => 0,
    };
    let y = match b {
        E::V(h) => *h,
        _ => 0,
    };
    x + y
}

/// C10 — a payload read whose result feeds a CALL argument, so the join is a call dest.
pub fn read_then_call(e: &E) -> u32 {
    plain(match e {
        E::V(h) => *h,
        _ => 0,
    })
}

#[inline(never)]
pub fn plain(x: u32) -> u32 {
    x
}

/// C11 — a payload read inside a CONST FN (the CTFE lane, where `emit_lifetime_markers` is off
/// and `markers_exact` is not a gate — so a body that flips here proves nothing about markers,
/// which is exactly why it is in the corpus).
pub const fn const_read(e: &E) -> u32 {
    match e {
        E::V(h) => *h,
        _ => 0,
    }
}

/// C12 — the payload read is the CONDITION of a later branch.
pub fn read_then_branch(e: &E) -> u32 {
    let h = match e {
        E::V(h) => *h,
        _ => 0,
    };
    if h > 3 { 1 } else { 2 }
}

// ---------------------------------------------------------------------------------------------
// C13..C18 — SURFACE FORMS THAT LOWER TO THE SAME MATCH. The plan reads trust-ir, not HIR, so
// every one of these is a candidate for the four-block grammar by a route the wave did not write.
// ---------------------------------------------------------------------------------------------

impl E {
    /// C13 — `if let` rather than `match`.
    pub fn if_let(&self) -> u32 {
        if let E::V(h) = self { *h } else { 0 }
    }
    /// C14 — `if let` with the arms inverted by a negation.
    pub fn if_let_else(&self) -> u32 {
        if let E::N = self { 0 } else if let E::V(h) = self { *h } else { 0 }
    }
    /// C15 — a `match` with a REDUNDANT guard that is always true (an extra `falseEdge`).
    pub fn guarded(&self) -> u32 {
        match self {
            E::V(h) if *h > 0 => *h,
            _ => 0,
        }
    }
    /// C16 — `ref` in the pattern rather than default binding modes.
    pub fn ref_pat(&self) -> u32 {
        match *self {
            E::V(ref h) => *h,
            _ => 0,
        }
    }
    /// C17 — a BY-VALUE match on a dereffed Copy enum. Built copies the enum out first.
    pub fn deref_match(&self) -> u32 {
        match *self {
            E::V(h) => h,
            _ => 0,
        }
    }
    /// C18 — an `@` binding over the payload.
    pub fn at_bind(&self) -> u32 {
        match self {
            E::V(h @ 0..=9) => *h,
            _ => 0,
        }
    }
}

// ---------------------------------------------------------------------------------------------
// C19..C22 — THE TRAMPOLINE'S OWN ASSUMPTION. `tramp: arm_a.id` is `func.blocks[1]`, asserted to
// be the FIRST source arm. These bodies make block order and source order disagree if anything
// in the producer reorders arms.
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Copy)]
#[repr(u32)]
pub enum Ordered {
    Hi = 900,
    Lo(u32) = 1,
}
impl Ordered {
    /// C19 — the payload arm's DISCRIMINANT sorts BEFORE the const arm's, while its SOURCE
    /// position is after. Any wave-YM discriminant sort that reaches block order shows up here.
    pub fn v(&self) -> u32 {
        match self {
            Ordered::Hi => 900,
            Ordered::Lo(x) => *x,
        }
    }
}

#[derive(Clone, Copy)]
#[repr(u32)]
pub enum Ordered2 {
    Lo(u32) = 1,
    Hi = 900,
}
impl Ordered2 {
    /// C20 — the mirror: source order and discriminant order AGREE.
    pub fn v(&self) -> u32 {
        match self {
            Ordered2::Lo(x) => *x,
            Ordered2::Hi => 900,
        }
    }
}

/// C21 — the payload arm reached through an OR-PATTERN on the const side (two candidates fold to
/// one arm, so built mints two `falseEdge` blocks for a two-BLOCK body).
#[derive(Clone, Copy)]
pub enum Or3 {
    A(u32),
    B,
    C,
}
impl Or3 {
    pub fn v(&self) -> u32 {
        match self {
            Or3::A(x) => *x,
            Or3::B | Or3::C => 0,
        }
    }
}

/// C22 — the const arm is an OR-pattern that comes FIRST.
impl Or3 {
    pub fn w(&self) -> u32 {
        match self {
            Or3::B | Or3::C => 0,
            Or3::A(x) => *x,
        }
    }
}
