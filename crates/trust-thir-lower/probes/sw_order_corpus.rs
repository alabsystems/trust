// Trust (LANE 1, switch-order) — the SWITCH CASE ORDER corpus.
//
// WHAT THIS MEASURES. `to_mir.rs`'s enum-reshape block emits the derived `SwitchInt` cases in
// some canonical order and the comparator walks successors in STORED order, so the case order is
// load-bearing twice: once for the case-value list and once for the canonical block numbering.
// Built (rustc `TestKind::Switch`, rustc_mir_build/src/builder/matches/test.rs:83) iterates
// `adt_def.discriminants(tcx)` — i.e. VARIANT INDEX order — and `SwitchTargets::new` preserves
// that iteration order verbatim. So built's order is variant-index order, which coincides with
// ascending-discriminant order ONLY when the discriminants ascend with the variant index.
//
// Every shape below names, in its doc comment, the three orders that can disagree:
//   ARM   — the producer's emission order (source arm order)
//   VIDX  — built's order (variant index order)
//   ASC   — the wave-YM ascending-discriminant sort's order
//
// A shape with VIDX != ASC is a `derived_mir: mismatch` under the wave-YM sort.
//
// AXES COVERED: ascending / descending / interleaved discriminants; explicit and implicit;
// repr(u8|u32|i64|C) and default repr; wildcard and exhaustive tails; 2..6 arms; arm order
// matching and not matching discriminant order; the payload / no-payload cross; by-ref (`&self`)
// and by-value scrutinees.

#![crate_type = "lib"]
#![allow(dead_code)]

// =============================================================================================
// GROUP A — 2 arms, PAYLOAD, EXHAUSTIVE, repr(u32). The arm-order x variant-order cross.
// =============================================================================================

#[repr(u32)]
pub enum A1 {
    Hi = 900,
    Lo(u32) = 1,
}
impl A1 {
    /// S01 — ARM [900,1] VIDX [900,1] ASC [1,900].  (this is `ep_review_corpus_c::Ordered::v`)
    pub fn v(&self) -> u32 {
        match self {
            A1::Hi => 900,
            A1::Lo(x) => *x,
        }
    }
}

#[repr(u32)]
pub enum A2 {
    Lo(u32) = 1,
    Hi = 900,
}
impl A2 {
    /// S02 — ARM [1,900] VIDX [1,900] ASC [1,900].  (this is `ep_review_corpus_c::Ordered2::v`)
    pub fn v(&self) -> u32 {
        match self {
            A2::Lo(x) => *x,
            A2::Hi => 900,
        }
    }
}

#[repr(u32)]
pub enum A3 {
    Hi = 900,
    Lo(u32) = 1,
}
impl A3 {
    /// S03 — ARM [1,900] VIDX [900,1] ASC [1,900].  arm order != variant order.
    pub fn v(&self) -> u32 {
        match self {
            A3::Lo(x) => *x,
            A3::Hi => 900,
        }
    }
}

#[repr(u32)]
pub enum A4 {
    Lo(u32) = 1,
    Hi = 900,
}
impl A4 {
    /// S04 — ARM [900,1] VIDX [1,900] ASC [1,900].  the wave-YM motivating shape (Option-like).
    pub fn v(&self) -> u32 {
        match self {
            A4::Hi => 900,
            A4::Lo(x) => *x,
        }
    }
}

// =============================================================================================
// GROUP B — 2 arms, NO PAYLOAD (discriminant-only), EXHAUSTIVE, repr(u8). Same cross.
// =============================================================================================

#[repr(u8)]
pub enum B1 {
    Hi = 200,
    Lo = 3,
}
impl B1 {
    /// S05 — ARM [200,3] VIDX [200,3] ASC [3,200].
    pub fn v(&self) -> u32 {
        match self {
            B1::Hi => 1,
            B1::Lo => 2,
        }
    }
}

#[repr(u8)]
pub enum B2 {
    Lo = 3,
    Hi = 200,
}
impl B2 {
    /// S06 — ARM [3,200] VIDX [3,200] ASC [3,200].
    pub fn v(&self) -> u32 {
        match self {
            B2::Lo => 2,
            B2::Hi => 1,
        }
    }
}

#[repr(u8)]
pub enum B3 {
    Hi = 200,
    Lo = 3,
}
impl B3 {
    /// S07 — ARM [3,200] VIDX [200,3] ASC [3,200].
    pub fn v(&self) -> u32 {
        match self {
            B3::Lo => 2,
            B3::Hi => 1,
        }
    }
}

#[repr(u8)]
pub enum B4 {
    Lo = 3,
    Hi = 200,
}
impl B4 {
    /// S08 — ARM [200,3] VIDX [3,200] ASC [3,200].
    pub fn v(&self) -> u32 {
        match self {
            B4::Hi => 1,
            B4::Lo => 2,
        }
    }
}

// =============================================================================================
// GROUP C — DESCENDING discriminants, 4 variants, 2 explicit arms + WILDCARD tail, payload.
// =============================================================================================

#[repr(u32)]
pub enum C1 {
    A = 30,
    B(u32) = 20,
    C = 10,
    D = 5,
}
impl C1 {
    /// S09 — ARM [30,20] VIDX [30,20] ASC [20,30].  wildcard tail.
    pub fn v(&self) -> u32 {
        match self {
            C1::A => 1,
            C1::B(x) => *x,
            _ => 0,
        }
    }
    /// S10 — ARM [20,30] VIDX [30,20] ASC [20,30].  wildcard tail, arms swapped.
    pub fn w(&self) -> u32 {
        match self {
            C1::B(x) => *x,
            C1::A => 1,
            _ => 0,
        }
    }
}

// =============================================================================================
// GROUP D — INTERLEAVED discriminants incl. NEGATIVE, 4 arms EXHAUSTIVE, repr(i64), no payload.
// (`ASC` here sorts by RAW two's-complement bits, so -3 sorts LAST.)
// =============================================================================================

#[repr(i64)]
pub enum D1 {
    P = 7,
    Q = -3,
    R = 100,
    S = 0,
}
impl D1 {
    /// S11 — ARM [7,-3,100,0] VIDX [7,-3,100,0] ASC [0,7,100,-3].
    pub fn v(&self) -> u32 {
        match self {
            D1::P => 1,
            D1::Q => 2,
            D1::R => 3,
            D1::S => 4,
        }
    }
    /// S12 — ARM [0,7,100,-3] VIDX [7,-3,100,0] ASC [0,7,100,-3].
    pub fn w(&self) -> u32 {
        match self {
            D1::S => 4,
            D1::P => 1,
            D1::R => 3,
            D1::Q => 2,
        }
    }
}

// =============================================================================================
// GROUP E — repr(C).
// =============================================================================================

#[repr(C)]
pub enum E1 {
    A,
    B(u32),
    C,
}
impl E1 {
    /// S13 — ARM [0,1,2] VIDX [0,1,2] ASC [0,1,2].  implicit discriminants, exhaustive.
    pub fn v(&self) -> u32 {
        match self {
            E1::A => 1,
            E1::B(x) => *x,
            E1::C => 3,
        }
    }
    /// S14 — ARM [2,1,0] VIDX [0,1,2] ASC [0,1,2].  reversed arms.
    pub fn w(&self) -> u32 {
        match self {
            E1::C => 3,
            E1::B(x) => *x,
            E1::A => 1,
        }
    }
}

#[repr(C)]
pub enum E2 {
    A = 5,
    B = 2,
    C = 9,
}
impl E2 {
    /// S15 — ARM [5,2,9] VIDX [5,2,9] ASC [2,5,9].  repr(C) explicit, interleaved.
    pub fn v(&self) -> u32 {
        match self {
            E2::A => 1,
            E2::B => 2,
            E2::C => 3,
        }
    }
    /// S16 — ARM [9,5,2] VIDX [5,2,9] ASC [2,5,9].
    pub fn w(&self) -> u32 {
        match self {
            E2::C => 3,
            E2::A => 1,
            E2::B => 2,
        }
    }
}

// =============================================================================================
// GROUP F — IMPLICIT discriminants that RESUME COUNTING after an explicit one.
// =============================================================================================

#[repr(u32)]
pub enum F1 {
    A = 10,
    B(u32),
    C,
}
impl F1 {
    /// S17 — ARM [10,11,12] VIDX [10,11,12] ASC [10,11,12].  ascending; the sort is a no-op.
    pub fn v(&self) -> u32 {
        match self {
            F1::A => 1,
            F1::B(x) => *x,
            F1::C => 3,
        }
    }
}

#[repr(u32)]
pub enum F2 {
    A = 10,
    B(u32),
    C = 1,
    D,
}
impl F2 {
    /// S18 — ARM [10,11,1,2] VIDX [10,11,1,2] ASC [1,2,10,11].  exhaustive, mixed implicit.
    pub fn v(&self) -> u32 {
        match self {
            F2::A => 1,
            F2::B(x) => *x,
            F2::C => 3,
            F2::D => 4,
        }
    }
    /// S19 — ARM [1,2,10,11] VIDX [10,11,1,2] ASC [1,2,10,11].
    pub fn w(&self) -> u32 {
        match self {
            F2::C => 3,
            F2::D => 4,
            F2::A => 1,
            F2::B(x) => *x,
        }
    }
}

// =============================================================================================
// GROUP G — 5 and 6 arms.
// =============================================================================================

#[repr(u8)]
pub enum G1 {
    V0 = 50,
    V1 = 40,
    V2 = 30,
    V3 = 20,
    V4 = 10,
}
impl G1 {
    /// S20 — ARM [50,40,30,20,10] VIDX [50,40,30,20,10] ASC [10,20,30,40,50].  5 arms, no payload.
    pub fn v(&self) -> u32 {
        match self {
            G1::V0 => 0,
            G1::V1 => 1,
            G1::V2 => 2,
            G1::V3 => 3,
            G1::V4 => 4,
        }
    }
    /// S21 — ARM [10,20,30,40,50] VIDX [50,40,30,20,10] ASC [10,20,30,40,50].
    pub fn w(&self) -> u32 {
        match self {
            G1::V4 => 4,
            G1::V3 => 3,
            G1::V2 => 2,
            G1::V1 => 1,
            G1::V0 => 0,
        }
    }
}

#[repr(u32)]
pub enum G2 {
    A = 6,
    B(u32) = 1,
    C = 5,
    D = 2,
    E = 4,
    F = 3,
}
impl G2 {
    /// S22 — ARM [6,1,5,2,4,3] VIDX [6,1,5,2,4,3] ASC [1,2,3,4,5,6].  6 arms, interleaved, payload.
    pub fn v(&self) -> u32 {
        match self {
            G2::A => 10,
            G2::B(x) => *x,
            G2::C => 30,
            G2::D => 40,
            G2::E => 50,
            G2::F => 60,
        }
    }
    /// S23 — ARM [1,2,3,4,5,6] VIDX [6,1,5,2,4,3] ASC [1,2,3,4,5,6].
    pub fn w(&self) -> u32 {
        match self {
            G2::B(x) => *x,
            G2::D => 40,
            G2::F => 60,
            G2::E => 50,
            G2::C => 30,
            G2::A => 10,
        }
    }
}

// =============================================================================================
// GROUP H — BY-VALUE scrutinees (the wave-YM flip class itself) + the wave-YM/wave-V controls
// that must not regress.
// =============================================================================================

#[repr(u32)]
pub enum H1 {
    Hi = 900,
    Lo(u32) = 1,
}
/// S24 — by-value. ARM [900,1] VIDX [900,1] ASC [1,900].
pub fn h1(e: H1) -> u32 {
    match e {
        H1::Hi => 900,
        H1::Lo(x) => x,
    }
}

#[repr(u32)]
pub enum H2 {
    Lo(u32) = 1,
    Hi = 900,
}
/// S25 — by-value. ARM [1,900] VIDX [1,900] ASC [1,900].
pub fn h2(e: H2) -> u32 {
    match e {
        H2::Lo(x) => x,
        H2::Hi => 900,
    }
}

/// S26 — wave-YM CONTROL `opt_match`. ARM [1,0] VIDX [0,1] ASC [0,1].  MUST keep flipping.
pub fn opt_match(o: Option<i32>) -> i32 {
    match o {
        Some(x) => x,
        None => 0,
    }
}

/// S27 — wave-YM CONTROL `res_match`. ARM [0,1] VIDX [0,1] ASC [0,1].  MUST keep flipping.
pub fn res_match(r: Result<i32, i32>) -> i32 {
    match r {
        Ok(v) => v,
        Err(e) => e,
    }
}

pub enum Dir {
    N,
    S,
    E,
    W,
}
/// S28 — wave-V CONTROL `dir_match`. ARM [0,1,2,3] VIDX [0,1,2,3] ASC [0,1,2,3].
pub fn dir_match(d: Dir) -> i32 {
    match d {
        Dir::N => 0,
        Dir::S => 1,
        Dir::E => 2,
        Dir::W => 3,
    }
}

pub enum GE {
    A(i32),
    B(bool),
}
/// S29 — slices-1-2 CONTROL `e_read`. ARM [0,1] VIDX [0,1] ASC [0,1].
pub fn e_read(e: GE) -> i32 {
    match e {
        GE::A(x) => x,
        GE::B(b) => b as i32,
    }
}

// =============================================================================================
// GROUP I — the WILDCARD / EXHAUSTIVE cross on one descending-discriminant enum.
// =============================================================================================

#[repr(u32)]
pub enum I1 {
    A = 200,
    B(u32) = 100,
    C = 50,
}
impl I1 {
    /// S30 — ARM [200,100] VIDX [200,100] ASC [100,200].  WILDCARD tail (C folded into `_`).
    pub fn v(&self) -> u32 {
        match self {
            I1::A => 1,
            I1::B(x) => *x,
            _ => 0,
        }
    }
    /// S31 — ARM [200,100,50] VIDX [200,100,50] ASC [50,100,200].  EXHAUSTIVE.
    pub fn w(&self) -> u32 {
        match self {
            I1::A => 1,
            I1::B(x) => *x,
            I1::C => 3,
        }
    }
    /// S32 — ARM [50,100,200] VIDX [200,100,50] ASC [50,100,200].  EXHAUSTIVE, reversed arms.
    pub fn x(&self) -> u32 {
        match self {
            I1::C => 3,
            I1::B(y) => *y,
            I1::A => 1,
        }
    }
}

// =============================================================================================
// GROUP J — repr(u8) boundary values 0 and 255.
// =============================================================================================

#[repr(u8)]
pub enum J1 {
    Max = 255,
    Zero = 0,
    Mid(u32) = 128,
}
impl J1 {
    /// S33 — ARM [255,0,128] VIDX [255,0,128] ASC [0,128,255].  EXHAUSTIVE, payload.
    pub fn v(&self) -> u32 {
        match self {
            J1::Max => 1,
            J1::Zero => 2,
            J1::Mid(x) => *x,
        }
    }
    /// S34 — ARM [0,128,255] VIDX [255,0,128] ASC [0,128,255].
    pub fn w(&self) -> u32 {
        match self {
            J1::Zero => 2,
            J1::Mid(x) => *x,
            J1::Max => 1,
        }
    }
}

// =============================================================================================
// GROUP K — the PAYLOAD / NO-PAYLOAD cross on one descending 3-variant enum, wildcard tail.
// =============================================================================================

#[repr(u32)]
pub enum K1 {
    A = 9,
    B = 6,
    C = 3,
}
impl K1 {
    /// S35 — ARM [9,6] VIDX [9,6] ASC [6,9].  NO payload, wildcard tail.
    pub fn v(&self) -> u32 {
        match self {
            K1::A => 1,
            K1::B => 2,
            _ => 0,
        }
    }
}

#[repr(u32)]
pub enum K2 {
    A(u32) = 9,
    B = 6,
    C = 3,
}
impl K2 {
    /// S36 — ARM [9,6] VIDX [9,6] ASC [6,9].  PAYLOAD, wildcard tail (the K1 twin).
    pub fn v(&self) -> u32 {
        match self {
            K2::A(x) => *x,
            K2::B => 2,
            _ => 0,
        }
    }
}
