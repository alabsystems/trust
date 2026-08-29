// LANE A0 / WALL A probe 2 — can the closure be CLOSED by respelling the source?
//
// Probe 1 measured the blockers for the real shape as
//     std::option::Option::<T>::as_deref / ::expect            (core)
// and, once those are re-declared locally and monomorphically, the NEXT layer:
//     <std::sync::Arc<T, A> as std::ops::Deref>::deref         (alloc)
//     std::fmt::Arguments::<'a>::from_str + std::rt::panic_fmt (the panic arm)
//
// So this probe asks the only remaining source-level question: is there a spelling
// of `LevelArc::deref` whose emitted body CALLS NOTHING? Four candidates, each one
// axis from the shipped shape.
//
// MEASURED 2026-08-20, same driver: ALL FOUR FAIL TO LOWER, and become
// `local-unlowered:` declarations — i.e. the rewrite CREATES a wall-A member.
//   D  Arc + total match + static fallback : Borrow(inner unlowered),
//                                            EnumMatch(default arm no value),
//                                            StaticRef(initializer not scalar)
//   B  Box + total match + static fallback : + Borrow(non-local place),
//                                            EnumMatch(case arm no value)
//   C  Box, non-optional, `&*self.0`       : Borrow(non-local place)   (one tag)
//   E  Box inline in the enum, no Deref    : Borrow(non-local place) x2,
//                                            Call(unsupported arg) x2, ...
//
// `Borrow(non-local place)` is the head of the B4 family, the open keystone item.
// The shipped `self.0.as_deref().expect(..)` is the ONLY one of the five spellings
// that lowers clean. See docs/design/2026-08-20-wall-a-reachable-closure.md §3.2.
#![allow(dead_code)]
use std::sync::Arc;

// ---- D: Arc payload, TOTAL match (no `expect`), static fallback (no panic arm).
pub enum LevelD {
    Zero,
    Succ(ArcD),
    Max(ArcD, ArcD),
    IMax(ArcD, ArcD),
    Param(u32),
}
pub struct ArcD(Option<Arc<LevelD>>);
static ZERO_D: LevelD = LevelD::Zero;
impl std::ops::Deref for ArcD {
    type Target = LevelD;
    fn deref(&self) -> &LevelD {
        match &self.0 {
            Some(a) => &**a,
            None => &ZERO_D,
        }
    }
}
impl LevelD {
    pub fn is_zero_d(&self) -> bool {
        match self {
            LevelD::Zero => true,
            LevelD::Succ(_) | LevelD::Param(_) => false,
            LevelD::Max(a, b) => a.is_zero_d() && b.is_zero_d(),
            LevelD::IMax(_, b) => b.is_zero_d(),
        }
    }
}

// ---- B: BOX payload, TOTAL match, static fallback. `Box` is the ONE type whose deref
// is a MIR builtin projection rather than a call.
pub enum LevelB {
    Zero,
    Succ(BoxB),
    Max(BoxB, BoxB),
    IMax(BoxB, BoxB),
    Param(u32),
}
pub struct BoxB(Option<Box<LevelB>>);
static ZERO_B: LevelB = LevelB::Zero;
impl std::ops::Deref for BoxB {
    type Target = LevelB;
    fn deref(&self) -> &LevelB {
        match &self.0 {
            Some(b) => &**b,
            None => &ZERO_B,
        }
    }
}
impl LevelB {
    pub fn is_zero_b(&self) -> bool {
        match self {
            LevelB::Zero => true,
            LevelB::Succ(_) | LevelB::Param(_) => false,
            LevelB::Max(a, b) => a.is_zero_b() && b.is_zero_b(),
            LevelB::IMax(_, b) => b.is_zero_b(),
        }
    }
}

// ---- C: BOX payload, NOT optional — the smallest possible edge.
pub enum LevelC {
    Zero,
    Succ(BoxC),
    Max(BoxC, BoxC),
    IMax(BoxC, BoxC),
    Param(u32),
}
pub struct BoxC(Box<LevelC>);
impl std::ops::Deref for BoxC {
    type Target = LevelC;
    fn deref(&self) -> &LevelC {
        &*self.0
    }
}
impl LevelC {
    pub fn is_zero_c(&self) -> bool {
        match self {
            LevelC::Zero => true,
            LevelC::Succ(_) | LevelC::Param(_) => false,
            LevelC::Max(a, b) => a.is_zero_c() && b.is_zero_c(),
            LevelC::IMax(_, b) => b.is_zero_c(),
        }
    }
}

// ---- E: Box payload, and NO Deref impl at all — the recursion spells the projection
// itself, so there is not even a `deref` frame in the closure.
pub enum LevelE {
    Zero,
    Succ(Box<LevelE>),
    Max(Box<LevelE>, Box<LevelE>),
    IMax(Box<LevelE>, Box<LevelE>),
    Param(u32),
}
impl LevelE {
    pub fn is_zero_e(&self) -> bool {
        match self {
            LevelE::Zero => true,
            LevelE::Succ(_) | LevelE::Param(_) => false,
            LevelE::Max(a, b) => a.is_zero_e() && b.is_zero_e(),
            LevelE::IMax(_, b) => b.is_zero_e(),
        }
    }
}
