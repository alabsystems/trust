// LANE A0 / WALL A probe 1 — WHICH refusal arm declares the callee.
//
// Wall A is "the reachable closure of `Level::is_zero` is not bodyful". Four
// variants of ONE body shape (`Level` / `LevelArc` / `is_zero`), differing only in
// where the two forwarding callees live and how polymorphic they are; the enum,
// the recursion and the payload edge are identical by construction.
//
//   X  the real clean-kernel shape: `Option::as_deref` + `Option::expect` (core)
//   M  local MONOMORPHIC twins of those two
//   G  local GENERIC twins   (the "just re-declare them locally" workaround)
//   I  a local generic whose SIGNATURE is instantiation-invariant (#197 3c's example)
//   Z  a call-free leaf, the POSITIVE CONTROL for the crate-seam differential
//
// MEASURED 2026-08-20, sealed driver trust ccf52b40c3, -Copt-level=3:
//   Z  z_caller -> z_leaf                  seam `agreed`, 5 samples   <- the seam works
//   X  deref  calls 0 res / 2 EXTERN / 0   -> `extern:` arm  (cross-crate)
//   M  twins SPLICE and LINK (2 resolved) and the closure is STILL refused, because
//      m_as_deref reaches `<Arc<T,A> as Deref>::deref` and m_expect reaches
//      `Arguments::from_str` + `panic_fmt`. Local re-declaration MOVES the wall.
//   G  bodies symbolic + unspliced, AND both call sites decline independently with
//      "callee link declined (signature not instantiation-invariant)"
//      -> calls 0 res / 0 ext / 2 UNRESOLVED  (`havoc:` arm)
//   I  i_caller -> i_invariant LINKS (1 resolved): the A-iii gate discriminates.
//
// See docs/design/2026-08-20-wall-a-reachable-closure.md §2.
#![allow(dead_code)]
use std::sync::Arc;

// ================================================================ X: the real shape
pub struct LevelArcX(Option<Arc<LevelX>>);
impl std::ops::Deref for LevelArcX {
    type Target = LevelX;
    fn deref(&self) -> &LevelX {
        self.0.as_deref().expect("live LevelArc must contain a level")
    }
}
pub enum LevelX {
    Zero,
    Succ(LevelArcX),
    Max(LevelArcX, LevelArcX),
    IMax(LevelArcX, LevelArcX),
    Param(u32),
}
impl LevelX {
    pub fn is_zero_x(&self) -> bool {
        match self {
            LevelX::Zero => true,
            LevelX::Succ(_) | LevelX::Param(_) => false,
            LevelX::Max(l1, l2) => l1.is_zero_x() && l2.is_zero_x(),
            LevelX::IMax(_, l2) => l2.is_zero_x(),
        }
    }
}

// ==================================================== M: local MONOMORPHIC forwarders
pub struct LevelArcM(Option<Arc<LevelM>>);
pub fn m_as_deref(o: &Option<Arc<LevelM>>) -> Option<&LevelM> {
    match o {
        Some(a) => Some(&**a),
        None => None,
    }
}
pub fn m_expect(o: Option<&LevelM>) -> &LevelM {
    match o {
        Some(v) => v,
        None => panic!("live LevelArc must contain a level"),
    }
}
impl std::ops::Deref for LevelArcM {
    type Target = LevelM;
    fn deref(&self) -> &LevelM {
        m_expect(m_as_deref(&self.0))
    }
}
pub enum LevelM {
    Zero,
    Succ(LevelArcM),
    Max(LevelArcM, LevelArcM),
    IMax(LevelArcM, LevelArcM),
    Param(u32),
}
impl LevelM {
    pub fn is_zero_m(&self) -> bool {
        match self {
            LevelM::Zero => true,
            LevelM::Succ(_) | LevelM::Param(_) => false,
            LevelM::Max(l1, l2) => l1.is_zero_m() && l2.is_zero_m(),
            LevelM::IMax(_, l2) => l2.is_zero_m(),
        }
    }
}

// ======================================================= G: local GENERIC forwarders
pub struct LevelArcG(Option<Arc<LevelG>>);
pub fn g_as_deref<T: std::ops::Deref>(o: &Option<T>) -> Option<&T::Target> {
    match o {
        Some(a) => Some(&**a),
        None => None,
    }
}
pub fn g_expect<T>(o: Option<T>) -> T {
    match o {
        Some(v) => v,
        None => panic!("live LevelArc must contain a level"),
    }
}
impl std::ops::Deref for LevelArcG {
    type Target = LevelG;
    fn deref(&self) -> &LevelG {
        g_expect(g_as_deref(&self.0))
    }
}
pub enum LevelG {
    Zero,
    Succ(LevelArcG),
    Max(LevelArcG, LevelArcG),
    IMax(LevelArcG, LevelArcG),
    Param(u32),
}
impl LevelG {
    pub fn is_zero_g(&self) -> bool {
        match self {
            LevelG::Zero => true,
            LevelG::Succ(_) | LevelG::Param(_) => false,
            LevelG::Max(l1, l2) => l1.is_zero_g() && l2.is_zero_g(),
            LevelG::IMax(_, l2) => l2.is_zero_g(),
        }
    }
}

// ============ I: local generic, signature INSTANTIATION-INVARIANT (#197 3c's example)
// Splits "the BODY did not splice" from "the CALL SITE declined to link".
pub fn i_invariant<T>(x: u32) -> u32 {
    x
}
pub fn i_caller(x: u32) -> u32 {
    i_invariant::<u8>(x)
}

// ============ Z: a call-free control, so the seam's step-0/step-2 split is visible
pub fn z_leaf(x: u32) -> u32 {
    x
}
pub fn z_caller(x: u32) -> u32 {
    z_leaf(x)
}
