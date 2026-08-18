// Trust (wave-EP, 2026-08-16) — the ENUM-PAYLOAD-READ storage-marker fidelity probe.
//
// Compile with the trust driver and read both channels:
//
//   trustc --edition 2021 --crate-type=lib --crate-name=epprobe \
//     -Ztrust-ir-lower -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Cdebug-assertions=off -Cpanic=abort -Coverflow-checks=on \
//     -Zdump-mir=all -Zdump-mir-dir=MIR -Ztrust-dump=ir:IR \
//     probes/mf_payload.rs --out-dir OUT
//
// `IR/epprobe.coverage.json`'s `derived_mir.markers_exact` is the oracle's verdict.
//
// WHAT BUILT DOES FOR `match self { E::V(h) => *h, .. }` UNDER A `&self` SCRUTINEE — measured in
// full on `env::types::Reducibility::height` (`clean-kernel`, `-Zdump-mir=all`, this compiler):
//
//   fn height(_1: &Reducibility) -> u32 {
//       let mut _0: u32; let mut _2: isize; let _3: &u32;
//       bb0: { PlaceMention(_1); _2 = discriminant((*_1));
//              switchInt(move _2) -> [1: bb2, otherwise: bb1]; }
//       bb1: { _0 = const 0_u32; goto -> bb6; }
//       bb2: { falseEdge -> [real: bb5, imaginary: bb1]; }
//       bb5: { StorageLive(_3);
//              _3 = &(((*_1) as Regular).0: u32);
//              _0 = copy (*_3);
//              StorageDead(_3);
//              goto -> bb6; }
//       bb6: { return; }
//   }
//
// TWO MARKERS, ONE TEMP, ONE ARM BLOCK — and it is the WHOLE obligation. `PlaceMention` and
// `falseEdge` are not markers; bb0, bb1 and bb6 carry none.
//
// TWO THINGS ARE LOAD-BEARING AND BOTH ARE MEASURED HERE:
//
//   1. The arm binding is a BORROW that the arm then reads THROUGH — `_3 = &(...)` and
//      `_0 = copy (*_3)`, two assignments, with the pair around them. A derived body that reads
//      the payload place directly has ONE assignment there and no `&u32` local to mark, which is
//      the `derived <end>` refusal this probe exists to close.
//   2. The EMPTY `falseEdge` BLOCK on the FIRST candidate's edge. `mir_differential::canon_markers`
//      walks the RAW CFG with no goto threading, so its fine block indices count that block.
//      `height` puts the payload arm FIRST and built's marker lands at fine index 2; `value` puts
//      it SECOND and built's lands at fine index 4. One empty trampoline on the first arm's edge
//      reproduces both, and nothing else does.
#![allow(dead_code)]

// ---------------------------------------------------------------------------------------------
// THE TWO SHIPPED TARGETS. Both are `clean-kernel` bodies, transcribed verbatim.
// ---------------------------------------------------------------------------------------------

/// `env::types::Reducibility` — the payload arm is the FIRST candidate, and the match is a
/// WILDCARD match over four variants (no exhaustive fold, so no `Unreachable` block).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum Reducibility {
    #[default]
    Reducible,
    Regular(u32),
    Irreducible,
    Opaque,
}

impl Reducibility {
    /// `env::types::Reducibility::height` — expected: `markers_exact`, 2 marker lines identical.
    pub fn height(&self) -> u32 {
        match self {
            Reducibility::Regular(h) => *h,
            _ => 0,
        }
    }
}

/// `env::types::SimpPriority` — the payload arm is the SECOND (and last) candidate, and the match
/// IS exhaustive, so the shim's wave-V reshape mints an `Unreachable` otherwise-block as well.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum SimpPriority {
    #[default]
    Default,
    Custom(u32),
}

impl SimpPriority {
    /// `env::types::SimpPriority::value` — expected: `markers_exact`, 2 marker lines identical.
    pub fn value(&self) -> u32 {
        match self {
            SimpPriority::Default => 1000,
            SimpPriority::Custom(p) => *p,
        }
    }
}

// ---------------------------------------------------------------------------------------------
// THE CONTROLS. Every one of these is OUTSIDE the plan, and each names the clause that refuses it.
// A control that starts flipping is a plan that widened without saying so.
// ---------------------------------------------------------------------------------------------

/// BY VALUE — no reference, no `gep`, no borrow: the producer emits `extractfield 1+k` and the
/// by-value payload arm owns it. Built mints no arm-binding borrow, so the plan must not engage.
pub fn height_byval(r: Reducibility) -> u32 {
    match r {
        Reducibility::Regular(h) => h,
        _ => 0,
    }
}

/// THREE CANDIDATES — built chains TWO `falseEdge` blocks and this plan mints one. Refused by the
/// four-block clause.
#[derive(Clone, Copy)]
pub enum Three {
    A(u32),
    B(u32),
    C,
}

impl Three {
    pub fn pick(&self) -> u32 {
        match self {
            Three::A(x) => *x,
            Three::B(y) => *y,
            _ => 0,
        }
    }
}

/// THE PAYLOAD READ CONSUMED TWICE — the arm computes after the read, so built's retirement is not
/// after the edge copy. Refused by the arm-is-exactly-the-triple-and-its-`Br` clause.
#[derive(Clone, Copy)]
pub enum Doubled {
    Only(u32),
    None_,
}

impl Doubled {
    pub fn twice(&self) -> u32 {
        match self {
            Doubled::Only(h) => *h + *h,
            _ => 0,
        }
    }
}

/// A JOIN THAT COMPUTES — the join parameter is not immediately returned. Refused by the join
/// clause.
impl Reducibility {
    pub fn height_plus_one(&self) -> u32 {
        let h = match self {
            Reducibility::Regular(h) => *h,
            _ => 0,
        };
        h + 1
    }
}
