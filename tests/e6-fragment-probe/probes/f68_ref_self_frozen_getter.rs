//@ probe-shape: Projection
//@ probe-expect: discharged
//@ probe-note: POSITIVE, ref-self I1. MEASURED on a stage-1 compiler carrying the
//@ probe-note: increment, together with its by-value twin `f69`.
//@ probe-note: The flagship of the borrow-erased E6 PARAMETER VIEW. `Point` is a
//@ probe-note: `Freeze` all-scalar struct, `&self` is a shared borrow bound by a plain
//@ probe-note: name, the body's only use of it is `Copy((*_1).0)`, and the return is a
//@ probe-note: by-value scalar. The view presents `_0 = Copy(_1)` over two by-value
//@ probe-note: `u32` parameters named `self.x` and `self.y`, which the UNCHANGED
//@ probe-note: recognizer reads as `Projection { param: 0 }` and the UNCHANGED mint
//@ probe-note: turns into `fun p0 p1 => p0`.
//@ probe-note: WHAT THIS ROW DOES NOT SAY: it is not `Certified`. The goal is about the
//@ probe-note: pointee's field VALUES at entry, which rests on owner ruling R1's
//@ probe-note: aliasing assumption; the row reports `Trusted`/`Constructive`, carries the
//@ probe-note: marker `frozen-shared-erased` on its spec-clean goal row, is ABSENT from
//@ probe-note: `of which N kernel-certified`, takes the distinct wire solver label
//@ probe-note: `clean-kernel-view-defeq` and ships NO kernel proof evidence, which is what
//@ probe-note: makes the authenticated `targo trust` lane withhold it. See
//@ probe-note: `docs/TCB.md` and `docs/design-notes/2026-09-18-e6-parameter-view-ruling.md`.
clean { def id32 (x : UInt32) : UInt32 := x }
pub struct Point { pub x: u32, pub y: u32 }
impl Point {
    pub fn x_ref(&self) -> u32
        ensures result == id32(self.x)
    { self.x }
}
