//@ probe-shape: Select
//@ probe-expect: discharged
//@ probe-note: The natural `<=` spelling. Discharges since 2026-07-26 — the `ite` mint
//@ probe-note: covers Le as well as Lt, so the fix generalized rather than special-casing
//@ probe-note: the one comparison it was aimed at.
clean { def min_isl (a : UInt64) (b : UInt64) : UInt64 := if a.toNat <= b.toNat then a else b }
pub fn min2(a: u64, b: u64) -> u64
    ensures result == min_isl(a, b)
{ if a <= b { a } else { b } }
