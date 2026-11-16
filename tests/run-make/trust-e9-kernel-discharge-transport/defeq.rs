// The probe's variant E (`reports/2026-09-11-island-probe-level-is-zero.md` §6):
// an UNCITED `ensures` that names a Clean island definition, discharged by the
// kernel through definitional equality (E9 defeq lane).
#![allow(dead_code)]
clean {
    def min_isl (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
}

pub fn min2(a: u64, b: u64) -> u64
    ensures result == min_isl(a, b)
{
    if a < b { a } else { b }
}
