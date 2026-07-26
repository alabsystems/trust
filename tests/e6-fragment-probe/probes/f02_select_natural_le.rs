//@ probe-shape: Select
//@ probe-expect: defeq-rejected
//@ probe-note: The `<=` spelling with an explicit .toNat, still not defeq.
clean { def min_isl (a : UInt64) (b : UInt64) : UInt64 := if a.toNat <= b.toNat then a else b }
pub fn min2(a: u64, b: u64) -> u64
    ensures result == min_isl(a, b)
{ if a <= b { a } else { b } }
