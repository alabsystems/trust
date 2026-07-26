//@ probe-shape: Select
//@ probe-expect: defeq-rejected
//@ probe-note: THE HEADLINE GAP. Identical program to d06, island written naturally.
//@ probe-note: Kernel says: "the two sides are not definitionally equal (Eq.refl does
//@ probe-note: not check)". This is what makes the second language unwritable today.
clean { def min2_isl (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b }
pub fn min2(a: u64, b: u64) -> u64
    ensures result == min2_isl(a, b)
{ if a < b { a } else { b } }
