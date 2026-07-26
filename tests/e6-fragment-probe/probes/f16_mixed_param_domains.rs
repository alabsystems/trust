//@ probe-shape: Projection
//@ probe-expect: clause-outside-fragment
//@ probe-note: One u64 and one bool parameter. Uniformity is required across ALL
//@ probe-note: parameters even when the extra one is irrelevant to the clause.
clean { def ident_isl (x : UInt64) : UInt64 := x }
pub fn f(x: u64, s: bool) -> u64
    ensures result == ident_isl(x)
{ x }
