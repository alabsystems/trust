//@ probe-shape: Projection
//@ probe-expect: clause-outside-fragment
//@ probe-note: usize is admissible on the body side (PtrSizedInt) but the clause side
//@ probe-note: disagrees — an internal inconsistency, not a deliberate exclusion.
clean { def ident_isl (x : UInt64) : UInt64 := x }
pub fn f(x: usize) -> usize
    ensures result == ident_isl(x)
{ x }
