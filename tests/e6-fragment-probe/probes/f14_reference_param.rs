//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: References are outside the scalar fragment entirely.
clean { def ident_isl (x : UInt64) : UInt64 := x }
pub fn deref(x: &u64) -> u64
    ensures result == ident_isl(*x)
{ *x }
