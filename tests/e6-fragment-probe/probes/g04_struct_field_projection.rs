//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: Field projection out of a newtype, isolated against d01 (parameter
//@ probe-note: projection, discharged). The Projection shape returns a PARAMETER verbatim;
//@ probe-note: reading a field of one is a different operation with no arm. Every
//@ probe-note: clean-kernel method on a newtype begins here.
clean { def ident_isl (x : UInt64) : UInt64 := x }
pub struct W(pub u64);
pub fn unwrap_w(w: W) -> u64
    ensures result == ident_isl(w.0)
{ w.0 }
