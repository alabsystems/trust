//@ probe-shape: Projection
//@ probe-expect: discharged
//@ probe-note: A `requires` clause alongside does not disturb the uncited ensures route.
clean { def ident_isl (x : UInt64) : UInt64 := x }
pub fn f(x: u64) -> u64
    requires x > 0
    ensures result == ident_isl(x)
{ x }
