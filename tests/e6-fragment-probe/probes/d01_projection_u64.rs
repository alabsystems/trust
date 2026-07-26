//@ probe-shape: Projection
//@ probe-expect: discharged
//@ probe-note: The baseline. A two-parameter projection against a matching island def.
clean { def fst_isl (x : UInt64) (y : UInt64) : UInt64 := x }
pub fn fst(x: u64, y: u64) -> u64
    ensures result == fst_isl(x, y)
{ x }
