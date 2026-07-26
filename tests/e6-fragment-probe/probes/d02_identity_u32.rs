//@ probe-shape: Projection
//@ probe-expect: discharged
//@ probe-note: Width symmetry — all four unsigned widths (8/16/32/64) behave alike.
clean { def ident32 (x : UInt32) : UInt32 := x }
pub fn id32(x: u32) -> u32
    ensures result == ident32(x)
{ x }
