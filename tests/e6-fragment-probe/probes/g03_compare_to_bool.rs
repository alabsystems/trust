//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: A comparison RETURNED as the value. Isolated against the Select shape,
//@ probe-note: which selects between parameters on a comparison but returns a PARAMETER,
//@ probe-note: never the comparison's own bool. `ExprMeta::has_loose_bvars` is exactly
//@ probe-note: this shape (`... > 0`). See g08.
clean { def nz_isl (x : UInt64) : Bool := x != 0 }
pub fn nz(x: u64) -> bool
    ensures result == nz_isl(x)
{ x > 0 }
