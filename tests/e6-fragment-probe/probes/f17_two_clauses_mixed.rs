//@ probe-shape: Projection
//@ probe-expect: unproved
//@ probe-note: ALL-OR-NOTHING: one island-calling clause and one ordinary clause, so
//@ probe-note: the uncited route declines entirely and NEITHER discharges. Charter
//@ probe-note: item 4 audits whether that is the intended contract.
clean { def ident_isl (x : UInt64) : UInt64 := x }
pub fn f(x: u64) -> u64
    ensures result == ident_isl(x)
    ensures result <= x
{ x }
