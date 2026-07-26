//@ probe-shape: UseChain
//@ probe-expect: discharged
//@ probe-note: E6 increment 2 — a chain of Rvalue::Use resolves back to a projection.
clean { def ident_isl (x : UInt64) : UInt64 := x }
pub fn pass_let(x: u64) -> u64
    ensures result == ident_isl(x)
{ let y = x; y }
