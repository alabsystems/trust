//@ probe-shape: Projection
//@ probe-expect: discharged
//@ probe-note: ITEM 5 END-TO-END. One island definition named twice in a single
//@ probe-note: clause. The per-callee admission loop reaches it twice; before the
//@ probe-note: idempotence fix the second attempt reported "collides with an existing
//@ probe-note: program-function facet key" and aborted the whole discharge.
clean { def ident_isl (x : UInt64) : UInt64 := x }
pub fn f(x: u64) -> u64
    ensures result == ident_isl(x) && x == ident_isl(x)
{ x }
