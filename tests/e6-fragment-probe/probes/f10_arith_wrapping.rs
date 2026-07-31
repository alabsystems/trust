//@ probe-shape: Arithmetic
//@ probe-expect: discharged
//@ probe-note: The compiler authenticates the exact core u64 wrapping_add DefId and
//@ probe-note: stamps a closed, non-source-spellable total-primitive marker. Facet
//@ probe-note: closure and the Arithmetic recognizer both require that marker and exact
//@ probe-note: width/type agreement; unmarked paths, lookalikes, signed/usize/u128
//@ probe-note: carriers, and malformed serialized markers fail closed.
clean { def winc_isl (x : UInt64) : UInt64 := x + 1 }
pub fn winc(x: u64) -> u64
    ensures result == winc_isl(x)
{ x.wrapping_add(1) }
