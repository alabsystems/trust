//@ probe-shape: Composed
//@ probe-expect: discharged
//@ probe-flags: -O
//@ probe-note: S4 composes two independently compiler-authenticated u64 primitive
//@ probe-note: calls. The recognizer requires one exact width across every argument,
//@ probe-note: temporary, destination, return, and literal encoding. This probe runs
//@ probe-note: under -O to pin that MIR optimization preserves those exact call identities
//@ probe-note: through verification instead of rewriting them into overflow-checked Add/Mul.
clean { def composed_isl (x : UInt64) : UInt64 := (x + 1) * 2 }
pub fn composed(x: u64) -> u64
    ensures result == composed_isl(x)
{ x.wrapping_add(1).wrapping_mul(2) }
