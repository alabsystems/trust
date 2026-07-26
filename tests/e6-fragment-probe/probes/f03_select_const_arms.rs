//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: Constant arms are not recognized as Select at all — the recognizer
//@ probe-note: requires each arm to assign from a bare PARAM.
clean { def sc (a : UInt64) (b : UInt64) : UInt64 := if a.toNat < b.toNat then 0 else 1 }
pub fn f(a: u64, b: u64) -> u64
    ensures result == sc(a, b)
{ if a < b { 0 } else { 1 } }
