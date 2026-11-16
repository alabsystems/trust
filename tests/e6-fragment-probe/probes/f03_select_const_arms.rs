//@ probe-shape: none
//@ probe-expect: discharged
//@ probe-note: Constant arms are not recognized as Select by the frozen recognizer,
//@ probe-note: which requires each arm to assign from a bare PARAM. Since E6 expansion
//@ probe-note: I4′ the E6-only tree reader reads it as `ite (a < b) 0 1`, and the kernel
//@ probe-note: unfolds `UInt64`'s `<` to meet this island's `a.toNat < b.toNat`. MEASURED
//@ probe-note: 2026-09-29: `discharged` on stage 1 of `e6/slice2` (`583de8e0bf6`),
//@ probe-note: `clause-outside-fragment` on the installed pack `4d9a20e3d`.
clean { def sc (a : UInt64) (b : UInt64) : UInt64 := if a.toNat < b.toNat then 0 else 1 }
pub fn f(a: u64, b: u64) -> u64
    ensures result == sc(a, b)
{
    if a < b { 0 } else { 1 }
}
