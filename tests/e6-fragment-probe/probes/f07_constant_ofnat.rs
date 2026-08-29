//@ probe-shape: ConstantUint
//@ probe-expect: discharged
//@ probe-note: WIDENED 2026-08-22 by 0acfcc223a2 (fix(spec-elab)) on 74f315aa368's
//@ probe-note: return-domain attach sites — the ISLAND side was never the obstacle;
//@ probe-note: the CLAUSE side's Nat default was, and it now derives from term evidence.
//@ probe-note: Explicit UInt64.ofNat, to test whether the literal's default type is
//@ probe-note: the obstacle. Confirmed: it was not, on either side.
clean { def c42 (x : UInt64) : UInt64 := UInt64.ofNat 42 }
pub fn answer() -> u64
    ensures result == c42(0)
{
    42
}
