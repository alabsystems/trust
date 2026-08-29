//@ probe-shape: ConstantUint
//@ probe-expect: discharged
//@ probe-note: WIDENED 2026-08-22 by 0acfcc223a2 (fix(spec-elab)) on 74f315aa368's
//@ probe-note: return-domain attach sites: a VARIABLE-FREE atom now takes its domain
//@ probe-note: from term evidence instead of defaulting to Nat, so the goal is the
//@ probe-note: well-typed `Eq UInt64 …` the kernel can close by Eq.refl.
//@ probe-note: A nullary Rust fn citing a one-parameter def applied to a literal.
clean { def c42 (x : UInt64) : UInt64 := 42 }
pub fn answer() -> u64
    ensures result == c42(0)
{
    42
}
