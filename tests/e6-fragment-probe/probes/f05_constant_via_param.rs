//@ probe-shape: ConstantUint
//@ probe-expect: discharged
//@ probe-note: WIDENED 2026-08-22 by 74f315aa368 (fix(certify/C6)): the ConstantUint
//@ probe-note: routing is arity-preserving, so a parametered constant mints
//@ probe-note: `fun p0 => 42` instead of a nullary side B, and the kernel closes
//@ probe-note: `(u : UInt64) -> Eq UInt64 (trust_import_probe__answer u) (const42 u)`.
//@ probe-note: Same constant, reached through a parameter the def ignores.
clean { def const42 (x : UInt64) : UInt64 := 42 }
pub fn answer(x: u64) -> u64
    ensures result == const42(x)
{
    42
}
