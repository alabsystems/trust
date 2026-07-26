//@ probe-shape: ConstantUint
//@ probe-expect: clause-outside-fragment
//@ probe-note: Same constant, reached through a parameter the def ignores.
clean { def const42 (x : UInt64) : UInt64 := 42 }
pub fn answer(x: u64) -> u64
    ensures result == const42(x)
{ 42 }
