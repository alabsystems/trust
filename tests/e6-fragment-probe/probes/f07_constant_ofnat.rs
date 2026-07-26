//@ probe-shape: ConstantUint
//@ probe-expect: defeq-rejected
//@ probe-note: Explicit UInt64.ofNat, to test whether the literal's default type is
//@ probe-note: the obstacle. It is not sufficient on its own.
clean { def c42 (x : UInt64) : UInt64 := UInt64.ofNat 42 }
pub fn answer() -> u64
    ensures result == c42(0)
{ 42 }
