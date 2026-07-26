//@ probe-shape: ConstantUint
//@ probe-expect: defeq-rejected
//@ probe-note: A nullary Rust fn citing a one-parameter def applied to a literal.
clean { def c42 (x : UInt64) : UInt64 := 42 }
pub fn answer() -> u64
    ensures result == c42(0)
{ 42 }
