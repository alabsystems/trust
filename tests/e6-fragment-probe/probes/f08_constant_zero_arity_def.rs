//@ probe-shape: ConstantUint
//@ probe-expect: defeq-rejected
//@ probe-note: Zero-arity def, called with an empty argument list from the clause.
clean { def c42 : UInt64 := UInt64.ofNat 42 }
pub fn answer() -> u64
    ensures result == c42()
{ 42 }
