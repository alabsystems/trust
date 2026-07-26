//@ probe-shape: ConstantUint
//@ probe-expect: defeq-rejected
//@ probe-note: Identity def applied to a literal — the clause side is a closed term,
//@ probe-note: so this isolates literal handling from constant-function minting.
clean { def cid (x : UInt64) : UInt64 := x }
pub fn answer() -> u64
    ensures result == cid(42)
{ 42 }
