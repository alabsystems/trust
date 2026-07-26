//@ probe-shape: ConstantUint
//@ probe-expect: unproved
//@ probe-note: ConstantUint is recognized and admitted, yet NO constant probe in this
//@ probe-note: corpus discharges. Two suspected defects: the arity-0 mint, and a
//@ probe-note: Nat-defaulted literal on the island side.
clean { def forty_two_isl : UInt64 := 42 }
pub fn answer() -> u64
    ensures result == forty_two_isl
{ 42 }
