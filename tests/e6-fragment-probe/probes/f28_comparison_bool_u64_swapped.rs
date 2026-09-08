//@ probe-shape: ComparisonBool
//@ probe-expect: discharged
//@ probe-note: The UNSIGNED twin of f27, and the `>=` operand-swap normalization: the
//@ probe-note: clause says `b >= a` while the body computes `a <= b`. `>`/`>=` normalize
//@ probe-note: by swapping operands — never by negation — so both land on the SAME
//@ probe-note: decided term. At an unsigned carrier that term goes through Clean's own
//@ probe-note: `instLEUInt64`/`instDecidableUInt64Le`, which is why the island can spell
//@ probe-note: the decision as plain `decide (a <= b)`; f27 pins the signed side, where
//@ probe-note: the BitVec order instances are unsigned and must NOT be reused.
clean {
    def le_u (a : UInt64) (b : UInt64) : Bool := decide (a <= b)
}
pub fn le_u64(a: u64, b: u64) -> bool
    ensures result == (b >= a) && result == le_u(a, b)
{ a <= b }
