//@ probe-shape: BoolBinary
//@ probe-expect: discharged
//@ probe-flags: -O
//@ probe-note: The disjunction positive: `x < -128 || x > 127` (the complement
//@ probe-note: of f45's range) recognized as BoolBinary{Or} and discharged by
//@ probe-note: defeq against the Bool.or island model. `>` is normalized by
//@ probe-note: operand swap (127 < x), never negation, exactly as the
//@ probe-note: single-comparison lane does.
clean {
    def key64 (v : BitVec 64) : Nat :=
        Nat.xor (BitVec.toNat v) 9223372036854775808
    def outside_isl (x : BitVec 64) : Bool :=
        Bool.or (@Decidable.decide (Nat.lt (key64 x) (key64 (BitVec.ofNat 64 18446744073709551488)))
                                  (Nat.decLt (key64 x) (key64 (BitVec.ofNat 64 18446744073709551488))))
                (@Decidable.decide (Nat.lt (key64 (BitVec.ofNat 64 127)) (key64 x))
                                  (Nat.decLt (key64 (BitVec.ofNat 64 127)) (key64 x)))
}
pub fn outside_range(x: i64) -> bool
    ensures result == outside_isl(x)
{ x < -128 || x > 127 }
