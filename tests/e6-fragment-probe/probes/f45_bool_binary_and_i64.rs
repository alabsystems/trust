//@ probe-shape: BoolBinary
//@ probe-expect: discharged
//@ probe-flags: -O
//@ probe-note: The bool-conjunction lane's positive: an i64 range guard
//@ probe-note: `x >= -128 && x <= 127` recognized as BoolBinary{And} and
//@ probe-note: discharged by defeq against an island model composed exactly as
//@ probe-note: the mint composes it -- Bool.and of the two decided key64
//@ probe-note: comparisons. The clause names the ISLAND CALL rather than
//@ probe-note: spelling the conjunction inline: the inline spelling
//@ probe-note: `result == (A && B)` is falsely refuted by the native
//@ probe-note: trust-mc lane (see f53) and the island-call form routes the
//@ probe-note: discharge through the kernel, which is the lane under test.
//@ probe-note: `18446744073709551488` is the two's-complement image of -128
//@ probe-note: at 64 bits. f47 is the paired NEG (Or-composed island model).
clean {
    def key64 (v : BitVec 64) : Nat :=
        Nat.xor (BitVec.toNat v) 9223372036854775808
    def range_isl (x : BitVec 64) : Bool :=
        Bool.and (@Decidable.decide (Nat.le (key64 (BitVec.ofNat 64 18446744073709551488)) (key64 x))
                                   (Nat.decLe (key64 (BitVec.ofNat 64 18446744073709551488)) (key64 x)))
                 (@Decidable.decide (Nat.le (key64 x) (key64 (BitVec.ofNat 64 127)))
                                   (Nat.decLe (key64 x) (key64 (BitVec.ofNat 64 127))))
}
pub fn in_range(x: i64) -> bool
    ensures result == range_isl(x)
{ x >= -128 && x <= 127 }
