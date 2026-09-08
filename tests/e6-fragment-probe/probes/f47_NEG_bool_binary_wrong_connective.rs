//@ probe-shape: BoolBinary
//@ probe-expect: defeq-rejected
//@ probe-flags: -O
//@ probe-note: NEGATIVE, must stay red. The body is f45's CONJUNCTION but the
//@ probe-note: island model is composed with Bool.or -- the same two decided
//@ probe-note: leaves under the WRONG connective. If this ever discharges, the
//@ probe-note: mint has stopped distinguishing And from Or and f45/f46 are
//@ probe-note: passing for an accidental reason. This is the connective half
//@ probe-note: of the recognizer's arm-arrangement keying; the arrangement
//@ probe-note: half (const-false-on-zero-edge = And) is pinned by unit tests
//@ probe-note: in trust-types.
clean {
    def key64 (v : BitVec 64) : Nat :=
        Nat.xor (BitVec.toNat v) 9223372036854775808
    def wrong_isl (x : BitVec 64) : Bool :=
        Bool.or (Decidable.decide (Nat.le (key64 (BitVec.ofNat 64 18446744073709551488)) (key64 x))
                                  (Nat.decLe (key64 (BitVec.ofNat 64 18446744073709551488)) (key64 x)))
                (Decidable.decide (Nat.le (key64 x) (key64 (BitVec.ofNat 64 127)))
                                  (Nat.decLe (key64 x) (key64 (BitVec.ofNat 64 127))))
}
pub fn in_range(x: i64) -> bool
    ensures result == wrong_isl(x)
{ x >= -128 && x <= 127 }
