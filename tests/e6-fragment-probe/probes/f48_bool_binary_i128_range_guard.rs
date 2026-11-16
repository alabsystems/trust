//@ probe-shape: BoolBinary
//@ probe-expect: discharged
//@ probe-flags: -O
//@ probe-note: The motivating client shape at the client's exact width: the
//@ probe-note: COMPLETE i64 width guard as one i128 conjunction, the body of
//@ probe-note: veripb's guard::fits_i64 after const-fold. The island model is
//@ probe-note: the Bool.and of the two decided key128 comparisons -- the same
//@ probe-note: structure veripb's guard_fits_exact theorem speaks about.
//@ probe-note: `340282366920938463454151235394913435648` is 2^128 - 2^63, the
//@ probe-note: two's-complement image of i64::MIN at 128 bits; the upper bound
//@ probe-note: i64::MAX sits below 2^64 and is sayable at all only because of
//@ probe-note: the BitVec.ofNat multi-limb lift (f43/f44).
clean {
    def key128 (v : BitVec 128) : Nat :=
        Nat.xor (BitVec.toNat v) 170141183460469231731687303715884105728
    def fits_isl (x : BitVec 128) : Bool :=
        Bool.and (@Decidable.decide (Nat.le (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x))
                                   (Nat.decLe (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x)))
                 (@Decidable.decide (Nat.le (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807)))
                                   (Nat.decLe (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807))))
}
pub fn in_i64_range(x: i128) -> bool
    ensures result == fits_isl(x)
{ x >= -9223372036854775808 && x <= 9223372036854775807 }
