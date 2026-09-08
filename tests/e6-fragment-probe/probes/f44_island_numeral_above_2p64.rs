//@ probe-shape: ComparisonBool
//@ probe-expect: discharged
//@ probe-note: The other half of the pair f43 opens; the only thing that differs is
//@ probe-note: the magnitude of the bound: 2^128 - 100 (the two's-complement image of
//@ probe-note: -100 at this width) is at or above 2^64. Before the BitVec.ofNat
//@ probe-note: multi-limb/OfNat lift (first-party/clean 05f6b0b3d) that magnitude was
//@ probe-note: the deciding fact -- this probe was green while f43 was red, isolating
//@ probe-note: a 2^64 numeral threshold in the island elaboration.
//@ probe-note:
//@ probe-note: Keep the two probes adjacent. Both discharge now, and the PAIR is the
//@ probe-note: pin: if either ever diverges from the other again, a magnitude
//@ probe-note: threshold has crept back into numeral normalization, and clients'
//@ probe-note: guard-bound contracts silently lose one side.
clean {
    def key128 (v : BitVec 128) : Nat :=
        Nat.xor (BitVec.toNat v) 170141183460469231731687303715884105728
    def bound_isl (x : BitVec 128) : Bool :=
        Decidable.decide (Nat.le (key128 x) (key128 (BitVec.ofNat 128 340282366920938463463374607431768211356)))
                         (Nat.decLe (key128 x) (key128 (BitVec.ofNat 128 340282366920938463463374607431768211356)))
}
pub fn at_bound(x: i128) -> bool
    ensures result == bound_isl(x)
{ x <= -100 }
