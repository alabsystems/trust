//@ probe-shape: WidenedEq
//@ probe-expect: clause-outside-fragment
//@ probe-flags: -O
//@ probe-note: The second paired NEGATIVE for f60, and the SHARPEST row of this lane: the
//@ probe-note: source is `u64`, so the cast is ZERO extension, not sign extension.
//@ probe-note: Measured 2026-08-26, its `-O` MIR is BYTE-FOR-BYTE the shape f60 admits —
//@ probe-note:   bb0: _3 = copy _1 as i128 (IntToInt);  _0 = Eq(move _3, copy _2);  return
//@ probe-note: — the SAME `IntToInt` cast to the SAME `i128` target, and the facet gate
//@ probe-note: admits it too (`admissible=true`, measured). NOTHING in the MIR spelling
//@ probe-note: distinguishes it. The ONLY discriminator is the DECLARED signedness of the
//@ probe-note: source local, and that is exactly the gate the recognizer pins.
//@ probe-note: Why it matters: zero and sign extension agree on every NON-NEGATIVE value
//@ probe-note: and disagree on every negative one. A test that only exercised
//@ probe-note: non-negative inputs would see no difference at all; the divergence starts
//@ probe-note: at the bit pattern `0xFFFF...F`, which sign-extends to -1 and zero-extends
//@ probe-note: to 2^64 - 1. Minting this body as sign extension would let the contract
//@ probe-note: claim a false equality for exactly the wrapped values the guard exists to
//@ probe-note: reject.
//@ probe-note: With the source refused, no admission is minted, `result` has no kernel
//@ probe-note: denotation, and the ensures fails closed before any defeq attempt.
//@ probe-note: If this probe ever discharges, a zero-extending cast has been minted as a
//@ probe-note: sign-extending one — a soundness incident, not a test update.
clean {
    def key64 (v : BitVec 64) : Nat :=
        Nat.xor (BitVec.toNat v) 9223372036854775808
    def toInt64 (v : BitVec 64) : Int :=
        match Nat.ble 9223372036854775808 (key64 v) with
        | true  => Int.ofNat (Nat.sub (key64 v) 9223372036854775808)
        | false => Int.negSucc (Nat.sub 9223372036854775807 (key64 v))
    def ofInt128 (x : Int) : BitVec 128 :=
        match Int.ble (Int.ofNat 0) x with
        | true  => BitVec.ofNat 128 (Int.toNat x)
        | false => BitVec.ofNat 128 (Int.toNat (Int.add x (Int.ofNat 340282366920938463463374607431768211456)))
    def sextWide (v : BitVec 64) : BitVec 128 :=
        ofInt128 (toInt64 v)
    def eq_ok_isl (m : BitVec 64) (t : BitVec 128) : Bool :=
        @Decidable.decide (Eq (BitVec.toNat (sextWide m)) (BitVec.toNat t))
                         (Nat.decEq (BitVec.toNat (sextWide m)) (BitVec.toNat t))
}
pub fn eq_zext(machine: u64, truth: i128) -> bool
    ensures result == eq_ok_isl(machine, truth)
{ (machine as i128) == truth }
