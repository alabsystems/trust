//@ probe-shape: WidenedEq
//@ probe-expect: clause-outside-fragment
//@ probe-flags: -O
//@ probe-note: The first paired NEGATIVE for f60 — the DIRECTION probe. The body is
//@ probe-note: `(machine as i64) == truth` at i128 -> i64: the cast is TRUNCATION, not
//@ probe-note: widening. It wraps every out-of-range wide value before comparing, so it
//@ probe-note: answers `true` for pairs the sign-extending model answers `false` for
//@ probe-note: (e.g. machine = 2^64, truth = 0) — the VeriPB bug-C wrong-ACCEPT class,
//@ probe-note: reached through the equality guard instead of the width guard.
//@ probe-note: Yet at `-O` its MIR is the SAME two-statement cast-then-`Eq` block as f60
//@ probe-note: (measured 2026-08-26), differing only in the declared widths, and it
//@ probe-note: claims the same contract against the same sign-extension island.
//@ probe-note: It must never ride the sign-extension lane. The recognizer refuses it on
//@ probe-note: the monomorphic width pin: `from_bits` must be 64 and `to_bits` 128, so a
//@ probe-note: 128 -> 64 cast is not merely unmatched but structurally unreachable here —
//@ probe-note: truncation belongs to the guarded-narrow lane, which models it as
//@ probe-note: truncation. With no E6 self-admission, `result` has no kernel denotation
//@ probe-note: and the ensures fails closed before any defeq attempt.
//@ probe-note: If this probe ever discharges, a truncating cast has been minted as a
//@ probe-note: value-preserving widening — a soundness incident, not a test update.
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
pub fn eq_trunc(machine: i128, truth: i64) -> bool
    ensures result == eq_ok_isl(truth, machine)
{ (machine as i64) == truth }
