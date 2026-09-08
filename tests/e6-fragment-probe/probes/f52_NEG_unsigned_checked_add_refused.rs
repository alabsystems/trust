//@ probe-shape: CheckedArithmetic
//@ probe-expect: unproved
//@ probe-note: The UNSIGNED negative (spec §5.5): `u64::checked_add` has different
//@ probe-note: semantics than the signed model (range [0, 2^64-1], underflow at 0 for
//@ probe-note: sub, a different Int bridge), so this increment refuses it EVERYWHERE —
//@ probe-note: the classifier marks signed impls only, the recognizer's Option-shape
//@ probe-note: gate requires a SIGNED payload, and the mint's parameter gate requires
//@ probe-note: the signed carrier. With no admission, the ensures fails closed. Flipping
//@ probe-note: this probe green is only legitimate in a commit that lands the separate
//@ probe-note: unsigned checked model with its own faithfulness argument.
clean {
    def cuadd_witness (a : BitVec 64) (b : BitVec 64) : Nat :=
        Nat.add (BitVec.toNat a) (BitVec.toNat b)
}
pub fn cuadd(a: u64, b: u64) -> Option<u64>
    ensures result == None
{ a.checked_add(b) }
