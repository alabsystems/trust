//@ probe-shape: ComparisonBool
//@ probe-expect: clause-outside-fragment
//@ probe-note: THE OTHER NET: `bool` has no ORDER. A decided bool-valued side may be
//@ probe-note: compared with `==` and nothing else, so `result <= le_isl(a, b)` stays
//@ probe-note: outside the fragment even though both halves are individually statable.
//@ probe-note: Widening `==` to a Bool relation carrier must not smuggle in an ordering
//@ probe-note: the carrier does not have; if it ever did, the goal would be `Nat.le`
//@ probe-note: applied to two `Bool`s and only the ill-typed-goal gate would stand
//@ probe-note: between that and a discharge.
clean {
    def le_isl (a : BitVec 64) (b : BitVec 64) : Bool :=
        decide (Nat.le (Nat.xor (BitVec.toNat a) 9223372036854775808)
                       (Nat.xor (BitVec.toNat b) 9223372036854775808))
}
pub fn le_i64_ord(a: i64, b: i64) -> bool
    ensures result <= le_isl(a, b)
{ a <= b }
