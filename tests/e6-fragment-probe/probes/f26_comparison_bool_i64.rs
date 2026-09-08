//@ probe-shape: ComparisonBool
//@ probe-expect: discharged
//@ probe-note: E6 WIDENING INCREMENT 5 (2026-08-23), now complete on both halves.
//@ probe-note: The BODY mint landed first: `fn le(a, b) -> bool { a <= b }` imports as
//@ probe-note: `Decidable.decide` over the same sign-flip order keys the select mint
//@ probe-note: scrutinizes. The CLAUSE half landed 2026-08-24: an `Admission` now
//@ probe-note: records its RETURN domain, so a call is typed as a Bool-valued TERM and
//@ probe-note: `result == le_isl(a, b)` builds an `Eq Bool` around two Bool-valued
//@ probe-note: sides instead of the `Eq (BitVec 64)` that the ill-typed-goal gate
//@ probe-note: (correctly) refused. The island spells the decision the way Clean's own
//@ probe-note: elaborator does — `decide (Nat.le ..)`, whose instance synthesis picks
//@ probe-note: `Nat.decLe` — which is byte-for-byte the mint. f32 is the paired NEG
//@ probe-note: probe: the equally-true `Nat.ble` spelling is a DIFFERENT stuck term and
//@ probe-note: is refused, so this probe cannot be passing for an accidental reason.
clean {
    def le_isl (a : BitVec 64) (b : BitVec 64) : Bool :=
        decide (Nat.le (Nat.xor (BitVec.toNat a) 9223372036854775808)
                       (Nat.xor (BitVec.toNat b) 9223372036854775808))
}
pub fn le_i64(a: i64, b: i64) -> bool
    ensures result == le_isl(a, b)
{ a <= b }
