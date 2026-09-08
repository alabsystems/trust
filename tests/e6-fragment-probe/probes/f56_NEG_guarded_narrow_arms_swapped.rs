//@ probe-shape: GuardedNarrow
//@ probe-expect: clause-outside-fragment
//@ probe-flags: -O
//@ probe-note: The ARMS-SWAPPED negative for f54: `None` on the guard-TRUE edge and
//@ probe-note: `Some(x as i64)` on the guard-FALSE edge — the guard is present and
//@ probe-note: correct, and it admits exactly the values it should refuse. This is the
//@ probe-note: false-`Some` wrong-verdict class in its purest form, and a positive
//@ probe-note: fixture alone would not catch it (a consistently-reversed mint would
//@ probe-note: close against a consistently-reversed model), so it is pinned twice:
//@ probe-note: here at the BODY level and in trust-certify's §5.7 def-eq oracle at the
//@ probe-note: MODEL level (`narrowWideSwapped`, plus a wrong-width truncation and a
//@ probe-note: guard widened to `fitsI128`, all three measurably not def-eq).
//@ probe-note: The recognizer forbids this shape STRUCTURALLY, not by matching against
//@ probe-note: it: it requires the `Some` arm on the `otherwise` edge of the SECOND
//@ probe-note: comparison and BOTH `0` edges to reach the SAME `None` block, so a body
//@ probe-note: whose `Some` is reachable with either comparison false cannot parse at
//@ probe-note: all. With no E6 admission, `result` has no kernel denotation.
//@ probe-note: If this probe ever discharges, the guard's polarity has stopped being
//@ probe-note: checked — a soundness incident, not a test update.
clean {
    def key128 (v : BitVec 128) : Nat :=
        Nat.xor (BitVec.toNat v) 170141183460469231731687303715884105728
    def toInt128 (v : BitVec 128) : Int :=
        match Nat.ble 170141183460469231731687303715884105728 (key128 v) with
        | true  => Int.ofNat (Nat.sub (key128 v) 170141183460469231731687303715884105728)
        | false => Int.negSucc (Nat.sub 170141183460469231731687303715884105727 (key128 v))
    def i64Max : Int := 9223372036854775807
    def i64Min : Int := Int.neg 9223372036854775808
    def fitsI64 (x : Int) : Bool :=
        match Int.ble i64Min x with
        | true  => Int.ble x i64Max
        | false => false
    def trunc64 (v : BitVec 128) : BitVec 64 :=
        BitVec.ofNat 64 (BitVec.toNat v)
    def narrow_isl (x : BitVec 128) : Option (BitVec 64) :=
        match fitsI64 (toInt128 x) with
        | true  => some (trunc64 x)
        | false => none
}
pub fn narrow_swapped(x: i128) -> Option<i64>
    ensures result == narrow_isl(x)
{
    if x >= i64::MIN as i128 && x <= i64::MAX as i128 {
        None
    } else {
        Some(x as i64)
    }
}
