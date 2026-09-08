//@ probe-shape: CheckedArithmetic
//@ probe-expect: clause-outside-fragment
//@ probe-note: The paired NEGATIVE for f49 — the SMUGGLING probe. The body is UNCHECKED
//@ probe-note: `a + b`: at `-O` it lowers to a bare `Add` (or, with overflow checks on,
//@ probe-note: to CheckedBinaryOp + an `Assert` on the flag). Either way it must never
//@ probe-note: ride the checked-arithmetic lane: the recognizer requires the pinned
//@ probe-note: std-Option return shape AND refuses ANY body containing an Assert, and
//@ probe-note: the facet gate refuses raw arithmetic's NoPanic. With no self-admission,
//@ probe-note: `result` has no kernel denotation and the ensures fails closed before any
//@ probe-note: defeq attempt. If this probe ever discharges, unchecked overflow has been
//@ probe-note: admitted as if it were checked — a soundness incident, not a test update.
clean {
    def key64 (v : BitVec 64) : Nat :=
        Nat.xor (BitVec.toNat v) 9223372036854775808
    def uadd_isl (a : BitVec 64) (b : BitVec 64) : BitVec 64 :=
        BitVec.ofNat 64 (Nat.add (BitVec.toNat a) (BitVec.toNat b))
}
pub fn uadd(a: i64, b: i64) -> i64
    ensures result == uadd_isl(a, b)
{ a + b }
