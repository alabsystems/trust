//@ probe-shape: ComparisonBool
//@ probe-expect: discharged
//@ probe-note: E6 WIDENING INCREMENT 6 — a LITERAL operand, the shape every width guard
//@ probe-note: is actually written in (`x <= HI`, `LO <= x`, `x >= 0`). The previous
//@ probe-note: recognizer pinned BOTH operands to bare parameters, so a bound against a
//@ probe-note: constant was outside the fragment no matter how simple. It also exercises
//@ probe-note: the `>=` swap: rustc lowers this body to `Ge(x, 0)` and the recognizer
//@ probe-note: normalizes it to `Le(0, x)` — the same normalization the clause lane
//@ probe-note: applies to `(x >= 0)`, which is why the two coincide. Note what a `const`
//@ probe-note: ITEM lowers to: a plain constant OPERAND, not an `Rvalue::Cast`, which is
//@ probe-note: why the const-item spelling of a bound reaches this recognizer while
//@ probe-note: `Wide::from(Coeff::MIN)` (a `From::from` call terminator) still does not.
//@ probe-note: The island shows what a minted signed literal actually looks like: at a
//@ probe-note: BitVec carrier `BitVec.toNat (BitVec.ofNat w n)` PARKS, so the bound's
//@ probe-note: order key is a stuck term. Both sides of the discharge build the same
//@ probe-note: stuck term, so it costs nothing here — but it is why an author writing
//@ probe-note: this island has to spell the embedding out.
clean {
    def key64 (v : BitVec 64) : Nat :=
        Nat.xor (BitVec.toNat v) 9223372036854775808
    def nonneg_isl (x : BitVec 64) : Bool :=
        decide (Nat.le (key64 (BitVec.ofNat 64 Nat.zero)) (key64 x))
}
pub fn nonneg(x: i64) -> bool
    ensures result == (x >= 0) && result == nonneg_isl(x)
{ x >= 0 }
