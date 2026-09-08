//@ probe-shape: ComparisonBool
//@ probe-expect: discharged
//@ probe-note: E6 WIDENING INCREMENT 5, CLAUSE HALF — the spelling an author actually
//@ probe-note: reaches for: `ensures result == (a <= b)`. Before this increment it was
//@ probe-note: refused as "mixed domains in one comparison": `atom_domain` typed the
//@ probe-note: whole atom from the NESTED comparison's i64 variables and never saw that
//@ probe-note: the outer `==` is a Bool equality. The fix splits the two — the operands
//@ probe-note: keep `BitVec 64`, the relation moves to `Eq Bool` — and elaborates the
//@ probe-note: nested comparison to the very `Decidable.decide` term the ComparisonBool
//@ probe-note: mint emits, so it closes by reflexivity with no theorem. An `Iff`, or the
//@ probe-note: equally-true `Nat.ble` spelling f32 pins, would be stuck at a different
//@ probe-note: head constant and no reducibility setting bridges an iota mismatch.
//@ probe-note: The second conjunct is what makes this measurable at all: the uncited
//@ probe-note: defeq route owns only clauses that CALL an island definition, so a
//@ probe-note: no-island clause never reaches the kernel to be judged. Pairing the two
//@ probe-note: spellings in one clause also states the stronger fact — that they are the
//@ probe-note: SAME term — since both conjuncts close against the same minted body.
clean {
    def le_isl (a : BitVec 64) (b : BitVec 64) : Bool :=
        decide (Nat.le (Nat.xor (BitVec.toNat a) 9223372036854775808)
                       (Nat.xor (BitVec.toNat b) 9223372036854775808))
}
pub fn le_i64(a: i64, b: i64) -> bool
    ensures result == (a <= b) && result == le_isl(a, b)
{ a <= b }
