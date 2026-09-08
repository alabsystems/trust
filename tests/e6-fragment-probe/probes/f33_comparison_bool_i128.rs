//@ probe-shape: ComparisonBool
//@ probe-expect: discharged
//@ probe-note: E6 WIDENING INCREMENT 6 — `i128` enters the import width table. Everything
//@ probe-note: below the table was already there: `MachineSIntWidth::I128`, the
//@ probe-note: `BitVec 128` carrier, the `2^127` sign-flip order key, and the `numeral`/
//@ probe-note: `negative_numeral` range checks. `signed_machine_width` stopping at 64 was
//@ probe-note: the whole gate, and its cost was not even a named refusal: with no
//@ probe-note: admission minted, `result` stayed universally quantified and the citation
//@ probe-note: failed with a multi-kilobyte raw `TermRejected` term dump. i128 is the
//@ probe-note: exact-arithmetic tier a fixed-width checker computes its overflow guards
//@ probe-note: in, so this is the width at which a guard mirror becomes statable at all.
//@ probe-note: One honest limit comes with it: the kernel's BitVec reducers fire on
//@ probe-note: u64-fitting Nat literals only, so a 128-bit NEGATIVE value (always a
//@ probe-note: multi-limb literal) has no reduction evidence. Nothing about that reaches
//@ probe-note: THIS lane, which compares the clause's term with the mint's.
clean {
    def le_w (a : BitVec 128) (b : BitVec 128) : Bool :=
        decide (Nat.le
            (Nat.xor (BitVec.toNat a) 170141183460469231731687303715884105728)
            (Nat.xor (BitVec.toNat b) 170141183460469231731687303715884105728))
}
pub fn le_wide(a: i128, b: i128) -> bool
    ensures result == (a <= b) && result == le_w(a, b)
{ a <= b }
