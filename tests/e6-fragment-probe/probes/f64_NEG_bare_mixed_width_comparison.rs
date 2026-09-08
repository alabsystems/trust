//@ probe-shape: WidenedEq
//@ probe-expect: clause-outside-fragment
//@ probe-flags: -O
//@ probe-note: THE PIN THAT KEEPS f60 FROM BEING A COERCION. f60's clause compares an
//@ probe-note: `i64` and an `i128` THROUGH a callee whose declaration says it takes one
//@ probe-note: of each — so the two widths are in one ARGUMENT LIST, never in one
//@ probe-note: comparison, and the sign extension that relates them is the callee's own
//@ probe-note: modelled body. This probe writes the same two parameters into a BARE
//@ probe-note: comparison, with no callee between them, and it must still be refused.
//@ probe-note:
//@ probe-note: The refusal is the elaborator's, not the kernel's: `machine == truth`
//@ probe-note: reports "mixed domains in one comparison (Signed(I64) and Signed(I128)) —
//@ probe-note: the operands of a single comparison must share a type", and that message
//@ probe-note: is CORRECT. There is no cast in the clause to justify the comparison, and
//@ probe-note: an elaborator that silently widened one side would be inventing the very
//@ probe-note: sign-extension step f60's mint had to seed, prove exact, and defend
//@ probe-note: against a zero-extending forgery (f62). Two ways of reading `machine ==
//@ probe-note: truth` disagree on every negative `machine`; the elaborator picks neither.
//@ probe-note:
//@ probe-note: WHAT THIS ROW MEASURES ACROSS THE INCREMENT is which conjunct does the
//@ probe-note: refusing. BEFORE, the FIRST conjunct already failed (that is f60), so the
//@ probe-note: verdict said nothing about the second. AFTER, the first conjunct
//@ probe-note: discharges and the whole clause is refused on the second alone — the
//@ probe-note: verdict is unchanged and now means what it says. The exact message is
//@ probe-note: pinned as a unit assertion in
//@ probe-note: `trust_spec_elab::a_call_types_its_arguments_by_the_callees_declared_carriers`
//@ probe-note: (NEG 1) and in `trust_certify::typed_call_arguments_take_the_callees_declared_carriers`
//@ probe-note: (case 3), where a probe verdict alone cannot distinguish the two.
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
        Decidable.decide (Eq (BitVec.toNat (sextWide m)) (BitVec.toNat t))
                         (Nat.decEq (BitVec.toNat (sextWide m)) (BitVec.toNat t))
}
pub fn eq_ok_bare(machine: i64, truth: i128) -> bool
    ensures result == eq_ok_isl(machine, truth) && machine == truth
{ i128::from(machine) == truth }
