//@ probe-shape: WidenedEq
//@ probe-expect: discharged
//@ probe-flags: -O
//@ probe-note: WIDENING-CAST COMPARISON ADMISSION — the body of veripb's `guard::eq_ok`,
//@ probe-note: the checked-equality choke point every machine-computed degree passes
//@ probe-note: through before the proved core will accept it. It was `admissible=true,
//@ probe-note: recognize=None`: `ComparisonBool`'s operands are a parameter or a literal
//@ probe-note: at ONE carrier, and no shape modeled a comparison whose two sides live at
//@ probe-note: DIFFERENT widths with one of them produced by a cast.
//@ probe-note: Measured `-O` MIR (2026-08-26) — ONE block, TWO value statements:
//@ probe-note:   bb0: _3 = copy _1 as i128 (IntToInt);  _0 = Eq(move _3, copy _2);  return
//@ probe-note: (`i128::from(machine)` and `machine as i128` measure IDENTICALLY: the
//@ probe-note: `From` impl inlines to the same cast.)
//@ probe-note:
//@ probe-note: THE MINT MODELS SIGN EXTENSION, unconditionally and on every input. The
//@ probe-note: extracted `Rvalue::Cast` carries no `CastKind`, so the kind is pinned by
//@ probe-note: TYPES exactly as the guarded-narrow lane pins its truncation: an `iW -> iN`
//@ probe-note: signature has only one rustc cast kind, `IntToInt`, and `IntToInt` from a
//@ probe-note: SIGNED source to a STRICTLY WIDER target preserves the value. The seeded
//@ probe-note: model is `sextWide v = ofInt128 (toInt64 v)` — the checked lane's own
//@ probe-note: exact-`Int` bridge, composed, introducing NO new primitive and NO new
//@ probe-note: literal. It is exact because `toInt64 v` lands in [-2^63, 2^63) and
//@ probe-note: `ofInt128` is exact on that whole range (both of its `ofNat` operands stay
//@ probe-note: below 2^128, neither wraps). At `v = -1` it yields the all-ones
//@ probe-note: `BitVec 128`, which is precisely where the zero-extension forgery of f62
//@ probe-note: diverges.
//@ probe-note: The comparison half claims nothing new: it is the same `Domain::Signed`
//@ probe-note: `Eq` spelling (`Eq Nat` over the two `BitVec.toNat`s, decided by
//@ probe-note: `Nat.decEq`) the ComparisonBool lane already mints, evaluated at the wide
//@ probe-note: carrier where both sides now live. Operand ORDER is reproduced, not
//@ probe-note: normalized: that spelling is not syntactically symmetric.
//@ probe-note: The clause closes by DELTA-DEFEQ against the island's authored model —
//@ probe-note: both sides unfold to the same stuck `toInt64`/`ofInt128` chain.
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
pub fn eq_ok(machine: i64, truth: i128) -> bool
    ensures result == eq_ok_isl(machine, truth)
{ i128::from(machine) == truth }
