//@ probe-shape: WidenedEq
//@ probe-expect: discharged
//@ probe-flags: -O
//@ probe-note: THE ATTRIBUTE SURFACE, UNCITED — f60's clause, moved from SIGNATURE position
//@ probe-note: into `#[trust::ensures(...)]`. Same predicate text, same body, same island
//@ probe-note: definition; the only difference is where the clause is written. Until this
//@ probe-note: probe existed the whole corpus spelled clauses one way, so nothing measured
//@ probe-note: whether the attribute form reached the same lane — and the attribute form is
//@ probe-note: the one a real crate must use, because `#[cfg_attr(feature = ..., ...)]` is
//@ probe-note: what lets the crate still build under stock rustc.
//@ probe-note:
//@ probe-note: THE CLAUSE IS UNCITED, so exactly one thing can close it: the R4 §1 composed
//@ probe-note: defeq lane. E6 admission mints `eq_ok`'s body as a kernel constant, the island
//@ probe-note: environment supplies `eq_ok_isl`, and the kernel judges the constructed
//@ probe-note: `Eq.refl` against the elaborated goal
//@ probe-note:   (m : BitVec 64) -> (t : BitVec 128) ->
//@ probe-note:       Eq Bool (trust_import_probe__eq_ok m t) (eq_ok_isl m t).
//@ probe-note: No solver participates and no citation is consulted; the clause's ONLY proof
//@ probe-note: is that both sides delta-unfold to the same stuck `toInt64`/`ofInt128` chain.
//@ probe-note:
//@ probe-note: `f66` is the other half and is the one that matters: it holds the body FIXED
//@ probe-note: at the wrap bug this guard exists to catch and pins that the same uncited
//@ probe-note: attribute clause cannot report `discharged` for it. A positive probe alone
//@ probe-note: cannot distinguish "the kernel checked it" from "the lane waved it through".
//@ probe-note: The `-O` MIR is one block, two value statements — the cast and the compare —
//@ probe-note: identical to f60's, so a divergence between the two rows is a divergence in
//@ probe-note: the SURFACE, never in the shape being minted.
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
#[trust::ensures(result == eq_ok_isl(machine, truth))]
pub fn eq_ok(machine: i64, truth: i128) -> bool { i128::from(machine) == truth }
