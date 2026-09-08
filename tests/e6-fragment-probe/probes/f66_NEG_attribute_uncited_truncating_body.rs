//@ probe-shape: WidenedEq
//@ probe-expect: clause-outside-fragment
//@ probe-flags: -O
//@ probe-note: THE ONE THAT MATTERS. Byte-for-byte `f65` — same island, same uncited
//@ probe-note: `#[trust::ensures(result == eq_ok_isl(machine, truth))]` — with the body
//@ probe-note: mutated to `machine == truth as i64`: the operands compared after
//@ probe-note: TRUNCATING the wide side, which is the exact wrap bug `eq_ok` exists to
//@ probe-note: catch (`truth = 2^64 + machine` passes it). This row must never read
//@ probe-note: `discharged`, in any compiler, for any reason.
//@ probe-note:
//@ probe-note: It is a NEGATIVE about the SURFACE, not about the kernel. The kernel half
//@ probe-note: was already pinned by `f61`/`f62` in signature position; what was never
//@ probe-note: pinned is that writing the SAME clause as an attribute cannot buy a pass.
//@ probe-note: That gap was real: an uncited attribute clause left `Unsupported` sentinel
//@ probe-note: obligations, and `-Ztrust-policy=advisory` downgrades those to warnings, so
//@ probe-note: a violated contract compiled green with nothing in the output naming the
//@ probe-note: clause that had stopped holding. The lane now emits
//@ probe-note:   error: uncited `ensures` naming the Clean island definition `eq_ok_isl`
//@ probe-note:          was not discharged by definitional equality: <verdict reason>
//@ probe-note: which is policy-independent, exactly like the cited lane's
//@ probe-note: `citation ... failed the strict Clean statement/certification audit`. Cited
//@ probe-note: and uncited clauses now fail the same way; the asymmetry between them WAS
//@ probe-note: the defect.
//@ probe-note:
//@ probe-note: The recorded verdict is `clause-outside-fragment`, not `defeq-rejected`, and
//@ probe-note: the distinction is load-bearing (see the README): the truncating body is not
//@ probe-note: E6-admissible at all, so the goal never reaches the kernel. `f61` is the
//@ probe-note: companion that pins the same mutation where the elaboration DOES complete.
//@ probe-note: Either verdict is a refusal; what this probe forbids is `discharged`.
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
#[trust::ensures(result == eq_ok_isl(machine, truth))]
pub fn eq_ok(machine: i64, truth: i128) -> bool { machine == truth as i64 }
