//@ probe-shape: GuardedNarrow
//@ probe-expect: clause-outside-fragment
//@ probe-flags: -O
//@ probe-note: The paired NEGATIVE for f54 — the SMUGGLING probe, and the single most
//@ probe-note: important row of this lane. The body is the UNGUARDED narrowing
//@ probe-note: `Some(x as i64)`: it silently WRAPS every out-of-range wide value into
//@ probe-note: storage, which is exactly the VeriPB bug-C wrong-ACCEPT class the width
//@ probe-note: guard exists to prevent. Yet it has the same signature and the same
//@ probe-note: `Some`-of-a-cast arm as f54, and it claims the same contract.
//@ probe-note: It must never ride the guarded-narrow lane. At `-O` (measured, probe c11)
//@ probe-note: it is ONE basic block with no `switchInt` at all, so the rigid diamond
//@ probe-note: matcher cannot reach it: the recognizer needs an entry comparison block
//@ probe-note: with a two-way switch, a second comparison block on its `otherwise`
//@ probe-note: edge, and BOTH `0` edges landing on the same `None` block. With no
//@ probe-note: E6 self-admission, `result` has no kernel denotation and the ensures
//@ probe-note: fails closed before any defeq attempt.
//@ probe-note: If this probe ever discharges, an unguarded truncation has been admitted
//@ probe-note: as if it were guarded — a soundness incident, not a test update.
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
pub fn narrow_wrap(x: i128) -> Option<i64>
    ensures result == narrow_isl(x)
{ Some(x as i64) }
