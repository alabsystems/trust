//@ probe-shape: GuardedNarrow
//@ probe-expect: discharged
//@ probe-flags: -O
//@ probe-note: f54's shape as the REAL veripb client body spells it — `if fits_i64(x)`
//@ probe-note: through a separate guard helper, which is verbatim `guard::narrow`
//@ probe-note: (lib.rs:571-577) modulo the pinned alias substitutions. This is the
//@ probe-note: probe that pins the shape actually shipped, so it is the one that must
//@ probe-note: stay green for the twin to keep carrying its contract.
//@ probe-note: Measured (probe c10): the helper inlines to the SAME conjunction
//@ probe-note: diamond, but with the block ORDER permuted (the second comparison is the
//@ probe-note: last block, the arms are the first two) and ONE bookkeeping `goto`
//@ probe-note: trampoline interposed on the first comparison's false edge. That is why
//@ probe-note: the recognizer chases EDGES and never block indices, and why it walks
//@ probe-note: value-neutral `goto`-only blocks before parsing an arm — while its final
//@ probe-note: block census still refuses ANY block that is neither one of the five
//@ probe-note: named ones nor a trampoline it actually walked.
//@ probe-note: The helper itself is separately admissible as BoolBinary{And, ...} (the
//@ probe-note: f45/f46/f48 lane), so this probe also pins that the two lanes agree on
//@ probe-note: one body: the guard predicate and the guarded admission are cited
//@ probe-note: against the SAME two literal bounds.
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
fn fits_i64(x: i128) -> bool {
    x >= i64::MIN as i128 && x <= i64::MAX as i128
}
pub fn narrow(x: i128) -> Option<i64>
    ensures result == narrow_isl(x)
{
    if fits_i64(x) {
        Some(x as i64)
    } else {
        None
    }
}
