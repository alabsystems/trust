//@ probe-shape: GuardedNarrow
//@ probe-expect: discharged
//@ probe-flags: -O
//@ probe-note: GUARDED-NARROW ADMISSION — the body of veripb's `guard::narrow`, the
//@ probe-note: width-guard choke point all 16 soundness-path narrowing sites consume.
//@ probe-note: At `-O` the `&&` guard lowers to the conjunction diamond (2 cmps + 2
//@ probe-note: switchInts) whose arms are `Some(x as i64 (IntToInt))` and the promoted
//@ probe-note: `const Option::<i64>::None`; the recognizer reads exactly that measured
//@ probe-note: shape by EDGE-chasing (never block indices — the call-inlined form f57
//@ probe-note: permutes them), the facet gate admits it (an `IntToInt` cast is pure,
//@ probe-note: total, deterministic and panic-free — no Assert anywhere), and the mint
//@ probe-note: seeds `trunc128to64` + `narrowI128toI64` on top of the checked model at
//@ probe-note: widths 64 and 128, then defines the import as that constant applied to
//@ probe-note: the parameter.
//@ probe-note: The clause closes by DELTA-DEFEQ against the island's authored model:
//@ probe-note: both sides unfold to the same Bool.casesOn over the same stuck
//@ probe-note: `fitsI64 (toInt128 x)` scrutinee, with the same stuck
//@ probe-note: `BitVec.ofNat 64 (BitVec.toNat x)` payload. The model is TRUNCATION, not
//@ probe-note: a guarded identity, so the defining equation is exact on EVERY input —
//@ probe-note: including inputs the guard rejects. That is what pins the payload
//@ probe-note: direction: an in-range value stored as anything but its own truncation
//@ probe-note: would fail here. No Option destructor appears anywhere — constructors,
//@ probe-note: an island call, and equality only.
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
pub fn narrow(x: i128) -> Option<i64>
    ensures result == narrow_isl(x)
{
    if x >= i64::MIN as i128 && x <= i64::MAX as i128 {
        Some(x as i64)
    } else {
        None
    }
}
