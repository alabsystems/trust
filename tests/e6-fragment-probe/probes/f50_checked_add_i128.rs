//@ probe-shape: CheckedArithmetic
//@ probe-expect: discharged
//@ probe-note: f49 at the REAL width of the veripb checker's exact-arithmetic tier:
//@ probe-note: `i128::checked_add` returning `Option<i128>`. The Int-bridge model is what
//@ probe-note: makes this width free — the exact sum lives in unbounded `Int`, so there
//@ probe-note: is no 256-bit carrier and no new reducer; the pivot/re-embed literals
//@ probe-note: (2^127, 2^128) are the multi-limb numerals the BitVec.ofNat lift already
//@ probe-note: reduces. The island is byte-for-byte the client kernel's authored i128
//@ probe-note: model (toInt128/fitsI128/ofInt128/checkedAdd128 spelling), so the ensures
//@ probe-note: closes by delta-defeq against the seeded mint model exactly as f49.
clean {
    def key128 (v : BitVec 128) : Nat :=
        Nat.xor (BitVec.toNat v) 170141183460469231731687303715884105728
    def toInt128 (v : BitVec 128) : Int :=
        match Nat.ble 170141183460469231731687303715884105728 (key128 v) with
        | true  => Int.ofNat (Nat.sub (key128 v) 170141183460469231731687303715884105728)
        | false => Int.negSucc (Nat.sub 170141183460469231731687303715884105727 (key128 v))
    def i128Max : Int := 170141183460469231731687303715884105727
    def i128Min : Int := Int.neg 170141183460469231731687303715884105728
    def fitsI128 (x : Int) : Bool :=
        match Int.ble i128Min x with
        | true  => Int.ble x i128Max
        | false => false
    def ofInt128 (x : Int) : BitVec 128 :=
        match Int.ble (Int.ofNat 0) x with
        | true  => BitVec.ofNat 128 (Int.toNat x)
        | false => BitVec.ofNat 128 (Int.toNat (Int.add x (Int.ofNat 340282366920938463463374607431768211456)))
    def cadd128_isl (a : BitVec 128) (b : BitVec 128) : Option (BitVec 128) :=
        match fitsI128 (Int.add (toInt128 a) (toInt128 b)) with
        | true  => some (ofInt128 (Int.add (toInt128 a) (toInt128 b)))
        | false => none
}
pub fn cadd128(a: i128, b: i128) -> Option<i128>
    ensures result == cadd128_isl(a, b)
{ a.checked_add(b) }
