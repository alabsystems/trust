//@ probe-shape: CheckedArithmetic
//@ probe-expect: discharged
//@ probe-note: CHECKED-ARITHMETIC ADMISSION — `i64::checked_add` as a whole-body leaf.
//@ probe-note: At `-O` the call inlines to the overflow-flag diamond (CheckedBinaryOp +
//@ probe-note: field reads + switchInt + a cold_path hint on the overflow edge + the two
//@ probe-note: Option aggregates); the recognizer reads exactly that measured shape, the
//@ probe-note: facet gate admits it (no Assert — the flag BRANCHES, it never panics; the
//@ probe-note: cold_path callee arrives with the compiler intrinsic marker), and the mint
//@ probe-note: seeds the Int-bridge model (sign-case-match toInt64, fitsI64 guard,
//@ probe-note: ofInt64 re-embed) and defines the import as `trust_checked_checkedAdd64`
//@ probe-note: applied to the parameters. The island below states the SAME authored
//@ probe-note: model (the veripb client kernel's normative spelling), so
//@ probe-note: `result == cadd_isl(a, b)` closes by DELTA-DEFEQ: both sides unfold to
//@ probe-note: the same Bool.casesOn over the same stuck fitsI64 scrutinee. No Option
//@ probe-note: destructor appears anywhere — constructors and equality only.
clean {
    def key64 (v : BitVec 64) : Nat :=
        Nat.xor (BitVec.toNat v) 9223372036854775808
    def toInt64 (v : BitVec 64) : Int :=
        match Nat.ble 9223372036854775808 (key64 v) with
        | true  => Int.ofNat (Nat.sub (key64 v) 9223372036854775808)
        | false => Int.negSucc (Nat.sub 9223372036854775807 (key64 v))
    def i64Max : Int := 9223372036854775807
    def i64Min : Int := Int.neg 9223372036854775808
    def fitsI64 (x : Int) : Bool :=
        match Int.ble i64Min x with
        | true  => Int.ble x i64Max
        | false => false
    def ofInt64 (x : Int) : BitVec 64 :=
        match Int.ble (Int.ofNat 0) x with
        | true  => BitVec.ofNat 64 (Int.toNat x)
        | false => BitVec.ofNat 64 (Int.toNat (Int.add x (Int.ofNat 18446744073709551616)))
    def cadd_isl (a : BitVec 64) (b : BitVec 64) : Option (BitVec 64) :=
        match fitsI64 (Int.add (toInt64 a) (toInt64 b)) with
        | true  => some (ofInt64 (Int.add (toInt64 a) (toInt64 b)))
        | false => none
}
pub fn cadd(a: i64, b: i64) -> Option<i64>
    ensures result == cadd_isl(a, b)
{ a.checked_add(b) }
