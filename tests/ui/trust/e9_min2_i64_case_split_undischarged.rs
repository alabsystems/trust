//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! Falsification pair of `e9_min2_i64_case_split_discharge`: the
//! min2_i64_le_left theorem proves `min2_i64(x,y) <= x` — citing it on
//! `min2_i64(x, y) <= y` (a different proposition this proof does not
//! inhabit) must fail closed. The signed lane inherits the u64 pair's
//! discipline: a widened encoding never widens what a citation may claim.

clean {
    def key64 (v : BitVec 64) : Nat :=
        Nat.xor (BitVec.toNat v) 9223372036854775808
    theorem min2_i64_le_left : forall (x : BitVec 64) (y : BitVec 64),
        Nat.le (key64 (if Nat.lt (key64 x) (key64 y) then x else y)) (key64 x) :=
        fun x y => Decidable.casesOn
            (motive := fun (d : Decidable (Nat.lt (key64 x) (key64 y))) =>
                Nat.le (key64 (Decidable.casesOn (motive := fun _ => BitVec 64)
                    d (fun _ => y) (fun _ => x))) (key64 x))
            (Nat.decLt (key64 x) (key64 y))
            (fun h => Iff.mp (Nat.not_lt (key64 x) (key64 y)) h)
            (fun h => Nat.le.refl (key64 x))
}

pub fn min2_i64(a: i64, b: i64) -> i64 { if a < b { a } else { b } }

pub fn caller(x: i64, y: i64) -> i64
    //~^ ERROR Trust Level 0 safety verification incomplete for
    //~| ERROR Trust strict verification failed for
    ensures min2_i64(x, y) <= y by min2_i64_le_left
    //~^ ERROR citation `min2_i64_le_left`
{ x }

fn main() {}
