//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! Falsification pair of `e9_min2_case_split_discharge`: the min2_le_left
//! theorem proves `min2(x,y) <= x` — citing it on `min2(x, y) <= y` (a
//! different proposition this proof does not inhabit) must fail closed.

clean {
    theorem min2_le_left : forall (x : UInt64) (y : UInt64),
        Nat.le (UInt64.toNat (if x < y then x else y)) (UInt64.toNat x) :=
        fun x y => Decidable.casesOn
            (motive := fun (d : Decidable (LT.lt x y)) =>
                Nat.le (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64)
                    d (fun _ => y) (fun _ => x))) (UInt64.toNat x))
            (instDecidableUInt64Lt x y)
            (fun h => Iff.mp (Nat.not_lt (UInt64.toNat x) (UInt64.toNat y)) h)
            (fun h => Nat.le.refl (UInt64.toNat x))
}

pub fn min2(a: u64, b: u64) -> u64 { if a < b { a } else { b } }

pub fn caller(x: u64, y: u64) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete for
    //~| ERROR Trust strict verification failed for
    ensures min2(x, y) <= y by min2_le_left
    //~^ ERROR citation `min2_le_left`
{ x }

fn main() {}
