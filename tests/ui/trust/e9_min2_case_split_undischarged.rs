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
    theorem min2_case : forall (x y : UInt64) (d : Bool),
        Eq Bool (Nat.ble (UInt64.toNat y) (UInt64.toNat x)) d ->
        Nat.le (UInt64.toNat (Bool.rec (fun _ => UInt64) y x (Bool.not d))) (UInt64.toNat x) :=
        fun x y d => Bool.rec
            (fun dd => Eq Bool (Nat.ble (UInt64.toNat y) (UInt64.toNat x)) dd ->
                Nat.le (UInt64.toNat (Bool.rec (fun _ => UInt64) y x (Bool.not dd))) (UInt64.toNat x))
            (fun h => Nat.le.refl (UInt64.toNat x))
            (fun h => Nat.le_of_ble_eq_true (UInt64.toNat y) (UInt64.toNat x) h)
            d
    theorem min2_le_left : forall (x y : UInt64),
        Nat.le (UInt64.toNat (Bool.rec (fun _ => UInt64) y x
            (Bool.not (Nat.ble (UInt64.toNat y) (UInt64.toNat x)))))
            (UInt64.toNat x) :=
        fun x y => min2_case x y (Nat.ble (UInt64.toNat y) (UInt64.toNat x))
            (Eq.refl Bool (Nat.ble (UInt64.toNat y) (UInt64.toNat x)))
}

pub fn min2(a: u64, b: u64) -> u64 { if a < b { a } else { b } }

pub fn caller(x: u64, y: u64) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete for
    //~| ERROR Trust strict verification failed for
    ensures min2(x, y) <= y by min2_le_left
    //~^ ERROR citation `min2_le_left`
{ x }

fn main() {}
