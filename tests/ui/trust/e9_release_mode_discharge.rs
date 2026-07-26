//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -O
//@ check-pass
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! RELEASE-MODE discharge: the same min2 case-split citation as
//! `e9_min2_case_split_discharge`, compiled under `-O`. The optimizer reshapes
//! the select lowering (branches assign the return place directly; bare-return
//! join) — the recognizer accepts both spellings, so admissions and discharges
//! survive release builds. A program must never verify in debug and fail in
//! release.

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

pub fn caller(x: u64, y: u64) -> u64 ensures min2(x, y) <= x by min2_le_left { x }

fn main() {}
