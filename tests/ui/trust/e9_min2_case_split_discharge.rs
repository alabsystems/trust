//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-require-annotations: NOTE
//! E9: THE CANONICAL min2 DISCHARGE (design doc §3.1/§12.3 class). `min2` is
//! E6-admitted via the select recognizer; the clause's call resolves to its
//! kernel-imported defining equation (`Bool.rec` over the machine `<`
//! decision); and the cited theorem is a REAL case-split proof — dependent
//! `Bool.rec` elimination over the `Nat.ble` decision plus the prelude's
//! `Nat.le_of_ble_eq_true` bridge — far beyond rfl-trivial. The statement is
//! authored over the unfolded encoding (the imported constant is not in scope
//! at island-check time) and matches the elaborated goal by delta-reduction.
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
