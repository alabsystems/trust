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
pub fn caller(x: u64, y: u64) -> u64 ensures min2(x, y) <= x by min2_le_left { x }

fn main() {}
