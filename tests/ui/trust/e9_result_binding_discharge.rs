//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-require-annotations: NOTE
//! E9: a RESULT-MENTIONING postcondition discharged by citation. The discharge
//! criterion binds `result` to the E6-imported defining equation of the
//! specified function — `ensures result >= x` elaborates to
//! `∀ x, identity_def(x) >= x`, which delta-reduces to `∀ x, x >= x` — so the
//! reflexivity theorem proves it. This is exactly the statement the
//! postcondition VC needs (NOT the generally-false `∀ result x, result >= x`
//! that a naive ∀-closure over `result` would produce; see the design note's
//! result-universal falsification case).

clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}

pub fn identity(x: u64) -> u64 ensures result >= x by u64_ge_refl { x }

fn main() {}
