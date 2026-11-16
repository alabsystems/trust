// The CITED sibling (`by <theorem>`), the same transport defect measured on
// `tests/ui/trust/e2_by_value_prime_discharge.rs`: `clean-kernel-citation`
// rows were transported `unknown`.
#![allow(dead_code)]
clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}

pub fn keep(x: u64) -> u64
    ensures x' >= x by u64_ge_refl
{
    x
}
