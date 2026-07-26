//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-require-annotations: NOTE
//! E9 slice-3: MULTI-CLAUSE discharge under the conjunction rule. Both ensures
//! clauses are cited and both citations Certified-grade against their goals, so
//! the conjunction of the postcondition surface is kernel-proven and every
//! clause obligation discharges. The paired negative shows that PARTIAL
//! citation (or a single grade miss) discharges NOTHING.

clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}

pub fn two(x: u64) -> u64
    ensures x >= x by u64_ge_refl
    ensures x <= x by u64_ge_refl
{ x }

fn main() {}
