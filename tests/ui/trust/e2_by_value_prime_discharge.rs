//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! E2 (two-language design: primes notation for post-state, no old()). A primed
//! post-state identifier `x'` for a BY-VALUE parameter denotes x's value in the
//! post-state — and a by-value binding is never reassigned across the call, so
//! `x'` is definitionally `x`. `ensures x' >= x` therefore discharges via the
//! reflexivity theorem exactly like `ensures x >= x`. The two-state `&mut`
//! semantics (a deref post-state that genuinely differs) remain fail-closed —
//! see the paired negative — and are the separate deep E2 lane.

clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}

pub fn keep(x: u64) -> u64 ensures x' >= x by u64_ge_refl { x }

fn main() {}
