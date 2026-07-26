//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-require-annotations: NOTE
//! E9: a postcondition that constrains only a SUBSET of the parameters — or a
//! quantified clause referencing none of them — discharges. The elaborated goal
//! binds exactly the variables the clause uses (an unmentioned parameter is
//! unconstrained), so `p(x, y) ensures x >= x` and `h(x) ensures forall i, i>=i`
//! both bind exactly their free variables and the reflexivity/quantified
//! theorems prove them.

clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
    theorem all_ge_self : forall (i : UInt64),
        Nat.le (UInt64.toNat i) (UInt64.toNat i) :=
        fun i => Nat.le.refl (UInt64.toNat i)
}

pub fn p(x: u64, y: u64) -> u64 ensures x >= x by u64_ge_refl { x }

pub fn h(x: u64) -> u64 ensures forall i: u64, i >= i by all_ge_self { x }

fn main() {}
