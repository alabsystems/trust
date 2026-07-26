//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-require-annotations: NOTE
//! E6+E9 FLAGSHIP (two-language design §3.1): a program function used
//! DEFINITIONALLY inside a spec clause, verified end-to-end. `ident` is
//! E6-admissible (all four inferred facets), so its defining equation is
//! kernel-imported; the clause `ensures ident(x) >= ident(x)` elaborates with
//! the call resolved to that imported definition, and the cited theorem's
//! proof term typechecks against the goal by delta-reduction (`ident_def x ≡ x`).
//! The clause is OUTSIDE the solver fragment (its obligation is the
//! fail-closed `SpecEnsuresUnparseable` sentinel) — the kernel discharge is
//! the ONLY proof, and the build passes. The paired negative
//! (`e9_definitional_call_undischarged`) removes the citation and must fail.

clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}

pub fn ident(x: u64) -> u64 { x }

pub fn caller(x: u64) -> u64 ensures ident(x) >= ident(x) by u64_ge_refl { x }

fn main() {}
