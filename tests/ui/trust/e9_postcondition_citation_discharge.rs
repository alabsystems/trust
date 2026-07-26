//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-require-annotations: NOTE
//! E9 DISCHARGE (two-language design; docs/design-notes/2026-07-15-e9-discharge-criterion.md):
//! a cited Clean island theorem PROVES a Rust postcondition end-to-end. The
//! `ensures x >= x by u64_ge_refl` clause on the E6-admissible leaf `identity`
//! elaborates to the goal `∀ x, Nat.le (toNat x) (toNat x)` — `result` bound to
//! the kernel-imported defining equation, ∀-closed over the parameters — and
//! the cited theorem's proof term is re-typechecked against exactly that goal
//! with a sorry/axiom-free transitive closure (`cert_meter::grade`). The
//! obligation is then kernel-certified: the build PASSES with no solver proof
//! of the clause. The paired negative (`e9_postcondition_citation_undischarged`)
//! is the SAME clause without the citation and must fail — the pass/fail delta
//! on the single `by` token is the load-bearing evidence.

clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}

pub fn identity(x: u64) -> u64 ensures x >= x by u64_ge_refl { x }

fn main() {}
