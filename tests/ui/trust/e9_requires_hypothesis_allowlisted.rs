//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: HELP
//! OR-A1 (owner ruling 2026-09-27), increment 1a — the ALLOW-LISTED link,
//! credited at `Trusted`, and H2: a conditional credit never demotes a row the
//! solver already proved `Certified`.
//!
//! `eqk` is probe r5's shape. The theorem consumes `Eq a b` at `UInt64` — the
//! Clean machine-carrier reading of `a == b` — while the lifted reading callers
//! are charged is `Eq Nat (UInt64.toNat a) (UInt64.toNat b)`. The two are
//! different terms (and not definitionally equal), so the theorem proves `G1`
//! and not `G1★`: the link is `allow-listed`. MEASURED (probe c3, the uncited
//! twin): the solver lane already proves this postcondition row, `Certified`
//! with `clean-cic` evidence. The conditional credit therefore installs NOTHING
//! on it — the row keeps its `KernelCertified` authority and its publishable
//! evidence (pinned in `tests/run-make/trust-e9-requires-conditioned-citation`),
//! and the citation is merely valid instead of a hard error.
//!
//! `eqk_five` is the same precondition with a clause the solver lane cannot
//! represent (it names the island definition `five`), so its only prover is the
//! citation: the conditional credit IS installed there, `Trusted`, on the
//! allow-listed link, under `clean-kernel-requires-allowlist-citation`.
//!
//! MEASURED on stage 1 (ora1-land, 2026-09-28): `eqk`'s postcondition rows keep
//! `trust-exact-source-clause-discharge` and `trust-full-verifier` (with
//! evidence) and none carries a `clean-kernel-requires-*` label; both of
//! `eqk_five`'s postcondition rows carry
//! `clean-kernel-requires-allowlist-citation` with no evidence. `congrArg`
//! resolves in the Clean prelude.

clean {
    def five (n : Nat) : Nat := n
    theorem eq_keep : forall (a : UInt64) (b : UInt64), Eq a b -> Eq a b :=
        fun a b h => h
    theorem eq_five : forall (a : UInt64) (b : UInt64),
        Eq a b -> Eq (UInt64.toNat a) (five (UInt64.toNat b)) :=
        fun a b h => congrArg UInt64.toNat h
}

pub fn eqk(a: u64, b: u64) -> u64
    requires a == b
    ensures result == b by eq_keep
    //~^ NOTE but not unconditionally (requires-link: allow-listed)
    //~| NOTE requires-link: allow-listed — the theorem consumes the Clean
    //~| HELP state each hypothesis over the lifted carrier
{
    a
}

pub fn eqk_five(a: u64, b: u64) -> u64
//~^ NOTE discharged by a cited theorem proved UNDER this function's own
//~| NOTE an allow-listed link rests on the arithmetic-free allow-list
    requires a == b
    ensures (result as nat) == five(b as nat) by eq_five
    //~^ NOTE but not unconditionally (requires-link: allow-listed)
    //~| NOTE creditable to the postcondition obligation at `Trusted`
    //~| HELP state each hypothesis over the lifted carrier
{
    a
}

fn main() {}
