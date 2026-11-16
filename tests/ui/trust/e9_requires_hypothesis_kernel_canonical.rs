//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: HELP
//! OR-A1 (owner ruling 2026-09-27), increments 0 and 1a — G1★, the
//! KERNEL-CANONICAL link, credited at `Trusted`.
//!
//! `keep` is probe r1's shape. Its clause is LIFTED (`(result as nat) == …`),
//! and before increment 0 the second rung could not even be built for it: the
//! ladder elaborated its conclusion in the strict mode and refused the cast, so
//! the build failed with "outside the exact statement fragment". The clause
//! names the island definition `spec`, so the solver lane cannot represent it
//! and its obligation is the `SpecEnsuresUnparseable` sentinel — NO other lane
//! proves this row, which is what makes the credit observable. The theorem
//! consumes `Nat.lt 0 (UInt64.toNat k)`, which IS the lifted reading of the
//! charged `k > 0` (`(k as nat) > 0`) up to definitional equality, so it proves
//! `G1★` and the credit takes the kernel-canonical link. The row is `Trusted`,
//! carries `clean-kernel-requires-canonical-citation` on the wire and no proof
//! evidence (pinned in `tests/run-make/trust-e9-requires-conditioned-citation`).
//!
//! `keep_positive` is probe r2's shape: the solver ALREADY proved the postcondition
//! row `Certified` (measured, r2.json.out), so the conditional credit installs
//! nothing (H2 — it never replaces a static proof) and the only change is that
//! the citation is valid and no longer a hard error.
//!
//! MEASURED on stage 1 (ora1-land, 2026-09-28): both of `keep`'s postcondition rows carry
//! `clean-kernel-requires-canonical-citation` with no evidence; `keep_positive`'s
//! rows keep `trust-exact-source-clause-discharge` / `trust-full-verifier`.

clean {
    def spec (n : Nat) : Nat := n
    theorem keep_spec : forall (k : UInt64),
        Nat.lt 0 (UInt64.toNat k) ->
        Eq (UInt64.toNat k) (spec (UInt64.toNat k)) :=
        fun k h => Eq.refl (UInt64.toNat k)
    theorem keep_pos_thm : forall (k : UInt64),
        Nat.lt 0 (UInt64.toNat k) ->
        Nat.lt 0 (UInt64.toNat k) :=
        fun k h => h
}

pub fn keep(k: u64) -> u64
//~^ NOTE discharged by a cited theorem proved UNDER this function's own
    requires k > 0
    ensures (result as nat) == spec(k as nat) by keep_spec
    //~^ NOTE but not unconditionally (requires-link: kernel-canonical)
    //~| NOTE these preconditions assumed: h0 = `k > 0` (`requires` #0)
    //~| NOTE creditable to the postcondition obligation at `Trusted`
{
    k
}

pub fn keep_positive(k: u64) -> u64
    requires k > 0
    ensures result > 0 by keep_pos_thm
    //~^ NOTE but not unconditionally (requires-link: kernel-canonical)
{
    k
}

fn main() {}
