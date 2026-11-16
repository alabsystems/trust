//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: HELP
//! OR-A1 (owner ruling 2026-09-27), increment 1a — H1, the MIXED surface, IN-WALK.
//!
//! A function whose `ensures` surface MIXES a cited clause and an uncited
//! island-defeq clause is discharged by the uncited lane, which receives the
//! cited half through `mixed_cited_part`. Before the rung was carried as data,
//! that hand-off was a bare theorem list and the uncited lane chose its label and
//! authority by the view marker alone — so a cited clause credited ONLY on the
//! allow-listed conditional rung came out as `EnsuresCitationDischarge`,
//! `Certified` (the critique's H1 scenario, this function verbatim).
//!
//! `eq_keep` proves `result == b` only under `requires a == b`, stated at the
//! machine carrier (`Eq a b`), so the cited half is credited on the ALLOW-LISTED
//! link. The uncited clause names the island definition `five` and
//! kernel-discharges by definitional equality. The row the citation lanes own —
//! the uncited clause's sentinel — must come out `Trusted` under
//! `clean-kernel-requires-allowlist-citation`, never `Certified` under
//! `clean-kernel-citation`. The cited clause's own row is proved by the solver
//! (as in `eqk`, probe c3) and keeps its `Certified` authority (H2); the wire
//! is pinned in `tests/run-make/trust-e9-requires-conditioned-citation`.
//!
//! The human-surface half of H1 is the annotation on `eqm`: the per-function
//! note naming rows discharged UNDER the function's own `requires` is read off
//! the SEALED authorities, so it appears only if the uncited lane sealed the
//! conditional variant — a row sealed `Certified` would not produce it.
//!
//! MEASURED on stage 1 (ora1-land, 2026-09-28): `eqm`'s two citation-owned rows carry
//! `clean-kernel-requires-allowlist-citation` with no evidence; its other two
//! postcondition rows keep `trust-exact-source-clause-discharge` /
//! `trust-full-verifier`; no row carries `clean-kernel-citation`.

clean {
    def five (n : Nat) : Nat := n
    theorem eq_keep : forall (a : UInt64) (b : UInt64), Eq a b -> Eq a b :=
        fun a b h => h
}

pub fn eqm(a: u64, b: u64) -> u64
//~^ NOTE discharged by a cited theorem proved UNDER this function's own
    requires a == b
    ensures result == b by eq_keep
    //~^ NOTE but not unconditionally (requires-link: allow-listed)
    ensures (result as nat) == five(a as nat)
{
    a
}

fn main() {}
