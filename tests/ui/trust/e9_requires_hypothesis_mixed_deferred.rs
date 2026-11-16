//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: HELP
//! OR-A1 (owner ruling 2026-09-27), increment 1a — H1, the MIXED surface,
//! DEFERRED post-walk lane.
//!
//! The twin of `e9_requires_hypothesis_mixed.rs` whose island is DEFERRED past
//! the body walk: an island whose text names `trust_import_` defers the whole
//! authored suffix (`defer_island_suffix`, the same device
//! `tests/run-make/trust-e9-kernel-discharge-transport` uses), so the citation is
//! graded by `grade_pending_import_citation_goals` and discharged by
//! `apply_pending_import_citation_discharge` — a different environment and a
//! different install site from the in-walk lane. The rung must travel through
//! THIS lane too: the theorem list comes back with its link, the label and
//! strength are decided from it, and the sealed authority is the conditional
//! variant. A deferred lane that dropped the rung would seal the mixed
//! surface's rows `Certified`.
//!
//! MEASURED on stage 1 (ora1-land, 2026-09-28): the same row split as the in-walk twin —
//! two rows under `clean-kernel-requires-allowlist-citation`, no evidence, and no
//! `clean-kernel-citation` row.

clean {
    -- naming trust_import_ here defers the whole island suffix past the walk
    def five (n : Nat) : Nat := n
    theorem eq_keep : forall (a : UInt64) (b : UInt64), Eq a b -> Eq a b :=
        fun a b h => h
}

pub fn eqm_deferred(a: u64, b: u64) -> u64
//~^ NOTE discharged by a cited theorem proved UNDER this function's own
    requires a == b
    ensures result == b by eq_keep
    //~^ NOTE but not unconditionally (requires-link: allow-listed)
    ensures (result as nat) == five(a as nat)
{
    a
}

fn main() {}
