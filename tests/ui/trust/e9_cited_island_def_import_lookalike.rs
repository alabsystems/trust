//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: ERROR
//! HIJACK NEGATIVE of `e9_cited_island_def_discharge`: the cited clause names a
//! look-alike of the compiler's kernel-import namespace. `trust_import_*` is
//! where the compiler mints the E6 defining equation of a Rust `fn`; an island
//! definition spelled into it could stand in for a function's import and be
//! "proved" about instead of the real body.
//!
//! Now that a CITED clause may name an island definition, this spelling has a
//! new place to be tried, so it is pinned here. It stays refused twice over,
//! and neither refusal is this lane's to relax:
//!  1. the island batch is rejected for declaring into the reserved namespace
//!     (`strict_leaf_policy_error`), which taints the session — a tainted
//!     session has no environment, so the cited lanes admit nothing;
//!  2. independently, `admit_certified_island_definition` refuses any
//!     `trust_import_*` name as a reflected carrier (I2), whatever table it is
//!     handed (pinned at the unit level in `trust-certify`).
//! The body really is `wadd`-shaped, so nothing but the namespace is wrong.
//!
//! `dont-require-annotations: ERROR` tolerates only the secondary
//! strict-verification errors; both primary refusals are pinned below.

// The annotation sits OUTSIDE the island (its text belongs to the Clean parser,
// where `//` is not a comment) and points up at the offending `def`.
clean {
    def trust_import_lookalike__spec (a b : UInt64) : UInt64 := a + b
    theorem lookalike_self : forall (a b : UInt64),
        trust_import_lookalike__spec a b = trust_import_lookalike__spec a b := fun a b => rfl
}
//~^^^^ ERROR declares into the compiler's kernel-import namespace

pub fn add2(a: u64, b: u64) -> u64
    //~^ ERROR Trust strict verification failed for
    ensures result == trust_import_lookalike__spec(a, b) by lookalike_self
    //~^ ERROR citation `lookalike_self` cannot be validated because an earlier Clean island was rejected
{
    a.wrapping_add(b)
}

fn main() {
    let _ = add2(1, 2);
}
