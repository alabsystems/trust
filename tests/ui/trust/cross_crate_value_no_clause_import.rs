//@ needs-trust-verify
//@ aux-build:cross_crate_value_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-bundle-foreign-crate=trust_xcbundle_dep
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! **ARM 5 — THE SOUNDNESS PIN FOR THE VALUE LANE. A foreign `ensures` is
//! RE-DERIVED, never ASSUMED, even now that the caller may assume the ones that
//! re-derive. This test must fail, and if it ever passes the lane is unsound.**
//!
//! `cross_crate_bundle_scope_no_clause_import.rs` is the same pin for the lane
//! that only reads BYTES. This one is stronger, because the thing it refuses is
//! now something the compiler otherwise DOES: arm 4 shows a foreign `ensures`
//! reaching a caller as an assumed fact. The question this arm settles is
//! whether the compiler can tell the two clauses apart.
//!
//! # The construction, and why both calls are in one body
//!
//! `trust_xcbundle_dep::overclaims` declares `ensures result <= 3` over a body
//! that returns `k` for every `k <= 31`, so `overclaims(10) == 10`. The clause is
//! FALSE of the code and the aux crate is compiled `-Ztrust-verify=off`, so
//! nothing that produced it has ever checked the clause.
//! `trust_xcbundle_dep::clamp_index` declares `result <= 31`, which is TRUE of
//! its body.
//!
//! `need_three` calls BOTH, on purpose. A blanket refusal — the lane switched
//! off, the crate mis-bucketed, the query answering `None` for every foreign key
//! — would also make this arm fail, and would look identical from the exit code.
//! With both calls in one body the run must show the compiler REFUSING one
//! callee and MINTING the other:
//!
//! ```text
//! TRUST_COMPOSE_DEBUG=1
//!   ... callee=trust_xcbundle_dep::clamp_index ... verdict=mint
//!   ... callee=trust_xcbundle_dep::overclaims  ... verdict=verdict:not-accounted
//! ```
//!
//! `verdict:not-accounted` is the assumption-root gate reading a re-derivation
//! this compilation performed: `overclaims`' own `Postcondition` row does not
//! discharge, so `has_nonzero_accounted_static_proof_under_own_requires` refuses
//! and the clause is never minted as reusable. That is the whole claim — the
//! refusal is a fact this compilation established about the callee's body, not
//! a policy that declined to look.
//!
//! Grading this arm on its exit code alone is a pass for the wrong reason.
//!
//! A sealed cross-compilation postcondition token was built once, in
//! `PostconditionAuthority`, and removed the same afternoon as a "forgeable
//! callee proof mint". `TrustProofResults` still derives
//! `TyEncodable`/`TyDecodable`/`StableHash`, and `trust_proof_results` is kept
//! `arena_cache`-only for exactly this reason. Do not add
//! `separate_provide_extern` or `cache_on_disk` to it. This test is the thing
//! that would notice.
extern crate trust_xcbundle_dep;

pub fn need_three(k: u8) -> u8 ensures result <= 3 {
    // The honest callee, whose clause DOES re-derive. Its `+ 0` keeps the
    // binding live without adding a second failure mode.
    let honest = trust_xcbundle_dep::clamp_index(3);
    if honest > 31 {
        return 0;
    }
    // The overclaiming callee. Its clause must NOT reach this body.
    trust_xcbundle_dep::overclaims(k)
}
