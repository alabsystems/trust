//@ no-prefer-dynamic
//@ compile-flags: -Z trust-verify=off
#![crate_type = "rlib"]

//! **A LIBRARY crate that DEFINES a well-founded-recursive Clean def.**
//!
//! Before 2026-09-16 this file did not build at all: the rmeta encoder demands
//! a `trust_clean_verdict_digest` row for EVERY local Clean-origin def, the
//! certificate wire has (deliberately) no tag for
//! `FaithfulnessMethod::WellFoundedFunctionalDefeq`, and the export provider
//! answered that known boundary with
//! `error: internal: refusing to export a certificate for Clean declaration …`
//! — after the local gate had ADMITTED the def (wf1 probes 36b/36d/18b/18c).
//! Recursion was bin-crate-only.
//!
//! The provider now writes a non-exportable NOTICE in the certificate's place
//! (`crates/trust-clean-origin/src/export_notice.rs`): this crate builds, and
//! the two downstream fixtures pin what may and may not happen next —
//!
//! * `clean_origin_wf_lib_wrapper_call.rs` calls `triangle`, an ORDINARY Rust
//!   `fn` compiled HERE, where the sole constructor gated `countdownSum`'s
//!   body. It builds and runs.
//! * `clean_origin_wf_lib_direct_call_refused.rs` calls `m::countdownSum`
//!   itself. No certificate crossed, so the importer's readmission chokepoint
//!   refuses with the notice's v7/D3 note.
//!
//! `pub mod m` on purpose: a private module would stop the negative fixture at
//! E0603 before the chokepoint (`clean_origin_cross_crate_private_mod.rs` pins
//! that path); the point here is a def downstream CAN name and still cannot
//! call. `countdownSum` is `clean_origin_wf_rec.rs`'s declaration, verbatim.
//!
//! `triangle` is deliberately non-generic and carries no `#[inline]`: a
//! wrapper whose MIR travels is instantiated downstream and lands on the same
//! refusal, which is what the refusal's first option says.

extern crate trust_bignum;

pub mod m {
    clean {
        def countdownSum (n : Nat) : Nat := if h : 0 < n then n + countdownSum (n - 1) else 0
        termination_by n
    }
}

pub fn triangle(n: u64) -> Option<u64> {
    m::countdownSum(trust_bignum::Nat::from_u64(n)).to_u64()
}
