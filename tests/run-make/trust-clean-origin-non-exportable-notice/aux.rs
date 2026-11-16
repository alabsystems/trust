//! **Non-exportable notice, transport control — the DEFINING library.**
//!
//! `countdownSum` is well-founded (`tests/ui/trust/clean_origin_wf_rec.rs`'s
//! declaration, verbatim). The local gate admits its emitted body by
//! `WellFoundedFunctionalDefeq`, an evidence form the certificate wire format
//! deliberately has no tag for, so this crate's export provider writes a
//! non-exportable NOTICE in the `trust_clean_verdict_digest` row where a
//! certificate would go (`crates/trust-clean-origin/src/export_notice.rs`).
//! Before 2026-09-16 that same boundary was a FATAL here, and this file did
//! not build as a library at all.
//!
//! `triangle` is the supported cross-crate surface: an ordinary, non-generic
//! Rust `fn` without `#[inline]`, compiled in THIS crate where the sole
//! constructor gated `countdownSum`'s body.
//!
//! Do NOT spell either four-byte wire magic in this file: doc comments are
//! encoded into the rmeta, and `rmake.rs` asserts its locator scan finds the
//! notice row exactly once (the kernel-skew fixture measured that trap).

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
