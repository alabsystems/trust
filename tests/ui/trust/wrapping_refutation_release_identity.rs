//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -O
//@ check-pass
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ normalize-stderr: "\n\n$" -> "\n"
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//@ normalize-stderr: "sha256:[0-9a-f]{64}" -> "sha256:$$DIGEST"
//@ normalize-stderr: "trust-mc@\d+\.\d+\.\d+" -> "trust-mc@$$ENGINE"
//! Release-mode identity pin for exact core wrapping calls outside the narrow
//! E6 import lane. Signed and pointer-sized add/sub remain available to the
//! full assertion-refutation model, while u128 remains a precise total
//! TrustIR operation even though the <=64-bit refutation model declines it.
//! If MIR inlining erases any of these authenticated call identities before
//! Trust verification, they become ordinary overflow-obligated arithmetic and
//! this strict `-O` fixture fails.
//!
//! RE-PIN 2026-08-15 — 1 proved -> 1 runtime-checked, caused by UPSTREAM
//! commit 983bc1a3b6 ("REMOVE the panic-freedom subsumption lane"), NOT by
//! anything on our side. That movement was strictly stronger: the compiler
//! REFUSED to credit a proof it used to credit, because the credit came from
//! `ResultProofAuthority::WholeFunctionPanicFreedomSubsumption`, minted over a
//! VACUOUSLY true premise conjunction (the aggregate was the sole row, so
//! `all()` ranged over the empty set) — exactly the false-proof shape upstream
//! 1ab7ee48f2 named and 983bc1a3b6 deleted. That deletion still stands (see
//! the "REMOVED (2026-08-14, FALSE PROOF)" marker in `trust_verify.rs`), and
//! the "1 proved" line below must NEVER be recovered by reviving it.
//!
//! RE-PIN 2026-08-18 — 1 runtime-checked -> 1 proved AND kernel-certified,
//! which is the honest close the previous re-pin named as the only acceptable
//! route. The row now carries `VerificationResult::Certified`: a clean CIC
//! kernel re-check with ZERO trust in the SMT solver, a STRICTLY STRONGER tier
//! than the solver-trusted `proved` the subsumption lane used to forge. The
//! two authorities are distinguishable in the stderr itself — the certified
//! tier prints "of which 1 kernel-certified by the clean CIC kernel", which
//! the deleted lane never could. If a future run restores "1 proved" WITHOUT
//! that note, treat it as the false proof returning and reject it.
//!
//! MEASURED on the stage2 built from 19403c8494 with this file's own
//! compile-flags: each function reports "1 proved, 0 failed, 0 unknown,
//! 0 timed out, 0 runtime-checked out of 1 obligation(s)" plus the
//! kernel-certified note. The cause is UPSTREAM again, and it is the named
//! follow-up arriving: 4309669255 dropped an unwanted ay proof-artifact
//! demand that had made the per-branch (case-split) certificate lane abstain
//! and decline EVERY certificate, and e7fd15b1e7 pinned clean/ay to the
//! array-ROW case-split wave. Attributed by ancestry, not by ablation.
//!
//! MECHANISM (unchanged — it is what this file exists to pin). Each of these
//! two functions lowers to exactly ONE compiler result row: the synthesized
//! `assertion:panic-freedom:0` aggregate (measured — the sibling
//! `trust_mc_default_function:0` is a default admission that returns
//! Unsupported, so it is never a counted row). `refute_full_assert_obligations`
//! proves the assert's panic path unreachable and re-points the aggregate at
//! the GROUNDED residual violation, and it fires only while the
//! `wrapping_add`/`wrapping_sub` call identities survive `-O`. If MIR inlining
//! erases those identities the calls become ordinary overflow-obligated
//! arithmetic, the grounded residual changes shape, and this strict `-O`
//! fixture fails — exactly the regression it is here to catch. Do NOT recover
//! a lost verdict by crediting the native trust-mc verdict: it is ChcValidity
//! (Chc/SmtBacked, not kernel-rechecked), which 983bc1a3b6 explicitly declined.

#![crate_type = "lib"]

pub fn signed_literal_roundtrip(x: i32) {
    assert!(x.wrapping_add(1).wrapping_sub(1) == x);
}

pub fn usize_roundtrip(x: usize, n: usize) {
    assert!(x.wrapping_add(n).wrapping_sub(n) == x);
}

pub fn u128_wrapping_is_total(x: u128, y: u128) -> u128 {
    x.wrapping_add(y)
}
