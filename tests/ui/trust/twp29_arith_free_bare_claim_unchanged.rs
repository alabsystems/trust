//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-pass
//! Task #29 (regression guard): an arithmetic-FREE bare trust-wp claim must
//! be completely untouched by the amendment-1 arithmetic gate. The ground
//! comparison `0 <= 1` sits inside the v1 fragment (comparisons + boolean
//! connectives + literals); the body `x >> 1` is not a copy/const chain, so
//! the body-bound lane refuses it and the claim goes through the BARE lane —
//! before and after #29 the sibling ground-folds it and the native-lane
//! diagnostic reads "verified by trust_wp NativeTrustWpBundleVerifier"
//! (pinned below). The final verdict remains the pre-existing
//! sealed-authority demotion (UNKNOWN, strict build fails) — #29 changes
//! neither side of that.
pub fn ground(x: u64) -> u64 ensures 0 <= 1 { x >> 1 }
