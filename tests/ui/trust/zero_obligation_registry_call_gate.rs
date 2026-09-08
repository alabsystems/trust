//@ needs-trust-verify
//@ build-pass
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib -Awarnings
//@ rustc-env:RUSTC_LOG=rustc_mir_transform::trust_verify=info
//! Production-path regression for the empty-result panic-free registry gate.
//!
//! `indirect` has no verifier result rows of its own, but its function-pointer
//! call is not authenticated totality evidence. It must therefore be refused
//! as registry authority. The leaf and its ordinary wrapper are the positive
//! controls: the leaf has no calls, and `leaf_wrapper` targets the exact leaf
//! identity registered earlier by the callee-first walk.
//!
//! The advisory policy lets the deliberately failing function remain in this
//! one compilation; it does not grant that function or the indirect wrapper
//! authority. Removing the fifth `all_calls_target_proven_panic_free`
//! conjunct flips the `indirect` trace below to `accepted=true`, so this test
//! is a mutation-sensitive check of the production decision rather than only
//! of its pure boolean helper.

#![allow(dead_code)]

#[inline(never)]
pub fn failing() {
    panic!("deliberate failing function-pointer target");
}

#[inline(never)]
pub fn indirect(target: fn()) {
    target();
}

#[inline(never)]
pub fn leaf() {}

#[inline(never)]
pub fn leaf_wrapper() {
    leaf();
}
