// Calling a `#[target_feature]` function from a context that lacks those
// features is unsafe (rustc's `CallToFunctionWith`) — even when the callee is
// SAFE-signatured (target_feature_11). Trust must CATCH it fail-closed.
//   trustc --crate-type lib --edition 2021 target_feature_call_caught.rs
#![feature(target_feature_11)]
#![allow(dead_code)]

// A SAFE-signatured fn that requires the `neon` feature (aarch64).
#[target_feature(enable = "neon")]
fn neon_op(x: u64) -> u64 {
    x.wrapping_add(1)
}

/// Caller WITHOUT `neon`: calling `neon_op` is unsafe — must be CAUGHT
/// (`[unsafe:unmodeled-call] ... (target-feature)`).
pub fn caller_without_feature(x: u64) -> u64 {
    unsafe { neon_op(x) }
}

/// Caller WITH `neon`: calling `neon_op` is SAFE — must NOT be flagged.
#[target_feature(enable = "neon")]
pub fn caller_with_feature(x: u64) -> u64 {
    neon_op(x)
}
