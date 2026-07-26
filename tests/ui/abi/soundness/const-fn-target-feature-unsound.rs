// tRust regression test for rust-lang/rust#86232
//
// SOUNDNESS BUG: #[target_feature(enable = "...")] combined with const fn
// creates a soundness hole. The issue is that target_feature functions are
// unsafe because they may use CPU instructions that the current hardware
// does not support. However, const fn evaluation happens at compile time,
// where the target features of the runtime hardware are unknown.
//
// Scenarios:
//
// 1. A const fn marked with #[target_feature(enable = "avx2")] could be
//    evaluated at compile time by const eval, which does not check whether
//    the compilation target actually supports AVX2. The result could embed
//    values computed via AVX2 semantics into code running on hardware
//    without AVX2.
//
// 2. A target_feature const fn could be called in a const context (e.g.,
//    array length, enum discriminant) where the "unsafe" marker is the
//    only protection, but the unsafety is about runtime hardware support,
//    not about memory safety in the traditional sense.
//
// FIX: The compiler now forbids combining #[target_feature(enable = "...")]
// with const fn. This is enforced as a hard error: you cannot declare a
// function that is both const and has target_feature attributes, because
// const evaluation cannot guarantee the target features are available.
//
// This test verifies that the safe patterns still work:
// - Regular (non-const) functions with target_feature
// - Const functions without target_feature
// - Using target_feature results in non-const contexts
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Reference: https://github.com/rust-lang/rust/issues/86232

//@ check-pass

#![allow(dead_code)]

// ---- Safe pattern: const fn WITHOUT target_feature ----
// Pure computation in const fn is always fine.
const fn safe_const_computation(x: u32) -> u32 {
    x.wrapping_mul(7).wrapping_add(3)
}

const COMPUTED: u32 = safe_const_computation(42);

// ---- Safe pattern: target_feature WITHOUT const ----
// Runtime-only target_feature functions are correct: the caller must
// use unsafe and ensure hardware support.

#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
mod platform {
    #[target_feature(enable = "sse2")]
    pub unsafe fn feature_computation(x: u32) -> u32 {
        // In real code, this would use SSE2 intrinsics.
        // The safety contract is that the caller ensures SSE2 is available.
        x.wrapping_mul(11)
    }

    // Demonstrate that the result of a target_feature function can be
    // used at runtime (not const), which is the correct pattern.
    pub fn use_feature_at_runtime(x: u32) -> u32 {
        // SAFETY: SSE2 is universally available on x86_64.
        // On x86 (32-bit), the caller should check, but for this test
        // we compile for x86_64 where SSE2 is baseline.
        unsafe { feature_computation(x) }
    }

    // The following would NOT compile (the bug fix):
    //
    //   #[target_feature(enable = "avx2")]
    //   const fn unsound_const_with_feature(x: u32) -> u32 { x }
    //
    // ERROR: cannot use `#[target_feature]` on a `const fn`
    //
    // Previously this compiled, allowing const eval to produce results
    // that assumed hardware features which may not be present at runtime.
}

#[cfg(target_arch = "aarch64")]
mod platform {
    #[target_feature(enable = "neon")]
    pub unsafe fn feature_computation(x: u32) -> u32 {
        x.wrapping_mul(11)
    }

    pub fn use_feature_at_runtime(x: u32) -> u32 {
        // SAFETY: NEON is universally available on AArch64.
        unsafe { feature_computation(x) }
    }
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "x86", target_arch = "aarch64")))]
mod platform {
    pub fn use_feature_at_runtime(x: u32) -> u32 {
        x.wrapping_mul(11)
    }
}

fn main() {
    // Const evaluation (safe: no target_feature involved).
    assert_eq!(COMPUTED, 42_u32.wrapping_mul(7).wrapping_add(3));

    // Runtime target_feature usage (safe: correct calling convention).
    let result = platform::use_feature_at_runtime(10);
    assert_eq!(result, 110);
}
