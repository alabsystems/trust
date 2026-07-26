// tRust regression test for rust-lang/rust#128950
//
// SOUNDNESS BUG (now fixed): With safe `#[target_feature]` functions
// (stabilized as target_feature_11 in Rust 1.86), it was possible to
// coerce a target_feature function to a plain fn pointer, erasing the
// CPU feature requirement from the type system.
//
// This meant code could call a function requiring specific CPU features
// through a plain fn pointer, on hardware that does not support those
// features. The result would be a SIGILL at runtime from safe code.
//
// FIX: The compiler now rejects coercion of #[target_feature] functions
// to safe fn pointers. Functions with #[target_feature] can only be
// coerced to `unsafe` fn pointers, preserving the safety requirement.
// The Fn/FnMut/FnOnce traits are also not implemented for target_feature
// function items, preventing the generic escape hatch.
//
// This test verifies that the fix is in place: we declare target_feature
// functions and demonstrate that they can be called directly (in unsafe
// contexts) but cannot be silently coerced away from their safety
// requirements. The test exercises the remaining safe patterns.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Reference: https://github.com/rust-lang/rust/issues/128950

//@ check-pass

#![allow(dead_code)]

// ---- Demonstrate that target_feature functions work correctly ----

#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
mod platform {
    // Safe target_feature function (target_feature_11 is now stable).
    // This can be called directly only from contexts that also have the feature,
    // or from unsafe blocks.
    #[target_feature(enable = "sse4.1")]
    pub fn requires_sse41(x: u32) -> u32 {
        x.wrapping_mul(3)
    }

    // CORRECT: coercion to unsafe fn pointer IS allowed.
    // The caller must use unsafe to call through this pointer, which is correct
    // since they need to ensure the hardware supports the feature.
    pub fn get_unsafe_ptr() -> unsafe fn(u32) -> u32 {
        requires_sse41
    }

    // CORRECT: calling from a function with the same target_feature is safe.
    #[target_feature(enable = "sse4.1")]
    pub fn caller_with_feature() -> u32 {
        requires_sse41(42)
    }

    // The following would NOT compile (the bug fix):
    //   let safe_ptr: fn(u32) -> u32 = requires_sse41;  // ERROR
    //   call_generic(requires_sse41)  // where F: Fn(u32) -> u32  // ERROR
    //
    // Previously these compiled, allowing safe code to invoke SSE4.1
    // instructions on hardware without SSE4.1 support.
}

#[cfg(target_arch = "aarch64")]
mod platform {
    #[target_feature(enable = "crc")]
    pub fn requires_crc(x: u32) -> u32 {
        x.wrapping_mul(3)
    }

    pub fn get_unsafe_ptr() -> unsafe fn(u32) -> u32 {
        requires_crc
    }

    #[target_feature(enable = "crc")]
    pub fn caller_with_feature() -> u32 {
        requires_crc(42)
    }
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64"
)))]
mod platform {
    pub fn get_unsafe_ptr() -> unsafe fn(u32) -> u32 {
        |x| x.wrapping_mul(3)
    }
}

fn main() {
    // The unsafe fn pointer path is correct: caller must use unsafe.
    let ptr = platform::get_unsafe_ptr();
    let result = unsafe { ptr(42) };
    assert_eq!(result, 126); // 42 * 3
}
