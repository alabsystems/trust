// tRust regression test for rust-lang/rust#116344 (target_feature safety aspect)
// and related inlining unsoundness from rust-lang/rust#116573
//
// SOUNDNESS BUG: Functions with #[target_feature(enable = "...")] are marked
// as `unsafe` because calling them on hardware lacking the feature is UB.
// However, several holes exist:
//
// 1. When a function with target_feature is inlined (#[inline(always)]) into
//    a caller without that feature, the inlined code may use instructions the
//    hardware does not support, causing SIGILL at runtime.
//
// 2. Closures inside target_feature functions inherit the feature but can
//    escape the function and be called in a context without the feature.
//    The returned closure is safe to call despite containing code that
//    requires the target feature.
//
// 3. Function pointers to target_feature functions lose the safety
//    requirement, allowing calls without the feature check.
//
// These holes mean that target_feature does not actually provide the safety
// guarantee it claims: that code using special CPU features can only run on
// hardware that supports them.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Reference: https://github.com/rust-lang/rust/issues/116344
// Reference: https://github.com/rust-lang/rust/issues/116573

//@ check-pass

#![allow(dead_code)]

// Use cfg-gated target features to be platform-independent.
// The soundness holes exist on all architectures with target_feature support.

// ---- Hole 1: closures escaping target_feature context ----
//
// Closures defined inside a target_feature function inherit the feature.
// But they can be returned and called from a context without the feature.
// The returned closure is safe to call despite potentially containing
// feature-dependent instructions.
//
// Note: #[inline(always)] + #[target_feature] is now rejected (rust#145574),
// which partially addresses rust#116573. However, the closure escape hole
// and function pointer coercion hole remain.

#[cfg(target_arch = "aarch64")]
mod platform {
    #[target_feature(enable = "crc")]
    pub unsafe fn feature_fn(x: u32) -> u32 {
        // In real code, this would use CRC32 intrinsics.
        x.wrapping_mul(7)
    }

    #[target_feature(enable = "crc")]
    pub unsafe fn make_closure() -> impl Fn() -> u32 {
        // This closure inherits target_feature(enable = "crc") from its
        // enclosing function.
        || 99
    }
}

#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
mod platform {
    #[target_feature(enable = "sse4.1")]
    pub unsafe fn feature_fn(x: u32) -> u32 {
        x.wrapping_mul(7)
    }

    #[target_feature(enable = "sse4.1")]
    pub unsafe fn make_closure() -> impl Fn() -> u32 {
        || 99
    }
}

#[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64", target_arch = "x86")))]
mod platform {
    pub unsafe fn feature_fn(x: u32) -> u32 {
        x.wrapping_mul(7)
    }
    pub unsafe fn make_closure() -> impl Fn() -> u32 {
        || 99
    }
}

// ---- Hole 2: closures escaping target_feature context ----
//
// The returned closure inherits target_feature from its enclosing function,
// but the caller of the closure has no such feature. The closure call is
// safe (not marked unsafe), yet may contain feature-dependent instructions.
fn call_escaped_closure() -> u32 {
    let closure = unsafe { platform::make_closure() };
    // This call is NOT unsafe, even though the closure inherited a
    // target_feature requirement. If hardware lacks the feature, this is UB.
    closure()
}

fn main() {
    let _ = call_escaped_closure();
}
