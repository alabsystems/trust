// tRust regression test for rust-lang/rust#114005
//
// SOUNDNESS BUG: Closures defined inside a function with #[target_feature]
// inherit the target feature for code generation but NOT for their calling
// convention. This creates an ABI mismatch: the closure body is compiled
// with, say, AVX enabled (so it may use wider registers for SIMD types),
// but its function pointer / Fn trait implementation uses the base ABI
// without AVX.
//
// When the closure captures SIMD-sized values or receives them as arguments,
// the caller and callee disagree on how those values are passed — the
// caller uses the base ABI (smaller registers, stack) while the callee
// expects the AVX ABI (wider registers). This results in silent data
// corruption.
//
// The issue is subtle because closures are not functions — they don't have
// an explicit ABI annotation. Their calling convention is determined by the
// compiler, which doesn't account for the inherited target_feature from
// the enclosing function.
//
// Status: open upstream. Affects any closure inside #[target_feature] fn
// that handles types whose ABI is feature-dependent (SIMD vectors, large
// structs passed in registers).
//
// tRust must ensure closures inherit the correct calling convention from
// their enclosing target_feature context.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Reference: https://github.com/rust-lang/rust/issues/114005

//@ check-pass

#![allow(dead_code)]

// Demonstrate the pattern on x86_64 with SSE2 (universally available).
// The real bug manifests with AVX/AVX-512 and __m256/__m512 types,
// but we demonstrate the structural pattern without requiring AVX hardware.

#[cfg(target_arch = "x86_64")]
mod test_body {
    // A function with target_feature. Closures defined inside it inherit
    // the feature for codegen but not for their calling convention ABI.
    #[target_feature(enable = "sse4.1")]
    unsafe fn with_feature() -> u32 {
        // This closure inherits SSE4.1 for code generation.
        // BUG: its Fn impl uses the base calling convention.
        let process = |x: u32, y: u32| -> u32 {
            x.wrapping_add(y)
        };

        // When this closure is called through Fn trait (e.g., passed to
        // a generic function), the caller uses base ABI, but the closure
        // body was compiled with SSE4.1 ABI assumptions.
        call_with_fn(process)
    }

    // A generic function that calls through Fn trait — no target_feature.
    // It uses the base calling convention to invoke `f`.
    fn call_with_fn(f: impl Fn(u32, u32) -> u32) -> u32 {
        f(10, 20)
    }

    // The pattern also applies to closures that capture data.
    #[target_feature(enable = "sse4.1")]
    unsafe fn with_capture() -> u32 {
        let base: u32 = 100;
        // This closure captures `base` and inherits SSE4.1.
        let add_base = |x: u32| x.wrapping_add(base);
        call_with_fn_unary(add_base)
    }

    fn call_with_fn_unary(f: impl Fn(u32) -> u32) -> u32 {
        f(42)
    }

    // FnMut closures have the same issue.
    #[target_feature(enable = "sse4.1")]
    unsafe fn with_fnmut() -> u32 {
        let mut acc: u32 = 0;
        let mut accumulate = |x: u32| {
            acc = acc.wrapping_add(x);
            acc
        };
        call_with_fnmut(&mut accumulate);
        acc
    }

    fn call_with_fnmut(f: &mut impl FnMut(u32) -> u32) -> u32 {
        f(1) + f(2) + f(3)
    }

    pub fn run() {
        // SAFETY: We don't actually use SSE4.1 intrinsics in the closures,
        // so this is safe to call for testing purposes.
        unsafe {
            let result = with_feature();
            assert_eq!(result, 30);

            let result = with_capture();
            assert_eq!(result, 142);

            let result = with_fnmut();
            assert_eq!(result, 6); // 1 + 2 + 3
        }
    }
}

#[cfg(not(target_arch = "x86_64"))]
mod test_body {
    pub fn run() {
        // Pattern not applicable on this architecture.
    }
}

fn main() {
    test_body::run();
}
