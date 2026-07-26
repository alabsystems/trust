// tRust regression test for rust-lang/rust#131282
//
// SOUNDNESS BUG: On Windows x86_64, __m128 (and other SSE vector types)
// are sometimes passed in the wrong register class or memory location.
// The Windows x64 calling convention has specific rules for __m128:
//
// - First 4 parameters: __m128 goes in XMM0-XMM3 (the floating-point/
//   vector registers), NOT in RCX/RDX/R8/R9 (the integer registers).
// - Beyond 4 parameters: __m128 is passed by reference on the stack.
// - Return value: __m128 is returned in XMM0.
//
// The bug: rustc does not always follow these rules correctly. In some
// cases, __m128 values are passed in integer registers (which truncates
// them to 64 bits, losing half the data) or are not properly aligned on
// the stack. This produces silent data corruption when calling across
// FFI boundaries or between functions with different target features.
//
// The issue is Windows-specific because the Windows x64 ABI differs from
// the System V AMD64 ABI used on Linux/macOS. System V passes __m128 in
// XMM registers more consistently, while Windows has the 4-register rule
// with stack fallback that rustc mishandles.
//
// Status: open upstream. Affects all Windows x86_64 targets.
//
// tRust must ensure correct vector register allocation for __m128/__m256
// types on the Windows x64 ABI.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Reference: https://github.com/rust-lang/rust/issues/131282

//@ only-x86_64
//@ check-pass

#![allow(dead_code)]

#[cfg(target_arch = "x86_64")]
mod test_body {
    use std::arch::x86_64::*;

    // Demonstrate the calling convention shape for __m128 on Windows.
    // On Windows x64: first 4 params in XMM0-3 (for float/vector), rest on stack.
    // On System V: first 8 vector params in XMM0-7.

    // 1 vector param: should go in XMM0 on both ABIs.
    #[allow(improper_ctypes_definitions)]
    extern "C" fn one_m128(x: __m128) -> __m128 {
        x
    }

    // 4 vector params: on Windows, XMM0-XMM3. On System V, XMM0-XMM3.
    // The 4th parameter is the boundary case for Windows.
    #[allow(improper_ctypes_definitions)]
    extern "C" fn four_m128(a: __m128, b: __m128, c: __m128, d: __m128) -> __m128 {
        // BUG: On Windows, if the compiler incorrectly puts these in integer
        // registers, only the lower 64 bits survive. Adding them together
        // would produce wrong results.
        unsafe {
            let sum1 = _mm_add_ps(a, b);
            let sum2 = _mm_add_ps(c, d);
            _mm_add_ps(sum1, sum2)
        }
    }

    // 5 vector params: on Windows, the 5th should be passed by reference
    // on the stack (not in a register). This is where bugs are most common.
    #[allow(improper_ctypes_definitions)]
    extern "C" fn five_m128(
        a: __m128,
        b: __m128,
        c: __m128,
        d: __m128,
        e: __m128,
    ) -> __m128 {
        unsafe {
            let sum1 = _mm_add_ps(a, b);
            let sum2 = _mm_add_ps(c, d);
            let sum3 = _mm_add_ps(sum1, sum2);
            _mm_add_ps(sum3, e)
        }
    }

    // Mixed integer and vector parameters — this exercises the shadow
    // register space on Windows x64 (integer params use RCX/RDX/R8/R9
    // while vector params use XMM0-3 in the same positional slots).
    #[allow(improper_ctypes_definitions)]
    extern "C" fn mixed_int_m128(n: u64, v: __m128, m: u64) -> __m128 {
        // On Windows x64: n in RCX, v in XMM1 (position 2), m in R8.
        // BUG: compiler may put v in RDX (integer reg for position 2)
        // instead of XMM1.
        let _ = n;
        let _ = m;
        v
    }

    // Struct containing __m128 — passed by reference on Windows x64
    // for sizes > 8 bytes, but the compiler may inline it incorrectly.
    #[repr(C)]
    struct SimdPair {
        a: __m128,
        b: __m128,
    }

    #[allow(improper_ctypes_definitions)]
    extern "C" fn pass_simd_pair(pair: SimdPair) -> __m128 {
        unsafe { _mm_add_ps(pair.a, pair.b) }
    }

    pub fn run() {
        unsafe {
            let v1 = _mm_set_ps(1.0, 2.0, 3.0, 4.0);
            let v2 = _mm_set_ps(5.0, 6.0, 7.0, 8.0);

            // Single param
            let r = one_m128(v1);
            let mut result = [0.0f32; 4];
            _mm_storeu_ps(result.as_mut_ptr(), r);
            assert_eq!(result, [4.0, 3.0, 2.0, 1.0]);

            // Four params (Windows boundary)
            let zeros = _mm_setzero_ps();
            let r = four_m128(v1, v2, zeros, zeros);
            _mm_storeu_ps(result.as_mut_ptr(), r);
            // v1 + v2 + 0 + 0 = (4+8, 3+7, 2+6, 1+5) = (12, 10, 8, 6)
            assert_eq!(result, [12.0, 10.0, 8.0, 6.0]);

            // Five params (Windows stack spillover)
            let ones = _mm_set1_ps(1.0);
            let r = five_m128(v1, v2, zeros, zeros, ones);
            _mm_storeu_ps(result.as_mut_ptr(), r);
            // v1 + v2 + 0 + 0 + 1 = (13, 11, 9, 7)
            assert_eq!(result, [13.0, 11.0, 9.0, 7.0]);

            // Mixed integer and vector
            let r = mixed_int_m128(999, v1, 888);
            _mm_storeu_ps(result.as_mut_ptr(), r);
            assert_eq!(result, [4.0, 3.0, 2.0, 1.0]);

            // Struct with SIMD
            let pair = SimdPair { a: v1, b: v2 };
            let r = pass_simd_pair(pair);
            _mm_storeu_ps(result.as_mut_ptr(), r);
            assert_eq!(result, [12.0, 10.0, 8.0, 6.0]);
        }
    }
}

#[cfg(not(target_arch = "x86_64"))]
mod test_body {
    pub fn run() {
        // __m128 is x86_64-specific.
    }
}

fn main() {
    test_body::run();
}
