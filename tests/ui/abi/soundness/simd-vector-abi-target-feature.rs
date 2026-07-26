// tRust regression test for rust-lang/rust#116558
//
// SOUNDNESS BUG: The extern "C" ABI of SIMD vector types depends on which
// target features are enabled. A function compiled with `target_feature(enable = "avx")`
// will pass __m256 in YMM registers, but a function without AVX will pass it
// on the stack or in pairs of XMM registers. When one calls the other, the
// callee reads garbage because caller and callee disagree on the calling convention.
//
// This is unsound because safe Rust code can observe corrupted values without
// any unsafe block at the call site. The caller simply invokes a safe extern "C"
// function, and the data arrives corrupted.
//
// Status: upstream has a future-incompatibility lint `abi_unsupported_vector_types`
// but no hard error yet. tRust should reject this at compile time.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Reference: https://github.com/rust-lang/rust/issues/116558

//@ only-x86_64
//@ check-pass

#[cfg(target_arch = "x86_64")]
mod test_body {
    use std::arch::x86_64::*;

    // This function does NOT have AVX enabled. On x86_64 without AVX, __m256
    // may be passed as two __m128 chunks or on the stack.
    #[allow(improper_ctypes_definitions)]
    pub extern "C" fn callee_no_avx(_dummy: f32, x: __m256) -> __m256 {
        // The callee reads `x` according to its own ABI (no AVX).
        x
    }

    // This function HAS AVX enabled. It will pass __m256 in a single YMM register.
    #[target_feature(enable = "avx")]
    pub unsafe fn caller_with_avx() {
        let val: __m256 = _mm256_set1_ps(42.0);
        // BUG: caller passes `val` in YMM0 (AVX convention), but `callee_no_avx`
        // expects it via the non-AVX convention. The callee reads junk.
        //
        // This call is to a safe function -- no unsafe needed at call site -- yet
        // it produces undefined behavior due to ABI mismatch.
        let result = callee_no_avx(0.0, val);
        let _ = result;
    }
}

fn main() {
    // This test verifies the code compiles on x86_64. The actual ABI mismatch
    // would manifest as corrupted data at runtime on machines with AVX.
    // tRust should eventually reject this at compile time.
}
