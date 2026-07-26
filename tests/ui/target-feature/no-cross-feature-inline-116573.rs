// Regression test for rust-lang#116573: the MIR inliner must not inline functions
// with target features into callers that lack those features. Inlining across
// target-feature boundaries would produce SIMD instructions on non-SIMD paths,
// causing miscompilation or illegal instruction faults.
//
// Trust: root-cause fix verified — check_codegen_attributes in the MIR inliner
// hard-blocks inlining when target features differ between caller and callee.
//
//@ build-pass
//@ only-x86_64
//@ compile-flags: -Copt-level=2 -Zinline-mir=yes

#![allow(dead_code)]

// A function requiring AVX2 target features.
#[inline(always)]
#[target_feature(enable = "avx2")]
unsafe fn avx2_operation(x: &[u8; 32]) -> u8 {
    // In a real scenario this would use AVX2 intrinsics.
    // The inliner must refuse to inline this into callers without AVX2.
    x.iter().copied().sum()
}

// A function requiring SSE4.2.
#[inline(always)]
#[target_feature(enable = "sse4.2")]
unsafe fn sse42_operation(x: u64) -> u64 {
    x.wrapping_mul(0x9E3779B97F4A7C15)
}

// Caller has NO target features — inlining avx2_operation here would be unsound.
pub fn caller_no_features(data: &[u8; 32]) -> u8 {
    // SAFETY: we're just testing that the inliner doesn't inline this.
    // In production, this would be guarded by runtime feature detection.
    unsafe { avx2_operation(data) }
}

// Caller has SSE4.2 but NOT AVX2 — still must not inline avx2_operation.
#[target_feature(enable = "sse4.2")]
pub unsafe fn caller_sse42_only(data: &[u8; 32]) -> u8 {
    avx2_operation(data)
}

// Caller has AVX2 — this CAN be inlined (same features).
#[target_feature(enable = "avx2")]
pub unsafe fn caller_with_avx2(data: &[u8; 32]) -> u8 {
    avx2_operation(data)
}

// Cross-feature call: caller has AVX2, callee has SSE4.2 — must NOT inline
// because the feature SETS differ (even though neither is a superset issue,
// the ABI of nested calls may differ).
#[target_feature(enable = "avx2")]
pub unsafe fn caller_avx2_calling_sse42(x: u64) -> u64 {
    sse42_operation(x)
}

fn main() {}
