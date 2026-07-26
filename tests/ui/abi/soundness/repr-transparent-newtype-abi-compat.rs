// tRust regression test for rust-lang/rust#122206
//
// SOUNDNESS BUG: #[repr(transparent)] newtypes do not always have ABI
// compatibility with their inner type in function signatures. The Rust
// Reference guarantees that repr(transparent) types have the same layout
// as their single non-ZST field, and this guarantee is supposed to extend
// to function call ABI. However, in practice the compiler sometimes
// generates different calling conventions for the wrapper and the inner
// type.
//
// The concrete manifestation: given `#[repr(transparent)] struct W(T)`,
// an `extern "C" fn(W) -> W` should pass/return W identically to
// `extern "C" fn(T) -> T`. But on some targets, W is passed indirectly
// (via pointer) while T is passed directly (in a register), or vice versa.
// This breaks transmute-based FFI patterns that rely on the transparency
// guarantee.
//
// The issue is distinct from #115404 (which focuses on specific tier-2
// targets). #122206 documents cases where the mismatch occurs even on
// tier-1 targets with certain type combinations, particularly:
// - Single-field structs wrapping SIMD types
// - Newtypes around multi-element arrays
// - Newtypes around unions
//
// Status: open upstream. The fix requires the ABI computation to
// consistently look through repr(transparent) wrappers.
//
// tRust must ensure repr(transparent) ABI equivalence as a hard invariant
// across all function signatures.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Reference: https://github.com/rust-lang/rust/issues/122206

//@ check-pass

#![allow(dead_code, improper_ctypes_definitions)]

// ---- Basic newtype patterns ----

#[repr(transparent)]
struct WrapU64(u64);

#[repr(transparent)]
struct WrapF64(f64);

// Nested transparency: the outermost wrapper should still be ABI-compatible
// with the innermost type.
#[repr(transparent)]
struct WrapWrapU64(WrapU64);

// ---- Newtypes around compound types ----

#[repr(transparent)]
struct WrapArray([u8; 16]);

#[repr(transparent)]
struct WrapPair((u64, u64));

// Newtype around a union — rare but legal with repr(transparent).
#[repr(C)]
union IntOrFloat {
    i: u64,
    f: f64,
}

#[repr(transparent)]
struct WrapUnion(IntOrFloat);

// ---- extern "C" functions: wrapper and inner type should have identical ABI ----

extern "C" fn pass_u64(x: u64) -> u64 {
    x.wrapping_add(1)
}

extern "C" fn pass_wrap_u64(x: WrapU64) -> WrapU64 {
    WrapU64(x.0.wrapping_add(1))
}

extern "C" fn pass_f64(x: f64) -> f64 {
    x + 1.0
}

extern "C" fn pass_wrap_f64(x: WrapF64) -> WrapF64 {
    WrapF64(x.0 + 1.0)
}

// Doubly-wrapped: should still match u64 ABI.
extern "C" fn pass_wrap_wrap_u64(x: WrapWrapU64) -> WrapWrapU64 {
    WrapWrapU64(WrapU64((x.0).0.wrapping_add(1)))
}

extern "C" fn pass_array(x: [u8; 16]) -> [u8; 16] {
    let mut result = x;
    result[0] = result[0].wrapping_add(1);
    result
}

extern "C" fn pass_wrap_array(x: WrapArray) -> WrapArray {
    let mut result = x.0;
    result[0] = result[0].wrapping_add(1);
    WrapArray(result)
}

// ---- Function pointers: transmuting between wrapper and inner fn types ----
// This is the pattern that breaks when ABI diverges.

type FnU64 = extern "C" fn(u64) -> u64;
type FnWrapU64 = extern "C" fn(WrapU64) -> WrapU64;

fn exercise_fn_ptr_equivalence() {
    // If repr(transparent) ABI guarantee holds, these function pointers
    // should be interchangeable. The bug is that they aren't always.
    let fn_u64: FnU64 = pass_u64;
    let fn_wrap: FnWrapU64 = pass_wrap_u64;

    let r1 = fn_u64(41);
    let r2 = fn_wrap(WrapU64(41));
    assert_eq!(r1, r2.0);
}

fn main() {
    // Exercise the extern "C" paths.
    let r1 = pass_u64(99);
    let r2 = pass_wrap_u64(WrapU64(99));
    assert_eq!(r1, r2.0);

    let r3 = pass_f64(1.5);
    let r4 = pass_wrap_f64(WrapF64(1.5));
    assert_eq!(r3, r4.0);

    let r5 = pass_u64(99);
    let r6 = pass_wrap_wrap_u64(WrapWrapU64(WrapU64(99)));
    assert_eq!(r5, (r6.0).0);

    let arr = [1u8; 16];
    let r7 = pass_array(arr);
    let r8 = pass_wrap_array(WrapArray(arr));
    assert_eq!(r7, r8.0);

    exercise_fn_ptr_equivalence();
}
