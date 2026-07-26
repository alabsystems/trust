// tRust regression test for rust-lang/rust#115404
//
// SOUNDNESS BUG: On certain architectures (mips64, s390x, sparc64), a
// #[repr(transparent)] wrapper around a type does not have the same ABI as
// the inner type. The wrapper gets passed differently (e.g., indirect vs.
// cast-to-register), which means that calling a function expecting Wrapper<T>
// with a T, or vice versa, silently corrupts data.
//
// repr(transparent) is specifically designed to guarantee ABI compatibility
// with the inner type. Violating this breaks FFI wrappers, newtypes used
// across extern "C" boundaries, and any code that relies on the documented
// layout guarantee.
//
// This affects real-world patterns like:
//   - NonZero<u32> passed to C functions expecting u32
//   - Custom newtypes wrapping C types for type safety
//   - Wrappers around SIMD types (also see #116558)
//
// Status: open upstream, no fix. Affects Tier 2/3 targets primarily, but the
// principle applies everywhere. tRust must ensure repr(transparent) ABI
// equivalence as an invariant.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Reference: https://github.com/rust-lang/rust/issues/115404

//@ check-pass

#[repr(transparent)]
struct FloatWrapper(f64);

#[repr(transparent)]
struct ArrayWrapper([u8; 16]);

// These extern "C" functions should have IDENTICAL ABI to their unwrapped
// counterparts. On mips64, s390x, and sparc64, they don't — the PassMode
// differs between the wrapped and unwrapped versions.

extern "C" fn takes_f64(x: f64) -> f64 {
    x
}

extern "C" fn takes_wrapped_f64(x: FloatWrapper) -> FloatWrapper {
    x
}

#[allow(improper_ctypes_definitions)]
extern "C" fn takes_array(x: [u8; 16]) -> [u8; 16] {
    x
}

#[allow(improper_ctypes_definitions)]
extern "C" fn takes_wrapped_array(x: ArrayWrapper) -> ArrayWrapper {
    x
}

// The bug: on affected targets, calling `takes_wrapped_f64` with the same
// bit pattern as `takes_f64` produces different results because the arguments
// are passed in different locations (register vs. stack, or different register
// classes).

fn main() {
    let val = 42.0_f64;
    let result_unwrapped = takes_f64(val);
    let result_wrapped = takes_wrapped_f64(FloatWrapper(val));

    // These should be bitwise identical. On buggy targets, they aren't.
    assert_eq!(result_unwrapped, result_wrapped.0);

    let arr = [1u8; 16];
    let result_arr = takes_array(arr);
    let result_warr = takes_wrapped_array(ArrayWrapper(arr));
    assert_eq!(result_arr, result_warr.0);
}
