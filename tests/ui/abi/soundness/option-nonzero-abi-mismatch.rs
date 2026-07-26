// tRust regression test for rust-lang/rust#104816
//
// SOUNDNESS BUG: extern "C" functions returning Option<NonZeroU8> (and similar
// Option<NonZero*> types) have an ABI mismatch with what callers expect. The
// niche optimization allows Option<NonZeroU8> to be represented as a single
// byte (0 for None, 1-255 for Some), giving it the same size as u8. However,
// the calling convention may treat it differently from a plain u8 — for example,
// passing it as a struct (indirect) rather than a scalar (in register).
//
// This means an extern "C" function returning Option<NonZeroU8> may place the
// value somewhere different from where the caller reads it, leading to silent
// data corruption. The caller reads garbage and interprets it as a valid
// Option<NonZeroU8>, potentially treating None as Some or vice versa.
//
// The issue generalizes to any niche-optimized enum in extern "C" signatures.
// The compiler's ABI computation doesn't always account for niche optimization
// when determining the calling convention, creating a mismatch between the
// Rust-side representation and the C ABI.
//
// Status: open upstream. Affects cross-language FFI and function pointers.
//
// tRust must ensure that niche-optimized types in extern "C" signatures use
// a calling convention consistent with their actual memory representation.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Reference: https://github.com/rust-lang/rust/issues/104816

//@ check-pass

#![allow(dead_code, improper_ctypes_definitions)]

use std::num::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroUsize};

// Option<NonZeroU8> has the same size as u8 due to niche optimization.
// But the ABI for returning it from extern "C" may differ from returning u8.

extern "C" fn returns_option_nzu8(x: u8) -> Option<NonZeroU8> {
    NonZeroU8::new(x)
}

extern "C" fn returns_plain_u8(x: u8) -> u8 {
    x
}

// Same issue with larger NonZero types.
extern "C" fn returns_option_nzu16(x: u16) -> Option<NonZeroU16> {
    NonZeroU16::new(x)
}

extern "C" fn returns_option_nzu32(x: u32) -> Option<NonZeroU32> {
    NonZeroU32::new(x)
}

extern "C" fn returns_option_nzusize(x: usize) -> Option<NonZeroUsize> {
    NonZeroUsize::new(x)
}

// The dangerous pattern: function pointer casts between ABI-compatible
// representations. If Option<NonZeroU8> has a different ABI than u8
// despite being the same size, transmuting function pointers is UB.
extern "C" fn accept_option_nzu8(val: Option<NonZeroU8>) -> u8 {
    match val {
        Some(n) => n.get(),
        None => 0,
    }
}

// Struct containing Option<NonZero*> in extern "C" — compounds the issue
// because struct layout includes the niche-optimized field.
#[repr(C)]
struct FfiResult {
    code: u32,
    value: Option<NonZeroU8>,
}

extern "C" fn returns_ffi_result(code: u32, val: u8) -> FfiResult {
    FfiResult {
        code,
        value: NonZeroU8::new(val),
    }
}

fn main() {
    // Verify niche optimization sizes match (the layout promise).
    assert_eq!(
        std::mem::size_of::<Option<NonZeroU8>>(),
        std::mem::size_of::<u8>()
    );
    assert_eq!(
        std::mem::size_of::<Option<NonZeroU16>>(),
        std::mem::size_of::<u16>()
    );

    // Exercise the extern "C" return paths.
    let some = returns_option_nzu8(42);
    let none = returns_option_nzu8(0);
    assert_eq!(some, NonZeroU8::new(42));
    assert_eq!(none, None);

    let some16 = returns_option_nzu16(1000);
    assert_eq!(some16, NonZeroU16::new(1000));

    let some32 = returns_option_nzu32(0xDEAD_BEEF);
    assert_eq!(some32, NonZeroU32::new(0xDEAD_BEEF));

    // Exercise the accept path.
    let val = accept_option_nzu8(NonZeroU8::new(99));
    assert_eq!(val, 99);
    let val = accept_option_nzu8(None);
    assert_eq!(val, 0);

    // Exercise struct return.
    let result = returns_ffi_result(200, 5);
    assert_eq!(result.code, 200);
    assert_eq!(result.value, NonZeroU8::new(5));
}
