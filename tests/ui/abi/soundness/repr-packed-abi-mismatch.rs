// tRust regression test for rust-lang/rust#133871
//
// SOUNDNESS BUG: When a #[repr(packed)] struct is passed by value across a
// function boundary with extern "C" ABI, the compiler may generate code that
// reads fields at their natural alignment instead of their packed offsets.
// This causes silent data corruption: the callee reads garbage because it
// disagrees with the caller about field locations within the struct.
//
// The problem occurs because LLVM's calling convention lowering may decompose
// a struct into register-sized pieces based on natural alignment, ignoring
// the packed attribute. When the caller packs fields tightly but the callee
// reads them at aligned offsets (or vice versa), the byte-level layout
// disagrees between caller and callee.
//
// Example on x86_64 SysV ABI:
//   #[repr(packed)] struct S { a: u8, b: u64 }
//   - Size = 9 bytes, alignment = 1, b is at offset 1
//   - Caller stores b at byte offset 1
//   - Callee may read b at byte offset 8 (aligned) if LLVM decomposes
//     the struct into two 8-byte pieces and reads the second piece
//
// This affects any packed struct with fields whose natural alignment exceeds
// the pack alignment, passed by value through extern "C" or other non-Rust ABIs.
//
// Status: open upstream. The fix requires the compiler to always pass packed
// structs by reference (indirectly) in extern ABIs, or to correctly
// communicate the packed layout to LLVM's ABI lowering.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Reference: https://github.com/rust-lang/rust/issues/133871

//@ check-pass

#![allow(dead_code)]

// A packed struct where fields have alignment > 1.
// Without packing: alignment of u64 is 8, so padding would be inserted.
// With packing: all fields are at consecutive byte offsets, alignment = 1.
#[repr(C, packed)]
#[derive(Clone, Copy)]
struct PackedMixed {
    tag: u8,     // offset 0, size 1
    value: u64,  // offset 1, size 8 (normally would be at offset 8)
    flag: u8,    // offset 9, size 1
}

// Same logical layout but NOT packed — for comparison.
#[repr(C)]
#[derive(Clone, Copy)]
struct UnpackedMixed {
    tag: u8,     // offset 0
    // 7 bytes padding
    value: u64,  // offset 8
    flag: u8,    // offset 16
    // 7 bytes padding
}

// Passing a packed struct by value through extern "C".
// BUG: The callee may receive corrupted field values if the ABI lowering
// disagrees about field offsets.
#[allow(improper_ctypes_definitions)]
extern "C" fn process_packed(s: PackedMixed) -> u64 {
    // Reading s.value here may yield garbage if the caller and callee
    // disagree on the byte offset of `value` within the struct.
    //
    // With correct packed layout: value is at offset 1
    // With buggy ABI lowering: value might be read from offset 8
    let v = { s.value }; // Copy to avoid unaligned reference
    v
}

// A more complex packed struct that triggers the bug on more targets.
#[repr(C, packed)]
#[derive(Clone, Copy)]
struct PackedWide {
    a: u8,
    b: u32,   // offset 1 (packed), naturally wants offset 4
    c: u8,
    d: u64,   // offset 6 (packed), naturally wants offset 8
}

#[allow(improper_ctypes_definitions)]
extern "C" fn process_packed_wide(s: PackedWide) -> u64 {
    let d = { s.d };
    d
}

// Returning a packed struct is equally problematic — the caller may
// read the return value with wrong field offsets.
#[allow(improper_ctypes_definitions)]
extern "C" fn return_packed() -> PackedMixed {
    PackedMixed {
        tag: 0xAB,
        value: 0x1234_5678_9ABC_DEF0,
        flag: 0xCD,
    }
}

fn main() {
    let s = PackedMixed {
        tag: 1,
        value: 0xDEAD_BEEF_CAFE_BABE,
        flag: 2,
    };

    // On a correct compiler, the round-trip through extern "C" preserves values.
    // On a buggy compiler, `result` may not equal s.value because the ABI
    // lowering read from the wrong offset.
    let result = process_packed(s);
    let v = { s.value };
    assert_eq!(result, v);

    // Test the return path as well.
    let returned = return_packed();
    let rv = { returned.value };
    assert_eq!(rv, 0x1234_5678_9ABC_DEF0);

    let wide = PackedWide {
        a: 1,
        b: 0xAAAA_BBBB,
        c: 2,
        d: 0x1111_2222_3333_4444,
    };
    let wide_result = process_packed_wide(wide);
    let wd = { wide.d };
    assert_eq!(wide_result, wd);
}
