// Regression test for rust-lang#123695.
// Incorrect codegen for packed struct field access: when accessing
// fields of a #[repr(packed)] struct, the compiler must generate
// unaligned loads/stores because packed structs have no padding and
// fields may not be naturally aligned. LLVM could incorrectly assume
// natural alignment for field accesses, generating aligned load/store
// instructions that would fault or return garbage on architectures
// that enforce alignment.
//
// The bug patterns:
// 1. Reading a u32/u64 field at an odd offset in a packed struct
// 2. Taking a reference to a packed field (which Rust now warns about)
// 3. Copying packed structs where the memcpy size/alignment was wrong
// 4. Nested packed structs where inner struct alignment was not
//    propagated correctly
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ build-pass
//@ compile-flags: -C opt-level=2

#![allow(dead_code)]

use std::mem;

// Basic packed struct: u8 followed by u32 means the u32 sits at offset 1.
#[repr(packed)]
#[derive(Clone, Copy)]
struct PackedBasic {
    tag: u8,
    value: u32,
}

// Packed struct with u64 field at misaligned offset.
#[repr(packed)]
#[derive(Clone, Copy)]
struct PackedWide {
    flag: u8,
    id: u64,
    count: u16,
}

// Nested packed: outer packed struct containing an inner packed struct.
#[repr(packed)]
#[derive(Clone, Copy)]
struct Inner {
    a: u8,
    b: u32,
}

#[repr(packed)]
#[derive(Clone, Copy)]
struct Outer {
    header: u8,
    inner: Inner,
    trailer: u16,
}

// Packed struct in an array — each element may start at a misaligned offset
// relative to the array base.
#[repr(packed)]
#[derive(Clone, Copy)]
struct PackedElement {
    x: u8,
    y: u32,
    z: u8,
}

// Read fields from packed struct through a function boundary to prevent
// the optimizer from constant-folding.
#[inline(never)]
fn read_packed_basic(p: &PackedBasic) -> (u8, u32) {
    // Must use copy semantics, not reference, for packed field access.
    let tag = p.tag;
    let value = p.value;
    (tag, value)
}

#[inline(never)]
fn read_packed_wide(p: &PackedWide) -> (u8, u64, u16) {
    (p.flag, p.id, p.count)
}

#[inline(never)]
fn read_outer(o: &Outer) -> (u8, u8, u32, u16) {
    let header = o.header;
    let a = o.inner.a;
    let b = o.inner.b;
    let trailer = o.trailer;
    (header, a, b, trailer)
}

// Write to packed struct fields.
#[inline(never)]
fn write_packed_basic(p: &mut PackedBasic, tag: u8, value: u32) {
    p.tag = tag;
    p.value = value;
}

// Copy a packed struct — the generated memcpy must use alignment 1.
#[inline(never)]
fn copy_packed(src: &PackedWide) -> PackedWide {
    *src
}

// Array of packed structs — exercise stride calculation.
#[inline(never)]
fn sum_packed_array(arr: &[PackedElement]) -> u32 {
    let mut sum = 0u32;
    for elem in arr {
        sum += elem.x as u32 + elem.y + elem.z as u32;
    }
    sum
}

fn main() {
    // Verify sizes are truly packed (no padding).
    assert_eq!(mem::size_of::<PackedBasic>(), 5); // 1 + 4
    assert_eq!(mem::size_of::<PackedWide>(), 11); // 1 + 8 + 2
    assert_eq!(mem::size_of::<Inner>(), 5); // 1 + 4
    assert_eq!(mem::size_of::<Outer>(), 8); // 1 + 5 + 2
    assert_eq!(mem::size_of::<PackedElement>(), 6); // 1 + 4 + 1

    // Basic packed read.
    let basic = PackedBasic { tag: 0xAB, value: 0xDEAD_BEEF };
    let (t, v) = read_packed_basic(&basic);
    assert_eq!(t, 0xAB);
    assert_eq!(v, 0xDEAD_BEEF);

    // Wide packed read.
    let wide = PackedWide {
        flag: 1,
        id: 0x0123_4567_89AB_CDEF,
        count: 999,
    };
    let (f, i, c) = read_packed_wide(&wide);
    assert_eq!(f, 1);
    assert_eq!(i, 0x0123_4567_89AB_CDEF);
    assert_eq!(c, 999);

    // Nested packed read.
    let outer = Outer {
        header: 42,
        inner: Inner { a: 7, b: 0x1234_5678 },
        trailer: 0xFFFF,
    };
    let (h, a, b, tr) = read_outer(&outer);
    assert_eq!(h, 42);
    assert_eq!(a, 7);
    assert_eq!(b, 0x1234_5678);
    assert_eq!(tr, 0xFFFF);

    // Write test.
    let mut basic2 = PackedBasic { tag: 0, value: 0 };
    write_packed_basic(&mut basic2, 0xCC, 0x1111_2222);
    let (t2, v2) = read_packed_basic(&basic2);
    assert_eq!(t2, 0xCC);
    assert_eq!(v2, 0x1111_2222);

    // Copy test — read through function to avoid packed field references.
    let copied = copy_packed(&wide);
    let (cf, ci, cc) = read_packed_wide(&copied);
    assert_eq!(cf, 1);
    assert_eq!(ci, 0x0123_4567_89AB_CDEF);
    assert_eq!(cc, 999);

    // Array test.
    let arr = [
        PackedElement { x: 1, y: 10, z: 100 },
        PackedElement { x: 2, y: 20, z: 200 },
        PackedElement { x: 3, y: 30, z: 44 },
    ];
    // (1+10+100) + (2+20+200) + (3+30+44) = 111 + 222 + 77 = 410
    assert_eq!(sum_packed_array(&arr), 410);
}
