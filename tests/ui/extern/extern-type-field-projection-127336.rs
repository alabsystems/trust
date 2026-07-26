// Trust: Regression test for rust-lang/rust#127336
// Projecting a field of extern type at non-zero offset must not miscompile.
// Previously, codegen would fall through to the DST alignment path which
// either panicked (defensive) or produced a garbage GEP offset (miscompile).
// The fix uses the statically-computed offset from the struct layout.
//
//@ run-crash
//@ known-bug: #127336
#![feature(extern_types)]

extern "C" {
    type Opaque;
}

#[repr(C)]
struct Wrapper {
    header: u32,
    tag: u32,
    data: Opaque,
}

struct Newtype(Opaque);

#[repr(C)]
struct WithNewtype {
    x: i32,
    y: i32,
    tail: Newtype,
}

fn main() {
    // A buffer we can safely reinterpret as our extern-type-containing structs.
    let buf = [0u32; 8];

    // Case 1: Projecting extern type field at offset 0 (always worked).
    let nt: &Newtype = unsafe { &*(&buf as *const _ as *const Newtype) };
    let field: &Opaque = &nt.0;
    // The pointer to field 0 should equal the pointer to the newtype.
    assert_eq!(
        field as *const Opaque as *const u8,
        nt as *const Newtype as *const u8
    );

    // Case 2: Projecting extern type field at non-zero offset (the bug).
    // This previously panicked or miscompiled.
    let w: &Wrapper = unsafe { &*(&buf as *const _ as *const Wrapper) };
    let data: &Opaque = &w.data;
    // The data field should be at offset 8 (after two u32 fields in repr(C)).
    let base = w as *const Wrapper as *const u8;
    let data_ptr = data as *const Opaque as *const u8;
    let offset = unsafe { data_ptr.offset_from(base) };
    assert_eq!(offset, 8, "extern type field should be at offset 8 (after header + tag)");

    // Case 3: Nested newtype at non-zero offset.
    let wn: &WithNewtype = unsafe { &*(&buf as *const _ as *const WithNewtype) };
    let tail: &Newtype = &wn.tail;
    let base = wn as *const WithNewtype as *const u8;
    let tail_ptr = tail as *const Newtype as *const u8;
    let offset = unsafe { tail_ptr.offset_from(base) };
    assert_eq!(offset, 8, "newtype(extern) field should be at offset 8 (after x + y)");

    // Case 4: Accessing sized fields still works fine.
    let header = &w.header;
    let tag = &w.tag;
    assert_eq!(*header, 0);
    assert_eq!(*tag, 0);

    std::hint::black_box(field);
    std::hint::black_box(data);
    std::hint::black_box(tail);
}
