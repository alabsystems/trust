//@ build-pass
//@ compile-flags: -O

// Regression test for rust-lang/rust#70022 and rust-lang/rust#70143.
// Verify that over-aligned types compile without unsound behavior.
// tRust clamps alignment to 65536 bytes in codegen to avoid LLVM
// misalignment bugs with alignments exceeding page size.

#[repr(align(65536))]
struct OverAlignedStatic {
    data: [u8; 64],
}

static ALIGNED: OverAlignedStatic = OverAlignedStatic { data: [0; 64] };

#[repr(align(4096))]
struct PageAligned {
    data: [u8; 4096],
}

fn stack_aligned() -> u8 {
    let local = PageAligned { data: [42; 4096] };
    local.data[0]
}

fn main() {
    assert_eq!(ALIGNED.data[0], 0);
    assert_eq!(stack_aligned(), 42);
}
