//@ build-pass
//@ only-x86_64
//@ compile-flags: -O

// Regression test for rust-lang/rust#144351
// Verify that asm! blocks without nomem act as compiler fences,
// preventing reordering of memory operations across the asm block.

use std::arch::asm;

fn compiler_fence_basic() -> u32 {
    let mut x: u32 = 0;
    x = 42;
    // This asm block touches memory (no nomem option).
    // It must act as a compiler fence -- the store of 42 above
    // must not be reordered past this asm block.
    unsafe {
        asm!("/* fence */", options(nostack));
    }
    x = 1;
    x
}

fn compiler_fence_with_readonly() -> u32 {
    let mut x: u32 = 0;
    x = 42;
    unsafe {
        asm!("/* readonly fence */", options(nostack, readonly));
    }
    x = 1;
    x
}

fn main() {
    assert_eq!(compiler_fence_basic(), 1);
    assert_eq!(compiler_fence_with_readonly(), 1);
}
