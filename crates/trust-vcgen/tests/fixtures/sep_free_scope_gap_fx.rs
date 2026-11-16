#![allow(dead_code)]
// The REVIEWER'S SCOPE PROBE for the global-deallocator free channel: CORRECT
// code on which that channel must mint NO use-after-free row. Each function
// frees `p` on ONE arm of a `SwitchInt` and reads (or writes, then reads)
// through it on the OTHER arm, which frees it only afterwards. No execution
// touches `p` after freeing it. The `g`/`h` calls put a block boundary after the
// free, so the free becomes visible (by dominance) in a block that is walked
// BEFORE the other arm's use.
use std::alloc::{Layout, alloc, dealloc};

unsafe extern "C" {
    fn g();
    fn h();
    fn fresh() -> *mut u8;
}

pub unsafe fn free_one_arm_use_other(c: bool) -> u8 {
    let l = unsafe { Layout::from_size_align_unchecked(8, 8) };
    let p = unsafe { alloc(l) };
    if c {
        unsafe { dealloc(p, l) };
        unsafe { g() };
        0
    } else {
        unsafe { h() };
        let v = unsafe { *p };
        unsafe { dealloc(p, l) };
        v
    }
}

pub unsafe fn write_other_arm(c: bool) -> u8 {
    let l = unsafe { Layout::from_size_align_unchecked(8, 8) };
    let p = unsafe { alloc(l) };
    if c {
        unsafe { dealloc(p, l) };
        unsafe { g() };
        0
    } else {
        unsafe { h() };
        unsafe { *p = 7 };
        let v = unsafe { *p };
        unsafe { dealloc(p, l) };
        v
    }
}

// The freed LOCAL is rebound by an unmodeled call before the read. The read is
// through the NEW pointer, so no execution reads freed memory here.
pub unsafe fn free_then_rebind_by_call() -> u8 {
    let l = unsafe { Layout::from_size_align_unchecked(8, 8) };
    let mut p = unsafe { alloc(l) };
    unsafe { dealloc(p, l) };
    p = unsafe { fresh() };
    unsafe { *p }
}

// The freed LOCAL is re-allocated in a block rustc's null-check pass APPENDS
// (the checked write through `q` splits the block, and everything after it,
// including the `alloc` call, moves to the new, highest-numbered block), while
// the read of the NEW allocation stays in the lower-numbered continuation block.
// The index-ordered walk therefore reaches the read before the re-allocation.
pub unsafe fn free_realloc_after_checked_write(q: *mut u8) -> u8 {
    let l = unsafe { Layout::from_size_align_unchecked(8, 8) };
    let mut p = unsafe { alloc(l) };
    unsafe { dealloc(p, l) };
    unsafe { *q = 1 };
    p = unsafe { alloc(l) };
    let v = unsafe { *p };
    unsafe { dealloc(p, l) };
    v
}
