#![allow(dead_code)]
use std::alloc::{Layout, alloc, dealloc};

// POSITIVE CONTROL: exactly one free of the tracked allocation. Correct code.
pub unsafe fn alloc_free_once() {
    let l = unsafe { Layout::from_size_align_unchecked(8, 8) };
    let p = unsafe { alloc(l) };
    unsafe { dealloc(p, l) };
}

// NEGATIVE CONTROL: a second free of the SAME tracked allocation. UB.
pub unsafe fn alloc_free_twice() {
    let l = unsafe { Layout::from_size_align_unchecked(8, 8) };
    let p = unsafe { alloc(l) };
    unsafe { dealloc(p, l) };
    unsafe { dealloc(p, l) };
}

// USE AFTER FREE: read through the pointer after its allocation was freed. UB.
pub unsafe fn alloc_free_then_read() -> u8 {
    let l = unsafe { Layout::from_size_align_unchecked(8, 8) };
    let p = unsafe { alloc(l) };
    unsafe { dealloc(p, l) };
    unsafe { *p }
}

// PATH CONTROL: two MUTUALLY EXCLUSIVE frees. Correct code; must NOT refute.
pub unsafe fn alloc_free_branch(c: bool) {
    let l = unsafe { Layout::from_size_align_unchecked(8, 8) };
    let p = unsafe { alloc(l) };
    if c {
        unsafe { dealloc(p, l) };
    } else {
        unsafe { dealloc(p, l) };
    }
}

// LOOP CONTROL: a single free inside a loop that runs once. Correct code.
pub unsafe fn alloc_free_loop(n: usize) {
    let l = unsafe { Layout::from_size_align_unchecked(8, 8) };
    let mut i = 0;
    while i < n {
        let p = unsafe { alloc(l) };
        unsafe { dealloc(p, l) };
        i += 1;
    }
}

// POSITIVE CONTROL: the SAME source local is re-allocated between the two
// frees, so the second `dealloc` frees a DIFFERENT allocation. Correct code.
// (Extracted with the others above, as `freeprobe::realloc_same_local`.)
pub unsafe fn realloc_same_local() {
    let l = unsafe { Layout::from_size_align_unchecked(8, 8) };
    let mut p = unsafe { alloc(l) };
    unsafe { dealloc(p, l) };
    p = unsafe { alloc(l) };
    unsafe { dealloc(p, l) };
}
