// Regression test for rust-lang#116485.
// Incorrect noalias on mutable references: LLVM was annotating mutable
// reference parameters with the `noalias` attribute, which tells LLVM
// that the pointer does not alias any other pointer accessible in the
// function. While Rust's borrow checker guarantees uniqueness of &mut,
// this interacts unsoundly with certain patterns:
//
// 1. Self-referential structures where &mut self contains a field
//    pointing back into the same allocation
// 2. Functions that take &mut and also access the data through a raw
//    pointer derived before the borrow
// 3. Patterns involving Pin<&mut T> where the optimizer incorrectly
//    reorders accesses
//
// The noalias annotation allowed LLVM to reorder, eliminate, or
// duplicate stores/loads, breaking programs that were correct under
// Rust's actual aliasing model.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ build-pass
//@ compile-flags: -C opt-level=2

#![allow(dead_code)]

use std::ptr;

// Pattern 1: Function taking &mut that internally creates a raw pointer
// to the same data. The noalias on &mut could cause LLVM to assume the
// raw pointer read sees the "old" value.
#[inline(never)]
fn modify_and_read_raw(x: &mut u64) -> u64 {
    let p = x as *const u64;
    *x = 42;
    // SAFETY: p points to x which is still valid; we're reading after write.
    unsafe { ptr::read(p) }
}

// Pattern 2: Two mutable references derived from a single allocation
// at different offsets. LLVM's noalias might incorrectly assume they
// don't alias the same cache line or allocation.
#[inline(never)]
fn swap_adjacent(arr: &mut [u32; 4]) {
    let p = arr.as_mut_ptr();
    for i in (0..arr.len()).step_by(2) {
        // SAFETY: i and i+1 are in bounds, non-overlapping.
        unsafe {
            let a = ptr::read(p.add(i));
            let b = ptr::read(p.add(i + 1));
            ptr::write(p.add(i), b);
            ptr::write(p.add(i + 1), a);
        }
    }
}

// Pattern 3: Mutable reference to a struct where we modify one field
// and read another. With incorrect noalias, LLVM might reorder the
// read before the write.
struct Pair {
    first: u64,
    second: u64,
}

#[inline(never)]
fn update_first_return_second(p: &mut Pair) -> u64 {
    p.first = p.second + 1;
    p.second
}

// Pattern 4: Passing &mut through a function pointer — the optimizer
// might not track the noalias correctly through indirect calls.
#[inline(never)]
fn apply_fn(x: &mut i32, f: fn(&mut i32)) {
    f(x);
}

fn double_in_place(x: &mut i32) {
    *x *= 2;
}

fn negate_in_place(x: &mut i32) {
    *x = -*x;
}

// Pattern 5: Reborrowing — creating a shorter-lived &mut from an
// existing &mut. Both point to the same data but LLVM should not
// assume the outer borrow's noalias applies during the inner borrow.
#[inline(never)]
fn nested_modify(x: &mut u64) -> u64 {
    *x = 10;
    let inner: &mut u64 = &mut *x;
    *inner = 20;
    *x
}

fn main() {
    // Pattern 1: raw pointer must see the updated value.
    let mut val = 0u64;
    assert_eq!(modify_and_read_raw(&mut val), 42);
    assert_eq!(val, 42);

    // Pattern 2: adjacent swap.
    let mut arr = [1u32, 2, 3, 4];
    swap_adjacent(&mut arr);
    assert_eq!(arr, [2, 1, 4, 3]);

    // Pattern 3: cross-field access.
    let mut pair = Pair { first: 0, second: 100 };
    let s = update_first_return_second(&mut pair);
    assert_eq!(s, 100);
    assert_eq!(pair.first, 101);

    // Pattern 4: function pointer with &mut.
    let mut x = 5i32;
    apply_fn(&mut x, double_in_place);
    assert_eq!(x, 10);
    apply_fn(&mut x, negate_in_place);
    assert_eq!(x, -10);

    // Pattern 5: reborrow must see final value.
    let mut v = 0u64;
    assert_eq!(nested_modify(&mut v), 20);
}
