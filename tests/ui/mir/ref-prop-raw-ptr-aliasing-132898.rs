//! Regression test for rust-lang#132898 (non-2-phase variant): ReferencePropagation
//! introduces UB by replacing raw pointer accesses with direct place accesses.
//!
//! This variant demonstrates the issue without 2-phase borrows, using raw pointers
//! directly. The pass replaces `*alias` (SRW access) with a direct field access
//! (Unique access), changing aliasing semantics.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//@ compile-flags: -Copt-level=2
//@ run-pass

fn main() {
    struct Foo(u64);
    impl Foo {
        fn add(ptr: *mut Self, n: u64) -> u64 {
            unsafe { (*ptr).0 + n }
        }
    }

    let mut f = Foo(0);
    let alias = &mut f.0 as *mut u64;
    let ptr = &raw mut f;
    // Writing through `alias` (raw pointer to f.0) should be valid because
    // both `alias` and `ptr` are raw pointers with SRW semantics.
    // The pass must NOT replace `*alias = 42` with `f.0 = 42`.
    unsafe { *alias = 42 };
    let res = Foo::add(ptr, 0);
    assert_eq!(res, 42);
}
