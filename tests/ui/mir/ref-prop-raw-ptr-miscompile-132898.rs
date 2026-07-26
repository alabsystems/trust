//! Regression test for rust-lang#132898: ReferencePropagation introduces UB with raw pointers.
//!
//! The ReferencePropagation MIR pass was replacing `*raw_ptr` accesses (which have
//! SharedReadWrite aliasing semantics) with direct place accesses (which have Unique
//! aliasing semantics). This changes the aliasing model and can invalidate live 2-phase
//! borrows, introducing undefined behavior.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//@ compile-flags: -Copt-level=2
//@ run-pass

fn main() {
    struct Foo(u64);
    impl Foo {
        fn add(&mut self, n: u64) -> u64 {
            self.0 + n
        }
    }

    let mut f = Foo(0);
    let alias = &mut f.0 as *mut u64;
    // The 2-phase borrow for `f.add(...)` creates a SharedReadWrite borrow.
    // Writing through `alias` (a raw pointer) should not invalidate it.
    // Before the fix, ReferencePropagation replaced `*alias = 42` with
    // `f.0 = 42` (a direct Unique access), which invalidated the 2-phase borrow.
    let res = f.add(unsafe {
        *alias = 42;
        0
    });
    assert_eq!(res, 42);
}
