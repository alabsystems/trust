// Trust: Regression test for rust-lang#152463
// Cloning a coroutine that holds references across yield points is unsound
// because the references may be self-referential (pointing into the coroutine's
// own frame). A memcpy clone copies pointer values without fixing them up.
//
// This test verifies that tRust rejects Clone for coroutines with references.

#![feature(coroutines, coroutine_trait, coroutine_clone, stmt_expr_attributes)]

use std::ops::Coroutine;
use std::pin::Pin;

fn assert_clone<T: Clone>(_: &T) {}

fn main() {
    let gen = #[coroutine] static || {
        let x = 42;
        let r = &x; // reference crosses yield point
        yield *r;
        yield *r + 1;
    };
    assert_clone(&gen); //~ ERROR the trait bound
}
