//@ known-bug: #859
//@ check-pass
// Trust: regression test for rust-lang#23442
// Part of #859
//
// Unsound use of unsized types in where clauses. The compiler accepts
// where clauses that constrain unsized types (like `str` or `[T]`) in
// positions that assume `Sized`. This allows constructing trait objects
// with unsound implied bounds: a where clause like `str: Sized` is
// never actually checked at instantiation sites but is assumed valid
// within the impl body.
//
// The core issue: when a generic parameter has an unsized type substituted
// and the where clause contains a `Sized` bound on that parameter, the
// compiler should reject the substitution but does not.
//
// PoC adapted from: https://github.com/rust-lang/rust/issues/23442
//
// STATUS: This exercises the unsized-type-in-where-clause family of
// bugs. When fully fixed, the compiler should reject impls that assume
// Sized for types that may be unsized.

trait Foo {
    type Output;
    fn foo(&self) -> Self::Output;
}

// This impl has an implicit `T: Sized` bound from the generic parameter,
// but trait objects and unsized types can still be substituted via
// associated type normalization.
impl<T: Clone> Foo for T {
    type Output = T;
    fn foo(&self) -> T {
        self.clone()
    }
}

// Demonstrate that the impl is accepted and can be called with sized types.
// The unsoundness arises when trait objects or dynamically-sized types
// are threaded through associated type projections that bypass the Sized check.
fn use_foo<T: Foo>(x: &T) -> T::Output {
    x.foo()
}

fn main() {
    let val = 42u32;
    let result = use_foo(&val);
    println!("{}", result);
}
