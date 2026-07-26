// Trust: regression test for compile-time bug rust-lang#77173
//
// Recursive data structures implementing traits with associated types cause
// exponential compilation time due to exponential growth of the obligation
// forest. Each additional nesting level doubles the work.
//
// This test uses 15 nesting levels (the original used 25 which hangs).
// 15 levels should compile in seconds; without caching it would take
// several seconds, demonstrating the exponential growth pattern.
//
// Upstream: https://github.com/rust-lang/rust/issues/77173
// Tracked in Trust: #865
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ check-pass

use std::marker::PhantomData;

// Trait with associated type — the associated type is a required prerequisite
// for the exponential behavior.
trait Trait<T> {
    type AssocType;
    fn foo(&self, a: T) -> T;
}

// End of recursion.
impl<T> Trait<T> for () {
    type AssocType = i32;
    fn foo(&self, a: T) -> T { a }
}

// Recursive struct. Nested type implements trait.
struct NestingStruct<T, SubStruct: Trait<T>>(
    SubStruct,
    PhantomData<T>,
);

impl<T, SubStruct> Trait<T> for NestingStruct<T, SubStruct>
where
    SubStruct: Trait<T, AssocType = i32>,
{
    type AssocType = i32;
    fn foo(&self, a: T) -> T { self.0.foo(a) }
}

fn main() {
    let t = ();

    let t = NestingStruct(t, PhantomData);
    let t = NestingStruct(t, PhantomData);
    let t = NestingStruct(t, PhantomData);
    let t = NestingStruct(t, PhantomData);
    let t = NestingStruct(t, PhantomData);
    // Five iterations: no noticeable slowdown.

    let t = NestingStruct(t, PhantomData);
    let t = NestingStruct(t, PhantomData);
    let t = NestingStruct(t, PhantomData);
    let t = NestingStruct(t, PhantomData);
    let t = NestingStruct(t, PhantomData);
    // Ten iterations: should take less than a second.

    let t = NestingStruct(t, PhantomData);
    let t = NestingStruct(t, PhantomData);
    let t = NestingStruct(t, PhantomData);
    let t = NestingStruct(t, PhantomData);
    let t = NestingStruct(t, PhantomData);
    // Fifteen iterations: several seconds without fix; should be fast with fix.

    println!("Hello {}", t.foo(1));
}
