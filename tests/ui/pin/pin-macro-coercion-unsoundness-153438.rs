// Regression test for rust-lang#153438: pin!() is unsound due to coercions.
// Trust: Part of #860
//
// The bug: without a type constraint in pin!(), a type annotation on the result
// can introduce deref coercions that bypass pinning. For example, given a value
// of type `&mut T`, writing `let x: Pin<&mut T> = pin!(&mut val)` would, without
// the fix, apply a deref coercion inside the macro — producing a Pin to an
// unpinned temporary rather than pinning the reference itself.
//
// The fix constrains pin!()'s return type to Pin<&mut T> where T is exactly the
// type of the expression, preventing type-annotation-driven coercions.

use std::pin::Pin;
use std::pin::pin;

fn main() {
    let mut val: u32 = 42;

    // Without the fix, this would compile by applying a deref coercion:
    // pin!(&mut val) would produce Pin<&mut u32> by dereferencing the &mut u32
    // to get a u32, then taking &mut of that — but that &mut points to an
    // unpinned location, violating Pin's guarantee.
    //
    // With the fix, pin!(&mut val) produces Pin<&mut &mut u32> (the exact type
    // of the expression is &mut u32, so Pin wraps that). Assigning this to
    // Pin<&mut u32> is a type mismatch.
    let _x: Pin<&mut u32> = pin!(&mut val);
    //~^ ERROR mismatched types
    // [pending soundness check] ERROR mismatched types
}
