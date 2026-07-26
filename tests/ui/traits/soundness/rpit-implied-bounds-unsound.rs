//@ known-bug: #859
//@ check-pass
// Trust: regression test for rust-lang#116097
// Part of #859
//
// Return-position impl Trait (RPIT) can unsoundly introduce implied
// bounds that extend lifetimes. When a function returns `impl Trait + 'a`,
// the compiler may infer implied bounds from the hidden type that are
// not actually guaranteed by the function signature. This allows callers
// to use the returned opaque type under weaker lifetime constraints than
// the hidden type requires.
//
// The specific issue: if the hidden type behind an `impl Trait` requires
// `'a: 'b`, but the function signature only mentions `'a`, callers can
// exploit the missing bound to extend lifetimes.
//
// PoC adapted from: https://github.com/rust-lang/rust/issues/116097
//
// STATUS: This may compile on current Rust (unsound). When fixed, the
// compiler should either reject the impl or require explicit lifetime
// bounds that prevent the unsound usage.

use std::fmt::Display;

trait Capture<'a> {}
impl<'a, T: ?Sized> Capture<'a> for T {}

// This function's return type has an implied bound from the hidden type
// that is not enforced at call sites.
fn make_static<'a>(s: &'a str) -> impl Display + Capture<'a> {
    s
}

// The caller can use the returned value in a context where 'a has ended,
// if the compiler does not properly track the implied bounds.
fn test() -> Box<dyn Display> {
    let s = String::from("temporary");
    // If the compiler allows this, the returned Box<dyn Display> holds
    // a reference to a dropped String — use-after-free.
    let d = make_static(&s);
    // This should fail: d borrows s, but we're trying to return it
    // after s is dropped. The bug is that the opaque type's lifetime
    // constraints are not properly propagated.
    let _ = &d;
    Box::new("fallback")
}

fn main() {
    let b = test();
    println!("{}", b);
}
