//@ known-bug: #112905
//@ check-pass
// Trust: regression test for rust-lang#112905
// Part of #859
//
// Unsound higher-ranked trait bound normalization. The compiler
// incorrectly normalizes associated types under higher-ranked trait
// bounds, equating types with different higher-ranked lifetimes.
//
// The core issue: `for<'a> fn(&'a u8, &'a u8)` and
// `for<'a, 'b> fn(&'a u8, &'b u8)` are DIFFERENT types (the first
// constrains both parameters to the same lifetime), but the compiler's
// coherence leak check treats them as potentially overlapping.
// This allows two impls that should be disjoint to coexist, and the
// wrong impl can be selected at a call site.
//
// PoC adapted from: https://github.com/rust-lang/rust/issues/112905
//
// STATUS: This currently COMPILES with a warning on stable Rust
// (unsound via coherence_leak_check). When fixed, the compiler should
// either reject the overlapping impls or correctly disambiguate.

#![allow(coherence_leak_check)]

trait Trait {
    type Ty;
}

impl Trait for for<'a> fn(&'a u8, &'a u8) {
    type Ty = u32;
}

impl Trait for for<'a, 'b> fn(&'a u8, &'b u8) {
    type Ty = String;
}

// The compiler allows both impls to coexist (with a lint warning).
// This is the unsound part — it should be a hard error because
// the function pointer types can overlap under HRTB normalization.

fn pick_impl<T: Trait>(x: T::Ty) -> T::Ty {
    x
}

fn main() {
    // The compiler resolves this to one of the two impls.
    // The fact that both exist is the soundness hole.
    let result: u32 = pick_impl::<for<'a> fn(&'a u8, &'a u8)>(42u32);
    println!("{}", result);
}
