// Trust: regression test for rust-lang#25860
// Part of #859
//
// Unsoundness in specialization (min_specialization / specialization feature).
// When specialization is enabled, a default impl can provide a method that
// returns a value of the associated type, and a more specific impl can
// override the associated type to a different concrete type. The default
// method body is NOT re-checked against the specialized associated type,
// allowing a type confusion / transmute in safe code.
//
// PoC adapted from: https://github.com/rust-lang/rust/issues/25860
// This is the fundamental specialization soundness hole that has kept the
// feature unstable since 2015.
//
// STATUS: Requires `#![feature(specialization)]` (nightly-only). The bug
// is the reason specialization has never been stabilized. When fixed,
// the compiler should reject the conflicting default method body.

#![feature(specialization)]
#![allow(incomplete_features)]

trait Specializable {
    type Output;
    fn produce(&self) -> Self::Output;
}

// Default impl: Output = &'static str, produce returns a string literal.
impl<T> Specializable for T {
    default type Output = &'static str;
    default fn produce(&self) -> Self::Output {
        "default" //~ ERROR mismatched types
    }
}

// Specialized impl for u32: overrides Output to u32 but does NOT override
// produce(). The default produce() body returns &'static str, which is
// now returned as u32. This is a type confusion.
impl Specializable for u32 {
    type Output = u32;
    // produce() is inherited from the default impl — it still returns
    // "default" (&'static str), but the signature says it returns u32.
}

fn main() {
    // If this compiles and runs, it reinterprets a &str as a u32.
    let val: u32 = 42u32.produce();
    println!("{}", val);
}
