//@ known-bug: #859
//@ check-pass
// Trust: regression test for rust-lang#85336
// Part of #859
//
// Unsound interaction between higher-ranked trait bounds (HRTB) and trait
// upcasting. When trait upcasting is enabled, a trait object `dyn Subtrait`
// can be upcast to `dyn Supertrait`. If the subtrait has a higher-ranked
// lifetime bound that implies a weaker supertrait bound, the upcast can
// lose lifetime constraints, allowing lifetime extension.
//
// PoC adapted from: https://github.com/rust-lang/rust/issues/85336
//
// STATUS: trait_upcasting is stable since Rust 1.86. When fixed, the
// compiler should reject the unsound upcast or enforce lifetime constraints
// through the upcasting coercion.

#![allow(dead_code)]

trait Supertrait {
    fn as_str(&self) -> &str;
}

trait Subtrait: Supertrait {
    fn make_str<'a>(&self, s: &'a str) -> &'a str;
}

struct MyStruct;

impl Supertrait for MyStruct {
    fn as_str(&self) -> &str {
        "static"
    }
}

impl Subtrait for MyStruct {
    fn make_str<'a>(&self, s: &'a str) -> &'a str {
        s
    }
}

// The upcast from &dyn Subtrait to &dyn Supertrait should preserve all
// lifetime constraints. The bug is that the compiler does not properly
// track the relationship between HRTB lifetimes and the supertrait
// vtable during upcasting.
fn upcast(x: &dyn Subtrait) -> &dyn Supertrait {
    x
}

fn main() {
    let s = MyStruct;
    let sup = upcast(&s);
    println!("{}", sup.as_str());
}
