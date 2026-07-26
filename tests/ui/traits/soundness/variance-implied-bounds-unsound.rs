//@ known-bug: #859
//@ check-pass
// Trust: regression test for rust-lang#80176
// Part of #859
//
// Unsound interaction between variance and implied bounds. The compiler
// allows implied bounds from trait implementations to interact with
// covariant type parameters in a way that enables lifetime smuggling.
//
// The specific mechanism: when a type implements a trait with an associated
// type that references a lifetime parameter, and the type is covariant
// in that lifetime, the compiler can use covariant subtyping to change
// the associated type's lifetime — but associated types should be
// invariant in the impl's lifetime parameters.
//
// This means `<Foo<'long> as Trait>::Assoc` can be coerced to
// `<Foo<'short> as Trait>::Assoc` through subtyping, even when
// the associated type contains the lifetime in a non-covariant position.
//
// Related: https://github.com/rust-lang/rust/issues/80176
//
// STATUS: This currently COMPILES on stable Rust (unsound). When fixed,
// the compiler should prevent associated type lifetime variance exploitation.

use std::marker::PhantomData;

trait GivesRef<'a> {
    type Ref;
    fn give(&self, x: Self::Ref) -> Self::Ref;
}

// Covariant<'a> is covariant in 'a, but its associated type
// Ref = &'a str contains 'a in a covariant position too.
// The danger: the compiler might allow subtyping on the Self type
// to cascade into the associated type unsoundly.
struct Covariant<'a>(PhantomData<&'a ()>);

impl<'a> GivesRef<'a> for Covariant<'a> {
    type Ref = &'a str;
    fn give(&self, x: Self::Ref) -> Self::Ref {
        x
    }
}

// This function is parameterized by a type that gives references.
// The caller controls the lifetime through the type parameter.
fn process<'a, T: GivesRef<'a>>(t: &T, x: T::Ref) -> T::Ref {
    t.give(x)
}

fn main() {
    let s = String::from("variance + implied bounds test");
    let c = Covariant(PhantomData);
    // This call works in the non-exploitative case. The test captures
    // the pattern; the unsoundness manifests when combined with
    // higher-ranked bounds that hide the lifetime relationship.
    let r = process(&c, &s);
    println!("{}", r);
}
