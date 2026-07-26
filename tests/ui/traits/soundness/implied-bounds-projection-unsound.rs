//@ known-bug: #100051
//@ check-pass
// Trust: regression test for rust-lang#100051
// Part of #859
//
// Implied bounds from projections in impl headers can be unsound.
// When an impl has a where-clause like `for<'what, 'ever> &'what &'ever (): Trait`,
// the compiler uses implied bounds from the projection `<&'b &'a () as Trait>::Type`
// to satisfy lifetime constraints that should not be satisfiable, allowing
// an `extend` function that converts `&'a str` to `&'b str` for arbitrary lifetimes.
//
// This is a variant of #98543 with a different failure path not fixed by #99217.
//
// PoC from upstream issue: https://github.com/rust-lang/rust/issues/100051
//
// STATUS: This currently COMPILES on stable Rust (unsound). When fixed,
// the compiler should reject the implied bound unsoundness.

trait Trait {
    type Type;
}

impl<T> Trait for T {
    type Type = ();
}

trait Extend<'a, 'b> {
    fn extend(self, s: &'a str) -> &'b str;
}

impl<'a, 'b> Extend<'a, 'b> for <&'b &'a () as Trait>::Type
where
    for<'what, 'ever> &'what &'ever (): Trait,
{
    fn extend(self, s: &'a str) -> &'b str {
        s
    }
}

fn main() {
    // This creates a dangling reference: the String is dropped but the
    // reference `y` still points to it.
    let y = <() as Extend<'_, '_>>::extend((), &String::from("Hello World"));
    println!("{}", y);
}
