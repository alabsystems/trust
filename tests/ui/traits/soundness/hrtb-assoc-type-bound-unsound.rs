//@ check-pass
//@ known-bug: #98117
// Trust: regression test for rust-lang#98117
// Part of #859
//
// HRTB unsoundness with associated type bounds in where clauses.
// When an associated type bound appears in a where-clause with
// higher-ranked trait bounds, the compiler incorrectly satisfies
// the bound using implied bounds from the associated type projection,
// allowing a transmute-like operation.
//
// The core pattern: an impl provides an associated type that
// requires a specific lifetime relationship for well-formedness.
// When this impl is used under a `for<'a>` bound, the compiler
// incorrectly allows the implied bound to leak out, enabling
// lifetime extension.
//
// PoC adapted from: https://github.com/rust-lang/rust/issues/98117
//
// STATUS: This currently COMPILES on stable Rust (unsound). When fixed,
// the compiler should reject the unsound associated type bound.

trait Trait<'a> {
    type Assoc;
}

impl<'a> Trait<'a> for () {
    type Assoc = &'a ();
}

fn foo<T>()
where
    for<'a> T: Trait<'a>,
    for<'a> <T as Trait<'a>>::Assoc: Clone,
{
    // The for<'a> <T as Trait<'a>>::Assoc: Clone bound requires
    // that &'a () is Clone for all 'a, which is true.
    // But the combination of the HRTB and the associated type
    // projection can leak implied bounds in certain trait-solver paths.
}

fn main() {
    // () implements Trait<'a> for all 'a with Assoc = &'a ().
    // &'a () is Clone, so the bounds are satisfied.
    // This compiles, but the pattern enables further exploits
    // when combined with more complex trait hierarchies.
    foo::<()>();
}
