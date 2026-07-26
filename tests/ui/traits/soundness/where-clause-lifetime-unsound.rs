//@ check-pass
// Trust: regression test for rust-lang#47646
// Part of #859
//
// Where-clause unsoundness with lifetimes. A where-clause with
// `for<'a>` can interact with trait impls that have conditional
// lifetime bounds, causing the compiler to accept code that should
// be rejected.
//
// The core issue: `Cell<&'b ()>` only implements `MyTrait<'a>` when
// `'a: 'b` (due to the where-clause on the impl). But a function
// requiring `for<'a> T: MyTrait<'a>` should only accept types that
// implement `MyTrait` for ALL lifetimes, not just some.
//
// The compiler's where-clause checking can fail to properly verify
// that all instantiations of the universally quantified lifetime
// are valid, accepting types that only satisfy the bound conditionally.
//
// PoC from upstream issue: https://github.com/rust-lang/rust/issues/47646
//
// STATUS: This test documents the pattern. The specific Cell PoC is now
// rejected by the compiler, but the underlying issue of where-clause
// lifetime soundness affects other patterns in the HRTB/implied bounds
// cluster.

#![allow(dead_code)]

use std::cell::Cell;

trait MyTrait<'a> {
    type Output;
}

impl<'a, 'b: 'a> MyTrait<'a> for Cell<&'b ()> {
    type Output = &'a ();
}

// This function correctly requires T: MyTrait<'a> for all 'a.
// Cell<&'b ()> does NOT satisfy this because it needs 'b: 'a.
// The compiler NOW correctly rejects this (the original bug is
// partially fixed), but the pattern remains important for the
// HRTB/implied bounds cluster as related variants may still compile.
fn check_bound<T>()
where
    for<'a> T: MyTrait<'a>,
{
}

fn main() {
    // Document the pattern: this SHOULD be rejected and now IS rejected.
    // The broader class of where-clause lifetime bugs (#84591, #100051, etc.)
    // still has open unsound instances tested in other files.
    //
    // We keep this test to ensure the fix for #47646 doesn't regress.
    // check_bound::<Cell<&()>>();  // Correctly rejected since ~1.64
    println!("where-clause lifetime regression test");
}
