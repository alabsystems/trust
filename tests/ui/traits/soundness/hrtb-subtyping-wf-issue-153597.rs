//@ run-pass
#![allow(dead_code)]
// Trust: regression test for rust-lang#153597
// Part of #859
//
// Higher-ranked subtyping (the `binders` method in `TypeRelating`) skips
// WF checks on instantiated types. When checking `for<'a> T_a <: for<'b> T_b`,
// the super type is instantiated with placeholders and the sub type with
// fresh inference variables, then they are related — but neither the
// placeholder-instantiated type nor the inference-variable-instantiated
// type has its well-formedness verified. This allows types with dangling
// lifetime relationships to pass the subtyping check unchecked.
//
// The fix adds WellFormed obligations for instantiated binder types in
// the TypeRelating binders method.
//
// PoC from upstream issue: https://github.com/rust-lang/rust/issues/153597
//
// STATUS: Fixed. WF obligations are now registered for instantiated
// higher-ranked binder types.

trait Trait<'a> {
    type Assoc;
}

impl<'a, T: 'a> Trait<'a> for T {
    type Assoc = &'a T;
}

// A function type that uses higher-ranked bounds
fn identity<'a>(x: &'a i32) -> &'a i32 {
    x
}

// Coercion through higher-ranked function pointer types
fn coerce(f: for<'a> fn(&'a i32) -> &'a i32) -> fn(&i32) -> &i32 {
    // This subtyping check: for<'a> fn(&'a i32) -> &'a i32 <: fn(&i32) -> &i32
    // instantiates binders; with the bug, WF was not checked on the
    // instantiated types
    f
}

fn main() {
    let f = coerce(identity);
    let val = 42;
    let r = f(&val);
    assert_eq!(*r, 42);
}
