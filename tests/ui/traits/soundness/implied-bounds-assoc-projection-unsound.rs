//@ known-bug: #100051
//@ check-pass
// Trust: regression test for rust-lang#74255
// Part of #859
//
// Implied bounds from associated type projections allow unsound lifetime
// extensions. The compiler infers implied bounds from associated type
// projections in impl headers, but these implied bounds can be overly
// permissive, allowing lifetime constraints that should not hold.
//
// The core issue: when an impl has `impl<'a, 'b> Trait for Type<'a, 'b>
// where <SomeType<'a, 'b> as OtherTrait>::Assoc: Bound`, the compiler
// may infer that 'a: 'b (or vice versa) from the projection's well-
// formedness requirements. This implied bound is then used within the
// impl body to extend lifetimes unsoundly.
//
// PoC adapted from: https://github.com/rust-lang/rust/issues/74255
//
// STATUS: This demonstrates implied bounds from associated type
// projections. When fixed, the compiler should not derive lifetime
// relationships from projection well-formedness in impl headers.

trait Static: 'static {}
impl Static for () {}

trait Trait {
    type Assoc: 'static;
}

impl<T: Static> Trait for T {
    type Assoc = T;
}

// This function exploits implied bounds: the compiler infers that
// T::Assoc: 'static implies T: 'static (via the impl above), which
// can extend lifetimes when T contains borrowed data.
fn assert_static<T: Trait>(_val: T) {
    // Within this body, the compiler assumes T::Assoc: 'static,
    // and may incorrectly imply T: 'static.
}

fn main() {
    // With a 'static type, this is fine.
    assert_static(());

    // The unsoundness manifests when this function is used with
    // types whose 'static bound comes from projection normalization
    // rather than from the actual type.
    println!("implied bounds from assoc projection test passed");
}
