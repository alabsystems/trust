//@ known-bug: #57893
//@ check-pass
// Trust: Regression test for rust-lang#57893
// A blanket impl `impl<T: ?Sized> Trait for T` overlaps with the
// built-in `impl Trait for dyn Trait`, which can be exploited for
// unsound transmutes through conflicting associated type definitions.
//
// This test verifies that tRust rejects such impls.

trait MyTrait {
    type Assoc;
}

// This should be rejected: `dyn MyTrait<Assoc=()>` satisfies `T: ?Sized`
// AND has a built-in impl of `MyTrait`, creating an overlap that allows
// conflicting associated type definitions.
impl<T: ?Sized> MyTrait for T {
    // [pending soundness check] ERROR the trait `MyTrait` cannot be implemented for a blanket type
    type Assoc = ();
}

fn main() {}
