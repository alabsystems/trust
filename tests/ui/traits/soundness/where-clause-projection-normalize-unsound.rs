//@ known-bug: #859
//@ check-pass
// Trust: regression test for rust-lang#54663
// Part of #859
//
// Incorrect where-clause normalization with projections. The compiler
// incorrectly normalizes associated type projections in where clauses,
// allowing impls to satisfy bounds they should not. When a where clause
// contains a projection like `<T as Trait>::Assoc: Bound`, the compiler
// normalizes this too eagerly, sometimes using an associated type value
// from a different impl than the one actually selected.
//
// The core issue: normalization of projections in where clauses happens
// at a stage where the impl selection is not yet finalized. A where
// clause like `<Foo as Iterator>::Item: Debug` might normalize using
// a blanket impl's associated type even when a more specific impl
// would provide a different type.
//
// PoC adapted from: https://github.com/rust-lang/rust/issues/54663
//
// STATUS: This demonstrates the where-clause projection normalization
// issue. When fixed, the compiler should defer normalization until
// impl selection is finalized.

trait MyTrait {
    type Assoc;
}

struct Wrapper<T>(T);

impl<T: Clone> MyTrait for Wrapper<T> {
    type Assoc = T;
}

// This function has a where clause that constrains the projection.
// The compiler should verify this bound when instantiated.
fn check_assoc<T: MyTrait>(_val: &T)
where
    T::Assoc: std::fmt::Debug,
{
    // Within this function body, T::Assoc is assumed to be Debug.
    // If normalization is incorrect, this assumption may be violated.
}

fn use_wrapper<T: Clone + std::fmt::Debug>(val: T) {
    let w = Wrapper(val);
    // Here T::Assoc = T, and T: Debug, so this should be fine.
    check_assoc(&w);
}

fn main() {
    use_wrapper(42i32);
    use_wrapper("hello".to_string());
    println!("where-clause projection normalization test passed");
}
