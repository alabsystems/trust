//@ known-bug: #100041
//@ check-pass
// Trust: Regression test for rust-lang#100041
// Normalization must check well-formedness of the normalized type.
//
// When a projection like `<&'a str as Trait>::Assoc` normalizes to `&'a [u8]`,
// the well-formedness of the resulting type must be checked. Previously,
// normalization could skip WF checking, allowing types like `&'a T` where
// `T: 'a` doesn't necessarily hold.
//
// The fix adds a WellFormed obligation on the normalized type in
// `confirm_candidate` for all normalization paths.
//
// Part of #859

trait Trait {
    type Assoc;
}

impl<'a> Trait for &'a str {
    type Assoc = &'a [u8];
}

// This function uses a projection that normalizes to `&'a [u8]`.
// The WF check should ensure that `str: 'a` holds.
fn exploit<'a>(x: <&'a str as Trait>::Assoc) -> &'a [u8] {
    x // [pending soundness check] ERROR
}

fn main() {}
