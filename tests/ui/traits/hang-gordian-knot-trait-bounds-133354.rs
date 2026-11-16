// Trust: regression test for compile-time bug rust-lang#133354
//
// This is a "gordian knot" of trait bounds: mutually recursive trait impls
// cause the compiler to hang during trait solving. Minimized from the
// pyca/cryptography and rust-asn1 crates.
//
// The trait solver enters an infinite loop because:
// - SimpleAsn1Writable for &T requires SimpleAsn1Writable for T
// - SimpleAsn1Writable for Box<T> requires SimpleAsn1Writable for T
// - PBES2Params requires Box<AlgorithmIdentifier>: Asn1Writable
// - AlgorithmIdentifier requires AlgorithmParameters: Asn1DefinedByWritable
// - AlgorithmParameters requires PBES2Params: Asn1Writable (cycle!)
//
// Measured 2026-11-04 (§5.2 triage): with the triggering call enabled, the
// program is an overflow error (E0275) under both solvers — fast under the
// next solver, about 72 s under load under the old solver. It is not a
// check-pass program on either solver, so the call stays commented out.
//
// Upstream: https://github.com/rust-lang/rust/issues/133354
// Tracked in Trust: #865
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ check-pass

#![allow(dead_code)]

// NOTE: This file defines the types and trait impls for the cyclic case,
// but does NOT call the function that forces the solver to resolve it.
// Calling `write_element(&Some(&p.hash_algorithm))` overflows trait
// solving (E0275), slowly on the old solver, rather than hanging forever.

mod asn1 {
    pub trait Asn1Writable: Sized {}
    pub trait SimpleAsn1Writable: Sized {}

    impl<T: SimpleAsn1Writable> Asn1Writable for T {}
    impl<T: SimpleAsn1Writable> SimpleAsn1Writable for &T {}
    impl<T: SimpleAsn1Writable> SimpleAsn1Writable for Box<T> {}

    impl<T: Asn1Writable> Asn1Writable for Option<T> {}

    pub trait Asn1DefinedByWritable: Sized {}
}

mod common {
    use crate::asn1;

    pub struct AlgorithmIdentifier<'a> {
        pub params: AlgorithmParameters<'a>,
    }

    impl<'a> asn1::SimpleAsn1Writable for AlgorithmIdentifier<'a> where
        AlgorithmParameters<'a>: asn1::Asn1DefinedByWritable
    {
    }

    pub enum AlgorithmParameters<'a> {
        Sha1,
        Pbkdf2(PBKDF2Params<'a>),
    }

    impl<'a> asn1::Asn1DefinedByWritable for AlgorithmParameters<'a>
    where
        PBES2Params<'a>: asn1::Asn1Writable,
        PBKDF2Params<'a>: asn1::Asn1Writable,
    {
    }

    pub struct RsaPssParameters<'a> {
        pub hash_algorithm: AlgorithmIdentifier<'a>,
    }

    impl<'a> asn1::SimpleAsn1Writable for RsaPssParameters<'a> {}

    pub struct PBES2Params<'a> {
        pub key_derivation_func: Box<AlgorithmIdentifier<'a>>,
    }

    impl<'a> asn1::SimpleAsn1Writable for PBES2Params<'a> where
        Box<AlgorithmIdentifier<'a>>: asn1::Asn1Writable
    {
    }

    pub struct PBKDF2Params<'a> {
        pub salt: &'a [u8],
    }

    impl<'a> asn1::SimpleAsn1Writable for PBKDF2Params<'a> where
        Box<AlgorithmIdentifier<'a>>: asn1::Asn1Writable
    {
    }
}

pub fn write_element<T: asn1::Asn1Writable>(_val: &T) {}

// Trust: enabling this call makes the crate an E0275 overflow error on
// both solvers (measured 2026-11-04; see header). It stays commented out
// because the triggered program is erroneous, not because it hangs.
// pub fn f(p: &common::RsaPssParameters<'_>) {
//     write_element(&Some(&p.hash_algorithm));
// }

fn main() {}
