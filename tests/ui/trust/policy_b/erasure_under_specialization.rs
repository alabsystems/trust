//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Review round 68: under specialization a derived impl inherits every method it does
//! not define from a parent `default fn` impl. `#[derive(PartialEq)]` defines only `eq`,
//! so `a != b` ran the user's `default fn ne`, and the comparison sentinel erased the
//! call on the strength of the derive. A crate enabling specialization gets no
//! derived-impl erasure.
#![allow(incomplete_features)]
#![feature(specialization)]
#![allow(dead_code)]

#[derive(PartialEq)]
pub struct W<T>(pub u32, pub *const T);

impl<T> PartialEq for W<T> {
    default fn eq(&self, o: &Self) -> bool {
        self.0 == o.0
    }
    default fn ne(&self, o: &Self) -> bool {
        self.0.ilog2() != o.0
    }
}

pub fn differs(a: W<u32>, b: W<u32>) -> bool {
    //~^ ERROR Trust strict verification failed for `erasure_under_specialization::differs`
    a != b
}
