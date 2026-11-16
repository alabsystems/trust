//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-pass
//@ dont-check-compiler-stderr
//! A function with a BY-VALUE argument of an uninhabited type can never be entered:
//! no value of that type exists, so its body starts at `Unreachable` and there is
//! nothing to verify. It used to take the fatal `UnreachableStart` skip, which
//! refused the common `impl From<Infallible> for MyError` (sweep `m22`, `p48`). The
//! refusing twin keeps an `unreachable_unchecked` body and an argument that is only a
//! REFERENCE to an uninhabited type (itself inhabited) refused.
use std::convert::Infallible;

pub enum Void {}

pub enum MyError {
    Bad,
}

impl From<Infallible> for MyError {
    fn from(x: Infallible) -> Self {
        match x {}
    }
}

pub fn void_and_more(v: Void, y: u8) -> u8 {
    let _ = y;
    match v {}
}
