//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Copt-level=0 --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! Trait ownership is outside the exact inherent-constructor admission.
pub struct A(pub u32);
pub trait Maker { fn new(x: u32) -> Self; }
impl Maker for A { fn new(x: u32) -> Self { Self(x) } }
pub fn make(x: u32) -> u32 {
    let a = <A as Maker>::new(x);
    if a.0 != x { panic!() }
    a.0
}
