//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Copt-level=0 --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! The bounded constructor recovery does not reuse a generic method's body.
pub struct A(pub u32);
impl A { pub fn new<T>(x: u32) -> Self { Self(x) } }
pub fn make(x: u32) -> u32 {
    let a = A::new::<u8>(x);
    if a.0 != x { panic!() }
    a.0
}
