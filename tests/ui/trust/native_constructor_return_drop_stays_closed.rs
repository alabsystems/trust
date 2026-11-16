//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Copt-level=0 --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! A scalar field cannot hide the output type's reachable destructor panic.
pub struct A(pub u32);
impl A { pub fn new(x: u32) -> Self { Self(x) } }
impl Drop for A {
    fn drop(&mut self) { if self.0 == 7 { panic!() } }
}
pub fn make(x: u32) -> u32 {
    let a = A::new(x);
    if a.0 != x { panic!() }
    a.0
}
