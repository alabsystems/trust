//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Copt-level=0 --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! Same short names and scalar layouts do not identify a checked return value.
pub mod left {
    pub struct A(pub u32);
    impl A { pub fn new(_x: u32) -> Self { Self(0) } }
}
pub mod right {
    pub struct A(pub u32);
    impl A { pub fn new(x: u32) -> Self { Self(x) } }
}
pub fn make(x: u32) -> u32 {
    let a = left::A::new(x);
    let b = right::A::new(x);
    if a.0 != b.0 { panic!() }
    a.0
}
