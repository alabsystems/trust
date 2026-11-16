//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Copt-level=0 --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-pass
//! Distinct inherent bodies and output types may share the short names A/new.
//! Each assertion needs its own exact source proof; no aggregate proof is lent.
pub mod left {
    pub struct A(pub u32);
    impl A { pub fn new(x: u32) -> Self { Self(x) } }
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
