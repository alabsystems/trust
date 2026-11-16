//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Copt-level=0 --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! An interposable method cannot lend its local body's return equality.
pub struct A(pub u32);
impl A {
    #[export_name = "trust_constructor_interposed_new"]
    pub fn new(x: u32) -> Self { Self(x) }
}
pub fn make(x: u32) -> u32 {
    let a = A::new(x);
    if a.0 != x { panic!() }
    a.0
}
