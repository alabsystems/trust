//@ needs-trust-verify
//@ edition: 2021
//@ revisions: refused control
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[refused] check-fail
//@[control] check-pass
//! Review round 69: `#[derive(PartialOrd)]` on a type that also has an `Ord` impl
//! expands to `Some(Ord::cmp(self, other))`, so `a < b` runs the fields' `Ord::cmp`.
//! The comparison sentinel erased `a < b` after checking the fields only under
//! `PartialOrd`, and a field with a derived `PartialOrd` but a hand-written panicking
//! `Ord` slipped through. `control` pins that a fully derived comparison still erases.
#![allow(dead_code)]

#[cfg(refused)]
#[derive(PartialEq, Eq, PartialOrd, Clone, Copy)]
pub struct F(pub u32);

#[cfg(refused)]
impl Ord for F {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        let t = [0u32; 10];
        t[(self.0 % 11) as usize].cmp(&other.0)
    }
}

#[cfg(refused)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct K(pub F);

#[cfg(refused)]
pub fn less(a: &K, b: &K) -> bool {
    //[refused]~^ ERROR Trust strict verification failed for `partial_ord_delegates_to_ord::less`
    a < b
}

#[cfg(control)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct D(pub u32);

#[cfg(control)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct E(pub D, pub u8);

#[cfg(control)]
pub fn less(a: &E, b: &E) -> bool {
    a < b
}

/// Review round 70: a HAND-WRITTEN `Ord` never coexists with `#[derive(Ord)]`, so a
/// derived `PartialOrd` beside it is field-wise and never calls it; that comparison
/// erases.
#[cfg(control)]
#[derive(PartialEq, Eq, PartialOrd)]
pub struct Rev {
    pub x: u8,
}

#[cfg(control)]
impl Ord for Rev {
    fn cmp(&self, o: &Self) -> core::cmp::Ordering {
        o.x.cmp(&self.x)
    }
}

#[cfg(control)]
pub fn vec_less(a: &Vec<Rev>, b: &Vec<Rev>) -> bool {
    a < b
}

/// Review round 70: a derived field whose type is a PROJECTION naming a hand-written
/// type was skipped by the container check (selection on the unnormalized alias is not
/// "unimplemented", it is unresolved). Fields are now normalized first.
#[cfg(refused)]
pub trait Tr {
    type A;
}
#[cfg(refused)]
impl Tr for u32 {
    type A = H;
}
#[cfg(refused)]
pub struct H(pub u32);
#[cfg(refused)]
impl PartialEq for H {
    fn eq(&self, o: &Self) -> bool {
        let t = [0u32; 4];
        t[(self.0 % 5) as usize] == o.0
    }
}
#[cfg(refused)]
#[derive(PartialEq)]
pub struct P(pub Box<<u32 as Tr>::A>);

#[cfg(refused)]
pub fn same(a: &P, b: &P) -> bool {
    //[refused]~^ ERROR Trust strict verification failed for `partial_ord_delegates_to_ord::same`
    a == b
}
