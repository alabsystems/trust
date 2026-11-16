//~ NOTE "proved":0,"failed":2,"unknown":1,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":3}
//~| NOTE "proved":0,"failed":1,"unknown":1,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":2}
//~| NOTE "proved":0,"failed":1,"unknown":1,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":2}
//~| NOTE "proved":0,"failed":1,"unknown":1,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":2}
//@ revisions: advisory strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-fail
//@[certify] check-fail
//! OD-1 phase 1 review (2026-10-04, D2): the argument-shape walk NORMALIZES every type
//! (the argument's and each ADT field's) in the body's typing environment before
//! shaping it. Before the fix an ADT field's projection was shaped unnormalized as an
//! inert type parameter, so a raw pointer (`<*mut u8 as Id>::Out`), a `&mut`
//! (`G<&mut u8>`'s `X::Out`) or a shared reference to a `Cell` hidden behind one was
//! ADMITTED with no havoc: the class (c) `failed` row was swapped for a conditional
//! hypothesis row at a site the design refuses. Every site here is now refused and
//! keeps its absent-callee `failed` row. `hidden_mut_ref_generic` is the case the alias
//! rule alone does not catch: `<&mut (u8, V) as Id>::Out` is still rooted in the
//! parameter `V` until the field type is normalized to the `&mut` it is. No function
//! carries a hypothesis row (pins:
//! `hidden_raw` also keeps its `&raw mut` row; the `skipped` row is the global-alloc
//! contract), and no `certify` error names an instance hypothesis.
use std::cell::Cell;

pub trait Id {
    type Out;
}

impl<X> Id for X {
    type Out = X;
}

pub struct P {
    pub p: <*mut u8 as Id>::Out,
}

pub struct G<X: Id> {
    pub r: X::Out,
}

pub struct C<'a> {
    pub c: <&'a Cell<u8> as Id>::Out,
}

pub trait Tr {
    fn raw(&self, h: P);
    fn mutref<'a>(&self, h: G<&'a mut u8>);
    fn cell(&self, h: C<'_>);
    fn mutref_generic<'a, U>(&self, h: G<&'a mut (u8, U)>);
}

pub fn hidden_raw<T: Tr>(t: &T) -> u8 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    let mut x: u8 = 0;
    t.raw(P { p: &mut x as *mut u8 });
    x
}

pub fn hidden_mut_ref<T: Tr>(t: &T) -> u8 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    let mut x: u8 = 0;
    t.mutref(G { r: &mut x });
    x
}

pub fn hidden_cell<T: Tr>(t: &T) -> u8 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    let c = Cell::new(0u8);
    t.cell(C { c: &c });
    c.get()
}

pub fn hidden_mut_ref_generic<T: Tr, V>(t: &T, v: V) -> u8 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    let mut x = (0u8, v);
    t.mutref_generic(G { r: &mut x });
    x.0
}
