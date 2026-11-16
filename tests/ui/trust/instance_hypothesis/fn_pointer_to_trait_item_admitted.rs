//~ NOTE "kind":"assumption:instance-hypothesis","description":"unverified assumption: [trust-instance-hypothesis] call through a fn pointer reified from `<T as fn_pointer_to_trait_item_admitted::Tr>::m` in `fn_pointer_to_trait_item_admitted::via_ptr`
//~| NOTE "proved":0,"failed":0,"unknown":2,"timed_out":0,"skipped":2,"runtime_checked":1,"cached":0,"total":3}
//~| NOTE "proved":0,"failed":1,"unknown":1,"timed_out":0,"skipped":1,"runtime_checked":1,"cached":0,"total":3}
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
//! OD-1 open shapes (2026-10-04; docs/DECISION_QUEUE.md "OD-1" item 14): a call through
//! a fn pointer the body REIFIED from an open trait item at its own parameters
//! (`let p: fn(&T) -> u32 = T::m; p(t)`) is the same open dispatch as `t.m()`: at every
//! instance the pointer IS `<τ as Tr>::m`. It is admitted under the same predicate,
//! publishes one hypothesis row (line 1, first pin), and each concrete
//! instance gets a discharge row read off the reification: `via_ptr::<Good>` is
//! `proved` (second pin: counted skipped), `via_ptr::<Bad>` is `failed` (third pin; an
//! error on the fail-closed lanes). Before this change the body published one
//! `native-verification-gap` `unknown` row and strict refused it at the indirect-call
//! gate, with no hypothesis and no per-instance charge.
pub trait Tr {
    fn m(&self) -> u32;
}

pub struct Good;
pub struct Bad;

impl Tr for Good {
    fn m(&self) -> u32 {
        1
    }
}

impl Tr for Bad {
    fn m(&self) -> u32 {
        //[strict]~^ ERROR Trust Level 0 safety verification incomplete
        //[strict]~^^ ERROR Trust strict verification failed
        //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
        //[certify]~^^^^ ERROR Trust strict verification failed
        panic!("bad")
    }
}

pub fn via_ptr<T: Tr>(t: &T) -> u32 {
    //[certify]~^ ERROR Trust certify verification failed for `fn_pointer_to_trait_item_admitted::via_ptr`: 1 instance hypothesis row(s)
    let p: fn(&T) -> u32 = T::m;
    p(t)
}

pub fn use_good() -> u32 {
    //[certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^ ERROR Trust strict verification failed
    via_ptr(&Good)
}

pub fn use_bad() -> u32 {
    //[strict]~^ ERROR Trust instance discharge not established for `fn_pointer_to_trait_item_admitted::use_bad`
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^ ERROR Trust instance discharge not established for `fn_pointer_to_trait_item_admitted::use_bad`
    //[certify]~^^^^ ERROR Trust strict verification failed
    via_ptr(&Bad)
}
