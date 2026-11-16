//~ NOTE "proved":1,"failed":0,"unknown":1,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":2}
//~| NOTE "proved":1,"failed":1,"unknown":0,"timed_out":0,"skipped":0,"runtime_checked":0,"cached":0,"total":2}
//~| NOTE "proved":0,"failed":1,"unknown":0,"timed_out":0,"skipped":0,"runtime_checked":1,"cached":0,"total":2}
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
//! OD-1 phase 1 review (2026-10-04, D1): the discharge of a hypothesis carried by a
//! TRAIT-IMPL method. `<W<T> as Run>::run` carries the hypothesis for its open
//! dispatch `<T as Tr>::m`. A mention of `<W<Good> as Run>::run` names the TRAIT ITEM
//! `Run::run`; before the fix the carrier test ran on that unresolved `DefId`, found
//! no carrier, and published no discharge row, so `reify_bad` passed strict although
//! its instance reaches `Bad::m`, which panics. The test now runs on the resolved
//! instance (the impl's method):
//! * `reify_good`: a `proved` discharge row (line 1, first pin: the `no_obligations`
//!   row and the discharge row, counted `skipped` — a discharge row reports the
//!   callee's verdict and carries no proof credit of its own);
//! * `reify_bad`: a `failed` discharge row (second pin), an error on every
//!   fail-closed lane;
//! * `through<T>` calls `<W<T> as Run>::run`, which RESOLVES to the carrier at
//!   still-generic arguments: it propagates the hypothesis, and `use_through_ugly`
//!   names `through::<Ugly>`, whose discharge goes through `through` to the impl's
//!   method at `Ugly` and fails (third pin: the discharge row beside the body's
//!   unchanged `runtime_checked` absent-callee row).
//!
//! Amended 2026-10-04 (OD-1 open shapes, DECISION_QUEUE "OD-1" item 14): `through`'s
//! call is now LOWERED under the propagated hypothesis (the impl's method proves
//! everything but its hypothesis on the instance-relative bar), so `through` no longer
//! carries a `runtime_checked` absent-callee row and passes strict CONDITIONALLY;
//! certify still refuses its hypothesis row. `use_through_ugly` is unchanged.
pub trait Tr {
    fn m(&self) -> u32;
}

pub struct Good;
pub struct Bad;
pub struct Ugly;

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

impl Tr for Ugly {
    fn m(&self) -> u32 {
        //[strict]~^ ERROR Trust Level 0 safety verification incomplete
        //[strict]~^^ ERROR Trust strict verification failed
        //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
        //[certify]~^^^^ ERROR Trust strict verification failed
        panic!("ugly")
    }
}

pub trait Run {
    fn run(&self) -> u32;
}

pub struct W<T>(pub T);

impl<T: Tr> Run for W<T> {
    fn run(&self) -> u32 {
        //[certify]~^ ERROR Trust certify verification failed
        self.0.m()
    }
}

pub fn reify_good() -> fn(&W<Good>) -> u32 {
    <W<Good> as Run>::run
}

pub fn reify_bad() -> fn(&W<Bad>) -> u32 {
    //[advisory]~^ WARN Trust instance discharge not established for `trait_impl_instance_discharge::reify_bad`: 1 instance(s)
    //[strict]~^^ ERROR Trust instance discharge not established for `trait_impl_instance_discharge::reify_bad`: 1 instance(s)
    //[certify]~^^^ ERROR Trust instance discharge not established for `trait_impl_instance_discharge::reify_bad`: 1 instance(s)
    <W<Bad> as Run>::run
}

pub fn through<T: Tr>(w: &W<T>) -> u32 {
    //[advisory]~^ WARN `trait_impl_instance_discharge::through`: 1 instance hypothesis row(s)
    //[strict]~^^ WARN `trait_impl_instance_discharge::through`: 1 instance hypothesis row(s)
    //[certify]~^^^ ERROR Trust certify verification failed for `trait_impl_instance_discharge::through`: 1 instance hypothesis row(s)
    w.run()
}

pub fn use_through_ugly() -> u32 {
    //[advisory]~^ WARN Trust instance discharge not established for `trait_impl_instance_discharge::use_through_ugly`: 1 instance(s)
    //[strict]~^^ ERROR Trust instance discharge not established for `trait_impl_instance_discharge::use_through_ugly`: 1 instance(s)
    //[strict]~^^^ ERROR Trust strict verification failed
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^^ ERROR Trust instance discharge not established for `trait_impl_instance_discharge::use_through_ugly`: 1 instance(s)
    //[certify]~^^^^^^ ERROR Trust strict verification failed
    through(&W(Ugly))
}
