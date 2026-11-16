//~ NOTE "proved":1,"failed":0,"unknown":1,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":2}
//~| NOTE "proved":0,"failed":1,"unknown":0,"timed_out":0,"skipped":0,"runtime_checked":1,"cached":0,"total":2}
//~| NOTE "proved":0,"failed":0,"unknown":3,"timed_out":0,"skipped":3,"runtime_checked":0,"cached":0,"total":3}
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
//! OD-1 phase 1: one instance discharge row per (admitted site, concrete instance)
//! this compilation names, carrying the RESOLVED callee's own verdict, keyed by the
//! interned instance (`f::<Good>` and `f::<Bad>` are two rows; one is never served
//! by the other). The definition `f` publishes its hypothesis (line 1, third pin:
//! hypothesis, inventory, global-alloc). `use_good` names `f::<Good>`: its discharge
//! row is `proved` (`Good::m` discharges panic-freedom on the shared evidence bar;
//! line 1, first pin: the whole-function row and the discharge row; the discharge row
//! is counted `skipped`, never `proved` — it reports the callee's verdict and carries
//! no proof credit of its own, review 2026-10-04). `use_bad` names
//! `f::<Bad>`: `Bad::m` panics, so its discharge row is `failed` (second pin), an
//! error on every fail-closed lane.
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

pub fn f<T: Tr>(t: &T) -> u32 {
    //[certify]~^ ERROR Trust certify verification failed for `discharge_row_per_instance::f`: 1 instance hypothesis row(s)
    t.m()
}

pub fn use_good() -> u32 {
    f(&Good)
}

pub fn use_bad() -> u32 {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete
    //[advisory]~^^ WARN Trust instance discharge not established for `discharge_row_per_instance::use_bad`: 1 instance(s)
    //[strict]~^^^ WARN Trust Level 0 safety verification incomplete
    //[strict]~^^^^ ERROR Trust instance discharge not established for `discharge_row_per_instance::use_bad`: 1 instance(s)
    //[strict]~^^^^^ ERROR Trust strict verification failed
    //[certify]~^^^^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^^^^ ERROR Trust instance discharge not established for `discharge_row_per_instance::use_bad`: 1 instance(s)
    //[certify]~^^^^^^^^ ERROR Trust strict verification failed
    f(&Bad)
}
