//~ NOTE "proved":1,"failed":0,"unknown":2,"timed_out":0,"skipped":0,"runtime_checked":1,"cached":0,"total":4}
//@ revisions: advisory strict
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-fail
//! Regression `discharge-cycle`, review defect 1 (2026-10-06): the carrier is a
//! SIBLING verified after the generic that reaches it. `inner<T>` calls `inner2<T>`,
//! which dispatches `t.m()` and calls `outer` back; `outer` names `inner::<Bad>`.
//! Declared in this order, the SCC is verified `inner`, `outer`, `inner2`: when
//! `inner` was verified `inner2` had recorded no sites, so `inner` got no `Via`
//! record, and `outer`'s mention of the COMPLETED `inner::<Bad>` (no carrier) was
//! taken as a real "no" — `inner2::<Bad>` (whose `Bad::m` panics) was never
//! discharged anywhere, no row at all. The late cycle call is now re-read from
//! `inner`'s completed body: `inner2` is still unverified there, so the row is
//! `unknown` (not established; a warning on advisory, an error on strict), never
//! silent. The control that a sibling verified by then is really discharged (and
//! refuted) is `mutual_recursion_discharge_late_cycle_call_refuted.rs`.
pub trait Tr {
    fn m(&self) -> u32;
}

pub struct Bad;

impl Tr for Bad {
    fn m(&self) -> u32 {
        //[strict]~^ ERROR Trust Level 0 safety verification incomplete
        //[strict]~^^ ERROR Trust strict verification failed
        panic!("bad")
    }
}

fn inner2<T: Tr>(t: &T, n: u32) -> u32 {
    //[strict]~^ ERROR Trust strict verification failed for `mutual_recursion_discharge_sibling_verified_later::inner2`
    let _ = t.m();
    outer(n)
}

fn inner<T: Tr>(t: &T, n: u32) -> u32 {
    //[strict]~^ ERROR Trust strict verification failed for `mutual_recursion_discharge_sibling_verified_later::inner`
    inner2(t, n)
}

pub fn outer(n: u32) -> u32 {
    //[advisory]~^ WARN Trust instance discharge not established for `mutual_recursion_discharge_sibling_verified_later::outer`: 1 instance(s)
    //[strict]~^^ ERROR Trust instance discharge not established for `mutual_recursion_discharge_sibling_verified_later::outer`: 1 instance(s)
    //[strict]~^^^ ERROR Trust strict verification failed for `mutual_recursion_discharge_sibling_verified_later::outer`
    if n == 0 { 0 } else { inner(&Bad, n - 1) }
}
