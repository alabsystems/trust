//~ NOTE "proved":0,"failed":1,"unknown":0,"timed_out":0,"skipped":0,"runtime_checked":1,"cached":0,"total":2}
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
//! Regression `discharge-cycle`, review defect 1 (2026-10-06), the control: `top`,
//! OUTSIDE the `inner` → `inner2` → `outer` → `inner` cycle, names `inner::<Bad>`.
//! `inner` was verified before its sibling `inner2` (the carrier: it dispatches
//! `t.m()`), so `inner` has no `Via` record and is no carrier; before the fix
//! `top`'s mention was taken as a real "no" and `inner2::<Bad>` got no discharge
//! row. By the time `top` is verified `inner2` IS a carrier, so the late cycle call
//! read back from `inner`'s completed body is discharged at `inner2::<Bad>`, and
//! the panicking `Bad::m` is a real `failed` refutation (the `top` pin), not an
//! `unknown`. `outer`, verified while `inner2` was not, keeps an `unknown` row for
//! `inner2::<Good>`.
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

pub struct Good;

impl Tr for Good {
    fn m(&self) -> u32 {
        1
    }
}

fn inner2<T: Tr>(t: &T, n: u32) -> u32 {
    //[strict]~^ ERROR Trust strict verification failed for `mutual_recursion_discharge_late_cycle_call_refuted::inner2`
    let _ = t.m();
    outer(n)
}

fn inner<T: Tr>(t: &T, n: u32) -> u32 {
    //[strict]~^ ERROR Trust strict verification failed for `mutual_recursion_discharge_late_cycle_call_refuted::inner`
    inner2(t, n)
}

fn outer(n: u32) -> u32 {
    //[advisory]~^ WARN Trust instance discharge not established for `mutual_recursion_discharge_late_cycle_call_refuted::outer`: 1 instance(s)
    //[strict]~^^ ERROR Trust instance discharge not established for `mutual_recursion_discharge_late_cycle_call_refuted::outer`: 1 instance(s)
    //[strict]~^^^ ERROR Trust strict verification failed for `mutual_recursion_discharge_late_cycle_call_refuted::outer`
    if n == 0 { 0 } else { inner(&Good, n - 1) }
}

pub fn top() -> u32 {
    //[advisory]~^ WARN Trust instance discharge not established for `mutual_recursion_discharge_late_cycle_call_refuted::top`: 1 instance(s)
    //[strict]~^^ ERROR Trust instance discharge not established for `mutual_recursion_discharge_late_cycle_call_refuted::top`: 1 instance(s)
    //[strict]~^^^ ERROR Trust strict verification failed for `mutual_recursion_discharge_late_cycle_call_refuted::top`
    inner(&Bad, 0)
}
