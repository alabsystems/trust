//~ NOTE "proved":0,"failed":0,"unknown":2,"timed_out":0,"skipped":2,"runtime_checked":0,"cached":0,"total":2}
//~| NOTE "proved":1,"failed":0,"unknown":1,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":2}
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
//@[strict] check-pass
//@[certify] check-fail
//! OD-1 open shapes (2026-10-04; docs/DECISION_QUEUE.md "OD-1" item 14): a caller of a
//! generic helper that does open dispatch. `caller<T>` calls `helper::<T>`, still
//! generic; `helper` carries an instance hypothesis and its own rows prove everything
//! else (the instance-RELATIVE evidence bar). The call is now lowered UNDER the
//! propagated hypothesis (havoc, no absent-callee marker), so `caller` publishes the
//! propagated hypothesis row and the global-alloc row, and nothing `runtime_checked`
//! (line 1, first pin). Before this change it also published
//! "call to absent callee `helper::<T>` (body not in the lowered bundle)"
//! `runtime_checked`, and strict refused it. `concrete` names `caller::<Good>` and
//! discharges `helper`'s site THROUGH `caller` (second pin: a `proved` discharge row,
//! counted skipped). Strict passes CONDITIONALLY; certify refuses both carriers.
//! Controls: `propagated_call_not_admitted_controls.rs`.
pub trait Tr {
    fn m(&self) -> u32;
}

pub struct Good;

impl Tr for Good {
    fn m(&self) -> u32 {
        1
    }
}

pub fn helper<T: Tr>(t: &T) -> u32 {
    //[certify]~^ ERROR Trust certify verification failed for `propagated_call_lowered_under_hypotheses::helper`: 1 instance hypothesis row(s)
    t.m()
}

pub fn caller<T: Tr>(t: &T) -> u32 {
    //[certify]~^ ERROR Trust certify verification failed for `propagated_call_lowered_under_hypotheses::caller`: 1 instance hypothesis row(s)
    helper(t)
}

pub fn concrete() -> u32 {
    caller(&Good)
}
