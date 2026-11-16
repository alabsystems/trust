//~ NOTE "proved":0,"failed":0,"unknown":3,"timed_out":0,"skipped":3,"runtime_checked":0,"cached":0,"total":3}
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
//! OD-1 phase 1 (docs/DECISION_QUEUE.md "OD-1"; design §2): ONE admitted open generic
//! dispatch site. `<T as Tr>::m` on the body's own type parameter, open, uncontracted,
//! unresolved, in a body with no unsafe operation and no raw-pointer argument, is no
//! longer a `failed` `[trust-absent-callee-assumption]` row (class (c) of "L0
//! refutation rows"): the body publishes one `assumption:instance-hypothesis` row
//! (skipped, `trust-classifier`), plus the crate's one inventory-incomplete row and the
//! vacuous global-alloc contract row (line 1: three skipped rows, nothing failed or
//! proved), and nothing failed. Advisory and strict pass (the
//! strict lane CONDITIONALLY: the rows are in the denominator, never proved); certify
//! refuses.
pub trait Tr {
    fn m(&self) -> u32;
}

pub fn one<T: Tr>(t: &T) -> u32 {
    //[certify]~^ ERROR Trust certify verification failed for `admitted_single_site::one`: 1 instance hypothesis row(s)
    //[advisory]~^^ WARN `admitted_single_site::one`: 1 instance hypothesis row(s)
    //[strict]~^^^ WARN `admitted_single_site::one`: 1 instance hypothesis row(s)
    t.m()
}
