//~ NOTE "proved":1,"failed":1,"unknown":1,"timed_out":0,"skipped":0,"runtime_checked":1,"cached":0,"total":4}
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
//! Regression `discharge-cycle` (2026-10-05), the control of
//! `mutual_recursion_discharge_reads_completed_carrier.rs`: the same mutual-recursion
//! shape at a PANICKING impl. `outer` names `inner::<Bad>`; the completed body is read
//! back, the site resolves to `Bad::m`, which panics, and the discharge row stays
//! `failed` (the pin: `"failed":1`, with the callee's reason, not "unresolvable") — a
//! warning on advisory and an error on strict. Reading a completed body never turns a
//! refutation OD-1 published into anything weaker.
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

pub fn outer(n: u32) -> u32 {
    //[advisory]~^ WARN Trust instance discharge not established for `mutual_recursion_discharge_refutation_kept::outer`: 1 instance(s)
    //[strict]~^^ ERROR Trust instance discharge not established for `mutual_recursion_discharge_refutation_kept::outer`: 1 instance(s)
    //[strict]~^^^ ERROR Trust strict verification failed for `mutual_recursion_discharge_refutation_kept::outer`
    if n == 0 { 0 } else { inner(&Bad, n - 1) }
}

fn inner<T: Tr>(t: &T, n: u32) -> u32 {
    //[strict]~^ ERROR Trust strict verification failed for `mutual_recursion_discharge_refutation_kept::inner`
    let _ = t.m();
    outer(n)
}
