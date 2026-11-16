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
//! Regression `discharge-cycle` (2026-10-05), the other order: `inner<T>` is
//! declared BEFORE `outer`, so inside their mutual-recursion SCC the callee-first
//! demand order verifies `outer` first. When `outer` names `inner::<Good>`, `inner`
//! has recorded no sites yet (the ledger is filled in verification order) and its
//! `optimized_mir` cannot be demanded without a query cycle, so the carrier test
//! said "no" and the instance was NEVER discharged — no row at all (`outer` pinned
//! `"unknown":1,"total":3`). It is now an `unknown` discharge row (the pin:
//! `"unknown":2,"total":4`) — not established, a warning on advisory and an error on
//! strict — never `failed` (nothing was refuted) and never silent. The termination
//! rows of the unmeasured recursion are the strict revision's other errors.
pub trait Tr {
    fn m(&self) -> u32;
}

pub struct Good;

impl Tr for Good {
    fn m(&self) -> u32 {
        1
    }
}

fn inner<T: Tr>(t: &T, n: u32) -> u32 {
    //[strict]~^ ERROR Trust strict verification failed for `mutual_recursion_discharge_carrier_verified_later::inner`
    let _ = t.m();
    outer(n)
}

pub fn outer(n: u32) -> u32 {
    //[advisory]~^ WARN Trust instance discharge not established for `mutual_recursion_discharge_carrier_verified_later::outer`: 1 instance(s)
    //[strict]~^^ ERROR Trust instance discharge not established for `mutual_recursion_discharge_carrier_verified_later::outer`: 1 instance(s)
    //[strict]~^^^ ERROR Trust strict verification failed for `mutual_recursion_discharge_carrier_verified_later::outer`
    if n == 0 { 0 } else { inner(&Good, n - 1) }
}
