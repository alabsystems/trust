//~ NOTE "proved":1,"failed":0,"unknown":2,"timed_out":0,"skipped":1,"runtime_checked":1,"cached":0,"total":4}
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
//! Regression `discharge-cycle` (2026-10-05, ty's `cvw::same_representation` ↔
//! `cvw::all_same`): a hypothesis-carrying generic in a MUTUAL-RECURSION cycle with
//! the body that names its instance. `inner<T>` dispatches `t.m()` (an admitted
//! site) and calls `outer`, which names `inner::<Good>`. The callee-first demand
//! order verifies `inner` first, so its `optimized_mir` has COMPLETED when `outer`'s
//! discharge reads the site back; the cycle oracle still declines every member of
//! the SCC, and the discharge used to publish `failed` ("unresolvable: the
//! definition's MIR is being computed up this stack") — a refutation of an instance
//! nothing refuted, and a strict error on `outer`. The read-back now takes the
//! completed body from the query cache (no provider runs, no cycle) and the row
//! carries the callee's own verdict: `proved` (the pin: the whole-function row and
//! the discharge row, counted `skipped`, no credit; it was
//! `"failed":1,"unknown":1,"skipped":0`), and `outer` owes no discharge error. The
//! refutation twin is `mutual_recursion_discharge_refutation_kept.rs`. Both
//! functions carry an unproved termination row (the recursion has no `decreases`),
//! which is what the strict revision's errors are.
pub trait Tr {
    fn m(&self) -> u32;
}

pub struct Good;

impl Tr for Good {
    fn m(&self) -> u32 {
        1
    }
}

pub fn outer(n: u32) -> u32 {
    //[strict]~^ ERROR Trust strict verification failed for `mutual_recursion_discharge_reads_completed_carrier::outer`
    if n == 0 { 0 } else { inner(&Good, n - 1) }
}

fn inner<T: Tr>(t: &T, n: u32) -> u32 {
    //[strict]~^ ERROR Trust strict verification failed for `mutual_recursion_discharge_reads_completed_carrier::inner`
    let _ = t.m();
    outer(n)
}
