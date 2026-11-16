//~ NOTE "proved":0,"failed":1,"unknown":1,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":2}
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
//! Control for `co_fold_open_dispatch_stays_failed.rs`: the same two calls with
//! the open dispatch FIRST, so the aggregate's representative is the open site
//! itself. This was `failed` before the per-fold-site fix (stage-1 `fbe76cb938`)
//! and must stay so; the two orders publish the same verdict.
//!
//! OD-1 phase 1 (2026-10-04): an open dispatch whose argument is a raw pointer is NOT
//! admitted as an instance hypothesis (design §2.3), so it keeps class (c) and this
//! fixture still pins the per-fold-site refutation. Before phase 1 the call took no
//! pointer; with that shape it is now admitted, is no fold site at all, and publishes
//! an `assumption:instance-hypothesis` row instead
//! (`co_fold_admitted_site_is_no_fold_site.rs`).
pub trait Tr {
    fn m(&self, p: *const u8) -> u32;
}

pub fn open_first<T: Tr>(v: &mut Vec<u32>, t: &T, p: *const u8) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~| ERROR Trust strict verification failed
    let r = t.m(p);
    v.push(1);
    r
}
