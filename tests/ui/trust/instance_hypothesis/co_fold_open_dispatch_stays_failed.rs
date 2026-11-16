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
//! OD-1 phase 0, the co-fold gap (design §2.4; KNOWN_HAZARDS, CLOSED 2026-10-04).
//! The panic-freedom aggregate is named after its FIRST marked site. Here that is
//! the tolerated concrete `Vec::<u32>::push`; the open, uncontracted generic
//! dispatch `<T as Tr>::m` is co-folded behind it. Measured on stage-1
//! `fbe76cb938` (2026-10-04): the row published `runtime_checked` and the Level-0
//! summary read "0 failed, 0 unknown or timed out, 1 runtime-checked" (JSON
//! `"failed":0,…,"runtime_checked":1`), while the same two calls in the other order
//! (`co_fold_open_dispatch_first_control.rs`) published `failed` — so
//! `targo trust check --allow-l0-gaps` would have conditional-passed this body.
//! The refutation is now decided per fold site: line 1 pins the row `failed` and
//! nothing runtime-checked; the strict summary is an ERROR with "1 failed".
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

pub fn concrete_first<T: Tr>(v: &mut Vec<u32>, t: &T, p: *const u8) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~| ERROR Trust strict verification failed
    v.push(1);
    t.m(p)
}
