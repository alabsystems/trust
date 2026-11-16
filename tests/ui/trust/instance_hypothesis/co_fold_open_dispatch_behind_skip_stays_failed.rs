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
//! OD-1 phase 0 review (KNOWN_HAZARDS, CLOSED 2026-10-04): the co-fold gap through
//! the ADVISORY expected-absent demotion. The panic-freedom aggregate keeps the
//! text of its FIRST fold site; here that is the `#[trust::skip]` callee
//! `skipped_helper`, and the open, uncontracted generic dispatch `<T as Tr>::m` is
//! co-folded behind it. The per-fold-site refutation stamped the row `failed`, then
//! the expected-absent post-pass (`-Ztrust-policy=advisory`, which is what
//! `targo trust check --allow-l0-gaps` passes) rewrote every non-proved row with the
//! expected-absent prefix into a `skipped` assumption row. Measured on the phase-0
//! build `52d352514b` (2026-10-04): JSON `"failed":0,…,"skipped":2` beside a Level-0
//! summary of "1 failed", while the reverse statement order published `failed`. A
//! refuted row is now never demoted: line 1 pins `"failed":1` (the only total-2 body
//! here; `skipped_helper` publishes total 1) in both lanes.
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

#[trust::skip]
pub fn skipped_helper(x: u32) -> u32 {
    //[strict]~^ ERROR Trust full verification skipped
    x
}

pub fn skip_first<T: Tr>(t: &T, p: *const u8) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~| ERROR Trust strict verification failed
    let a = skipped_helper(1);
    a.wrapping_add(t.m(p))
}
