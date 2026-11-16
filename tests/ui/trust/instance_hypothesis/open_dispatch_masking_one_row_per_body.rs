//~ NOTE "proved":0,"failed":0,"unknown":6,"timed_out":0,"skipped":6,"runtime_checked":0,"cached":0,"total":6}
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
//! OD-1 (docs/design/2026-10-03-open-generic-dispatch-obligations.md). Phase 0 pinned
//! the masking here: four unresolved calls through an open, uncontracted trait on the
//! body's own type parameter published ONE `[trust-absent-callee-assumption]` row,
//! `failed` (`"failed":1,"skipped":1,"total":2`, stage-1 `fbe76cb938`), because the
//! whole-function panic-freedom FOLD collected every absent callee into one row named
//! after its first site.
//!
//! UPDATED DELIBERATELY BY PHASE 1 (2026-10-04), as the phase-0 note required (design
//! §6: "4-call body (4 hypothesis rows, 0 failed)"): each admitted site is lowered
//! without the `Assert(false)` marker and without a `PanicFreedom` obligation, so it is
//! no fold site, and the compiler mints its row OUTSIDE the fold, one per site. Line 1
//! pins `"failed":0` and six skipped rows: the four per-site
//! `assumption:instance-hypothesis` rows (the warning below counts them), the crate's
//! one `assumption:instance-hypothesis:inventory-incomplete` row and the vacuous
//! global-alloc contract row. No proved row: the claim is relative to the hypotheses,
//! so the synthetic `no_obligations` row is withheld. Strict passes CONDITIONALLY,
//! certify refuses.
pub trait Tr {
    fn m(&self) -> u32;
}

pub fn four<T: Tr>(t: &T) -> u32 {
    //[certify]~^ ERROR Trust certify verification failed for `open_dispatch_masking_one_row_per_body::four`: 4 instance hypothesis row(s)
    //[advisory]~^^ WARN `open_dispatch_masking_one_row_per_body::four`: 4 instance hypothesis row(s)
    //[strict]~^^^ WARN `open_dispatch_masking_one_row_per_body::four`: 4 instance hypothesis row(s)
    let a = t.m();
    let b = t.m();
    let c = t.m();
    let d = t.m();
    a.wrapping_add(b).wrapping_add(c).wrapping_add(d)
}
