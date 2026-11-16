//@ needs-trust-verify
//@ edition: 2021
//@ aux-crate: core=step_by_range_impostor/core.rs
//@ revisions: certify strict
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[strict] compile-flags: -Ztrust-policy=strict
//@ rustc-env:TRUST_NATIVE_DEBUG=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//@ forbid-output: role=iterator-step-by
//~? RAW [STEP_BY_CANDIDATE] fn=step_by_constructor_no_core_range_lang_item_impostor_refuted::victim role=NONE
//! THE PLANTED REFUTATION for `step_by_constructor::candidate` deciding "this
//! callee is core's `Iterator::step_by`" from SOURCE-DECLARABLE anchors only:
//! the `Range` lang item's crate, the `Iterator` diagnostic item, and a rendered
//! `core::iter::adapters::step_by::StepBy` path.
//!
//! This crate is `#![no_core]`. The auxiliary is a whole-`core` impostor
//! (`auxiliary/step_by_range_impostor/core.rs`, crate name `core`, verify-off,
//! passed as `--extern core=`) that owns the `Range` lang item and the
//! `Iterator` diagnostic item, with a PROVIDED `step_by` that panics on every
//! call. No real `core` is loaded, so rustc's duplicate checks never fire, and
//! every conjunct of `candidate` held: the classification answered
//! `IteratorStepBy` for the impostor's body.
//!
//! MEASURED on stage-1 `trustc` at `246ceb451e5` (origin/main) plus the
//! `[STEP_BY_CANDIDATE]` trace, without the fix: `[STEP_BY_CANDIDATE]
//! fn=…::victim role=iterator-step-by callee=__trust_crate@…::<core::ops::Range<u32>
//! as core::iter::Iterator>::step_by`, in both revisions. The build still failed
//! closed (an absent-callee panic-freedom row), but only because the
//! foreign-callee collector's own admission gate (`crate_is_authentic_foundational`,
//! residency-conjoined since 2026-09-28) declined to bundle the callee, which
//! starves `derived_summary` (`(0 entries)`). `candidate` also exempts a callee
//! from the collector's total-std-iterator decline, so a TRUE answer is a grant
//! input, not a label. The fix conjoins artifact residency
//! (`trust_mir_extract::is_real_sysroot_crate`) on the `Range` lang item's crate,
//! so the classification itself refuses a non-resident `core`.
//!
//! Pinned per revision: the classification is forbidden (`forbid-output`), the
//! trace is shown to have run and declined (`RAW … role=NONE`, so the forbid is
//! not vacuous), and the call keeps its may-panic refusal. The honest control is
//! `step_by_constructor_resident_core_keeps_candidate.rs`. Fix the compiler,
//! not this file.
#![feature(no_core)]
#![no_core]

extern crate core;

use core::iter::Iterator;
use core::ops::Range;

pub fn victim() {
    //~^ ERROR Trust strict verification failed for `step_by_constructor_no_core_range_lang_item_impostor_refuted::victim`
    //[certify]~| ERROR Trust Level 0 safety verification incomplete for `step_by_constructor_no_core_range_lang_item_impostor_refuted::victim`
    let r: Range<u32> = Range { start: 0, end: 10 };
    let _s = r.step_by(2);
}
