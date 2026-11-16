//@ revisions: field param fnitem swap mutref slice_inclusive_escape
//@ revisions: closure_field closure_whole inclusive_escape duration_closure duration_mutref
//@ revisions: controls next_then_sum
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ compile-flags: -Ztrust-verify-output=json --error-format=human
//@[field] compile-flags: -Ztrust-policy=certify
//@[param] compile-flags: -Ztrust-policy=certify
//@[fnitem] compile-flags: -Ztrust-policy=certify
//@[swap] compile-flags: -Ztrust-policy=certify
//@[mutref] compile-flags: -Ztrust-policy=certify
//@[slice_inclusive_escape] compile-flags: -Ztrust-policy=certify
//@[controls] compile-flags: -Ztrust-policy=certify
//@[next_then_sum] compile-flags: -Ztrust-policy=certify
//@[field] check-fail
//@[param] check-fail
//@[fnitem] check-fail
//@[swap] check-fail
//@[mutref] check-fail
//@[slice_inclusive_escape] check-fail
//@[closure_field] check-fail
//@[closure_whole] check-fail
//@[inclusive_escape] check-fail
//@[duration_closure] check-fail
//@[duration_mutref] check-fail
//@[controls] check-pass
//@[next_then_sum] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@[field] forbid-output: "line_start":89,"col_start":4,"line_end":89,"col_end":17},"outcome":"proved"
//@[param] forbid-output: "line_start":96,"col_start":4,"line_end":96,"col_end":17},"outcome":"proved"
//@[fnitem] forbid-output: "line_start":108,"col_start":4,"line_end":108,"col_end":17},"outcome":"proved"
//@[swap] forbid-output: "line_start":116,"col_start":4,"line_end":116,"col_end":17},"outcome":"proved"
//@[mutref] forbid-output: "line_start":124,"col_start":4,"line_end":124,"col_end":17},"outcome":"proved"
//@[slice_inclusive_escape] forbid-output: "line_start":132,"col_start":22,"line_end":132,"col_end":25},"outcome":"proved"
//@[closure_field] forbid-output: "line_start":142,"col_start":4,"line_end":142,"col_end":17},"outcome":"proved"
//@[closure_whole] forbid-output: "line_start":150,"col_start":4,"line_end":150,"col_end":17},"outcome":"proved"
//@[inclusive_escape] forbid-output: "line_start":158,"col_start":4,"line_end":158,"col_end":17},"outcome":"proved"
//@[duration_closure] forbid-output: "line_start":166,"col_start":4,"line_end":166,"col_end":30},"outcome":"proved"
//@[duration_mutref] forbid-output: "line_start":174,"col_start":4,"line_end":174,"col_end":30},"outcome":"proved"
//! CL-FOLD-LOCALDEF-1: a `Range` (or a `Duration`) that is CHANGED after it is
//! built is not the value it was built with.
//!
//! `alloc_vcs::local_def` inlines a local's one defining statement into a formula.
//! It asked only `local_defs::has_one_explicit_def`, the COUNTING question, which by
//! design does not count a field store (`Partial`) or a `&mut` alias (`Escape`). So
//! the `Iterator::sum` overflow lane (`fold_source_bound`), the slice-index lane's
//! `RangeInclusive::new` arm and the `Duration` literal lane read the construction-
//! time `0u8..4` / `0usize..=0` / `Duration::from_secs(1)` after `r.end = 200`, a
//! `&mut` callee, `mem::swap`, a store through `&mut r`, or a closure that captures
//! `r` (or `r.end`) by unique borrow had replaced it.
//!
//! BEFORE (the stage 1 of `2bf0ad72e3`, `scratchpad/stage1-w22probe`, 2026-10-11;
//! each revision's flags plus `--cfg <revision> --emit=metadata`): every revision
//! below exits 0. The certify revisions report the sum (or the slice) row `proved`
//! with clean-kernel `Certified`/`KernelRechecked` evidence ("of which 1
//! kernel-certified by the clean CIC kernel"); the default-policy revisions report
//! the same row `proved` (the closure shapes are refused under certify only by an
//! unrelated whole-function `assert` row). Built with verification off, every one of
//! these bodies panics (`fold_source_range_rewritten_after_construction_run.rs`).
//!
//! AFTER (measured 2026-10-11, stage 1 of `618d7bd287`): `local_def` asks the VALUE question
//! `local_defs::unique_value_modulo_whole_drops` (one definition, nothing else). The
//! sum rows read the `iterator-fold-overflow` Unknown and the `Duration` rows the
//! `duration-arith-overflow-unmodeled` Unknown; neither has a runtime fallback, so
//! the default policy refuses them too. The slice row is no longer resolved through
//! the overwritten `RangeInclusive::new`.
//!
//! Controls (`controls`, `next_then_sum`, check-pass under certify): an unmodified
//! `0u8..4` sum and an unmodified `0usize..=3` slice still prove; and `r.next();
//! r.sum()` still proves, because `fold_source_bound` re-admits a `&mut r` whose every
//! use is the receiver of core's own `Iterator::next` (by path and compiler-minted
//! key): `next` only moves `start` forward, so the construction-time range still
//! bounds the count and every item (DECISION_QUEUE CL-FOLD-LOCALDEF-1).

use core::ops::Range;
use std::time::Duration;

// ---- certify: each of these was a kernel-certified false proof ----

#[cfg(field)]
pub fn f() -> u8 {
    let mut r = 0u8..4;
    r.end = 200;
    r.sum::<u8>()
}

#[cfg(param)]
pub fn f(n: u8) -> u8 {
    let mut r = 0u8..4;
    r.end = n;
    r.sum::<u8>()
}

#[cfg(fnitem)]
fn widen(q: &mut Range<u8>) {
    q.end = 200;
}

#[cfg(fnitem)]
pub fn f() -> u8 {
    let mut r = 0u8..4;
    widen(&mut r);
    r.sum::<u8>()
}

#[cfg(swap)]
pub fn f() -> u8 {
    let mut r = 0u8..4;
    let mut big = 0u8..200;
    core::mem::swap(&mut r, &mut big);
    r.sum::<u8>()
}

#[cfg(mutref)]
pub fn f() -> u8 {
    let mut r = 0u8..4;
    let p = &mut r;
    p.end = 200;
    r.sum::<u8>()
}

#[cfg(slice_inclusive_escape)]
pub fn f(v: &[u8]) -> usize {
    let mut r = 0usize..=0;
    let p = &mut r;
    *p = 0..=100;
    if v.len() > 0 { v[r].len() } else { 0 }
}

// ---- default policy: the sum / `Duration` row was proved ----

#[cfg(closure_field)]
pub fn f() -> u8 {
    let mut r = 0u8..4;
    let mut g = || r.end = 200;
    g();
    r.sum::<u8>()
}

#[cfg(closure_whole)]
pub fn f() -> u8 {
    let mut r = 0u8..4;
    let mut g = || r = 0..200;
    g();
    r.sum::<u8>()
}

#[cfg(inclusive_escape)]
pub fn f() -> u8 {
    let mut r = 0u8..=3;
    let p = &mut r;
    *p = 0..=200;
    r.sum::<u8>()
}

#[cfg(duration_closure)]
pub fn f() -> Duration {
    let mut d = Duration::from_secs(1);
    let mut g = || d = Duration::MAX;
    g();
    d + Duration::from_secs(2)
}

#[cfg(duration_mutref)]
pub fn f() -> Duration {
    let mut d = Duration::from_secs(1);
    let p = &mut d;
    *p = Duration::MAX;
    d + Duration::from_secs(2)
}

// ---- controls: still proved ----

#[cfg(controls)]
pub fn f() -> u8 {
    let r = 0u8..4;
    r.sum::<u8>()
}

#[cfg(controls)]
pub fn g(v: &[u8]) -> usize {
    let r = 0usize..=3;
    if v.len() > 3 { v[r].len() } else { 0 }
}

#[cfg(next_then_sum)]
pub fn f() -> u8 {
    let mut r = 0u8..4;
    r.next();
    r.sum::<u8>()
}
