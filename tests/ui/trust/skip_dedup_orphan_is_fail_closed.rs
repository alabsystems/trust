//@ needs-trust-verify
//@ revisions: deduped orphaned
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[orphaned] rustc-env:TRUST_SKIP_DEDUP_ORPHAN_FAULT=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! THE PLANTED REFUTATION for the skip-deduplication lane.
//!
//! `#[trust::skip]` on a function covers the closures defined inside it — one
//! attribute, one gap — so the closures' own `Trust full verification skipped`
//! errors are DEFERRED to the declaration rather than printed again. The
//! deferral is only sound if the declaration actually reports. Round 1 argued
//! that it must: the declaration is local and function-like, so it reaches the
//! same pass, takes the same `UserOptOut` decision under the same policy, and
//! errors. That is an implication over `classify_def` agreement, walk
//! reachability and policy agreement — and if it ever fails, the closures'
//! findings are withheld and NOTHING says so. A gap reaches a green build.
//!
//! The divergence is reachable for real: `verification_decision` consults
//! `classify_def` (a PER-DEF classification, narrowable by the step-4 library
//! lane) BEFORE it ever looks at `#[trust::skip]`. A declaration classified
//! out-of-scope returns `Skip(ExternalDependencyScope)` and prints nothing,
//! while a nested body classified in-scope still returns `Skip(UserOptOut)`
//! and is deferred to that silent declaration.
//!
//! `TRUST_SKIP_DEDUP_ORPHAN_FAULT` puts the census into exactly that state by
//! rewriting the recorded ORIGIN to a name no declaration can carry. It cannot
//! mute anything: the declaration still emits its own error, and the knob's
//! only possible effect is that the reconciliation ADDS the recovered ones.
//!
//! `deduped` (no fault): the declaration reports and the two closures are
//! folded into it — EXACTLY one skip error. ERROR annotations are required in
//! both revisions (no `dont-require-annotations: ERROR`), so a closure error
//! that came back unannotated fails this revision: it pins the deduplication
//! itself, not only its fail-closed recovery.
//!
//! `orphaned` (fault): the deferral points at nothing, and the crate
//! checkpoint emits the two withheld errors itself rather than dropping them.
//! Under round 1 this revision produced NO error for either closure: the
//! `duplicate_of_declaration` arm had no emission path at all.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![feature(register_tool)]
#![register_tool(trust)]

#[trust::skip]
pub fn parent(v: &[u32]) -> u32 {
    // The declaration reports in BOTH revisions: the fault knob rewrites only
    // the recorded ORIGIN of a deferral, never an emission.
    //~^^^ ERROR Trust full verification skipped `skip_dedup_orphan_is_fail_closed::parent`
    let f = |a: u32| a + 1;
    //[orphaned]~^ ERROR Trust full verification skipped `skip_dedup_orphan_is_fail_closed::parent::{closure#0}`
    let g = |a: u32| a + 2;
    //[orphaned]~^ ERROR Trust full verification skipped `skip_dedup_orphan_is_fail_closed::parent::{closure#1}`
    // ONLY under the injected orphan state do those two deferred closure bodies
    // come back — emitted by the crate checkpoint, which is the whole point.
    v.iter().copied().map(f).map(g).sum()
}
