//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off --crate-type=lib
//@ check-pass
//! `-Ztrust-verify=off` must compile a contract-bearing crate CLEANLY.
//!
//! In the compatibility lane the contract is deliberately NOT CHECKED, so the
//! correct behaviour is: no ICE, no obligations, no verification report — the
//! `ensures` clauses below are simply inert.
//!
//! REGRESSION (the off-switch ICE). `trust_check_clean_islands` runs the
//! `trust_contracts` query unconditionally, including under
//! `-Ztrust-verify=off`, because contract bundles are language-integrity /
//! metadata work rather than verifier-router work. While building the
//! source-sort environment for a contract's parameters,
//! `loop_source_sort_from_ty` named each opaque aggregate with a bare
//! `format!("{ty}")`. Displaying a `DefId`-bearing type consults the
//! `trimmed_def_paths` query, which arms `DiagCtxt::set_must_produce_diag`;
//! rustc then asserts at drop that a diagnostic was actually emitted. With
//! verification off nothing is ever emitted, so EVERY contract-bearing crate
//! aborted with
//!
//!     `trimmed_def_paths` called, diagnostics were expected but none were emitted
//!
//! at `rustc_errors/src/lib.rs`. The fix routes those names through
//! `opaque_sort_name`, i.e. `with_no_trimmed_paths!` — the same policy
//! `trust_mir_extract::safe_def_path_str` already applies to every other Trust
//! identity string, and independently required for sort identity: a trimmed
//! path is a context-dependent, non-injective spelling and must never decide
//! `Sort::Datatype` equality.
//!
//! `//@ needs-trust-verify` matches the sibling verify-off fixtures
//! (`clean_island_no_verify_sorry.rs`). Its only effect here is that the
//! `--trust-vanilla` replay skips this file; since the flags above are explicit,
//! that replay would have run it in exactly the same mode, so nothing is lost.
//!
//! THIS TEST DELIBERATELY HAS NO `.stderr` FILE. Expected compiler output is
//! exactly empty, which is what pins "no obligations": under `-Ztrust-verify=off`
//! a Trust verification report is a `note:` on stderr, so any obligation
//! reaching the reporter would fail this test. Do NOT add
//! `dont-check-compiler-stderr` here — that would discard the pin.
//!
//! Each item below covers a distinct arm of `loop_source_sort_from_ty` that
//! reaches a `DefId`-bearing `Display`; all of them ICEd before the fix, and a
//! purely scalar signature did not, so the coverage is not incidental.

pub struct S {
    pub flag: bool,
}

pub struct P {
    pub a: i32,
}

// `ty::Adt` behind `&mut` — the original `abort_reflow_offload`-shaped repro.
impl S {
    pub fn close(&mut self)
        ensures !self.flag
    {
        self.flag = false;
    }
}

// `ty::Adt` by value.
pub fn take(s: S) -> bool
    ensures result == result
{
    s.flag
}

// A foreign generic `ty::Adt`. `std::vec::Vec<i32>` is precisely the shape a
// trimmed path shortens (to `Vec<i32>`), so this is the sharpest trimming
// trigger available.
pub fn borrow_vec(v: &Vec<i32>) -> usize
    ensures result == result
{
    v.len()
}

// `ty::Array` whose element is an ADT: the element recurses into the `ty::Adt`
// arm.
pub fn first_of_array(xs: &[P; 2]) -> i32
    ensures result == result
{
    xs[0].a
}

// `ty::Slice` whose element has NO source sort (`&P` is a reference), so the
// name comes from the separate `unwrap_or_else` fallback rather than the
// `ty::Adt` arm. Both fallbacks had to be fixed.
pub fn len_of_ref_slice(xs: &[&P]) -> usize
    ensures result == result
{
    xs.len()
}

// Contrast case: a purely scalar signature never reaches a `DefId` display and
// never ICEd, so it documents the boundary of the bug rather than re-testing
// it. NOTE the honest limit of this file: with verification off a contract is
// inert BY DESIGN, so nothing here can distinguish "contracts lower and are
// not checked" from "contracts do not lower at all". That contracts really do
// lower into obligations is pinned by the `-Ztrust-verify=on` tests beside
// this one; this file pins only the compatibility lane's silence.
pub fn scalar(x: i32) -> i32
    requires x > 0
    ensures result == x
{
    x
}
