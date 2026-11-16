//@ needs-trust-verify
//@ edition: 2021
//@ revisions: stable opt new_range const_item inline_const
//@ revisions: guarded_loss controls
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[opt] compile-flags: -Copt-level=3
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[stable] check-fail
//@[opt] check-fail
//@[new_range] check-fail
//@[const_item] check-fail
//@[inline_const] check-fail
//@[guarded_loss] check-fail
//@[controls] check-pass
//! **Indexing a slice or `str` with the new range API's types is charged
//! (UTF8-CORE-RANGE-INDEX-1; docs/KNOWN_HAZARDS.md, "FIXED 2026-10-05 …
//! UTF8-CORE-RANGE-INDEX-1"; docs/DECISION_QUEUE.md, UTF8-CORE-RANGE-1).**
//!
//! `core::range::{Range, RangeFrom, RangeInclusive, RangeToInclusive}` (stable
//! since 1.95/1.96, and what `a..b`, `a..`, `a..=b`, `..=b` build under
//! `#![feature(new_range)]`) panic as a slice or `str` index exactly like their
//! `core::ops` namesakes: out of bounds, start past end, and for a `str` an
//! endpoint inside a character. The `RangeIndex` lane recognized only the
//! `core::ops` types, so these indexes got NO bounds row and NO char-boundary row,
//! only the policy-B absent-callee row, which the default policy reports as
//! runtime-checked.
//!
//! # Before (stage 1 of `dc15b882f6`, main plus wave 16, measured 2026-10-05 with
//! exactly these revisions' flags)
//!
//! `stable`, `opt`, `new_range`, `inline` and `guarded_loss` built rc=0, one
//! runtime-checked row per function (`TRUST_VANILLA_DEBUG=1`: the root ledger admits e.g.
//! `<str as core::ops::index::Index<core::range::RangeFrom<usize>>>::index::<__trust_str_index>`
//! as `vanilla=true`). `controls` built rc=0. The witness
//! `core_range_index_charged_run.rs` panics on the `str_from` and `slice_range`
//! bodies.
//!
//! # After (predicted before the build; measured 2026-10-06 on the stage 1 of
//! `0ac7a96d9f`, `integ/wave18`: every check-fail function is refused with "2
//! obligation(s) were not proved", the new `[slice]` row FAILED beside the old
//! runtime-checked one, and `controls` builds rc=0)
//!
//! `panic_calls::new_range_index_adt_name` makes `operand_is_panicking_range` see
//! these types. No tracer reads their layouts, so every such index takes the
//! untraceable-range fail-close: an always-violated `SliceBoundsCheck` row (for a
//! `str`, the char-boundary fail-close too), refuted, so the default policy
//! refuses. Predicted from twins on the BEFORE compiler — each check-fail body with
//! a `core::ops` range handed in by parameter (untraceable, the same arm), which
//! exits 1 for every receiver here at `-O0` and `-O3` — and from
//! `crates/trust-vcgen/tests/core_range_index_realmir.rs` (this file's functions'
//! extracted MIR: one refuted `SliceBoundsCheck` row each). `controls` (the
//! `core::ops` types, the `core::range` re-exports of `RangeTo`/`RangeFull`, which
//! the extractor prints by their `core::ops` path, and the total `get`) is unchanged.
//!
//! `inline`: an index over a `core::ops` range that an explicit MIR inliner rewrote.
//! Core's `SliceIndex<str>` impl for `core::ops::Range` forwards to the
//! `core::range::Range` impl, so under `-Zinline-mir=yes` the caller's MIR calls
//! `<core::range::Range<usize> as core::slice::index::SliceIndex<str>>::index_mut`
//! directly. `&mut s[0..5]` built rc=0 that way, BEFORE, while the same body without
//! the flag is refused; it panics "end byte index 5 is out of bounds" on `"ab"`.
//! AFTER it takes the same fail-closed row (measured). The cost has the same shape:
//! a `&mut s[0..0]` under that flag, which cannot panic, is refused too (measured:
//! rc=0 on the stage 1 of `9e11546767`, rc=1 on the stage 1 of `0ac7a96d9f`).
//!
//! # `const_item`, `inline_const`, `opt_mir`, `inline_incl` (2026-10-06, review of wave 18)
//!
//! The fix above did not reach two shapes. Both built rc=0 on the stage 1 of `0ac7a96d9f`
//! and panicked (measured; the run witness's `const_incl`, `const_str` and `inline_incl`).
//!
//! * A range that reaches the index as a CONSTANT operand, which has no type: a `const`
//!   item, an inline `const { .. }`, or a body GVN folds to a constant under `-Copt-level=3
//!   -Zmir-opt-level=2` (`opt_mir`, where `mut_str` and `mut_str_inlined` were accepted).
//!   This holds for `core::ops` ranges too. CONST-RANGE-INDEX-1: the `RangeIndex` arm reads
//!   the range type from the callee's instantiation (`callee_panicking_range_index`).
//! * An inclusive range under an explicit MIR inliner (`inline_incl`): the caller builds
//!   `core::ops::RangeInclusive { .., exhausted: false }`, and that `bool` field's
//!   downcast twin made the VC sort-invalid, so its always-violated row came back
//!   `Unknown` (runtime-checked). AGG-BOOL-TWIN-SORT-1 fixes the aggregate definition.
//!
//! MEASURED on the stage 1 of this change against `0ac7a96d9f`, outside compiletest:
//!
//! * `const_item`, `inline_const` and `inline_incl` refuse no function BEFORE (rc=0) and
//!   every function AFTER.
//! * `opt_mir` refuses 9 functions BEFORE and all 15 AFTER.
//! * `guarded_loss` adds `guarded_const` AFTER (the cost below).
//! * `controls` (with the constant `RangeFull`) exits 0 on both.
//!
//! # The capability loss, on purpose
//!
//! `guarded_loss`: a GUARDED index over a `core::range` type cannot panic and is
//! refused — the guard cannot reach a row no tracer reads. The `core::ops` twin
//! (`controls::ops_guarded`) proves. Recovery is work: teach the tracer the new
//! layouts (`Range { start, end }`, `RangeFrom { start }`, `RangeInclusive { start,
//! last }`, `RangeToInclusive { last }`) behind an exact-path gate.
//!
//! `guarded_loss::guarded_const` (CONST-RANGE-INDEX-1): a guarded index over a `core::ops`
//! CONSTANT range cannot panic and is refused. No tracer reads a constant. Recovery: extract a
//! constant range's scalar fields.

//!
//! UNDER AN EXPLICIT MIR INLINER, FOUR `str` FUNCTIONS CARRY A DIFFERENT HEADER (2026-10-08,
//! the trust-open-false-accepts landing). In `opt_mir` and `inline_incl` the `str` index's
//! std member is inlined into `str_from`, `string_from`, `str_incl_from` and
//! `ops_incl_black_box_str`, and keeps an internal `Assert` the runtime-checked std-member
//! disposition would tolerate. `inlined_sysroot_panic` withholds that disposition from a body
//! carrying a foreign panic path the inliner copied in (docs/KNOWN_HAZARDS.md, "CLOSED
//! 2026-09-29 / 2026-10-02 — under an explicit `-Zinline-mir=yes` ..."), with its own header:
//! "Trust full verification failed ... a bundled std/core/alloc member's internal Assert was
//! kept as a runtime check, and this body carries a foreign panic path the MIR inliner copied
//! into it". Same verdict as on main (refused, exit 1, measured on main `de6288dddf` and on the
//! merged build); the slice and array functions keep the strict header in every revision.

#![cfg_attr(new_range, feature(new_range))]

#[cfg(any(stable, opt, guarded_loss))]
#[allow(unused_imports)]
use core::range::{Range, RangeFrom, RangeInclusive, RangeToInclusive};

#[cfg(any(stable, opt))]
pub fn str_from(s: &str) -> &str {
    //[stable,opt]~^ ERROR Trust strict verification failed for `core_range_index_charged::str_from`
    if s.len() >= 1 { &s[RangeFrom::from(1..)] } else { "" }
}

#[cfg(any(stable, opt))]
pub fn slice_range(v: &[u8]) -> &[u8] {
    //[stable,opt]~^ ERROR Trust strict verification failed for `core_range_index_charged::slice_range`
    &v[Range::from(0..5)]
}

#[cfg(any(stable, opt))]
pub fn slice_lit(v: &[u8]) -> &[u8] {
    //[stable,opt]~^ ERROR Trust strict verification failed for `core_range_index_charged::slice_lit`
    &v[Range { start: 0, end: 5 }]
}

#[cfg(any(stable, opt))]
pub fn array_range(a: &[u8; 3]) -> &[u8] {
    //[stable,opt]~^ ERROR Trust strict verification failed for `core_range_index_charged::array_range`
    &a[Range::from(1..5)]
}

#[cfg(any(stable, opt))]
pub fn string_from(s: &String) -> &str {
    //[stable,opt]~^ ERROR Trust strict verification failed for `core_range_index_charged::string_from`
    &s[RangeFrom::from(1..)]
}

#[cfg(any(stable, opt))]
pub fn mut_str(s: &mut str) -> &mut str {
    //[stable,opt]~^ ERROR Trust strict verification failed for `core_range_index_charged::mut_str`
    &mut s[Range::from(0..1)]
}

#[cfg(any(stable, opt))]
pub fn vec_incl(v: &Vec<u8>) -> &[u8] {
    //[stable,opt]~^ ERROR Trust strict verification failed for `core_range_index_charged::vec_incl`
    &v[RangeInclusive::from(0..=4)]
}

#[cfg(any(stable, opt))]
pub fn vec_mut(v: &mut Vec<u8>) {
    //[stable,opt]~^ ERROR Trust strict verification failed for `core_range_index_charged::vec_mut`
    v[Range::from(2..9)].fill(0);
}

#[cfg(any(stable, opt))]
pub fn slice_to_incl(v: &[u8]) -> &[u8] {
    //[stable,opt]~^ ERROR Trust strict verification failed for `core_range_index_charged::slice_to_incl`
    &v[RangeToInclusive::from(..=4)]
}

#[cfg(any(stable, opt))]
pub fn by_param(v: &[u8], r: Range<usize>) -> &[u8] {
    //[stable,opt]~^ ERROR Trust strict verification failed for `core_range_index_charged::by_param`
    &v[r]
}

#[cfg(new_range)]
pub fn str_from(s: &str) -> &str {
    //[new_range]~^ ERROR Trust strict verification failed for `core_range_index_charged::str_from`
    if s.len() >= 1 { &s[1..] } else { "" }
}

#[cfg(new_range)]
pub fn slice_range(v: &[u8]) -> &[u8] {
    //[new_range]~^ ERROR Trust strict verification failed for `core_range_index_charged::slice_range`
    &v[0..5]
}

#[cfg(new_range)]
pub fn slice_incl(v: &[u8]) -> &[u8] {
    //[new_range]~^ ERROR Trust strict verification failed for `core_range_index_charged::slice_incl`
    &v[0..=4]
}

#[cfg(new_range)]
pub fn slice_to_incl(v: &[u8]) -> &[u8] {
    //[new_range]~^ ERROR Trust strict verification failed for `core_range_index_charged::slice_to_incl`
    &v[..=4]
}

#[cfg(new_range)]
pub fn str_to_incl(s: &str) -> &str {
    //[new_range]~^ ERROR Trust strict verification failed for `core_range_index_charged::str_to_incl`
    &s[..=0]
}

// `inline_incl` (and `opt_mir`): an inclusive range under an explicit MIR inliner.
// Core's `SliceIndex` impls for `core::range::RangeInclusive` forward to the
// `core::ops` one, so the caller's MIR builds `core::ops::RangeInclusive { start,
// end, exhausted: false }` and calls its `SliceIndex::index` range first.

// `const_item`: the range is a `const` item, so it reaches the index as a constant
// operand with no type; the callee's instantiation names it.

#[cfg(const_item)]
const CR_INCL: core::range::RangeInclusive<usize> = core::range::RangeInclusive { start: 0, last: 4 };

#[cfg(const_item)]
pub fn const_cr_incl(a: &[u8; 3]) -> &[u8] {
    //[const_item]~^ ERROR Trust strict verification failed for `core_range_index_charged::const_cr_incl`
    &a[CR_INCL]
}

#[cfg(const_item)]
const CR_FROM: core::range::RangeFrom<usize> = core::range::RangeFrom { start: 1 };

#[cfg(const_item)]
pub fn const_cr_from_str(s: &str) -> &str {
    //[const_item]~^ ERROR Trust strict verification failed for `core_range_index_charged::const_cr_from_str`
    &s[CR_FROM]
}

#[cfg(const_item)]
const CR_RANGE: core::range::Range<usize> = core::range::Range { start: 0, end: 5 };

#[cfg(const_item)]
pub fn const_cr_range(v: &[u8]) -> &[u8] {
    //[const_item]~^ ERROR Trust strict verification failed for `core_range_index_charged::const_cr_range`
    &v[CR_RANGE]
}

#[cfg(const_item)]
const OPS_RANGE: core::ops::Range<usize> = 0..5;

#[cfg(const_item)]
pub fn const_ops_range(v: &[u8]) -> &[u8] {
    //[const_item]~^ ERROR Trust strict verification failed for `core_range_index_charged::const_ops_range`
    &v[OPS_RANGE]
}

#[cfg(const_item)]
const OPS_FROM: core::ops::RangeFrom<usize> = 1..;

#[cfg(const_item)]
pub fn const_ops_from_str(s: &str) -> &str {
    //[const_item]~^ ERROR Trust strict verification failed for `core_range_index_charged::const_ops_from_str`
    &s[OPS_FROM]
}

#[cfg(const_item)]
const OPS_INCL: core::ops::RangeInclusive<usize> = 0..=4;

#[cfg(const_item)]
pub fn const_ops_incl_mut(v: &mut [u8]) -> &mut [u8] {
    //[const_item]~^ ERROR Trust strict verification failed for `core_range_index_charged::const_ops_incl_mut`
    &mut v[OPS_INCL]
}

#[cfg(const_item)]
const BOUNDS: (core::ops::Bound<usize>, core::ops::Bound<usize>) =
    (core::ops::Bound::Included(0), core::ops::Bound::Excluded(5));

#[cfg(const_item)]
pub fn const_bounds(v: &[u8]) -> &[u8] {
    //[const_item]~^ ERROR Trust strict verification failed for `core_range_index_charged::const_bounds`
    &v[BOUNDS]
}

// `inline_const`: an inline `const { .. }` block, the same constant operand.

#[cfg(inline_const)]
pub fn inline_const_mut_str(s: &mut str) -> &mut str {
    //[inline_const]~^ ERROR Trust strict verification failed for `core_range_index_charged::inline_const_mut_str`
    &mut s[const { core::range::Range { start: 0, end: 5 } }]
}

#[cfg(inline_const)]
pub fn inline_const_ops(v: &[u8]) -> &[u8] {
    //[inline_const]~^ ERROR Trust strict verification failed for `core_range_index_charged::inline_const_ops`
    &v[const { 0..5 }]
}

#[cfg(guarded_loss)]
pub fn guarded(v: &[u8]) -> &[u8] {
    //[guarded_loss]~^ ERROR Trust strict verification failed for `core_range_index_charged::guarded`
    if v.len() >= 5 { &v[Range::from(0..5)] } else { v }
}

#[cfg(guarded_loss)]
pub fn guarded_from(v: &[u8]) -> &[u8] {
    //[guarded_loss]~^ ERROR Trust strict verification failed for `core_range_index_charged::guarded_from`
    if v.len() >= 1 { &v[RangeFrom::from(1..)] } else { v }
}

#[cfg(guarded_loss)]
const GUARDED_OPS: core::ops::Range<usize> = 0..5;

#[cfg(guarded_loss)]
pub fn guarded_const(v: &[u8]) -> &[u8] {
    //[guarded_loss]~^ ERROR Trust strict verification failed for `core_range_index_charged::guarded_const`
    if v.len() >= 5 { &v[GUARDED_OPS] } else { v }
}

#[cfg(controls)]
pub fn ops_guarded(v: &[u8]) -> &[u8] {
    if v.len() >= 5 { &v[0..5] } else { v }
}

#[cfg(controls)]
pub fn ops_full(v: &[u8]) -> &[u8] {
    &v[..]
}

#[cfg(controls)]
pub fn reexport_to(v: &[u8]) -> &[u8] {
    if v.len() >= 2 { &v[core::range::RangeTo { end: 2 }] } else { v }
}

#[cfg(controls)]
pub fn reexport_full(v: &[u8]) -> &[u8] {
    &v[core::range::RangeFull]
}

#[cfg(controls)]
pub fn checked_get(v: &[u8]) -> Option<&[u8]> {
    v.get(core::range::Range::from(0..5))
}

#[cfg(controls)]
const FULL: core::ops::RangeFull = ..;

#[cfg(controls)]
pub fn const_full(v: &[u8]) -> &[u8] {
    &v[FULL]
}
