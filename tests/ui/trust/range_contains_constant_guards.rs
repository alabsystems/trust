//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! `(L..=U).contains(&x)` and `(L..U).contains(&x)` over a CONSTANT range narrow
//! `x` for the code they guard.
//!
//! MEASURED 2026-09-29: the extractor's rewrite of such a call into
//! `x >= L & x <= U` (`rewrite_range_contains_calls`) recognized the callee by its
//! rendered path ending in `::contains`, and call names now carry the method's own
//! generic arguments (`RangeInclusive::<u8>::contains::<u8>`), so the rewrite never
//! fired and every function below was refuted — `c - 32` with `c = 0`. No test
//! covered the rewrite. The callee is now identified by DefId: the inherent
//! `contains` of the `Range`/`RangeInclusive` lang item, over a primitive integer
//! compared with an item of the same type (`range_lang_item_contains`).
//!
//! `range_contains_constant_guards_refused.rs` holds the twins whose guard does not
//! cover the operation, which really panic.
//!
//! RE-PINNED 2026-10-15: refused, a recorded capability loss of the merge of 2026-10-14
//! (see `upper_ascii`).

pub fn upper_ascii(c: u8) -> u8 {
    //~^ ERROR Trust strict verification failed for `range_contains_constant_guards::upper_ascii`
    //~| ERROR Trust Level 0 safety verification incomplete for `range_contains_constant_guards::upper_ascii`
    // CAPABILITY LOSS, re-pinned 2026-10-15 (the merge of 2026-10-14; DECISION_QUEUE
    // EXTRACT-REWRITE-1 and D103(i)): the merge kept main's DELETION of the range-`contains`
    // rewrite (EXTRACT-REWRITE-1: it was keyed on the rendered path, and a user
    // `RangeInclusive` got it) over this line's DefId/lang-item re-anchoring (587b080b351),
    // which EXTRACT-REWRITE-1 left as open capability work (it also needs a `const`
    // `RangeInclusive`'s `exhausted` field read as `false`). So the guard says nothing about
    // `x` and every function below is refused. Fail-closed. Flip back to `check-pass` when it
    // returns.
    if (b'a'..=b'z').contains(&c) { c - 32 } else { c }
}

pub fn shifted(c: u32) -> u32 {
    //~^ ERROR Trust strict verification failed for `range_contains_constant_guards::shifted`
    //~| ERROR Trust Level 0 safety verification incomplete for `range_contains_constant_guards::shifted`
    // See `upper_ascii` (CAPABILITY LOSS, re-pinned 2026-10-15).
    if (100..201).contains(&c) { c - 50 } else { c }
}

pub fn scaled(c: i32) -> i32 {
    //~^ ERROR Trust strict verification failed for `range_contains_constant_guards::scaled`
    //~| ERROR Trust Level 0 safety verification incomplete for `range_contains_constant_guards::scaled`
    // See `upper_ascii` (CAPABILITY LOSS, re-pinned 2026-10-15).
    if (-5..=5).contains(&c) { c * 1000 } else { 0 }
}

pub fn lookup(t: &[u8; 10], i: usize) -> u8 {
    //~^ ERROR Trust strict verification failed for `range_contains_constant_guards::lookup`
    //~| ERROR Trust Level 0 safety verification incomplete for `range_contains_constant_guards::lookup`
    // See `upper_ascii` (CAPABILITY LOSS, re-pinned 2026-10-15).
    if (0..10).contains(&i) { t[i] } else { 0 }
}
