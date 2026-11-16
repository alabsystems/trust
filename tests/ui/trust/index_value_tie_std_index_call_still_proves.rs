//@ revisions: default strict
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@ check-pass
//@ dont-check-compiler-stderr
//! IDX-TIE-1 positive control (docs/DECISION_QUEUE.md IDX-TIE-1): the index value
//! tie still fires for std's OWN `Index<usize>` on a slice.
//!
//! An explicit `Index::index(v, i)` call on `&[u32]` lowers to
//! `<[u32] as core::ops::index::Index<usize>>::index` (the extractor's spelling,
//! measured on stage1-w10 with `-Ztrust-dump=mir-only`). The `+ 1` on the second
//! read is safe only because both reads return the same element, which only the
//! tie states; without it the row is refuted (the counterexample reads 0 and then
//! `u32::MAX` at one index) and the build fails. So this file passing is the
//! measurement that the anchor kept the std capability.
//!
//! Measured on stage1-w10 (2026-10-03), before the fix: both revisions exit 0,
//! `overflow:add` proved and its check elided, plus one `runtime_checked` row
//! (std's own bounds assertion inside the absent `Index::index` body), which is
//! what the two warnings report. certify and memory-safe refuse that row, so they
//! are not revisions here. The same holds on the stage 1 of `936573497e` (with the
//! fix, 2026-10-04): both revisions exit 0 and the check is still elided.

use core::ops::Index;

pub fn std_index_call_twice(v: &[u32], i: usize) -> u32 {
    //~^ WARN Trust Level 0 safety verification incomplete for `index_value_tie_std_index_call_still_proves::std_index_call_twice`
    //~| WARN Trust verification advisory for `index_value_tie_std_index_call_still_proves::std_index_call_twice`
    if i < v.len() && *Index::index(v, i) < 10 { *Index::index(v, i) + 1 } else { 0 }
}
