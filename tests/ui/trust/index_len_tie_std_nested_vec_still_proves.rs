//@ revisions: default strict
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@ check-pass
//@ dont-check-compiler-stderr
//! The control for `index_len_tie_requires_std_index.rs` (IDX-TIE-1, second
//! consumer): the shape `value_facts::build_immutable_index_len_tie_facts` was
//! written for. Both `v[i]` are std's `<alloc::vec::Vec<alloc::vec::Vec<u32>> as
//! core::ops::index::Index<usize>>::index` on the root `v`, which the extractor types
//! `&Seq<Seq<u32>>`; the two inner `Vec`s are one, their lengths are tied, and the
//! `j < v[i].len()` guard discharges `v[i][j]`.
//!
//! Measured on the stage 1 of integ/wave11 `936573497e` (2026-10-04), before the
//! anchor: exit 0 under both revisions, rows `slice proved` (three, ay-in-process)
//! and one `assert` runtime-checked. The anchor must keep that: the annotations pin
//! exactly one obligation not proved, and a refuted `slice` row would add an
//! unannotated strict-verification error.
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14): on the merged stage 1 the `assert`
//! row is proved as well (`3 proved`, all kernel-certified, under both revisions), so
//! `nest` carries no warning. A refuted `slice` row would still add an unannotated
//! error, which is what this control pins.

pub fn nest(v: &Vec<Vec<u32>>, i: usize, j: usize) -> u32 {
    if i < v.len() && j < v[i].len() { v[i][j] } else { 0 }
}
