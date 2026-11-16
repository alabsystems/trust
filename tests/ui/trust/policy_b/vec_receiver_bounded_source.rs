//@ needs-trust-verify
//@ edition: 2021
//@ revisions: bounded charged
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[bounded] check-pass
//@[charged] check-fail
//! A `Vec` receiver (`Ty::Seq`, minted only for the real sysroot `Vec`) is an
//! authenticated bounded source: `v.into_iter().collect()` over an owned `Vec` and a
//! count that is `len()` of a `&Vec` are granted under `docs/DECISION_QUEUE.md` D12
//! option (a). The `Vec` -> `Ty::Seq` representation change had left both refused.
//! A widening factor above 2 and a zero-sized element keep their charge.
//! Since D102 (2026-10-15) a counted `with_capacity(v.len())` is skipped only where
//! main's availability theorem also holds (source stride at least the target's), so
//! the factor-2 `sized_like` moved to `charged`.
#![allow(dead_code)]

#[cfg(bounded)]
pub fn owned(v: Vec<u8>) -> Vec<u8> {
    v.into_iter().collect()
}

// MOVED to `charged` 2026-10-15 (DECISION_QUEUE D102, fail-closed meanwhile): the
// count is a live length and the capacity fits (factor 2), but the target stride (8)
// exceeds the source's (4), so main's ALLOC-LEN availability theorem keeps the
// `2^28`-element ceiling, and the existing-length skip now applies only where that
// theorem holds (measured on the merged stage 1: `[unbounded_allocation] FAILED` at
// `v = 268435456`).
#[cfg(charged)]
pub fn sized_like(v: &Vec<i32>) -> Vec<i64> {
    //[charged]~^ ERROR Trust Level 0 safety verification incomplete for `vec_receiver_bounded_source::sized_like`
    Vec::with_capacity(v.len())
}

#[cfg(bounded)]
pub struct Holder {
    pub items: Vec<u32>,
}

#[cfg(bounded)]
pub fn field_len(h: &Holder) -> Vec<u32> {
    Vec::with_capacity(h.items.len())
}

#[cfg(charged)]
pub fn widened(v: Vec<u8>) -> Vec<u64> {
    //[charged]~^ ERROR Trust Level 0 safety verification incomplete for `vec_receiver_bounded_source::widened`
    v.into_iter().map(|x| x as u64).collect()
}

#[cfg(charged)]
pub fn units_len(v: &Vec<()>) -> Vec<u8> {
    //[charged]~^ ERROR Trust Level 0 safety verification incomplete for `vec_receiver_bounded_source::units_len`
    Vec::with_capacity(v.len())
}
