//@ needs-trust-verify
//@ edition: 2021
//@ revisions: mut_param_front owned_front field_guarded sibling_guard sibling_cleared_first
//@ revisions: param_call_arg owned_call_arg owned_vec_call_arg local_call_arg sibling_both_charged
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[mut_param_front] check-pass
//@[owned_front] check-pass
//@[field_guarded] check-pass
//@[sibling_guard] check-fail
//@[sibling_cleared_first] check-fail
//@[param_call_arg] check-pass
//@[owned_call_arg] check-pass
//@[owned_vec_call_arg] check-pass
//@[local_call_arg] check-pass
//@[sibling_both_charged] check-fail
//! **A `Vec` index mutator whose receiver is a struct FIELD (VEC-INSERT-FIELD,
//! Trust 2026-10-07).**
//!
//! The pre-mutation region (`trust-vcgen/src/generate/vec_region.rs`, pinned for
//! whole-local bases by `vec_index_mutator_region.rs`) resolved only a WHOLE-local
//! base. `m.rows.insert(0, x)` borrows `&mut ((*m).0)`, matched no base, kept the
//! fail-honest `vec-panic-method-index-unmodeled` row, and Level 0 reclassified it to
//! a FAILED `Call::insert::panic-freedom-unverified` row (trust-ir-conformance
//! `tests/generate/refuse.rs:619`, `module.drop_glue.insert(0, entry)`).
//!
//! # Before (stage 1 snapshot of `7be75e9a80`, 2026-10-07)
//!
//! `mut_param_front`: `0 proved, 1 failed, 1 unknown, 0 timed out, 1 runtime-checked,
//! 1 skipped out of 4`, rc=1; the same call on `v: &mut Vec<u32>` was `1 proved`.
//! `owned_front` (`mut m: M`) was refused the same way.
//!
//! # After (stage 1 of this branch, 2026-10-07)
//!
//! `mut_param_front`, `owned_front`, `field_guarded`: `1 proved, 0 failed, 0 unknown, 0
//! timed out, 1 runtime-checked, 1 skipped out of 3`, rc=0 (the counts `rotate` in
//! `vec_index_mutator_region.rs` carries). `sibling_guard`: `[slice] FAILED`, rc=1.
//! `sibling_cleared_first`: the old unmodeled row, rc=1.
//!
//! A field reached through plain `Field` projections from a by-value local or an
//! `&mut` parameter is a region base. Its region is the ROOT's (any mutation of any
//! part of the root ends it), and each field path has its own length symbol, so a
//! guard over a sibling field's length discharges nothing (`sibling_guard`, `[slice]
//! FAILED`) and a sibling `clear()` before the call keeps the old row
//! (`sibling_cleared_first`, a conservative over-refusal).
//!
//! # A receiver borrow RESERVED before a call-computed argument (VEC-INSERT-FIELD-2)
//!
//! `m.rows.insert(0, mk(k))` takes the two-phase borrow `_t = &mut ((*_1).0)` in the
//! block that calls `mk`, and activates it in the next. The field fix alone did not
//! see it: `param_call_arg`, `owned_call_arg` and `owned_vec_call_arg` (a WHOLE owned
//! `Vec`) all stayed `0 proved, 1 failed, 1 unknown` on the e4adfeb86f stage 1 (only a
//! `&mut Vec` PARAMETER proved, through its `copy _1` receiver). `local_call_arg` is
//! the by-value local bound from another value, read by `len()` first.
//! `sibling_both_charged` charges BOTH fields so both get region facts: a shared
//! length symbol would prove the `rows` insert guarded by `cols.len()`.

pub struct M {
    pub rows: Vec<u32>,
    pub cols: Vec<u32>,
}

#[cfg(mut_param_front)]
pub fn front(m: &mut M, x: u32) {
    //[mut_param_front]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown
    m.rows.insert(0, x);
}

#[cfg(owned_front)]
pub fn owned_front(mut m: M, x: u32) -> M {
    //[owned_front]~^ NOTE 0 failed, 0 unknown
    m.rows.insert(0, x);
    m
}

#[cfg(field_guarded)]
pub fn put(m: &mut M, i: usize, x: u32) {
    //[field_guarded]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown
    if i <= m.rows.len() {
        m.rows.insert(i, x);
    }
}

#[cfg(sibling_guard)]
pub fn put_by_cols(m: &mut M, i: usize, x: u32) {
    //[sibling_guard]~^ NOTE [slice] FAILED
    if i <= m.cols.len() {
        m.rows.insert(i, x);
    }
}

#[cfg(sibling_cleared_first)]
pub fn clear_then_front(m: &mut M, x: u32) {
    //[sibling_cleared_first]~^ NOTE unsupported MIR `vec-panic-method-index-unmodeled`
    m.cols.clear();
    m.rows.insert(0, x);
}

#[cfg(any(param_call_arg, owned_call_arg, owned_vec_call_arg, local_call_arg))]
#[inline(never)]
pub fn mk(k: u32) -> u32 {
    k
}

#[cfg(param_call_arg)]
pub fn param_call_arg(m: &mut M, k: u32) {
    //[param_call_arg]~^ NOTE 0 failed, 0 unknown
    m.rows.insert(0, mk(k));
}

#[cfg(owned_call_arg)]
pub fn owned_call_arg(mut m: M, k: u32) -> M {
    //[owned_call_arg]~^ NOTE 0 failed, 0 unknown
    m.rows.insert(0, mk(k));
    m
}

#[cfg(owned_vec_call_arg)]
pub fn owned_vec_call_arg(mut v: Vec<u32>, k: u32) -> Vec<u32> {
    //[owned_vec_call_arg]~^ NOTE 0 failed, 0 unknown
    v.insert(0, mk(k));
    v
}

#[cfg(local_call_arg)]
pub fn local_call_arg(src: M) -> M {
    //[local_call_arg]~^ NOTE 0 failed, 0 unknown
    let mut module = src;
    let k = module.rows.len() as u32;
    module.rows.insert(0, mk(k));
    module
}

#[cfg(sibling_both_charged)]
pub fn both(m: &mut M, i: usize, x: u32) {
    //[sibling_both_charged]~^ NOTE [slice] FAILED
    let n = m.cols.len();
    if i <= n {
        m.rows.insert(i, x);
    } else {
        m.cols.insert(0, x);
    }
}
