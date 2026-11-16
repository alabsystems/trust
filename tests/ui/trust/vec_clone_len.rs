//@ needs-trust-verify
//@ edition: 2021
//@ revisions: clone_ref clone_owned clone_short clone_cleared
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[clone_ref] check-pass
//@[clone_owned] check-pass
//@[clone_short] check-fail
//@[clone_cleared] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! Trust (2026-10-05, VEC_CLONE_LEN): `w = v.clone()` on a std `Vec` has exactly `v`'s
//! length (`guards::slice_last_some_nonempty_definitions`). The extractor renders the call
//! as the shared `__trust_total_clone` sentinel, so the lane keys on the callee's DefId
//! (`SysrootItem::CloneClone`) and a std-`Vec` destination, which fixes the impl to alloc's.
//!
//! # Before (measured on the sealed `trustc 0.10.0+g4d9a20e3d`, 2026-10-05)
//!
//! `clone_ref` and `clone_owned`: the index into the clone was not proved.
//!
//! # The refused rails, each a program that really panics
//!
//! * `clone_short` — `v.len() >= 3`, then `v.clone()[3]`: equal lengths give no slack.
//! * `clone_cleared` — the clone is cleared before the index, so its length is not
//!   stable for the body and the tie is declined.

#[cfg(clone_ref)]
pub fn clone_ref(v: &Vec<u8>) -> u8 {
    if v.len() < 4 {
        return 0;
    }
    let w = v.clone();
    w[3]
}

#[cfg(clone_owned)]
pub fn clone_owned(v: Vec<u8>) -> u8 {
    if v.len() < 2 {
        return 0;
    }
    let w = v.clone();
    w[1]
}

#[cfg(clone_short)]
pub fn clone_short(v: &Vec<u8>) -> u8 {
    if v.len() < 3 {
        return 0;
    }
    let w = v.clone();
    w[3]
}

#[cfg(clone_cleared)]
pub fn clone_cleared(v: &Vec<u8>) -> u8 {
    if v.len() < 4 {
        return 0;
    }
    let mut w = v.clone();
    w.clear();
    w[3]
}
