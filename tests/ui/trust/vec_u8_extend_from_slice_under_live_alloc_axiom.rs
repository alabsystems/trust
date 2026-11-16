//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: panicking_allocator_dep.rs
//@ revisions: global custom_alloc
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[global] check-pass
//@[custom_alloc] check-fail
//! **`Vec<u8>::extend_from_slice` verifies under `MAX_LIVE_ALLOC_BYTES` again (Trust,
//! 2026-09-28).**
//!
//! The bridge's `Vec<u8>` grow summary charges the call's only panic, capacity overflow
//! (`old_len + buf.len() > isize::MAX`), and discharges it under the documented
//! `MAX_LIVE_ALLOC_BYTES` axiom (`docs/TCB.md`). Two things had silently disabled it
//! for the sweep's t14 (`dst.extend_from_slice(src)`):
//!
//! * its 64-bit width witness read the receiver's `len` field, and a std `Vec` has been
//!   extracted as `Ty::Seq`, which has no fields, so the summary never fired. The width
//!   now comes from the compiler's recorded target (`trust_types::target_pointer_bits`);
//! * once it fired, its two axiom lengths were unstamped `Undef`s, which trust-mc's
//!   native input gate refuses along with the whole bundle. They are now stamped
//!   `FreshSymbolicHavoc`, which is sound because the body carries the call's whole
//!   panic set.
//!
//! * `global`: POSITIVE, the t14 shape. Before the fix it was refused under `certify`.
//! * `custom_alloc`: the NEGATIVE. `Seq` erases the allocator, so the callee spelling
//!   must pin `Global`. A caller-selected allocator's `grow` is user code, and
//!   `PanicOnFree` frees (and so panics) on every reallocation. If the summary applied
//!   here, `push_all` would verify and its annotation would go unmatched.
#![cfg_attr(custom_alloc, feature(allocator_api))]

#[cfg(custom_alloc)]
extern crate panicking_allocator_dep;

#[cfg(global)]
pub fn push_all(dst: &mut Vec<u8>, src: &[u8]) {
    dst.extend_from_slice(src);
}

#[cfg(custom_alloc)]
pub fn push_all(dst: &mut Vec<u8, panicking_allocator_dep::PanicOnFree>, src: &[u8]) {
    //[custom_alloc]~^ ERROR Trust Level 0 safety verification incomplete for `vec_u8_extend_from_slice_under_live_alloc_axiom::push_all`
    dst.extend_from_slice(src);
}
