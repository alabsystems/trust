//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ edition: 2021
//@ no-prefer-dynamic
//! VEC-REGION-DEF-BLOCK-STASH-1 (docs/KNOWN_HAZARDS.md, 2026-10-13): the stash shape as a
//! SOUND dependency API. `stash` is safe and only records the address in an `AtomicPtr`;
//! `clear_stashed` is an `unsafe fn` whose contract the caller meets (the `Vec` last
//! stashed is live and not borrowed). Built with verification off, as `targo` builds
//! every dependency. (The scout's `vrdep.rs`.)

use std::sync::atomic::{AtomicPtr, Ordering};

static P: AtomicPtr<Vec<u8>> = AtomicPtr::new(std::ptr::null_mut());

/// Safe: only records the address.
#[inline(never)]
pub fn stash(v: &mut Vec<u8>) {
    P.store(v, Ordering::Relaxed);
}

/// # Safety
///
/// The `Vec` last passed to `stash` is still live and not borrowed.
#[inline(never)]
pub unsafe fn clear_stashed() {
    unsafe {
        (*P.load(Ordering::Relaxed)).clear();
    }
}
