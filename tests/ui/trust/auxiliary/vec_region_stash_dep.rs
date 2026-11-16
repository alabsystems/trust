//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ edition: 2021
//@ no-prefer-dynamic
//! VEC-REGION-DEF-BLOCK-STASH-1 (docs/KNOWN_HAZARDS.md, 2026-10-13): a dependency that
//! KEEPS the pointer it was lent. `stash` records the `Vec` (or, `stash_first`, the first
//! `&mut Vec` held by a `Vec<&mut Vec<u8>>`) in a `static mut`; a later `clear_it`, which
//! names no `Vec` at all, clears it through that pointer. Built with verification off, as
//! `targo` builds every dependency, so neither body is in the caller's bundle. The
//! caller holding a `Vec` it lent to `stash` and reading it again after `clear_it` has no
//! UB under Stacked or Tree Borrows (the wave-26 scout's argument; not run under Miri).
//! (The scout's `stdep.rs`, plus `stash_first`.)

static mut P: *mut Vec<u8> = std::ptr::null_mut();

#[inline(never)]
pub fn stash(v: &mut Vec<u8>) {
    unsafe {
        P = v as *mut Vec<u8>;
    }
}

#[inline(never)]
pub fn stash_first(vv: &mut Vec<&mut Vec<u8>>) {
    if let Some(r) = vv.first_mut() {
        unsafe {
            P = &mut **r as *mut Vec<u8>;
        }
    }
}

#[inline(never)]
pub fn clear_it() {
    unsafe {
        (*P).clear();
    }
}
