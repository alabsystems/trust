//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_inlined_std.rs` and `_holds.rs`, built
//! OPTIMIZED, so that std's fns its fns call are inlined into them. Its fns
//! are safe to call, and sound.

/// Reads only, and has no `unsafe` of its own: what `v.iter().count()`
/// leaves here once std's `slice::iter` and `Iter::count` are inlined is
/// std's code (a pointer cast among it).
pub fn count<T>(v: &Vec<T>) -> usize {
    v.iter().count()
}

/// Its own `unsafe`: a call of std's `unsafe fn Vec::set_len`, which the
/// optimizer inlines away to a plain write of the length.
pub fn forget_all<T>(v: &mut Vec<T>) {
    unsafe { v.set_len(0) }
}
