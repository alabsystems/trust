//@ needs-trust-verify
//@ edition: 2021
//@ no-prefer-dynamic
//@ aux-build:panicking_allocator_dep.rs
//@ aux-build:dropglue_bomb_dep.rs
//@ aux-build:panicking_clone_dep.rs
//@ revisions: user global
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[user] check-fail
//@[global] check-pass
//! The extractor's total-call licence ERASES a `Vec`/`String` `extend` (and a keyed
//! `collect`), and with it every allocation of the receiver and every deallocation
//! of a consumed source. Review round 61: with a caller-supplied allocator those are
//! user code that may panic, and `d.extend(..)` into a `Vec<u64, Q>` or from a
//! `Vec<u64, Q>` was proved under `certify` and panicked in `Q`. The licence now
//! requires `Global` for every sysroot container in the receiver and the source.
//!
//! Review round 62: the erased call also DROPS (a `BTreeMap` drops the value a
//! repeated key replaces; `from_iter` drops sorted-out duplicates; a consumed source
//! drops what it does not yield), so the receiver/destination and the source must be
//! drop-total too. A user `Drop` value, or a user allocator hidden in a user field, is
//! refused the way a body-level drop of the same type already is.
//!
//! Review round 63: the erased call also runs everything the SOURCE chain does per
//! item, so a function parameter must be a closure or a function of this crate, an
//! adapter's dropped inner items must be drop-total, `Cloned` needs a total `Clone`,
//! and the set operations (which run the source sets' `Ord`/`Hash`) are refused.
#![feature(allocator_api)]
#![allow(dead_code)]
extern crate dropglue_bomb_dep;
extern crate panicking_clone_dep;
extern crate panicking_allocator_dep;

#[cfg(user)]
use panicking_allocator_dep::Q;

#[cfg(user)]
pub fn into_user_allocator(d: &mut Vec<u64, Q>, v: &[u64]) {
    //[user]~^ ERROR Trust strict verification failed for `extend_licence_requires_global_allocator::into_user_allocator`
    d.extend(v.iter().copied());
}

#[cfg(user)]
pub fn from_user_allocator(d: &mut Vec<u64>, v: Vec<u64, Q>) {
    //[user]~^ ERROR Trust strict verification failed for `extend_licence_requires_global_allocator::from_user_allocator`
    d.extend(v);
}

#[cfg(user)]
pub fn replaces_a_bomb(d: &mut std::collections::BTreeMap<u64, dropglue_bomb_dep::Bomb>, v: Vec<(u64, dropglue_bomb_dep::Bomb)>) {
    //[user]~^ ERROR Trust strict verification failed for `extend_licence_requires_global_allocator::replaces_a_bomb`
    d.extend(v);
}

#[cfg(user)]
pub struct Wrapped(pub Vec<u64, Q>);

#[cfg(user)]
pub fn hidden_allocator(d: &mut std::collections::BTreeMap<u64, Wrapped>, v: Vec<(u64, Wrapped)>) {
    //[user]~^ ERROR Trust strict verification failed for `extend_licence_requires_global_allocator::hidden_allocator`
    d.extend(v);
}

#[cfg(user)]
pub fn map_through_fn_pointer(
    d: &mut std::collections::BTreeSet<u8>,
    it: std::iter::Map<std::slice::Iter<'_, u8>, fn(&u8) -> u8>,
) {
    //[user]~^^^^ ERROR Trust strict verification failed for `extend_licence_requires_global_allocator::map_through_fn_pointer`
    d.extend(it);
}

#[cfg(user)]
fn defuse(b: dropglue_bomb_dep::Bomb) -> u8 {
    let n = b.0 as u8;
    core::mem::forget(b);
    n
}

#[cfg(user)]
pub fn filter_drops_a_bomb(d: &mut std::collections::BTreeSet<u8>, v: std::slice::Iter<'_, u8>) {
    //[user]~^ ERROR Trust strict verification failed for `extend_licence_requires_global_allocator::filter_drops_a_bomb`
    d.extend(v.map(|x| dropglue_bomb_dep::Bomb(*x as i32)).filter(|_| false).map(defuse));
}

#[cfg(user)]
pub fn clones_through_user_clone(d: &mut Vec<panicking_clone_dep::Ck>, v: std::slice::Iter<'_, panicking_clone_dep::Ck>) {
    //[user]~^ ERROR Trust strict verification failed for `extend_licence_requires_global_allocator::clones_through_user_clone`
    d.extend(v.cloned());
}

/// Review round 64: `Vec`'s `Extend<&T>` runs `.cloned()` on every item.
#[cfg(user)]
pub fn extends_by_reference(d: &mut Vec<panicking_clone_dep::CopyCk>, v: &[panicking_clone_dep::CopyCk]) {
    //[user]~^ ERROR Trust strict verification failed for `extend_licence_requires_global_allocator::extends_by_reference`
    d.extend(v.iter().filter(|s| s.0 > 3));
}

#[cfg(global)]
pub fn btree_extend_plain(d: &mut std::collections::BTreeMap<u64, u64>, v: &[(u64, u64)]) {
    d.extend(v.iter().copied());
}

#[cfg(global)]
pub fn global_extend(d: &mut Vec<u64>, v: &[u64]) {
    d.extend(v.iter().copied());
}
