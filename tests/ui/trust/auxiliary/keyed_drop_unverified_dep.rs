//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ edition: 2021
//@ no-prefer-dynamic
//! An ordinary dependency, compiled the way `targo` compiles every dependency
//! unit: `-Ztrust-verify=off`, so NOTHING in this file is verified. Every type here
//! runs this file's code when a value of it is DROPPED, and that code panics once
//! `ARMED` is set (the first armed drop disarms it again, so the panic fires once and
//! unwinding drops the rest normally):
//!  * `Bomb` (a map VALUE) and `BombKey` (a KEY with derived, total `Ord`/`Hash`/`Eq`)
//!    have a hand-written `Drop`;
//!  * `BombBox`/`BombStr` have no `Drop` of their own, but are boxed at `DeallocBomb`,
//!    so their std drop glue calls `DeallocBomb::deallocate`.
//! A keyed std collection drops the old value (and the passed key) on a key
//! collision inside `insert`/`extend`, `BTreeMap`/`BTreeSet` `from_iter` drops the
//! earlier of two equal keys, and `String::extend` drops every owned item it appends,
//! so a downstream `collect`/`extend` over one of these runs this file's code inside
//! the call. The aliases let a stable downstream crate name the boxes without
//! `#![feature(allocator_api)]`. Used by `keyed_collect_extend_drops_inside_the_call.rs`.

#![feature(allocator_api)]

use std::alloc::{AllocError, Allocator, Global, Layout};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicBool, Ordering};

/// Arms every destructor below (so values can be built and moved before they panic).
pub static ARMED: AtomicBool = AtomicBool::new(false);

fn armed() -> bool {
    ARMED.swap(false, Ordering::SeqCst)
}

/// A map VALUE whose destructor panics once `ARMED`.
pub struct Bomb(pub u8);

impl Drop for Bomb {
    fn drop(&mut self) {
        if armed() {
            panic!("keyed_drop_unverified_dep::Bomb::drop")
        }
    }
}

/// A map/set KEY with derived (total) `Ord`/`Hash`/`Eq` but a destructor that panics
/// once `ARMED`.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BombKey(pub u32);

impl Drop for BombKey {
    fn drop(&mut self) {
        if armed() {
            panic!("keyed_drop_unverified_dep::BombKey::drop")
        }
    }
}

/// An allocator whose `deallocate` panics once `ARMED`.
#[derive(Clone, Copy)]
pub struct DeallocBomb;

unsafe impl Allocator for DeallocBomb {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        Global.allocate(layout)
    }
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        if armed() {
            panic!("keyed_drop_unverified_dep::DeallocBomb::deallocate")
        }
        unsafe { Global.deallocate(ptr, layout) }
    }
}

/// A `u32` boxed at `DeallocBomb`: no `Drop` of its own, a dependency's code in its glue.
pub type BombBox = Box<u32, DeallocBomb>;
/// A `str` boxed at `DeallocBomb` (a `String::extend` item).
pub type BombStr = Box<str, DeallocBomb>;

pub fn bomb_box(x: u32) -> BombBox {
    Box::new_in(x, DeallocBomb)
}

pub fn bomb_str(s: &str) -> BombStr {
    let b: Box<[u8], DeallocBomb> = {
        let mut v = Vec::with_capacity_in(s.len(), DeallocBomb);
        v.extend_from_slice(s.as_bytes());
        v.into_boxed_slice()
    };
    let (ptr, alloc) = Box::into_raw_with_allocator(b);
    // SAFETY: the bytes were copied from a `str`, so they are valid UTF-8, and
    // `[u8]` and `str` have the same layout.
    unsafe { Box::from_raw_in(ptr as *mut str, alloc) }
}
