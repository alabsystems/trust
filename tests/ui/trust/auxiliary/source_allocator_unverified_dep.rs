//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ edition: 2021
//@ no-prefer-dynamic
//! An ordinary dependency, compiled the way `targo` compiles every dependency
//! unit: `-Ztrust-verify=off`, so NOTHING in this file is verified. It defines three
//! allocators that forward to `Global` until `ARMED` is set, and then panic once:
//! one in its hand-written `Clone`, one in `deallocate`, one in `allocate`. A std
//! `BTreeMap`/`BTreeSet` owning iterator calls its allocator's `clone` inside `next`
//! (`dying_next`), a `LinkedList` owning iterator frees each node through
//! `deallocate` inside `next` (`pop_front`), and an `extend` RECEIVER reserves
//! through its allocator (`Vec`) or clones it per insert (`BTreeSet`), so a
//! downstream `collect`/`extend` over one of these runs this file's code inside the
//! call. The aliases let a stable downstream crate name the collections without
//! `#![feature(allocator_api)]`. Used by
//! `collect_extend_source_allocator_and_counter.rs`.

#![feature(allocator_api, btreemap_alloc)]

use std::alloc::{AllocError, Allocator, AllocatorClone, Global, Layout};
use std::collections::{btree_map, btree_set, linked_list, BTreeMap, BTreeSet, LinkedList};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicBool, Ordering};

/// Arms the allocators (so a collection can be built before they panic). The
/// first armed call disarms it again, so the panic fires once and unwinding
/// drops the rest normally.
pub static ARMED: AtomicBool = AtomicBool::new(false);

fn armed() -> bool {
    ARMED.swap(false, Ordering::SeqCst)
}

/// An allocator whose hand-written `Clone` panics once `ARMED`.
pub struct CloneBomb;

impl Clone for CloneBomb {
    fn clone(&self) -> CloneBomb {
        if armed() {
            panic!("source_allocator_unverified_dep::CloneBomb::clone")
        }
        CloneBomb
    }
}

unsafe impl Allocator for CloneBomb {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        Global.allocate(layout)
    }
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        unsafe { Global.deallocate(ptr, layout) }
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
            panic!("source_allocator_unverified_dep::DeallocBomb::deallocate")
        }
        unsafe { Global.deallocate(ptr, layout) }
    }
}

/// An allocator whose `allocate` panics once `ARMED` (`grow` is the trait's
/// default, which calls `allocate`).
#[derive(Clone, Copy)]
pub struct AllocBomb;

unsafe impl Allocator for AllocBomb {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        if armed() {
            panic!("source_allocator_unverified_dep::AllocBomb::allocate")
        }
        Global.allocate(layout)
    }
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        unsafe { Global.deallocate(ptr, layout) }
    }
}

// Since 1.101 the btree/linked-list constructors require `AllocatorClone`.
// These impls are the unverified dependency's own (unsafe) assertion that its
// clones are interchangeable; `CloneBomb`'s hand-written `Clone` then breaks
// the no-unwind half of that promise when armed, exactly the hostile shape
// the downstream test exists to refuse to trust.
unsafe impl AllocatorClone for CloneBomb {}
unsafe impl AllocatorClone for DeallocBomb {}
unsafe impl AllocatorClone for AllocBomb {}

pub type CloneBombSet = BTreeSet<u32, CloneBomb>;
pub type CloneBombSetIter = btree_set::IntoIter<u32, CloneBomb>;
pub type CloneBombMap = BTreeMap<u32, u32, CloneBomb>;
pub type CloneBombKeys = btree_map::IntoKeys<u32, u32, CloneBomb>;
pub type CloneBombValues = btree_map::IntoValues<u32, u32, CloneBomb>;
pub type BombKeys = btree_map::IntoKeys<u32, u8, DeallocBomb>;
pub type BombList = LinkedList<u32, DeallocBomb>;
pub type BombListIter = linked_list::IntoIter<u32, DeallocBomb>;
pub type BombVec = Vec<u32, DeallocBomb>;
pub type AllocBombVec = Vec<u32, AllocBomb>;

/// `{1, 2, 3}` in a `CloneBomb` set, built while the allocator is disarmed.
pub fn clone_bomb_set() -> CloneBombSet {
    let mut s = BTreeSet::new_in(CloneBomb);
    s.extend([1u32, 2, 3]);
    s
}

/// `{1: 10, 2: 20, 3: 30}` in a `CloneBomb` map, built while disarmed.
pub fn clone_bomb_map() -> CloneBombMap {
    let mut m = BTreeMap::new_in(CloneBomb);
    m.extend([(1u32, 10u32), (2, 20), (3, 30)]);
    m
}

/// `[1, 2, 3]` in a `DeallocBomb` list, built while disarmed.
pub fn bomb_list() -> BombList {
    let mut l = LinkedList::new_in(DeallocBomb);
    l.extend([1u32, 2, 3]);
    l
}

/// `[1, 2, 3]` in a `DeallocBomb` vector, built while disarmed.
pub fn bomb_vec() -> BombVec {
    let mut v = Vec::new_in(DeallocBomb);
    v.extend([1u32, 2, 3]);
    v
}

/// An empty `AllocBomb` vector (an `extend` receiver).
pub fn alloc_bomb_vec() -> AllocBombVec {
    Vec::new_in(AllocBomb)
}

/// An empty `CloneBomb` set (an `extend` receiver).
pub fn clone_bomb_set_empty() -> CloneBombSet {
    BTreeSet::new_in(CloneBomb)
}
