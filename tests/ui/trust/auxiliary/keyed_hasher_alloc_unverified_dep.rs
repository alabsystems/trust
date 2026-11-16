//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ edition: 2021
//@ no-prefer-dynamic
//! An ordinary dependency, compiled the way `targo` compiles every dependency
//! unit: `-Ztrust-verify=off`, so NOTHING in this file is verified. Each type here
//! runs this file's code from INSIDE a std hash-collection call, and that code panics
//! once `ARMED` is set (the first armed call disarms it again, so the panic fires once):
//!  * `DropHasher` (harmless `Default`/`write`/`finish`, a `Drop` that panics): a
//!    `BuildHasherDefault<DropHasher>` builds one for every hash and drops it inside
//!    `hash_one`;
//!  * `BadHasher` (a `write` that panics): a `BuildHasherDefault<BadHasher>` writes the
//!    key into it, and `Box<BadHasher>` forwards `write_*` to it;
//!  * `DeallocBomb`/`AllocBomb` (an allocator whose `deallocate`/`allocate` panics): a
//!    hash table at either grows through it inside `insert`.
//! The aliases and constructors let a stable downstream crate name these maps without
//! `#![feature(allocator_api)]`. Used by `keyed_collection_hasher_and_query_allocator.rs`.

#![feature(allocator_api)]

use std::alloc::{AllocError, Allocator, Global, Layout};
use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasherDefault, Hasher, RandomState};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicBool, Ordering};

/// Arms every bomb below (so collections can be built and filled before they panic).
pub static ARMED: AtomicBool = AtomicBool::new(false);

fn armed() -> bool {
    ARMED.swap(false, Ordering::SeqCst)
}

/// A hasher with a benign `write`/`finish` whose destructor panics once `ARMED`.
#[derive(Default)]
pub struct DropHasher(u64);

impl Hasher for DropHasher {
    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.0 = self.0.wrapping_mul(31).wrapping_add(*b as u64);
        }
    }
    fn finish(&self) -> u64 {
        self.0
    }
}

impl Drop for DropHasher {
    fn drop(&mut self) {
        if armed() {
            panic!("keyed_hasher_alloc_unverified_dep::DropHasher::drop")
        }
    }
}

/// A hasher whose `write` panics once `ARMED`.
#[derive(Default)]
pub struct BadHasher(u64);

impl Hasher for BadHasher {
    fn write(&mut self, bytes: &[u8]) {
        if armed() {
            panic!("keyed_hasher_alloc_unverified_dep::BadHasher::write")
        }
        for b in bytes {
            self.0 ^= *b as u64;
        }
    }
    fn finish(&self) -> u64 {
        self.0
    }
}

pub type DropBuild = BuildHasherDefault<DropHasher>;
pub type BadBuild = BuildHasherDefault<BadHasher>;

/// An allocator whose `deallocate` panics once `ARMED`.
#[derive(Clone, Copy, Default)]
pub struct DeallocBomb;

unsafe impl Allocator for DeallocBomb {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        Global.allocate(layout)
    }
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        if armed() {
            panic!("keyed_hasher_alloc_unverified_dep::DeallocBomb::deallocate")
        }
        unsafe { Global.deallocate(ptr, layout) }
    }
}

/// An allocator whose `allocate` panics once `ARMED`.
#[derive(Clone, Copy, Default)]
pub struct AllocBomb;

unsafe impl Allocator for AllocBomb {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        if armed() {
            panic!("keyed_hasher_alloc_unverified_dep::AllocBomb::allocate")
        }
        Global.allocate(layout)
    }
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        unsafe { Global.deallocate(ptr, layout) }
    }
}

pub type DeallocMap = HashMap<u32, u8, RandomState, DeallocBomb>;
pub type DeallocSet = HashSet<u32, RandomState, DeallocBomb>;
pub type AllocMap = HashMap<u32, u8, RandomState, AllocBomb>;
pub type DeallocStringMap = HashMap<String, u8, RandomState, DeallocBomb>;

pub fn dealloc_map() -> DeallocMap {
    HashMap::with_hasher_in(RandomState::new(), DeallocBomb)
}

pub fn dealloc_set() -> DeallocSet {
    HashSet::with_hasher_in(RandomState::new(), DeallocBomb)
}

pub fn alloc_map() -> AllocMap {
    HashMap::with_hasher_in(RandomState::new(), AllocBomb)
}

pub fn dealloc_string_map() -> DeallocStringMap {
    HashMap::with_hasher_in(RandomState::new(), DeallocBomb)
}
