//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ edition: 2021
//@ no-prefer-dynamic
//! An ordinary dependency, compiled the way `targo` compiles every dependency
//! unit: `-Ztrust-verify=off`, so NOTHING in this file is verified. Each item here
//! is code a std call runs INSIDE itself because one of the call's TYPE ARGUMENTS
//! chose it (docs/design/2026-10-10-call-reach-1-instance-type-arguments.md §2.1),
//! and that code panics once `ARMED` is set (the first armed call disarms it again,
//! so the panic fires once):
//!  * `BadHasher` (H1): a hasher whose `write` panics; `HashMap::eq`/`HashSet::eq`
//!    at `BuildHasherDefault<BadHasher>` hash every key of one side through it;
//!  * `BombAlloc` (H2): an allocator whose `allocate` panics; `Vec<u8, &'static
//!    BombAlloc>::clone` allocates through `<&A as Allocator>::allocate`;
//!  * `Q` (H3): a query type whose `Hash` panics, with the orphan-legal
//!    `impl Borrow<Q> for u32`, so `HashMap<u32, _>::get(&q)` hashes `q` with it;
//!  * `Bomb` (H4): a `PartialEq` whose `eq` panics; `Option<Bomb> == Option<Bomb>`
//!    calls it when both sides hold a payload;
//!  * `DeallocBomb` and `mk` (H5): an allocator whose `deallocate` panics, and a
//!    `Box<str, DeallocBomb>` maker; `String: FromIterator<Box<str, A>>` drops every
//!    item it collects;
//!  * `Plain`: a type that runs no code at all (no `Drop`, no impls but `Copy`), for
//!    the controls a type rule alone would wrongly refuse.
//! The aliases and constructors let a stable downstream crate name these types
//! without `#![feature(allocator_api)]`. Used by
//! `sysroot_call_reach_type_arguments.rs`.

#![feature(allocator_api)]

use std::alloc::{AllocError, Allocator, Global, Layout};
use std::borrow::Borrow;
use std::hash::{BuildHasherDefault, Hash, Hasher};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicBool, Ordering};

/// Arms every bomb below (so values can be built before they panic).
pub static ARMED: AtomicBool = AtomicBool::new(false);

fn armed() -> bool {
    ARMED.swap(false, Ordering::SeqCst)
}

// ---- H1: the hasher a hash collection's `eq` hashes through ----

/// A hasher whose `write` panics once `ARMED`.
#[derive(Default)]
pub struct BadHasher(u64);

impl Hasher for BadHasher {
    fn write(&mut self, bytes: &[u8]) {
        if armed() {
            panic!("sysroot_call_reach_unverified_dep::BadHasher::write")
        }
        for b in bytes {
            self.0 ^= *b as u64;
        }
    }
    fn finish(&self) -> u64 {
        self.0
    }
}

pub type BadBuild = BuildHasherDefault<BadHasher>;

// ---- H2: the allocator behind a `&'static` that `Clone` allocates through ----

/// An allocator whose `allocate` panics once `ARMED`.
pub struct BombAlloc;

unsafe impl Allocator for BombAlloc {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        if armed() {
            panic!("sysroot_call_reach_unverified_dep::BombAlloc::allocate")
        }
        Global.allocate(layout)
    }
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        unsafe { Global.deallocate(ptr, layout) }
    }
}

pub static BOMB_ALLOC: BombAlloc = BombAlloc;

pub type BombVec = Vec<u8, &'static BombAlloc>;

pub fn bomb_vec() -> BombVec {
    let mut v = Vec::new_in(&BOMB_ALLOC);
    v.push(7);
    v
}

// ---- H3: a hash query's own type argument ----

/// A query type whose `Hash` panics once `ARMED`; it hashes and compares as the
/// `u32` it wraps, so a `HashMap<u32, _>` lookup through it is a real lookup.
#[repr(transparent)]
pub struct Q(pub u32);

impl Hash for Q {
    fn hash<H: Hasher>(&self, state: &mut H) {
        if armed() {
            panic!("sysroot_call_reach_unverified_dep::Q::hash")
        }
        self.0.hash(state)
    }
}

impl PartialEq for Q {
    fn eq(&self, other: &Q) -> bool {
        self.0 == other.0
    }
}

impl Eq for Q {}

/// Orphan-legal: `Borrow` and `u32` are foreign, `Q` is this crate's (RFC 2451).
impl Borrow<Q> for u32 {
    fn borrow(&self) -> &Q {
        // SAFETY: `Q` is `repr(transparent)` over `u32`.
        unsafe { &*(self as *const u32 as *const Q) }
    }
}

// ---- H4: the payload `eq` of `Option == Option` ----

/// A `PartialEq` whose `eq` panics once `ARMED`.
pub struct Bomb(pub u32);

impl PartialEq for Bomb {
    fn eq(&self, other: &Bomb) -> bool {
        if armed() {
            panic!("sysroot_call_reach_unverified_dep::Bomb::eq")
        }
        self.0 == other.0
    }
}

// ---- H5: what `collect` drops in its destination's `from_iter` ----

/// An allocator whose `deallocate` panics once `ARMED`.
#[derive(Clone, Copy, Default)]
pub struct DeallocBomb;

unsafe impl Allocator for DeallocBomb {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        Global.allocate(layout)
    }
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        if armed() {
            panic!("sysroot_call_reach_unverified_dep::DeallocBomb::deallocate")
        }
        unsafe { Global.deallocate(ptr, layout) }
    }
}

/// A one-letter `str` boxed at `DeallocBomb`.
pub fn mk(x: u8) -> Box<str, DeallocBomb> {
    let mut v = Vec::new_in(DeallocBomb);
    v.push(b'a' + x % 26);
    let (raw, alloc) = Box::into_raw_with_allocator(v.into_boxed_slice());
    // SAFETY: the bytes are one ASCII letter, so valid UTF-8; `[u8]` and `str` share
    // their layout and metadata.
    unsafe { Box::from_raw_in(raw as *mut str, alloc) }
}

// ---- the controls: a dependency type that runs no code ----

#[derive(Clone, Copy)]
pub struct Plain(pub u32);
