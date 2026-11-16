//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency compiled with verification OFF, the way Targo compiles every
//! dependency unit (`sysroot_drop_reaches_dependency_code.rs`): a type whose
//! `Drop` panics on 7, a type with no destructor at all, and an allocator whose
//! `deallocate` panics on 7. Each is reached from a caller only through a std
//! owner's drop glue.
#![feature(allocator_api)]
use std::alloc::{AllocError, Allocator, Global, Layout};
use std::ptr::NonNull;

/// `Drop` panics on 7.
pub struct Bomb(pub u32);
impl Drop for Bomb {
    fn drop(&mut self) {
        if self.0 == 7 {
            panic!("DEP BOMB DROP PANIC (unverified crate)")
        }
    }
}

/// No destructor: its drop glue is nothing, wherever it sits.
pub struct Plain(pub u32);

/// No destructor of its own; its glue is a sysroot `String`'s.
pub struct Named(pub String);

/// An allocator whose `deallocate` panics on 7.
pub struct DepAlloc(pub u32);
// SAFETY: forwards to `Global`.
unsafe impl Allocator for DepAlloc {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        Global.allocate(layout)
    }
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        if self.0 == 7 {
            panic!("DEP DEALLOCATE PANIC (unverified crate)")
        }
        // SAFETY: `ptr` came from `Global.allocate` with `layout`.
        unsafe { Global.deallocate(ptr, layout) }
    }
}

/// A dependency struct owning a `Box` at `DepAlloc`: a caller holds and drops one
/// without spelling the allocator, and needs no `allocator_api` gate.
pub struct HBox(pub Box<u32, DepAlloc>);

/// The same `Box` behind an alias, so a caller's signature names no allocator.
pub type BoxIn = Box<u32, DepAlloc>;
