//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! An unverified dependency supplying an `Allocator` whose `allocate` and
//! `deallocate` panic on large layouts. Review round 61: the extractor's total-call
//! licences erased a `Vec`/`String` extend or keyed collect without asking whose
//! allocator it runs.
#![feature(allocator_api)]
use std::alloc::{AllocError, Allocator, Global, Layout};
use std::ptr::NonNull;

#[derive(Clone, Copy)]
pub struct Q;

unsafe impl Allocator for Q {
    fn allocate(&self, l: Layout) -> Result<NonNull<[u8]>, AllocError> {
        if l.size() > 64 {
            panic!("allocate panics")
        }
        Global.allocate(l)
    }
    unsafe fn deallocate(&self, p: NonNull<u8>, l: Layout) {
        if l.size() > 8 {
            panic!("deallocate panics")
        }
        unsafe { Global.deallocate(p, l) }
    }
}
