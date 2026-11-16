//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A verify-off dependency whose `Allocator` panics in `deallocate`. Nothing in this
//! file is verified. Consumed by `std_container_allocator_must_be_global.rs`; see that
//! file for the defect this pins.
//!
//! `Allocator` is an `unsafe trait`, but its contract does not forbid unwinding (only a
//! `#[global_allocator]` must not unwind), so this impl is legal and the panic is real.
#![feature(allocator_api)]

use std::alloc::{AllocError, Allocator, Global, Layout};
use std::ptr::NonNull;

pub struct PanicOnFree;

unsafe impl Allocator for PanicOnFree {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        Global.allocate(layout)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        let _ = (ptr, layout);
        panic!("PanicOnFree::deallocate");
    }
}
