//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Refuted 2026-09-16 (allocator lens, resumed): `ALLOC_OWNING_PARTS` names owners,
//! and deliberately treats `NonNull`/`PhantomData` as non-allocating scaffold — so
//! `std::io::Error` (a `Box<Custom>` behind a tagged `NonNull` that only `Repr`'s
//! manual `Drop` knows about) was never charged, and `consume` proved panic-free
//! while a user `#[global_allocator]` whose `dealloc` panics was in the graph; the
//! panic came from this body's drop glue. Under a user allocator any `Drop` of a
//! `needs_drop` type is now charged — the same conservative rule the call side
//! already applies. The allocator's own bodies are the contract's subject, not its
//! clients: `dealloc` below carries only its own refutation, `alloc` nothing.
use std::alloc::{GlobalAlloc, Layout};

pub struct PanickyDealloc;

unsafe impl GlobalAlloc for PanickyDealloc {
    unsafe fn alloc(&self, _layout: Layout) -> *mut u8 {
        core::ptr::null_mut()
    }
    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {
        panic!("dealloc panics");
    }
}

#[global_allocator]
pub static A: PanickyDealloc = PanickyDealloc;

pub fn consume(e: std::io::Error) {
    //~^ ERROR the `contract:global-alloc-dealloc-panic-free`
    let _ = e;
}
