//@ needs-trust-verify
//@ edition: 2021
//@ revisions: owned field compound new_box returned_box mut_ref escape ro_alloc dangling_alloc
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[owned] check-pass
//@[field] check-pass
//@[compound] check-pass
//@[new_box] check-pass
//@[returned_box] check-pass
//@[mut_ref] check-pass
//@[escape] check-fail
//@[ro_alloc] check-fail
//@[dangling_alloc] check-fail
//! A STORE through a validity-rooted box (2026-10-09). The compiler now nominates the
//! destination deref of a synthesized box pointer, and a read inside an operator
//! (`*b ^= 1`), so `*b = v` no longer keeps `[unsafe:sep:deref]`/`[unsafe:sep:write]`
//! rows on a valid, uniquely owned box. Before, every such store failed the default
//! lane. `mut_ref` writes through a `&mut Box` argument under the disclosed D14
//! premise.
//!
//! Must stay refused: `escape` hands a raw pointer to the allocation to a callee that
//! frees it, then stores (the body-wide fence). `ro_alloc` and `dangling_alloc` (review
//! round 89) use a USER allocator whose safe `allocate` returns read-only or dangling
//! memory: a `Box<T, A>` is only as valid as its allocator's unchecked promise, so
//! only `Box<T, Global>` is ever rooted. Measured before the fix: SIGBUS and SIGSEGV
//! with the rows dropped.
#![cfg_attr(any(ro_alloc, dangling_alloc), feature(allocator_api))]

#[cfg(owned)]
pub fn f(mut b: Box<u32>, v: u32) -> u32 {
    *b = v;
    *b / 2
}

#[cfg(field)]
pub fn f(mut b: Box<(u32, u64)>) -> u32 {
    b.0 = 3;
    b.0
}

#[cfg(compound)]
pub fn f(mut b: Box<u32>, c: Box<u32>) -> u32 {
    let x = *c;
    *b ^= 1;
    x
}

#[cfg(new_box)]
pub fn f(v: u32) -> u32 {
    let mut b = Box::new(0u32);
    *b = v;
    let r = *b;
    r / 2
}

// A box returned by a verified safe call (the D8 root); formerly pinned as
// refused in `returned_box_refused_calls.rs#write_through`.
#[cfg(returned_box)]
pub fn defaults() -> Box<u32> {
    Box::new(3)
}

#[cfg(returned_box)]
pub fn f() -> u32 {
    let mut b = defaults();
    *b = 4;
    *b
}

#[cfg(mut_ref)]
pub fn f(b: &mut Box<u32>) -> u32 {
    //[mut_ref]~^ NOTE Trust argument-validity premise REFERENCE_ARG_BOX_VALID
    **b = 4;
    **b / 2
}

#[cfg(escape)]
fn sink(p: *const u32) {
    unsafe { drop(Box::from_raw(p as *mut u32)) }
}

#[cfg(escape)]
pub fn f(mut b: Box<u32>) -> u32 {
    //[escape]~^ ERROR Trust strict verification failed for `store_through_rooted_box::f`
    sink(std::ptr::addr_of!(*b));
    *b = 5;
    *b
}

#[cfg(any(ro_alloc, dangling_alloc))]
use std::alloc::{AllocError, Allocator, Layout};
#[cfg(any(ro_alloc, dangling_alloc))]
use std::mem::MaybeUninit;
#[cfg(any(ro_alloc, dangling_alloc))]
use std::ptr::NonNull;

#[cfg(ro_alloc)]
static RO: [u64; 4] = [0; 4];

#[cfg(any(ro_alloc, dangling_alloc))]
pub struct UserAlloc;

#[cfg(any(ro_alloc, dangling_alloc))]
unsafe impl Allocator for UserAlloc {
    fn allocate(&self, l: Layout) -> Result<NonNull<[u8]>, AllocError> {
        #[cfg(ro_alloc)]
        let p: NonNull<u8> = NonNull::from(&RO).cast();
        #[cfg(dangling_alloc)]
        let p: NonNull<u8> = NonNull::<u64>::dangling().cast();
        Ok(NonNull::slice_from_raw_parts(p, l.size()))
    }
    unsafe fn deallocate(&self, _p: NonNull<u8>, _l: Layout) {}
}

#[cfg(ro_alloc)]
pub fn f(mut b: Box<MaybeUninit<u64>, UserAlloc>) -> Box<MaybeUninit<u64>, UserAlloc> {
    //[ro_alloc]~^ ERROR Trust strict verification failed for `store_through_rooted_box::f`
    *b = MaybeUninit::new(5);
    b
}

#[cfg(dangling_alloc)]
pub fn f(b: Box<MaybeUninit<u64>, UserAlloc>) -> MaybeUninit<u64> {
    //[dangling_alloc]~^ ERROR Trust strict verification failed for `store_through_rooted_box::f`
    *b
}
