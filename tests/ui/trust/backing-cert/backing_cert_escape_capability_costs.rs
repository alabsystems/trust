//@ revisions: ptr_eq thread_local
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ rustc-env:TRUST_CERT_DEBUG=1
//@ forbid-output: backing inventory INCOMPLETE
//! CAPABILITY COST of the backing-certificate escape census (2026-09-30), named
//! rather than implied. Each revision certified `Buf` on the base compiler, and none
//! of them writes `Buf`'s bytes — but each goes through a door the census cannot see
//! past, so each is now DENIED:
//!
//! * `ptr_eq`: `ptr::eq(a, b)` coerces `&Buf` to `*const Buf`, a held raw pointer.
//!   The census does not track a raw pointer's provenance, so it cannot tell this
//!   one (which a write through would be UB to use) from one that came from a
//!   `*mut`; it denies every held raw pointer to `Buf`, so comparing addresses
//!   costs the certificate.
//! * `thread_local`: `thread_local!` expands to `LocalKey::new`, an unsafe sysroot
//!   constructor whose accessor returns `*const T`.
//!
//! The escape for each is the safe spelling (a `static` behind a `Mutex`, comparing
//! a field instead of the address). If one of these starts certifying again, it must
//! be because the census learned to prove it harmless, not because a rule was
//! dropped. (`get_unchecked_mut` and `unwrap_unchecked`, once here, now certify:
//! they are parametric accessors whose unsafety is a precondition — see
//! `backing_cert_escape_precision.rs`.)

#![feature(register_tool)]
#![register_tool(trust)]
#![allow(dead_code)]

extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, offset: i64) -> *mut u8;
}

#[trust::backing]
pub struct Buf {
    ptr: *const u8,
    len: usize,
}

impl Buf {
    pub unsafe fn map(len: usize) -> Buf {
        let p = mmap(core::ptr::null_mut(), len, 0, 0, -1, 0);
        Buf { ptr: p as *const u8, len }
    }

    pub fn get(&self, i: usize) -> u8 {
        if i < self.len { unsafe { *self.ptr.add(i) } } else { 0 }
    }
}

#[cfg(ptr_eq)]
pub fn same(a: &Buf, b: &Buf) -> bool {
    core::ptr::eq(a, b)
}

#[cfg(thread_local)]
thread_local! {
    static TL: core::cell::RefCell<Option<Buf>> = const { core::cell::RefCell::new(None) };
}
#[cfg(thread_local)]
pub fn first() -> u8 {
    TL.with(|c| c.borrow().as_ref().map_or(0, |b| b.get(0)))
}

fn main() {}

//~? RAW established = {}
//[ptr_eq]~? RAW DENIED: a raw pointer is taken to storage that holds it in `same`
//[thread_local]~? RAW DENIED: the unsafe function `std::thread::LocalKey::<T>::new`, whose body is not in this crate, is applied to it
