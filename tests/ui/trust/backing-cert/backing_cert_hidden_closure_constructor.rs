//! SOUNDNESS REGRESSION (backing-cert inventory): a closure body is a
//! `DefKind::Closure` body `mir_keys` yields, and the old
//! `DefKind::Fn | AssocFn` filter in `trust_init_backing_certificates` dropped
//! it. A closure that CONSTRUCTS the backing struct (a local of type `Buf`
//! plus the `Buf { .. }` aggregate, both inside the closure body) was
//! therefore invisible: `Buf` certified from `map` alone and the use-site
//! ASSUME `alloc_size >= self.len` turned `as_slice`'s CAUGHT obligation into
//! PROVED. Stable Rust, no feature gate.
//!
//! (A closure that merely MUTATES a captured `buf.len` through a `&mut usize`
//! upvar would not discriminate — under precise capture its locals never
//! mention `Buf`, so `certify_backing_invariants` skips it as irrelevant. The
//! constructing form below is the one the inventory hole actually admits.)
//!
//! With closures inventoried, the non-establishing aggregate is seen and
//! certification is DENIED. On the unrepaired compiler this test fails: the
//! debug line reads `established = {"backing_cert_hidden_closure_constructor::Buf"}`.

//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=advisory
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ rustc-env:TRUST_CERT_DEBUG=1

#![feature(register_tool)]
#![register_tool(trust)]
#![allow(dead_code)]

use std::slice;

extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, offset: i64) -> *mut u8;
}

#[trust::backing]
pub struct Buf {
    ptr: *const u8,
    len: usize,
}

impl Buf {
    // VISIBLE establishing constructor (see the const-constructor sibling test
    // for why one must be present for the fixture to discriminate).
    pub unsafe fn map(len: usize) -> Buf {
        let p = mmap(core::ptr::null_mut(), len, 0, 0, -1, 0);
        Buf { ptr: p as *const u8, len }
    }

    pub fn as_slice(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.ptr, self.len) }
    }
}

// HIDDEN non-establishing constructor: the closure body holds the aggregate;
// this function's own body only calls it.
fn from_closure() -> Buf {
    let build = || Buf { ptr: core::ptr::null(), len: 4096 };
    build()
}

fn main() {}

//~? RAW established = {}
