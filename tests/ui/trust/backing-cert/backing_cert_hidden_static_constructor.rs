//! SOUNDNESS REGRESSION (backing-cert inventory): a `static` initializer is a
//! `DefKind::Static` body `mir_keys` yields, and the old
//! `DefKind::Fn | AssocFn` filter in `trust_init_backing_certificates` dropped
//! it — so the non-establishing constructor below was invisible, `Buf`
//! certified from `map` alone, and the use-site ASSUME
//! `alloc_size >= self.len` turned `as_slice`'s CAUGHT obligation into PROVED.
//! Stable Rust, no feature gate: this is the most reachable variant of the
//! hole (`static B: S = S { ptr, len }`).
//!
//! With the complete inventory (static bodies recovered via `mir_for_ctfe`),
//! certification must be DENIED: the debug line must report an empty
//! established set. On the unrepaired compiler this test fails: the line reads
//! `established = {"backing_cert_hidden_static_constructor::Buf"}`.

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

// Required for a `static Buf` (raw pointers are not `Sync`); irrelevant to the
// backing analysis itself.
unsafe impl Sync for Buf {}

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

// HIDDEN non-establishing constructor: a `DefKind::Static` body.
static SCRATCH: Buf = Buf { ptr: core::ptr::null(), len: 4096 };

fn main() {}

//~? RAW established = {}
