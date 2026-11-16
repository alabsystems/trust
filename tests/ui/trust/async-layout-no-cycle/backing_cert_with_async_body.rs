//@ revisions: benign hidden
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ rustc-env:TRUST_CERT_DEBUG=1
//@ forbid-output: E0391
//@ forbid-output: cycle detected
//@ forbid-output: backing inventory INCOMPLETE
//! Backing certificates in a crate with an `async` body. The certifier requires
//! a COMPLETE writer inventory (`backing_inventory_complete`). Before
//! 2026-09-29 a coroutine's layout was read from its `optimized_mir`, which
//! `run_required_analyses` demanded for every coroutine and which stole the
//! coroutine's elaborated MIR before the backing-certificate seam ran — so the
//! inventory of every crate with an `async fn` was incomplete and no
//! certificate was issued (fail-closed). The layout is now read pre-steal
//! (`trust_local_coroutine_layout`), so the coroutine body is IN the inventory:
//!
//! * `benign`: an unrelated `async fn` touches no `Buf`; the certificate is now
//!   issued (before: `backing inventory INCOMPLETE`, `established = {}`).
//! * `hidden`: the `async` body is a non-establishing constructor of `Buf`; it
//!   is seen, and certification is DENIED — the gain is completeness, not a
//!   dropped check.

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
    // Sole visible constructor, establishing: the mapping is exactly `len` bytes.
    pub unsafe fn map(len: usize) -> Buf {
        let p = mmap(core::ptr::null_mut(), len, 0, 0, -1, 0);
        Buf { ptr: p as *const u8, len }
    }

    pub fn as_slice(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.ptr, self.len) }
    }
}

#[cfg(benign)]
pub async fn tick(x: u32) -> u32 {
    x.wrapping_add(1)
}

// HIDDEN non-establishing constructor inside the coroutine body.
#[cfg(hidden)]
pub async fn from_async() -> usize {
    let b = Buf { ptr: core::ptr::null(), len: 4096 };
    b.len
}

fn main() {}

//[benign]~? RAW established = {"backing_cert_with_async_body::Buf"}
//[hidden]~? RAW established = {}
