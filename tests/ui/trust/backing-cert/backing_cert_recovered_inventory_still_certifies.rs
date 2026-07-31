//! CAPABILITY CONTROL for the backing-cert inventory fix: closing the
//! incomplete-inventory hole by ABANDONING the certificate whenever any body
//! was stolen or non-`Fn`-like (the force-empty half of the paired-condvar
//! discipline) would darken backing certification for effectively every crate
//! — any non-trivial const, static, closure, promoted fragment, or stolen
//! `#[rustc_comptime]` fn would kill it. The fix must instead RECOVER those
//! bodies (`mir_for_ctfe` is the const-context steal's consumer) so a crate
//! whose extra bodies are BENIGN still certifies.
//!
//! This fixture pairs the establishing constructor with one benign body of
//! every recovered class: a non-trivial const, a stolen comptime fn (its
//! caller const makes `check_crate` consume the `Steal` before the hook), a
//! closure, and a promotable `&'static` borrow. None of them touches `Buf`,
//! so certification must STILL be issued — pinning that the fix recovers
//! rather than abandons. (The hidden-constructor siblings pin the denial
//! direction.)

//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=advisory
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ rustc-env:TRUST_CERT_DEBUG=1

#![feature(register_tool)]
#![feature(rustc_attrs)]
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
    // Sole constructor, establishing: the mapping is exactly `len` bytes, so
    // the establish obligation `len < len` is UNSAT.
    pub unsafe fn map(len: usize) -> Buf {
        let p = mmap(core::ptr::null_mut(), len, 0, 0, -1, 0);
        Buf { ptr: p as *const u8, len }
    }

    pub fn as_slice(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.ptr, self.len) }
    }
}

// Benign NON-TRIVIAL const body (indexing keeps it off the trivial-const fast
// path): recovered via `mir_for_ctfe`, mentions no `Buf`.
const K: usize = [1usize, 2, 3][1];

// Benign always-const fn whose elaborated `Steal` is consumed by the eager
// const-eval of `SEVEN` before the backing hook runs: recovered, no `Buf`.
#[rustc_comptime]
fn seven() -> usize {
    7
}
const SEVEN: usize = seven();

// Benign closure body: inventoried, no `Buf`.
fn inc_all() -> usize {
    let inc = |a: usize| a.wrapping_add(1);
    inc(K)
}

// Benign promoted fragment (`&[…]` is promoted out of this body): the
// promoted-body extraction must not deny either.
fn table() -> &'static [usize; 3] {
    &[1, 2, 3]
}

fn main() {}

//~? RAW established = {"backing_cert_recovered_inventory_still_certifies::Buf"}
