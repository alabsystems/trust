//! SOUNDNESS REGRESSION (backing-cert inventory, the stolen-body variant): a
//! `#[rustc_comptime]` fn has `Constness::Const { always: true }`, which
//! `hir_body_const_context` maps to `ConstContext::Const { .. }`, so
//! `inner_mir_for_ctfe` takes its STEALING arm — and `check_crate` eagerly
//! evaluates `SCRATCH` below, consuming `scratch`'s elaborated `Steal` BEFORE
//! `trust_init_backing_certificates` runs. The old loop answered that state
//! with `if steal.is_stolen() { continue; }`, silently dropping the body from
//! the certification inventory — and since `certify_backing_invariants` only
//! weakens from evidence it sees, the omission pushed TOWARD certification:
//! `Buf` certified from `map` alone while its only other constructor built it
//! from an untracked pointer with a fabricated length.
//!
//! The fix RECOVERS the stolen body through `mir_for_ctfe` — the steal
//! CONSUMER, a tracked query returning a stable `&Body` after the steal — the
//! same discipline `certify_paired_condvars_for_crate` uses for const-context
//! bodies. The non-establishing aggregate in `scratch` is then seen and
//! certification is DENIED. On the unrepaired compiler this test fails: the
//! debug line reads `established = {"backing_cert_hidden_comptime_constructor::Buf"}`.

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

// HIDDEN non-establishing constructor: an always-const fn body. The evidence
// (the `Buf { .. }` aggregate over an untracked pointer) lives HERE — the
// `SCRATCH` initializer body only carries the call — so only the recovery of
// this STOLEN body can deny certification.
#[rustc_comptime]
fn scratch() -> Buf {
    Buf { ptr: core::ptr::null(), len: 4096 }
}

// Eagerly const-evaluated by `check_crate`, which steals `scratch`'s
// elaborated MIR before the backing-certificate hook runs.
const SCRATCH: Buf = scratch();

fn main() {}

//~? RAW established = {}
