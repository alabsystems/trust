//! SOUNDNESS REGRESSION (backing-cert inventory): a `const` item's initializer
//! is itself a body that can CONSTRUCT a `#[trust::backing]` struct, and
//! `certify_backing_invariants` only ever weakens `all_establish` /
//! `broken_by_mutation` from evidence it SEES — so a body dropped from the
//! inventory pushes TOWARD certification. `trust_init_backing_certificates`
//! used to filter `mir_keys` to `DefKind::Fn | AssocFn`, dropping every
//! const-item body: `SCRATCH` below builds `Buf` from an untracked pointer
//! with a fabricated length, yet `Buf` still certified from `map` alone, and
//! the use-site ASSUME `alloc_size >= self.len` turned `as_slice`'s CAUGHT
//! out-of-bounds obligation into PROVED.
//!
//! The fix inventories every `mir_keys` body owner (recovering const-context
//! bodies via `mir_for_ctfe`, the steal consumer), so the non-establishing
//! constructor in `SCRATCH` is seen and certification is DENIED: the debug
//! line must report an empty established set. On the unrepaired compiler this
//! test fails: the line reads `established = {"backing_cert_hidden_const_constructor::Buf"}`.

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
    // VISIBLE establishing constructor: the mapping is exactly `len` bytes, so
    // the establish obligation is `len < len` (UNSAT). Needed so that, without
    // the hidden constructor below, `Buf` genuinely WOULD certify — a struct
    // with no establishing constructor never certifies, before or after the
    // fix, and could not discriminate.
    pub unsafe fn map(len: usize) -> Buf {
        let p = mmap(core::ptr::null_mut(), len, 0, 0, -1, 0);
        Buf { ptr: p as *const u8, len }
    }

    pub fn as_slice(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.ptr, self.len) }
    }
}

// HIDDEN non-establishing constructor: a `DefKind::Const` body. Its establish
// obligation is `Lt(<untracked>, 4096)` — not UNSAT — so once this body is
// inventoried, certification must be denied.
const SCRATCH: Buf = Buf { ptr: core::ptr::null(), len: 4096 };

fn main() {}

//~? RAW established = {}
