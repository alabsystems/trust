//! SOUNDNESS REGRESSION (backing-cert inventory, promoted lane): a PROMOTED
//! body can CONSTRUCT a `#[trust::backing]` struct while its parent const body
//! holds only a reference to the promoted — no aggregate at all. `const R:
//! &'static Buf = &Buf { .. }` lowers the aggregate into `promoted[0]` and
//! leaves `_0 = &promoted[0]` in the parent. `certify_backing_invariants` only
//! ever weakens `all_establish` / `broken_by_mutation` from evidence it SEES,
//! so an un-inventoried promoted pushes TOWARD certification.
//!
//! This fixture discriminates the PROMOTED half of the inventory fix
//! specifically, which its siblings cannot: on the unrepaired compiler `Buf`
//! certifies; on a repair that recovers const bodies via `mir_for_ctfe` but
//! skips `promoted_mir`, `Buf` STILL certifies (the parent body has no
//! aggregate to see); only the full repair — which walks
//! `tcx.promoted_mir(def_id)` beside every recovered const body — sees the
//! non-establishing constructor in the promoted fragment and DENIES:
//! `established` must be empty. On either weaker compiler this test fails with
//! `established = {"backing_cert_hidden_promoted_constructor::Buf"}`.

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

// HIDDEN non-establishing constructor, in a PROMOTED body. The aggregate
// `Buf { ptr: null, len: 4096 }` is promoted out of this initializer:
// `R`'s own const body carries only `&promoted[0]`. Its establish obligation
// is `Lt(<untracked>, 4096)` — not UNSAT — so once promoted fragments are
// inventoried, certification must be denied.
const R: &'static Buf = &Buf { ptr: core::ptr::null(), len: 4096 };

fn main() {}

//~? RAW established = {}
