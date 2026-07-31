//! SOUNDNESS REGRESSION (backing-cert inventory): a tuple-struct constructor
//! used as a function VALUE constructs inside the compiler-generated ctor SHIM
//! (`_0 = Buf(move _1, move _2)`), a `DefKind::Ctor` body `mir_keys` yields —
//! the calling function only carries an indirect call. The old
//! `DefKind::Fn | AssocFn` filter dropped the shim, so the non-establishing
//! construction in `from_fn_ptr` below was invisible and `Buf` certified from
//! `map` alone. Tuple fields are private by default, so the struct still
//! passed the sealed check — stable Rust, no feature gate.
//!
//! With the complete inventory (ctor shims served by `mir_for_ctfe` via
//! `shim::build_adt_ctor`), the shim's establish obligation
//! `Lt(<untracked param>, len)` is seen — not UNSAT — and certification is
//! DENIED. On the unrepaired compiler this test fails: the debug line reads
//! `established = {"backing_cert_hidden_ctor_shim_constructor::Buf"}`.

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
pub struct Buf(*const u8, usize);

impl Buf {
    // VISIBLE establishing constructor: a DIRECT ctor call lowers to an
    // aggregate in THIS body, with the mmap-tracked pointer — `len < len` is
    // UNSAT.
    //
    // NOTE (capability, stated honestly): on the repaired compiler a tuple
    // `#[trust::backing]` struct can NEVER certify, with or without
    // `from_fn_ptr` below. `mir_keys` inserts the tuple-ctor shim
    // unconditionally (rustc_mir_transform/src/lib.rs, mir_keys push of ctors),
    // and the shim body constructs from its UNTRACKED parameter pointer, whose
    // establish obligation is symbolic-size (sep_engine.rs, the untracked-param
    // arm) — never UNSAT. So this fixture does not discriminate "hidden shim
    // seen vs unseen" by certification outcome alone; it pins that the shim is
    // INVENTORIED (the established set stays empty for the right reason, with
    // the shim's obligation present) rather than dropped. The categorical
    // tuple-struct capability regression is recorded at the `DefKind::Ctor`
    // inventory arm in trust_verify.rs.
    pub unsafe fn map(len: usize) -> Buf {
        let p = mmap(core::ptr::null_mut(), len, 0, 0, -1, 0);
        Buf(p as *const u8, len)
    }

    pub fn as_slice(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.0, self.1) }
    }
}

// HIDDEN non-establishing constructor: the ctor SHIM body. This function's own
// body holds only `ctor(<untracked>, 4096)` — an indirect call, no aggregate.
fn from_fn_ptr() -> Buf {
    let ctor: fn(*const u8, usize) -> Buf = Buf;
    ctor(core::ptr::null(), 4096)
}

fn main() {}

//~? RAW established = {}
