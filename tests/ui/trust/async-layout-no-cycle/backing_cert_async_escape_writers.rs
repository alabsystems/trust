//@ revisions: wrap_field rawptr_field cast_ptr union_pun transmute_ctor write_bytes ffi_whole
//@ revisions: whole_capture sync_writer_async_crate field_capture benign
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@ compile-flags: -Ztrust-verify-output=json --error-format=human
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ rustc-env:TRUST_CERT_DEBUG=1
//@ forbid-output: backing inventory INCOMPLETE
//@ forbid-output: E0391
//@ forbid-output: cycle detected
//@[wrap_field] forbid-output: "line_start":72,"col_start":36,"line_end":72,"col_end":51},"outcome":"proved"
//@[rawptr_field] forbid-output: "line_start":72,"col_start":36,"line_end":72,"col_end":51},"outcome":"proved"
//@[cast_ptr] forbid-output: "line_start":72,"col_start":36,"line_end":72,"col_end":51},"outcome":"proved"
//@[union_pun] forbid-output: "line_start":72,"col_start":36,"line_end":72,"col_end":51},"outcome":"proved"
//@[transmute_ctor] forbid-output: "line_start":72,"col_start":36,"line_end":72,"col_end":51},"outcome":"proved"
//@[write_bytes] forbid-output: "line_start":72,"col_start":36,"line_end":72,"col_end":51},"outcome":"proved"
//@[ffi_whole] forbid-output: "line_start":72,"col_start":36,"line_end":72,"col_end":51},"outcome":"proved"
//@[whole_capture] forbid-output: "line_start":72,"col_start":36,"line_end":72,"col_end":51},"outcome":"proved"
//@[sync_writer_async_crate] forbid-output: "line_start":72,"col_start":36,"line_end":72,"col_end":51},"outcome":"proved"
//! SOUNDNESS PIN (backing certificates in `async` crates, 2026-09-30).
//!
//! Before the async-layout change a coroutine's layout was read from its
//! `optimized_mir` during `run_required_analyses`, which stole the coroutine's
//! elaborated MIR before the backing-certificate seam, so the inventory of EVERY
//! crate with an `async` body was incomplete and no certificate was issued: the
//! writers below were fail-closed by accident, never by a check. The layout is
//! now read pre-steal (`trust_local_coroutine_layout`), the coroutine bodies are
//! in the inventory, and a certificate CAN be issued in an `async` crate — so a
//! writer inside a coroutine must be seen. On the async-layout branch before the
//! escape census existed, the cast-pointer, union, `Wrap` and raw-pointer field
//! writers below certified `Buf` with `get`'s offset row PROVED (reviewer probes
//! `x3`, `x9`, `bc_w1_get`, `c2`). Each revision here writes or forges `Buf`'s
//! bytes from inside an `async` body (or, in `sync_writer_async_crate`, from a
//! plain fn of a crate that also has one); the escape census
//! (`backing_escape_census` in `trust_verify.rs`) scans the coroutine bodies like
//! any other and DENIES `Buf` in each, naming the coroutine, so the established
//! set is empty and `get`'s `[unsafe:sep:offset]` row is not proved.
//!
//! Precision controls, which must still certify (the gain of the change):
//!
//! * `field_capture`: an `async move` block captures only `b.len` by edition-2021
//!   PRECISE capture — its own `usize` copy — so writing it changes no `Buf`.
//! * `benign`: an unrelated `async fn` touches no `Buf`.

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
    // Sole establishing constructor: the mapping is exactly `len` bytes.
    pub unsafe fn map(len: usize) -> Buf {
        let p = mmap(core::ptr::null_mut(), len, 0, 0, -1, 0);
        Buf { ptr: p as *const u8, len }
    }

    pub fn get(&self, i: usize) -> u8 {
        if i < self.len { unsafe { *self.ptr.add(i) } } else { 0 }
    }
}

pub struct Wrap {
    pub b: Buf,
}

#[cfg(wrap_field)]
pub async fn grow(w: &mut Wrap) {
    std::future::ready(()).await;
    w.b.len = 1 << 20;
}

#[cfg(rawptr_field)]
pub async fn grow(b: *mut Buf) {
    std::future::ready(()).await;
    unsafe {
        (*b).len = 1 << 33;
    }
}

#[cfg(cast_ptr)]
pub async fn grow(b: &mut Buf) {
    unsafe {
        *((b as *mut Buf as *mut usize).add(1)) = 1 << 20;
    }
}

#[cfg(union_pun)]
pub union U {
    b: core::mem::ManuallyDrop<Buf>,
    raw: (usize, usize),
}

#[cfg(union_pun)]
pub async fn grow(u: &mut U) {
    unsafe {
        u.raw.1 = 1 << 20;
    }
}

#[cfg(transmute_ctor)]
pub async fn forge(p: *const u8) -> Buf {
    unsafe { core::mem::transmute::<(*const u8, usize), Buf>((p, 1 << 20)) }
}

#[cfg(write_bytes)]
pub async fn grow(b: &mut Buf) {
    unsafe { core::ptr::write_bytes(b as *mut Buf, 0xff, 1) }
}

#[cfg(ffi_whole)]
extern "C" {
    fn clobber(b: *mut Buf);
}

#[cfg(ffi_whole)]
pub async fn grow(b: &mut Buf) {
    unsafe { clobber(b) }
}

#[cfg(whole_capture)]
pub fn grow(mut b: Buf) -> impl core::future::Future<Output = u8> {
    async move {
        b.len = 1 << 20;
        b.get(5)
    }
}

#[cfg(sync_writer_async_crate)]
pub fn grow(w: &mut Wrap) {
    w.b.len = 1 << 20;
}

#[cfg(sync_writer_async_crate)]
pub async fn tick(x: u32) -> u32 {
    x.wrapping_add(1)
}

#[cfg(field_capture)]
pub fn grow(mut b: Buf) {
    let c = async move {
        b.len = 1 << 20;
    };
    drop(c);
}

#[cfg(benign)]
pub async fn tick(x: u32) -> u32 {
    x.wrapping_add(1)
}

fn main() {}

//[wrap_field]~? RAW DENIED: its length field is written in `grow::{closure#0}`
//[rawptr_field]~? RAW DENIED: its length field is written in `grow::{closure#0}`
//[cast_ptr]~? RAW DENIED: a raw pointer to it is cast (`*mut Buf` to `*mut usize`) in `grow::{closure#0}`
//[union_pun]~? RAW DENIED: the union `U` that holds it is accessed by a field in `grow::{closure#0}`
//[transmute_ctor]~? RAW DENIED: it is transmuted (`(*const u8, usize)` to `Buf`) in `forge::{closure#0}`
//[write_bytes]~? RAW DENIED: the unsafe function `std::ptr::write_bytes`, whose body is not in this crate, is applied to it in `grow::{closure#0}`
//[ffi_whole]~? RAW DENIED: the foreign function `clobber` receives or returns it in `grow::{closure#0}`
//[whole_capture]~? RAW DENIED: its length field is written in `grow::{closure#0}`
//[sync_writer_async_crate]~? RAW DENIED: its length field is written in `grow`
//[wrap_field,rawptr_field,cast_ptr,union_pun,transmute_ctor,write_bytes,ffi_whole,whole_capture,sync_writer_async_crate]~? RAW established = {}
//[wrap_field,rawptr_field,cast_ptr,union_pun,transmute_ctor,write_bytes,ffi_whole,whole_capture,sync_writer_async_crate]~? RAW "line_start":72,"col_start":36,"line_end":72,"col_end":51},"outcome":"failed"
//[field_capture,benign]~? RAW established = {"backing_cert_async_escape_writers::Buf"}
//[field_capture,benign]~? RAW "line_start":72,"col_start":36,"line_end":72,"col_end":51},"outcome":"proved"
