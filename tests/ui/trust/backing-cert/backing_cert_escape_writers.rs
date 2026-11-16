//@ revisions: cast_ptr union_pun transmute_ctor ffi_whole write_bytes raw_field mem_replace
//@ revisions: generic_setter closure_write rawptr_param nonnull_cast generic_clobber
//@ revisions: generic_trait_impl dyn_vtable static_mut zeroed maybe_uninit exported_fn
//@ revisions: foreign_static transmute_ref ptr_read_forge sysroot_callback generic_drop
//@ revisions: inline_asm exported_static third_party dyn_erase box_dyn_erase
//@[third_party] aux-build:backing_escape_dep.rs
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
//@ forbid-output: "line_start":89,"col_start":36,"line_end":89,"col_end":51},"outcome":"proved"
//! SOUNDNESS REGRESSION (backing certificates, 2026-09-30): the escape census.
//!
//! `Buf`'s certificate publishes the use-site ASSUME `alloc_size >= self.len`, which
//! makes `get`'s `[unsafe:sep:offset]` row (line 89, `self.ptr.add(i)`) PROVED. That
//! is sound only if no code can write `Buf`'s pointer or length except through a
//! struct literal the certifier audited. Every revision below writes (or forges)
//! `Buf`'s bytes, and none of them through a field store the certifier relates to
//! `Buf`. On the base compiler each of the first 23 revisions certified `Buf` and
//! reported that row `proved` (measured on the stage-1 `trustc` of `9aef5ba867`,
//! `origin/main` `98568062d8` merged). The census (`backing_escape_census` in
//! `trust_verify.rs`) scans every inventoried body on its rustc MIR, every local
//! generic body again per instantiation, and the item declarations; it denies `Buf`
//! in each revision, the debug report names the path (pinned per revision), the
//! established set is empty, and the offset row is not proved (the `forbid-output`
//! on its exact span; the row's outcome is pinned as `failed` below).
//!
//! * byte-level writers: `cast_ptr`, `union_pun`, `write_bytes`, `ffi_whole`,
//!   `nonnull_cast` (no `*mut Buf` local ever exists — only a `NonNull<Buf>`),
//!   `transmute_ref` (`&mut Buf` reinterpreted as `&mut [usize; 2]`),
//!   `inline_asm` (`&mut Buf` handed to assembly), `third_party` (`&mut Buf`
//!   handed to a non-sysroot crate's generic function);
//! * field-projection writers the certifier's local-type gate skipped:
//!   `raw_field` (`&raw mut w.b.len`), `mem_replace`, `generic_setter`,
//!   `closure_write`, `rawptr_param` (`(*b).len = ..` through `b: *mut Buf`);
//! * forged values: `transmute_ctor`, `zeroed`, `maybe_uninit`, `ptr_read_forge`
//!   (a `*const Buf` over two `usize`s);
//! * storage other code reaches: `static_mut` (`&raw const` of a static holding
//!   `Buf`), `exported_fn` (foreign code calls it with any `Buf`),
//!   `exported_static`, `foreign_static` (a `Buf` whose bytes come from C);
//! * generic code followed per instantiation: `generic_clobber` (a local generic
//!   fn whose `T` is `Buf` at the call), `generic_trait_impl` (a local generic impl
//!   selected by trait resolution), `dyn_vtable` (the same impl reached only through
//!   a `dyn` coercion's vtable), `sysroot_callback` (a local generic `Clone` reached
//!   only through `Vec::clone`'s `T: Clone` bound, inside the sysroot),
//!   `generic_drop` (a local generic `Drop` impl run by drop glue);
//! * `dyn` erasure that discards the vtable: `dyn_erase` (`&mut Buf` erased to
//!   `&mut dyn Any`, then the fat pointer cast to a thin `*mut usize` and written
//!   past offset 0), `box_dyn_erase` (the same through `Box<dyn Any>` and
//!   `Box::into_raw`). The concrete type is gone from the `dyn` pointer, so the type
//!   walks cannot see `Buf` behind it — the census instead denies every struct it
//!   erased into a `dyn` once any body recovers a thin pointer out of one.

#![feature(register_tool)]
#![register_tool(trust)]
#![allow(dead_code, unused_mut, unused_variables, static_mut_refs, improper_ctypes)]

#[cfg(third_party)]
extern crate backing_escape_dep;

use core::mem::{ManuallyDrop, MaybeUninit};
use core::ptr::{self, NonNull};

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

#[cfg(cast_ptr)]
pub fn grow(b: &mut Buf) {
    unsafe { *((b as *mut Buf as *mut usize).add(1)) = 1 << 20 }
}

#[cfg(union_pun)]
pub union U {
    b: ManuallyDrop<Buf>,
    raw: (usize, usize),
}
#[cfg(union_pun)]
pub fn grow(u: &mut U) {
    unsafe { u.raw.1 = 1 << 20 }
}

#[cfg(transmute_ctor)]
pub fn forge(p: *const u8) -> Buf {
    unsafe { core::mem::transmute::<(*const u8, usize), Buf>((p, 1 << 20)) }
}

#[cfg(ffi_whole)]
extern "C" {
    fn clobber(b: *mut Buf);
}
#[cfg(ffi_whole)]
pub fn grow(b: &mut Buf) {
    unsafe { clobber(b) }
}

#[cfg(write_bytes)]
pub fn grow(b: &mut Buf) {
    unsafe { ptr::write_bytes(b as *mut Buf, 0xff, 1) }
}

#[cfg(raw_field)]
pub fn grow(w: &mut Wrap) {
    unsafe { ptr::write(&raw mut w.b.len, 1 << 20) }
}

#[cfg(mem_replace)]
pub fn grow(w: &mut Wrap) {
    let _ = core::mem::replace(&mut w.b.len, 1 << 20);
}

#[cfg(generic_setter)]
fn set<T>(x: &mut T, v: T) {
    *x = v;
}
#[cfg(generic_setter)]
pub fn grow(w: &mut Wrap) {
    set(&mut w.b.len, 1 << 20);
}

#[cfg(closure_write)]
pub fn grow(w: &mut Wrap) {
    let mut f = || w.b.len = 1 << 20;
    f();
}

#[cfg(rawptr_param)]
pub fn grow(b: *mut Buf) {
    unsafe { (*b).len = 1 << 20 }
}

#[cfg(nonnull_cast)]
pub fn grow(b: &mut Buf) {
    unsafe { NonNull::from(b).cast::<usize>().add(1).write(1 << 20) }
}

#[cfg(generic_clobber)]
fn clobber<T>(x: &mut T) {
    unsafe { *(x as *mut T as *mut usize).add(1) = 1 << 20 }
}
#[cfg(generic_clobber)]
pub fn grow(b: &mut Buf) {
    clobber(b)
}

#[cfg(any(generic_trait_impl, dyn_vtable))]
pub struct Holder<T>(T);
#[cfg(any(generic_trait_impl, dyn_vtable))]
pub trait Poke {
    fn poke(&mut self);
}
#[cfg(any(generic_trait_impl, dyn_vtable))]
impl<T> Poke for Holder<T> {
    fn poke(&mut self) {
        let n = core::mem::size_of::<T>();
        unsafe { ptr::write_bytes(&mut self.0 as *mut T as *mut u8, 0xff, n) }
    }
}
#[cfg(generic_trait_impl)]
pub fn grow(h: &mut Holder<Buf>) {
    h.poke()
}
#[cfg(dyn_vtable)]
pub fn erase(h: &mut Holder<Buf>) -> &mut dyn Poke {
    h
}

#[cfg(static_mut)]
pub static mut G: Option<Buf> = None;
#[cfg(static_mut)]
pub fn peek() -> u8 {
    unsafe { (*(&raw const G)).as_ref().map_or(0, |b| b.get(0)) }
}

#[cfg(zeroed)]
pub fn forge() -> Buf {
    unsafe { core::mem::zeroed::<Buf>() }
}

#[cfg(maybe_uninit)]
pub fn forge() -> Buf {
    unsafe { MaybeUninit::<Buf>::uninit().assume_init() }
}

#[cfg(exported_fn)]
#[no_mangle]
pub extern "C" fn buf_get(b: &Buf, i: usize) -> u8 {
    b.get(i)
}

#[cfg(foreign_static)]
extern "C" {
    static EXT: Buf;
}
#[cfg(foreign_static)]
pub fn peek() -> u8 {
    unsafe { EXT.get(0) }
}

#[cfg(transmute_ref)]
pub fn grow(b: &mut Buf) {
    let words = unsafe { core::mem::transmute::<&mut Buf, &mut [usize; 2]>(b) };
    words[1] = 1 << 20;
}

#[cfg(ptr_read_forge)]
pub fn forge() -> Buf {
    let words = [0usize, 1 << 20];
    unsafe { ptr::read(&words as *const [usize; 2] as *const Buf) }
}

#[cfg(sysroot_callback)]
pub struct Pair<T>(T);
#[cfg(sysroot_callback)]
impl<T> Clone for Pair<T> {
    fn clone(&self) -> Self {
        let n = core::mem::size_of::<Self>();
        unsafe {
            let mut copy: Self = ptr::read(self);
            ptr::write_bytes(&mut copy as *mut Self as *mut u8, 0xff, n);
            copy
        }
    }
}
#[cfg(sysroot_callback)]
pub fn dup(v: &Vec<Pair<Buf>>) -> Vec<Pair<Buf>> {
    v.clone()
}

#[cfg(generic_drop)]
pub struct Guard<T>(T);
#[cfg(generic_drop)]
impl<T> Drop for Guard<T> {
    fn drop(&mut self) {
        let n = core::mem::size_of::<T>();
        unsafe { ptr::write_bytes(&mut self.0 as *mut T as *mut u8, 0xff, n) }
    }
}
#[cfg(generic_drop)]
pub fn hold(b: Buf) -> u8 {
    let g = Guard(b);
    g.0.get(0)
}

#[cfg(inline_asm)]
pub fn grow(b: &mut Buf) {
    unsafe { core::arch::asm!("/* {0} */", in(reg) b) }
}

#[cfg(exported_static)]
#[no_mangle]
pub static mut EXPORTED: Option<Buf> = None;

#[cfg(third_party)]
pub fn grow(b: &mut Buf) {
    backing_escape_dep::touch(b);
}

// A `dyn` object erases the concrete type, so a `dyn` pointer's own type reaches
// nothing: casting the fat pointer to a thin `*mut usize` recovers raw byte access
// to the erased `Buf` past its vtable. The census records what a body erases into a
// `dyn` and denies it once any body makes such a thin cast.
#[cfg(dyn_erase)]
pub fn grow(b: &mut Buf) {
    let r: &mut dyn core::any::Any = b;
    let p = r as *mut dyn core::any::Any as *mut usize;
    unsafe { *p.add(1) = 1 << 20 }
}

#[cfg(box_dyn_erase)]
pub fn grown(n: usize) -> Box<dyn core::any::Any> {
    let b: Box<dyn core::any::Any> = Box::new(unsafe { Buf::map(n) });
    let p: *mut dyn core::any::Any = Box::into_raw(b);
    unsafe {
        *(p as *mut usize).add(1) = 1 << 20;
        Box::from_raw(p)
    }
}

fn main() {}

//~? RAW established = {}
//~? RAW "line_start":89,"col_start":36,"line_end":89,"col_end":51},"outcome":"failed"
//[cast_ptr]~? RAW DENIED: a raw pointer to it is cast (`*mut Buf` to `*mut usize`) in `grow`
//[union_pun]~? RAW DENIED: the union `U` is declared over it
//[union_pun]~? RAW DENIED: the union `U` that holds it is accessed by a field in `grow`
//[transmute_ctor]~? RAW DENIED: it is transmuted (`(*const u8, usize)` to `Buf`) in `forge`
//[ffi_whole]~? RAW DENIED: the foreign function `clobber` is declared over it
//[ffi_whole]~? RAW DENIED: the foreign function `clobber` receives or returns it in `grow`
//[write_bytes]~? RAW DENIED: the unsafe function `std::ptr::write_bytes`, whose body is not in this crate, is applied to it in `grow`
//[raw_field]~? RAW DENIED: its length field is written in `grow`
//[mem_replace]~? RAW DENIED: its length field is written in `grow`
//[generic_setter]~? RAW DENIED: its length field is written in `grow`
//[closure_write]~? RAW DENIED: its length field is written in `grow`
//[rawptr_param]~? RAW DENIED: its length field is written in `grow`
//[rawptr_param]~? RAW DENIED: a raw pointer to it is held (`*mut Buf`) in `grow`
//[nonnull_cast]~? RAW DENIED: a raw pointer to it is held (`NonNull<Buf>`) in `grow`
//[generic_clobber]~? RAW DENIED: a raw pointer is taken to storage that holds it in `clobber instantiated with [Buf]`
//[generic_trait_impl]~? RAW DENIED: a raw pointer is taken to storage that holds it in `<Holder<T> as Poke>::poke instantiated with [Buf]`
//[dyn_vtable]~? RAW DENIED: a raw pointer is taken to storage that holds it in `<Holder<T> as Poke>::poke instantiated with [Buf]`
//[static_mut]~? RAW DENIED: a raw pointer is taken to storage that holds it in `peek`
//[zeroed]~? RAW DENIED: the unsafe function `std::mem::zeroed`, whose body is not in this crate, is applied to it in `forge`
//[maybe_uninit]~? RAW DENIED: the unsafe function `std::mem::MaybeUninit::<T>::assume_init`, whose body is not in this crate, is applied to it in `forge`
//[exported_fn]~? RAW DENIED: `buf_get` is exported or has a foreign ABI, so code outside Rust can call it with a value of it
//[foreign_static]~? RAW DENIED: the foreign static `EXT` holds it
//[transmute_ref]~? RAW DENIED: it is transmuted (`&mut Buf` to `&mut [usize; 2]`) in `grow`
//[ptr_read_forge]~? RAW DENIED: a raw pointer to it is cast (`*const [usize; 2]` to `*const Buf`) in `forge`
//[sysroot_callback]~? RAW DENIED: a raw pointer is taken to storage that holds it in `<Pair<T> as std::clone::Clone>::clone instantiated with [Buf]`
//[generic_drop]~? RAW DENIED: a raw pointer is taken to storage that holds it in `<Guard<T> as std::ops::Drop>::drop instantiated with [Buf]`
//[inline_asm]~? RAW DENIED: inline assembly reaches it in `grow`
//[exported_static]~? RAW DENIED: the exported static `EXPORTED` holds it
//[third_party]~? RAW DENIED: `backing_escape_dep::touch`, from a crate that is neither this crate nor the sysroot, is handed a mutable reference or raw pointer that reaches it in `grow`
//[dyn_erase]~? RAW DENIED: it is erased into a `dyn Trait` and a thin pointer is recovered from it (`*mut dyn Any` to `*mut usize`) in `grow`, which recovers raw byte access to it past the vtable
//[box_dyn_erase]~? RAW DENIED: it is erased into a `dyn Trait` and a thin pointer is recovered from it (`*mut dyn Any` to `*mut usize`) in `grown`, which recovers raw byte access to it past the vtable
