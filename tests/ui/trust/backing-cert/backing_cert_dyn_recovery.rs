//@ revisions: transmute_parts box_transmute_parts ptr_cast_call nonnull_cast_call raw_parts
//@ revisions: generic_strip union_parts fat_storage fat_storage_call expose_addr
//@ revisions: sysroot_erased erase_only
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
//@[transmute_parts] forbid-output: "line_start":84,"col_start":36,"line_end":84,"col_end":51},"outcome":"proved"
//@[box_transmute_parts] forbid-output: "line_start":84,"col_start":36,"line_end":84,"col_end":51},"outcome":"proved"
//@[ptr_cast_call] forbid-output: "line_start":84,"col_start":36,"line_end":84,"col_end":51},"outcome":"proved"
//@[nonnull_cast_call] forbid-output: "line_start":84,"col_start":36,"line_end":84,"col_end":51},"outcome":"proved"
//@[raw_parts] forbid-output: "line_start":84,"col_start":36,"line_end":84,"col_end":51},"outcome":"proved"
//@[generic_strip] forbid-output: "line_start":84,"col_start":36,"line_end":84,"col_end":51},"outcome":"proved"
//@[union_parts] forbid-output: "line_start":84,"col_start":36,"line_end":84,"col_end":51},"outcome":"proved"
//@[fat_storage] forbid-output: "line_start":84,"col_start":36,"line_end":84,"col_end":51},"outcome":"proved"
//@[fat_storage_call] forbid-output: "line_start":84,"col_start":36,"line_end":84,"col_end":51},"outcome":"proved"
//@[expose_addr] forbid-output: "line_start":84,"col_start":36,"line_end":84,"col_end":51},"outcome":"proved"
//@[sysroot_erased] forbid-output: "line_start":84,"col_start":36,"line_end":84,"col_end":51},"outcome":"proved"
//! SOUNDNESS REGRESSION (backing certificates, 2026-10-01): every way to recover a
//! `dyn` pointer's data pointer past its vtable is a `dyn` recovery.
//!
//! `Buf`'s certificate makes `get`'s `[unsafe:sep:offset]` row (line 84)
//! PROVED, sound only if no code can write `Buf`'s bytes except through a struct
//! literal the certifier audited. Once `Buf` is erased into a `dyn`, no type names
//! it, so the escape census (`backing_escape_census`, `trust_verify.rs`) denies
//! every struct erased into a `dyn` when ANY body recovers a thin pointer or an
//! address out of one (`Census::finish`). It used to recognize only an `as` cast of
//! a `dyn` pointer to a thin pointer or an integer; each revision below recovers the
//! data pointer another way and writes `Buf`'s length through it. On `origin/main`
//! `93f05556da` every one of them certified `Buf` with that row PROVED (measured on
//! its stage 1, `TRUST_CERT_DEBUG=1`):
//!
//! * `transmute_parts`, `box_transmute_parts`: `&mut dyn Any` / `Box<dyn Any>`
//!   transmuted to a `(data, vtable)` pair of pointers;
//! * `ptr_cast_call`, `nonnull_cast_call`, `raw_parts`, `expose_addr`: the
//!   `core::ptr` API — `<*mut dyn Any>::cast`, `NonNull::<dyn Any>::cast`,
//!   `to_raw_parts`, `expose_provenance` then `with_exposed_provenance_mut`;
//! * `generic_strip`: a local generic `p as *mut usize` for `p: *mut T`,
//!   `T: ?Sized`, instantiated with `dyn Any` (its scan as written sees only `T`);
//! * `union_parts`: a union over the fat pointer and a pointer pair;
//! * `fat_storage`, `fat_storage_call`: the fat pointer's own storage read as a
//!   thin pointer, by an `as` cast or `<*const _>::cast`;
//! * `sysroot_erased`: `Buf` is erased into `Box<dyn Any + Send>` by the SYSROOT
//!   (`std::panic::panic_any`), not by this crate, and comes back through
//!   `catch_unwind`; the census also denies a struct handed to code it does not
//!   scan, which can erase it.
//!
//! `erase_only` erases `Buf` into a `dyn` and recovers nothing: it still certifies,
//! row `proved`.

#![feature(register_tool)]
#![register_tool(trust)]
#![cfg_attr(raw_parts, feature(ptr_metadata))]
#![allow(dead_code, unused_mut, unused_variables)]

use core::any::Any;
use core::ptr::NonNull;

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
#[cfg(transmute_parts)]
pub fn grow(b: &mut Buf) {
    let r: &mut dyn Any = b;
    let (data, _vtable): (*mut usize, *const ()) = unsafe { core::mem::transmute(r) };
    unsafe { *data.add(1) = 1 << 20 }
}

#[cfg(box_transmute_parts)]
pub fn grown(n: usize) -> u8 {
    let b: Box<dyn Any> = Box::new(unsafe { Buf::map(n) });
    let (data, vtable): (*mut usize, *const ()) = unsafe { core::mem::transmute(b) };
    unsafe { *data.add(1) = 1 << 20 };
    let b: Box<dyn Any> = unsafe { core::mem::transmute((data, vtable)) };
    b.downcast_ref::<Buf>().map_or(0, |b| b.get(100))
}

#[cfg(ptr_cast_call)]
pub fn grow(b: &mut Buf) {
    let r: &mut dyn Any = b;
    let p = (r as *mut dyn Any).cast::<usize>();
    unsafe { *p.add(1) = 1 << 20 }
}

#[cfg(nonnull_cast_call)]
pub fn grow(b: &mut Buf) {
    let r: &mut dyn Any = b;
    let p = NonNull::from(r).cast::<usize>();
    unsafe { p.add(1).write(1 << 20) }
}

#[cfg(raw_parts)]
pub fn grow(b: &mut Buf) {
    let r: &mut dyn Any = b;
    let (data, _meta) = (r as *mut dyn Any).to_raw_parts();
    unsafe { *(data as *mut usize).add(1) = 1 << 20 }
}

#[cfg(generic_strip)]
fn strip<T: ?Sized>(p: *mut T) -> *mut usize {
    p as *mut usize
}
#[cfg(generic_strip)]
pub fn grow(b: &mut Buf) {
    let r: &mut dyn Any = b;
    let p = strip(r as *mut dyn Any);
    unsafe { *p.add(1) = 1 << 20 }
}

#[cfg(union_parts)]
pub union Parts {
    fat: *mut dyn Any,
    parts: (*mut usize, *const ()),
}
#[cfg(union_parts)]
pub fn grow(b: &mut Buf) {
    let r: &mut dyn Any = b;
    let u = Parts { fat: r };
    unsafe { *u.parts.0.add(1) = 1 << 20 }
}

#[cfg(fat_storage)]
pub fn grow(b: &mut Buf) {
    let r: &mut dyn Any = b;
    let fat: *mut dyn Any = r;
    let data = unsafe { *(&raw const fat as *const *mut usize) };
    unsafe { *data.add(1) = 1 << 20 }
}

#[cfg(fat_storage_call)]
pub fn grow(b: &mut Buf) {
    let r: &mut dyn Any = b;
    let fat: *mut dyn Any = r;
    let data = unsafe { *(&raw const fat).cast::<*mut usize>() };
    unsafe { *data.add(1) = 1 << 20 }
}

#[cfg(expose_addr)]
pub fn grow(b: &mut Buf) {
    let r: &mut dyn Any = b;
    let a = (r as *mut dyn Any).expose_provenance();
    let p = core::ptr::with_exposed_provenance_mut::<usize>(a);
    unsafe { *p.add(1) = 1 << 20 }
}

#[cfg(sysroot_erased)]
pub struct SendBuf(Buf);
#[cfg(sysroot_erased)]
unsafe impl Send for SendBuf {}
#[cfg(sysroot_erased)]
pub fn grown(n: usize) -> u8 {
    let caught = std::panic::catch_unwind(move || {
        std::panic::panic_any(SendBuf(unsafe { Buf::map(n) }));
    });
    let Err(payload) = caught else { return 0 };
    let p = Box::into_raw(payload);
    unsafe { *(p as *mut usize).add(1) = 1 << 20 };
    let payload = unsafe { Box::from_raw(p) };
    payload.downcast_ref::<SendBuf>().map_or(0, |b| b.0.get(100))
}

#[cfg(erase_only)]
pub fn erase(b: &mut Buf) -> usize {
    let r: &mut dyn Any = b;
    r.downcast_mut::<Buf>().map_or(0, |b| b.get(0) as usize)
}

fn main() {}

//[transmute_parts,box_transmute_parts,ptr_cast_call,nonnull_cast_call,raw_parts]~? RAW established = {}
//[generic_strip,union_parts,fat_storage,fat_storage_call,expose_addr,sysroot_erased]~? RAW established = {}
//[erase_only]~? RAW established = {"backing_cert_dyn_recovery::Buf"}
//[transmute_parts,box_transmute_parts,ptr_cast_call,nonnull_cast_call,raw_parts]~? RAW "line_start":84,"col_start":36,"line_end":84,"col_end":51},"outcome":"failed"
//[generic_strip,union_parts,fat_storage,fat_storage_call,expose_addr,sysroot_erased]~? RAW "line_start":84,"col_start":36,"line_end":84,"col_end":51},"outcome":"failed"
//[erase_only]~? RAW "line_start":84,"col_start":36,"line_end":84,"col_end":51},"outcome":"proved"
//[transmute_parts]~? RAW DENIED: it is erased into a `dyn Trait` and a thin pointer is recovered from it (`&mut dyn Any` to `(*mut usize, *const ())`) in `grow`, which recovers raw byte access to it past the vtable
//[box_transmute_parts]~? RAW DENIED: it is erased into a `dyn Trait` and a thin pointer is recovered from it (`Box<dyn Any>` to `(*mut usize, *const ())`) in `grown`, which recovers raw byte access to it past the vtable
//[ptr_cast_call]~? RAW DENIED: it is erased into a `dyn Trait` and `std::ptr::mut_ptr::<impl *mut T>::cast` returns an address taken from a `dyn` (`*mut usize`) in `grow`, which recovers raw byte access to it past the vtable
//[nonnull_cast_call]~? RAW DENIED: it is erased into a `dyn Trait` and `std::ptr::NonNull::<T>::cast` returns an address taken from a `dyn` (`NonNull<usize>`) in `grow`, which recovers raw byte access to it past the vtable
//[raw_parts]~? RAW DENIED: it is erased into a `dyn Trait` and `std::ptr::mut_ptr::<impl *mut T>::to_raw_parts` returns an address taken from a `dyn` (`(*mut (), DynMetadata<dyn Any>)`) in `grow`, which recovers raw byte access to it past the vtable
//[generic_strip]~? RAW DENIED: it is erased into a `dyn Trait` and a thin pointer is recovered from it (`*mut dyn Any` to `*mut usize`) in `strip instantiated with [dyn [Binder { value: Trait(std::any::Any), bound_vars: [] }] + '{erased}]`, which recovers raw byte access to it past the vtable
//[union_parts]~? RAW DENIED: it is erased into a `dyn Trait` and a union `Parts` over a `dyn` pointer is constructed in `grow`, which recovers raw byte access to it past the vtable
//[fat_storage]~? RAW DENIED: it is erased into a `dyn Trait` and a thin pointer is recovered from it (`*const *mut dyn Any` to `*const *mut usize`) in `grow`, which recovers raw byte access to it past the vtable
//[fat_storage_call]~? RAW DENIED: it is erased into a `dyn Trait` and `std::ptr::const_ptr::<impl *const T>::cast` returns an address taken from a `dyn` (`*const *mut usize`) in `grow`, which recovers raw byte access to it past the vtable
//[expose_addr]~? RAW DENIED: it is erased into a `dyn Trait` and `std::ptr::mut_ptr::<impl *mut T>::expose_provenance` returns an address taken from a `dyn` (`usize`) in `grow`, which recovers raw byte access to it past the vtable
//[sysroot_erased]~? RAW DENIED: it is handed to code the census does not scan, which can erase it into a `dyn Trait`, and a thin pointer is recovered from it (`*mut dyn Any + Send` to `*mut usize`) in `grown`, which recovers raw byte access to it past the vtable
