//@ revisions: plain boxed vec_push swap_whole option_read read_through_wrap
//@ revisions: by_value_capture debug_format dyn_shared generic_identity generic_accessor
//@ revisions: foreign_value_args dyn_typed_uses
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
//@ forbid-output: DENIED
//@ forbid-output: backing inventory INCOMPLETE
//! CAPABILITY CONTROLS for the backing-certificate escape census (2026-09-30).
//!
//! The census denies a sealed struct on any raw pointer, transmute, union, foreign
//! or unsafe callee, or generic instantiation that reaches its storage. These
//! revisions use `Buf` in the ordinary safe ways a crate that owns it does — and
//! the MIR those ways lower to (`Box` derefs become a transmute to `*const Buf`,
//! `vec![..]` writes through `MaybeUninit`'s union field, `format!` coerces to
//! `&dyn Debug`, generic helpers are instantiated with `Buf`) — and each must STILL
//! certify, and `get`'s `[unsafe:sep:offset]` row (line 74) must still be PROVED,
//! so the census is not a switch that turns the lane off:
//!
//! * `plain`: the establishing constructor and the reader alone.
//! * `boxed`: `Box<Buf>` and a method call through it (the `ElaborateBoxDerefs`
//!   temporary is only ever dereferenced).
//! * `vec_push`: `Vec<Buf>::push` — a safe sysroot API over `&mut Vec<Buf>`.
//! * `swap_whole`: `mem::swap` of two whole `Buf`s — a safe sysroot API over
//!   `&mut Buf`; each value still satisfies the invariant.
//! * `option_read`: `Option<Buf>::as_mut` and a read through the result.
//! * `read_through_wrap`: a READ of `w.b.len` through `&Wrap`.
//! * `by_value_capture`: a `move` closure that writes its own precise copy of
//!   `b.len` (the upvar is a `usize`; no value of `Buf` changes).
//! * `debug_format`: `#[derive(Debug)]` and `format!("{b:?}")`.
//! * `dyn_shared`: `&Buf` coerced to `&dyn Debug`; the vtable's method is the local,
//!   non-generic `Debug` impl.
//! * `generic_identity` / `generic_accessor`: local generic code instantiated with
//!   `Buf` whose instantiated body does nothing to its storage.
//! * `foreign_value_args`: the constructor's own foreign call, `mmap`, whose
//!   signature does not mention `Buf`.
//! * `dyn_typed_uses`: `Buf` erased into a `dyn Any`, alongside the uses of a `dyn`
//!   that keep it typed — `size_of_val`, `ptr::eq`, `Box::into_raw`/`from_raw`, a
//!   lifetime-extending transmute of `&mut dyn Any`, a `?Sized` generic identity
//!   instantiated with `dyn Any`, and the typed `downcast_mut` back to `Buf`. None
//!   recovers the data pointer at another type (the `dyn`-recovery census,
//!   `backing_cert_dyn_recovery.rs`).

#![feature(register_tool)]
#![register_tool(trust)]
#![allow(dead_code, unused_mut, unused_variables, unused_assignments)]

extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, offset: i64) -> *mut u8;
}

#[trust::backing]
#[cfg_attr(any(debug_format, dyn_shared), derive(Debug))]
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

    pub fn as_slice(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self.ptr, self.len) }
    }
}

pub struct Wrap {
    pub b: Buf,
}

#[cfg(boxed)]
pub fn boxed(n: usize) -> u8 {
    let b = Box::new(unsafe { Buf::map(n) });
    b.get(0)
}

#[cfg(vec_push)]
pub fn many(v: &mut Vec<Buf>, n: usize) -> usize {
    v.push(unsafe { Buf::map(n) });
    v.len()
}

// `slot` is the struct itself, not a field of a wrapper: `certify_backing_invariants`
// reads any `Field(0 | 1)` borrow in a body that mentions `Buf` as a backing-field
// escape, whatever the projection's base type, so `&mut w.b` would deny `Buf` there
// (as would `vec![..]`'s store into `MaybeUninit`'s field 1) before the census runs.
#[cfg(swap_whole)]
pub fn swap_in(slot: &mut Buf, n: usize) -> Buf {
    let mut fresh = unsafe { Buf::map(n) };
    core::mem::swap(slot, &mut fresh);
    fresh
}

#[cfg(option_read)]
pub fn first(o: &mut Option<Buf>) -> u8 {
    o.as_mut().map_or(0, |b| b.get(0))
}

#[cfg(read_through_wrap)]
pub fn len_of(w: &Wrap) -> usize {
    w.b.len
}

#[cfg(by_value_capture)]
pub fn count(mut b: Buf) -> usize {
    let mut f = move || {
        b.len = 5;
        b.len
    };
    f()
}

#[cfg(debug_format)]
pub fn show(b: &Buf) -> String {
    format!("{b:?}")
}

#[cfg(dyn_shared)]
pub fn erase(b: &Buf) -> &dyn core::fmt::Debug {
    b
}

#[cfg(generic_identity)]
fn id<T>(x: T) -> T {
    x
}
#[cfg(generic_identity)]
pub fn pass(b: Buf) -> Buf {
    id(b)
}

#[cfg(generic_accessor)]
pub struct Holder<T>(T);
#[cfg(generic_accessor)]
impl<T> Holder<T> {
    pub fn inner(&self) -> &T {
        &self.0
    }
}
#[cfg(generic_accessor)]
pub fn peek(h: &Holder<Buf>) -> u8 {
    h.inner().get(0)
}

#[cfg(foreign_value_args)]
pub fn mapped(len: usize) -> usize {
    let b = unsafe { Buf::map(len) };
    b.as_slice().len()
}

#[cfg(dyn_typed_uses)]
fn same<T: ?Sized>(x: &mut T) -> &mut T {
    x
}
#[cfg(dyn_typed_uses)]
pub fn dyn_uses(b: &'static mut Buf, other: Box<dyn core::any::Any>) -> usize {
    let n = core::mem::size_of_val::<dyn core::any::Any>(&*other);
    let raw: *mut dyn core::any::Any = Box::into_raw(other);
    let eq = core::ptr::eq(raw as *const dyn core::any::Any, raw) as usize;
    drop(unsafe { Box::from_raw(raw) });
    let r: &mut dyn core::any::Any = b;
    let r = unsafe {
        core::mem::transmute::<&mut dyn core::any::Any, &'static mut dyn core::any::Any>(r)
    };
    let got = same(r).downcast_mut::<Buf>().map_or(0, |b| b.get(0) as usize);
    n + eq + got
}

fn main() {}

//~? RAW established = {"backing_cert_escape_benign_controls::Buf"}
//~? RAW "line_start":74,"col_start":36,"line_end":74,"col_end":51},"outcome":"proved"
