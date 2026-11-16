//@ revisions: slice_index box_slice shared_slice phantom hash_key collect_generic
//@ revisions: generic_dyn manually_drop md_take get_unchecked unwrap_unchecked
//@ revisions: local_unsafe_impl sysroot_unsafe_impl dep_byval dep_borrow
//@[dep_byval] aux-build:backing_escape_dep.rs
//@[dep_borrow] aux-build:backing_escape_dep.rs
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
//@[slice_index] forbid-output: DENIED
//@[box_slice] forbid-output: DENIED
//@[shared_slice] forbid-output: DENIED
//@[phantom] forbid-output: DENIED
//@[hash_key] forbid-output: DENIED
//@[generic_dyn] forbid-output: DENIED
//@[manually_drop] forbid-output: DENIED
//@[md_take] forbid-output: DENIED
//@[get_unchecked] forbid-output: DENIED
//@[unwrap_unchecked] forbid-output: DENIED
//@[local_unsafe_impl] forbid-output: DENIED
//@[sysroot_unsafe_impl] forbid-output: DENIED
//@ forbid-output: backing inventory INCOMPLETE
//! PRECISION of the backing-certificate escape census (2026-09-30): shapes that
//! reach `Buf` but are NOT escapes, each of which the census must still certify —
//! EXCEPT `collect_generic`, `dep_byval` and `dep_borrow`, given up on 2026-10-11 (see
//! their entries below).
//! `get`'s `[unsafe:sep:offset]` row (line 105) stays PROVED. Every revision here
//! certified on a compiler with no census, was DENIED by the first census, and is
//! restored by a targeted precision fix — none of them can write, forge, or hand
//! out un-inventoried mutable access to `Buf`:
//!
//! * `slice_index` / `box_slice` / `shared_slice`: indexing or a field read on
//!   `&mut [Buf]`, `Box<[Buf]>`, or a shared `&[Buf]`. The MIR builder reads a
//!   slice's length through a `RawPtrKind::FakeForPtrMetadata` pointer that names no
//!   field and the program cannot hold; it is not a raw pointer to `Buf`'s storage.
//! * `phantom`: a typed handle whose only `Buf`-typed part is a
//!   `PhantomData<*const Buf>` variance marker, which holds no pointer.
//! * `hash_key`: a local generic impl whose method has its own parameters
//!   (`Hash::hash<H>`), reached through a sysroot bound. The impl's arguments
//!   (`T = Buf`) are fixed and its body scanned; the method's own parameters,
//!   supplied by the sysroot from types that do not hold `Buf`, stay parametric.
//! * `collect_generic` — NO LONGER CERTIFIED (2026-10-11, the one revision here that is
//!   DENIED; it is pinned so, not dropped). `FromIterator::from_iter<I: IntoIterator>`
//!   holds a local of type `<I as IntoIterator>::IntoIter`: a projection over a generic
//!   parameter. Under CENSUS-PROJECTION-1 (KNOWN_HAZARDS; DECISION_QUEUE TINV-33,
//!   amended 2026-10-11: fail closed on every lane) such a projection reaches EVERY sealed
//!   struct, because it can be a `Buf` that no type argument of any instantiation shows,
//!   and the census cannot rely on every concrete instantiation being scanned. So `Buf`
//!   is denied ("a raw pointer to it is held (`<I as IntoIterator>::IntoIter`)") and
//!   `get`'s line-105 row is no longer proved. What would restore it is precision work,
//!   not a relaxation: scan the CONCRETE instantiation `from_iter::<Map<Range<usize>,
//!   {closure}>>` (where `IntoIter` normalizes to a type that does not reach `Buf`) and
//!   accept the projection only when every instantiation is provably enumerated and
//!   scanned (the per-instantiation scan the census keeps as a refinement).
//! * `generic_dyn`: a `dyn` coercion of a generic type holding `Buf` in a generic
//!   context (`Cont<T>` shown as `dyn Fn`). The vtable's method is a local body the
//!   inventory already scans; the concrete vtable need not be resolved here.
//! * `manually_drop` / `md_take`: `ManuallyDrop::{drop,take}` — parametric unsafe
//!   accessors whose unsafety is a drop-state precondition, not type-punning.
//! * `get_unchecked` / `unwrap_unchecked`: parametric unsafe accessors whose
//!   unsafety is a bounds/`is_some` precondition; under no UB they return a valid
//!   `Buf` or `&mut Buf`, never a forged one.
//! * `local_unsafe_impl` / `sysroot_unsafe_impl`: an `unsafe impl` of a LOCAL or
//!   SYSROOT trait (a marker, `GlobalAlloc` on an mmap arena). The `unsafe` keyword
//!   grants no write access; the impl's own methods are local bodies the inventory
//!   scans.
//! * `dep_byval` / `dep_borrow` — NO LONGER CERTIFIED (2026-10-11, pinned DENIED, not
//!   dropped): `Buf` passed BY VALUE, or by shared `&Buf`, to a third-party crate. The
//!   precise census allowed both (ownership transfer, or a read-only borrow; only `&mut Buf`
//!   was denied). Under CENSUS-THIRD-PARTY-1 (DECISION_QUEUE; KNOWN_HAZARDS
//!   CENSUS-PROJECTION-1 round 4) a crate that calls, implements or stores ANY third-party
//!   code gets no certificate at all: three rounds of review kept finding ways for
//!   third-party code to forge or corrupt a sealed value that the precise rules missed. What
//!   would restore these: a third-party crate verified (or attested) under the same
//!   discipline, so its bodies join the inventory; the precise analysis stays as a refinement
//!   that can only add denials.

#![feature(register_tool)]
#![register_tool(trust)]
#![allow(dead_code, unused_mut, unused_variables, improper_ctypes)]

extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, offset: i64) -> *mut u8;
}

#[trust::backing]
pub struct Buf {
    ptr: *const u8,
    len: usize,
}

impl Buf {
    pub unsafe fn map(len: usize) -> Buf {
        let p = mmap(core::ptr::null_mut(), len, 0, 0, -1, 0);
        Buf { ptr: p as *const u8, len }
    }

    pub fn get(&self, i: usize) -> u8 {
        if i < self.len { unsafe { *self.ptr.add(i) } } else { 0 }
    }

    pub fn size(&self) -> usize {
        self.len
    }
}

#[cfg(slice_index)]
pub fn pick(v: &mut [Buf], i: usize) -> u8 {
    v[i].get(0)
}

#[cfg(box_slice)]
pub struct Pool {
    bufs: Box<[Buf]>,
}
#[cfg(box_slice)]
impl Pool {
    pub fn byte(&self, i: usize) -> u8 {
        self.bufs[i].get(0)
    }
}

#[cfg(shared_slice)]
pub struct View<'a> {
    tag: u8,
    bufs: &'a [Buf],
}
#[cfg(shared_slice)]
impl View<'_> {
    pub fn byte(&self, i: usize) -> u8 {
        self.bufs[i].get(0)
    }
}

#[cfg(phantom)]
pub struct Handle<T> {
    idx: usize,
    _t: core::marker::PhantomData<*const T>,
}
#[cfg(phantom)]
pub struct Store {
    bufs: Vec<Buf>,
}
#[cfg(phantom)]
impl Store {
    pub fn get(&self, h: Handle<Buf>) -> u8 {
        self.bufs.get(h.idx).map_or(0, |b| b.get(0))
    }
}

#[cfg(hash_key)]
use std::collections::HashMap;
#[cfg(hash_key)]
#[derive(PartialEq, Eq, Hash)]
pub struct Key<T>(T);
#[cfg(hash_key)]
impl PartialEq for Buf {
    fn eq(&self, o: &Self) -> bool {
        self.size() == o.size()
    }
}
#[cfg(hash_key)]
impl Eq for Buf {}
#[cfg(hash_key)]
impl core::hash::Hash for Buf {
    fn hash<H: core::hash::Hasher>(&self, h: &mut H) {
        self.size().hash(h)
    }
}
#[cfg(hash_key)]
pub fn index(m: &mut HashMap<Key<Buf>, u32>, n: usize) -> usize {
    m.insert(Key(unsafe { Buf::map(n) }), 1);
    m.len()
}

#[cfg(collect_generic)]
pub struct Bag<T>(Vec<T>);
#[cfg(collect_generic)]
impl<T> FromIterator<T> for Bag<T> {
    fn from_iter<I: IntoIterator<Item = T>>(i: I) -> Self {
        Bag(i.into_iter().collect())
    }
}
#[cfg(collect_generic)]
pub fn bag(n: usize) -> usize {
    let b: Bag<Buf> = (0..n).map(|k| unsafe { Buf::map(k) }).collect();
    b.0.len()
}

#[cfg(generic_dyn)]
pub struct Cont<T> {
    tag: T,
    buf: Buf,
}
#[cfg(generic_dyn)]
impl<T> Cont<T> {
    pub fn hook(&self) -> Box<dyn Fn() -> u8 + '_> {
        Box::new(move || self.buf.get(0))
    }
}
#[cfg(generic_dyn)]
pub fn use_it(c: &Cont<u32>) -> u8 {
    (c.hook())()
}

#[cfg(manually_drop)]
pub struct Owned {
    tag: u8,
    pad: u8,
    b: core::mem::ManuallyDrop<Buf>,
}
#[cfg(manually_drop)]
impl Drop for Owned {
    fn drop(&mut self) {
        unsafe { core::mem::ManuallyDrop::drop(&mut self.b) }
    }
}

#[cfg(md_take)]
pub struct Slot {
    tag: u8,
    pad: u8,
    b: core::mem::ManuallyDrop<Buf>,
}
#[cfg(md_take)]
impl Slot {
    pub fn into_buf(mut self) -> Buf {
        let b = unsafe { core::mem::ManuallyDrop::take(&mut self.b) };
        core::mem::forget(self);
        b
    }
}

#[cfg(get_unchecked)]
pub fn first(v: &mut [Buf]) -> u8 {
    if v.is_empty() { 0 } else { unsafe { v.get_unchecked_mut(0).get(0) } }
}

#[cfg(unwrap_unchecked)]
pub fn first(o: Option<Buf>) -> u8 {
    if o.is_some() { unsafe { o.unwrap_unchecked().get(0) } } else { 0 }
}

#[cfg(local_unsafe_impl)]
/// # Safety: implementors are mmap-backed.
pub unsafe trait Mapped {}
#[cfg(local_unsafe_impl)]
unsafe impl Mapped for Buf {}
#[cfg(local_unsafe_impl)]
pub fn go(b: &Buf) -> u8 {
    b.get(0)
}

#[cfg(sysroot_unsafe_impl)]
use std::alloc::{GlobalAlloc, Layout};
#[cfg(sysroot_unsafe_impl)]
pub struct Arena {
    buf: Buf,
    off: core::sync::atomic::AtomicUsize,
}
#[cfg(sysroot_unsafe_impl)]
unsafe impl GlobalAlloc for Arena {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let _ = self.buf.get(0);
        let _ = l.size();
        core::ptr::null_mut()
    }
    unsafe fn dealloc(&self, _p: *mut u8, _l: Layout) {}
}

#[cfg(any(dep_byval, dep_borrow))]
extern crate backing_escape_dep;

#[cfg(dep_byval)]
pub fn give(n: usize) -> usize {
    backing_escape_dep::consume(unsafe { Buf::map(n) })
}

#[cfg(dep_borrow)]
pub fn look(b: &Buf) -> usize {
    backing_escape_dep::borrow(b)
}

fn main() {}

//[slice_index,box_slice,shared_slice,phantom,hash_key,generic_dyn,manually_drop,md_take,get_unchecked,unwrap_unchecked,local_unsafe_impl,sysroot_unsafe_impl]~? RAW established = {"backing_cert_escape_precision::Buf"}
//[slice_index,box_slice,shared_slice,phantom,hash_key,generic_dyn,manually_drop,md_take,get_unchecked,unwrap_unchecked,local_unsafe_impl,sysroot_unsafe_impl]~? RAW "line_start":105,"col_start":36,"line_end":105,"col_end":51},"outcome":"proved"
// `collect_generic` is GIVEN UP (KNOWN_HAZARDS CENSUS-PROJECTION-1, DECISION_QUEUE TINV-33 amended 2026-10-11):
//[collect_generic]~? RAW DENIED: a raw pointer to it is held (`<I as IntoIterator>::IntoIter`) in `<Bag<T> as std::iter::FromIterator<T>>::from_iter`
//[collect_generic]~? RAW established = {}
//[collect_generic]~? RAW "line_start":105,"col_start":36,"line_end":105,"col_end":51},"outcome":"failed"
// `dep_byval` / `dep_borrow` are GIVEN UP (CENSUS-THIRD-PARTY-1, DECISION_QUEUE 2026-10-11):
//[dep_byval]~? RAW DENIED: the crate uses third-party code (the crate graph links `backing_escape_dep`; first use found: `give` calls the third-party `backing_escape_dep::consume`)
//[dep_borrow]~? RAW DENIED: the crate uses third-party code (the crate graph links `backing_escape_dep`; first use found: `look` calls the third-party `backing_escape_dep::borrow`)
//[dep_byval,dep_borrow]~? RAW established = {}
//[dep_byval,dep_borrow]~? RAW "line_start":105,"col_start":36,"line_end":105,"col_end":51},"outcome":"failed"
