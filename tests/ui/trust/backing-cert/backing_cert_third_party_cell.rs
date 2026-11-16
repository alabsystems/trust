//@ revisions: shared cell
//@ aux-build:backing_alias_dep.rs
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ compile-flags: -Ztrust-verify-output=json --error-format=human
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ rustc-env:TRUST_CERT_DEBUG=1
//@ forbid-output: backing inventory INCOMPLETE
//@ forbid-output: established = {"backing_cert_third_party_cell::Buf"}
//! SOUNDNESS (backing lane, round 4 of the `tinv/alab-blockers` review, 2026-10-11):
//! interior mutability below a SHARED reference. `shared`: a third-party
//! `Shared<T>(UnsafeCell<T>)` whose `poke(&self)` overwrites `Buf`; `cell`: a third-party
//! `zap<T>(&Cell<T>)` that writes through `Cell::as_ptr`. The census read `&Shared<Buf>` /
//! `&Cell<Buf>` as read-only, so rule 4 never fired and `Buf` certified. Now `Buf` is
//! denied twice: by CENSUS-THIRD-PARTY-1 (any third-party code denies every certificate),
//! and by rule 4, because a `!Freeze` ADT is writable below a shared reference.
#![feature(register_tool)]
#![register_tool(trust)]
#![allow(dead_code, improper_ctypes)]

extern crate backing_alias_dep;

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
}

#[cfg(shared)]
pub fn poked(n: usize) -> u8 {
    let s = backing_alias_dep::Shared::new(unsafe { Buf::map(n) });
    s.poke();
    s.get().get(0)
}

#[cfg(cell)]
pub fn zapped(n: usize) -> u8 {
    let c = core::cell::Cell::new(unsafe { Buf::map(n) });
    backing_alias_dep::zap(&c);
    c.into_inner().get(0)
}

//[shared]~? RAW DENIED: the crate uses third-party code (the crate graph links `backing_alias_dep`; first use found: `poked` calls the third-party `backing_alias_dep::Shared::<T>::new`)
//[shared]~? RAW DENIED: `backing_alias_dep::Shared::<T>::poke`, from a crate that is neither this crate nor the sysroot, is handed a mutable reference or raw pointer that reaches it in `poked`
//[cell]~? RAW DENIED: the crate uses third-party code (the crate graph links `backing_alias_dep`; first use found: `zapped` calls the third-party `backing_alias_dep::zap`)
//[cell]~? RAW DENIED: `backing_alias_dep::zap`, from a crate that is neither this crate nor the sysroot, is handed a mutable reference or raw pointer that reaches it in `zapped`
//[shared,cell]~? RAW established = {}
