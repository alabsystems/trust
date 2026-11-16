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
//@ forbid-output: established = {"backing_cert_third_party_alias::Buf"}
//! SOUNDNESS (backing lane, final review of `tinv/alab-blockers`, 2026-10-11): a
//! THIRD-PARTY `Alias<T>(*mut T)` takes a `Buf` by `Box`, then `poke(&self)` overwrites
//! `Buf`'s pointer and length through its raw pointer, and `get(&self)` reads it back.
//! Before the fix the census read every foreign ADT's `*mut T` field as a `T` held by
//! value (a precision rule meant for sysroot `Vec`/`Box`), so `Alias<Buf>` was an owned
//! `Buf` behind a shared `&`: rule 4 (third-party `&mut`/raw path) never fired and `Buf`
//! certified while `poke` could rewrite it. Now only an artifact-authenticated sysroot ADT
//! gets that reading, and `Buf` is DENIED. The TINV lane's twin is the `alias_poke`
//! revision of `tests/ui/trust/tinv/tinv_census_projection.rs`.
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

pub fn poked(n: usize) -> u8 {
    let a = backing_alias_dep::Alias::from_box(Box::new(unsafe { Buf::map(n) }));
    a.poke();
    a.get().get(0)
}

//~? RAW DENIED: `backing_alias_dep::Alias::<T>::poke`, from a crate that is neither this crate nor the sysroot, is handed a mutable reference or raw pointer that reaches it in `poked`
//~? RAW DENIED: a raw pointer to it is held (`Alias<Buf>`) in `poked`
//~? RAW established = {}
