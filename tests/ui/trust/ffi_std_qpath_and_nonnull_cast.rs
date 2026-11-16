//@ needs-trust-verify
//@ edition: 2024
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//@ rustc-env:TRUST_VERIFY_ROW_DIAGNOSTICS=1
//! Two false `hardened_ffi_boundary` rows claude-code-alab's strict gate carried
//! (2026-10-25), on the COMPILER path (the vcgen lane on the same shapes' extracted MIR
//! is `crates/trust-vcgen/tests/ffi_std_qpath_nonnull_cast_realmir.rs`).
//!
//! FFI-STD-QPATH-1. A safe std call whose std ffi type sits in a qualified-path header
//! or a generic argument (`<std::ffi::os_str::OsString as core::ops::deref::Deref>::deref`,
//! `<alloc::vec::Vec<std::ffi::os_str::OsString> as core::clone::Clone>::clone`) went to
//! the FFI lane's no-summary branch (`unmodeled FFI call: no summary, cannot prove
//! safe`), because `ffi_vcgen::is_extern_call` exempted std's ffi namespaces only when
//! the callee string STARTED with `core::`/`std::`/`alloc::`. A user `ffi` module
//! anywhere in the callee keeps the row (`user_*` below).
//!
//! FFI-NONNULL-CAST-1. `<*const T>::cast` / `<*mut T>::cast` is a CALL in MIR, and
//! `container_len::ffi_nonnull_locals` never derived its destination, so
//! `write(fd, (&raw const byte).cast(), 1)` kept `parameter 1 must be non-null` while
//! its `as *const c_void` twin was discharged. The same scan admitted a local on ANY
//! non-null write: a pointer reassigned to null on a path (`reassigned_as`) or through a
//! `&mut` alias (`escaped`) had the row discharged. Both are fixed: the cast hop is keyed
//! on std's `ConstPtrCast`/`MutPtrCast`/… tags, and a local is non-null only when every
//! value it can hold is.
//!
//! Measured 2026-10-26 on the stage 1 of `fix/ffi-std-qpath-20261025` (version identity
//! `003c01d50`), with the header's flags plus `-Zui-testing -Zdeduplicate-diagnostics=no
//! -A unused --emit=metadata`: every annotation below fires and nothing else is reported.
//! The same file on atpkg Trust 15698 (`trustc 20565c325`) has `TRUST_JSON` rows (with
//! `-Ztrust-verify-output=both`) that differ from the stage 1's in the FFI rows ONLY.
//! The `unmodeled FFI call` rows for `deref` (on `m` and `std_deref`) and for
//! `clone`/`into_iter`/`next`/`eq` (on `std_args`) are present there. So is the non-null
//! row on `cast_call`/`read_cast`. The non-null row on `reassigned_as`/`escaped` is
//! absent there. So that compiler fails this file in both directions. `m`, `std_deref`
//! and `std_args` get a Level 0 ERROR (2, 2 and 5 obligations) where a warning (1) is
//! annotated. `cast_call`/`read_cast` report 3 where 2 is annotated, and
//! `reassigned_as`/`escaped` report 2 where 3 is. Every other function is unchanged:
//! the `user_*` controls keep their `unmodeled FFI call` row, and `cast_of_param`,
//! `user_cast` and `reassigned` keep their non-null row.
//!
//! Runs with `TRUST_NO_SYSROOT_CENSUS=1`: the counts are the FFI lane's, and the sysroot
//! panic census only removes proof from them.
//!
//! G3-MANDATE-L1-ONLY-1 (2026-10-27): the `user_*` controls' strict gate is an ERROR,
//! not the advisory WARN measured above. Their `unmodeled FFI call` row is an L0
//! `ffi_boundary` modelling gap whose violation is the literal `Bool(true)`, and the
//! compiler used to call any hardened `Bool(true)` row a design mandate and skip it in
//! the default policy's tolerance, in a function with no bounded local only (every
//! other function here, with a bounded local, already got the ERROR). A mandate is now
//! an L1 profile rule only (`VcKind::is_hardened_design_mandate`); the row counts are
//! unchanged.
//!
//! FFI-BUFFER-CAPACITY-1 additionally requires a live byte extent for a positive
//! byte count. A known fixed extent discharges that demand; an unknown pointer
//! or an escaped/reassigned owner retains it, alongside the non-null demand.
//! The strict header takes the larger independently authenticated legacy/native
//! gap inventory. Native pre-bridge gaps can include a row the legacy kernel
//! discharged, so that header can exceed the Level 0 gap count. The annotations
//! below retain the exact normal stage-1 93019b431 diagnostic counts, including
//! all newly emitted capacity coverage. Final public rows are retained as
//! diagnostics as well; no missing native credit is promoted by this fixture.

use core::ffi::{c_int, c_void};
use std::ffi::{OsStr, OsString};

unsafe extern "C" {
    fn write(fd: c_int, buf: *const c_void, n: usize) -> isize;
    fn read(fd: c_int, buf: *mut c_void, n: usize) -> isize;
}

pub mod my_sys {
    pub mod ffi {
        pub struct Handle(pub i32);
        pub trait Tr {
            fn m(&self) -> usize;
        }
        impl Tr for std::ffi::OsString {
            // `self.len()` derefs to `OsStr`: a std qualified-path call inside a USER
            // `ffi` module, whose own path does not route its callees.
            fn m(&self) -> usize {
                //~^ WARN Trust Level 0 safety verification incomplete for `<std::ffi::os_str::OsString as ffi_std_qpath_and_nonnull_cast::my_sys::ffi::Tr>::m`: 1 obligation(s) were not proved
                //~^^ WARN Trust verification advisory for `<std::ffi::os_str::OsString as ffi_std_qpath_and_nonnull_cast::my_sys::ffi::Tr>::m`: 1 obligation(s) were not fully verified
                self.len()
            }
        }
        pub fn f() -> i32 {
            7
        }
    }
}
use my_sys::ffi::{Handle, Tr};

pub trait Convert {
    fn convert(&self) -> i32;
}
impl Convert for Handle {
    fn convert(&self) -> i32 {
        self.0
    }
}

pub trait MyCast {
    fn cast(self) -> *const c_void;
}
impl MyCast for *const u8 {
    fn cast(self) -> *const c_void {
        core::ptr::null()
    }
}

// ── FFI-STD-QPATH-1: std callees, no FFI row after the fix ─────────────────────────

/// `<std::ffi::os_str::OsString as core::ops::deref::Deref>::deref`.
pub fn std_deref(s: &OsString) -> &OsStr {
    //~^ WARN Trust Level 0 safety verification incomplete for `ffi_std_qpath_and_nonnull_cast::std_deref`: 1 obligation(s) were not proved
    //~^^ WARN Trust verification advisory for `ffi_std_qpath_and_nonnull_cast::std_deref`: 1 obligation(s) were not fully verified
    s
}

/// `<Vec<OsString> as Clone>::clone`, `<Vec<OsString> as IntoIterator>::into_iter`,
/// `<IntoIter<OsString> as Iterator>::next`, `<OsString as PartialEq<&str>>::eq`.
pub fn std_args(v: &Vec<OsString>) -> usize {
    //~^ WARN Trust Level 0 safety verification incomplete for `ffi_std_qpath_and_nonnull_cast::std_args`: 1 obligation(s) were not proved
    //~^^ WARN Trust verification advisory for `ffi_std_qpath_and_nonnull_cast::std_args`: 1 obligation(s) were not fully verified
    let w = v.clone();
    let mut n = 0usize;
    for a in w.into_iter() {
        if a == "--version" {
            n = 1;
        }
    }
    n
}

// ── FFI-STD-QPATH-1: user `ffi` callees keep their row ─────────────────────────────

/// The head: `…::my_sys::ffi::f`.
pub fn user_free() -> i32 {
    //~^ ERROR Trust Level 0 safety verification incomplete for `ffi_std_qpath_and_nonnull_cast::user_free`: 1 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_and_nonnull_cast::user_free`: 1 obligation(s) were not fully verified
    my_sys::ffi::f()
}

/// The qualified `Self` type: `<…::my_sys::ffi::Handle as …::Convert>::convert`.
pub fn user_self(h: &Handle) -> i32 {
    //~^ ERROR Trust Level 0 safety verification incomplete for `ffi_std_qpath_and_nonnull_cast::user_self`: 1 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_and_nonnull_cast::user_self`: 1 obligation(s) were not fully verified
    <Handle as Convert>::convert(h)
}

/// A user `ffi` trait over a std type: `<std::ffi::os_str::OsString as …::my_sys::ffi::Tr>::m`.
pub fn user_trait(s: &OsString) -> usize {
    //~^ ERROR Trust Level 0 safety verification incomplete for `ffi_std_qpath_and_nonnull_cast::user_trait`: 2 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_and_nonnull_cast::user_trait`: 2 obligation(s) were not fully verified
    <OsString as Tr>::m(s)
}

/// A generic argument of a std `Self`: `<alloc::vec::Vec<…::my_sys::ffi::Handle> as …>::into_iter`.
pub fn user_in_std_generic(v: Vec<Handle>) -> usize {
    //~^ ERROR Trust Level 0 safety verification incomplete for `ffi_std_qpath_and_nonnull_cast::user_in_std_generic`: 3 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_and_nonnull_cast::user_in_std_generic`: 3 obligation(s) were not fully verified
    let mut n = 0usize;
    for h in v.into_iter() {
        n = n.wrapping_add(h.0 as usize);
    }
    n
}

// ── FFI-NONNULL-CAST-1: std `cast` carries the fact ────────────────────────────────

/// claude-code-alab `on_signal`: a raw borrow, retyped by `<*const T>::cast`.
pub fn cast_call(fd: c_int, byte: u8) -> isize {
    //~^ ERROR Trust Level 0 safety verification incomplete for `ffi_std_qpath_and_nonnull_cast::cast_call`: 2 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_and_nonnull_cast::cast_call`: 3 obligation(s) were not fully verified
    unsafe { write(fd, (&raw const byte).cast(), 1) }
}

/// claude-code-alab `SignalPipe::wait`: a std `as_mut_ptr`, retyped by `<*mut T>::cast`.
pub fn read_cast(fd: c_int) -> isize {
    //~^ ERROR Trust Level 0 safety verification incomplete for `ffi_std_qpath_and_nonnull_cast::read_cast`: 2 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_and_nonnull_cast::read_cast`: 3 obligation(s) were not fully verified
    let mut buf = [0u8; 64];
    unsafe { read(fd, buf.as_mut_ptr().cast(), buf.len()) }
}

/// The `as` twin of `cast_call`: discharged before and after.
pub fn as_cast(fd: c_int, byte: u8) -> isize {
    //~^ ERROR Trust Level 0 safety verification incomplete for `ffi_std_qpath_and_nonnull_cast::as_cast`: 1 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_and_nonnull_cast::as_cast`: 2 obligation(s) were not fully verified
    unsafe { write(fd, &raw const byte as *const c_void, 1) }
}

// ── FFI-NONNULL-CAST-1: a pointer that may be null keeps its row ───────────────────

/// `.cast()` of a pointer that may be null.
pub fn cast_of_param(fd: c_int, p: *const u8) -> isize {
    //~^ ERROR Trust Level 0 safety verification incomplete for `ffi_std_qpath_and_nonnull_cast::cast_of_param`: 4 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_and_nonnull_cast::cast_of_param`: 4 obligation(s) were not fully verified
    unsafe { write(fd, p.cast(), 1) }
}

/// A USER method named `cast` (it returns null) over a non-null receiver.
pub fn user_cast(fd: c_int, byte: u8) -> isize {
    //~^ ERROR Trust Level 0 safety verification incomplete for `ffi_std_qpath_and_nonnull_cast::user_cast`: 4 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_and_nonnull_cast::user_cast`: 4 obligation(s) were not fully verified
    unsafe { write(fd, MyCast::cast(&raw const byte), 1) }
}

/// Reassigned to null on a path, then retyped by std's `cast`.
pub fn reassigned(fd: c_int, c: bool) -> isize {
    //~^ ERROR Trust Level 0 safety verification incomplete for `ffi_std_qpath_and_nonnull_cast::reassigned`: 5 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_and_nonnull_cast::reassigned`: 5 obligation(s) were not fully verified
    let x = 0u8;
    let mut p: *const u8 = &raw const x;
    if c {
        p = core::ptr::null();
    }
    unsafe { write(fd, p.cast(), 1) }
}

/// Reassigned to null on a path, `as` spelling: DISCHARGED before the fix.
pub fn reassigned_as(fd: c_int, c: bool) -> isize {
    //~^ ERROR Trust Level 0 safety verification incomplete for `ffi_std_qpath_and_nonnull_cast::reassigned_as`: 4 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_and_nonnull_cast::reassigned_as`: 4 obligation(s) were not fully verified
    let x = 0u8;
    let mut p: *const u8 = &raw const x;
    if c {
        p = core::ptr::null();
    }
    unsafe { write(fd, p as *const c_void, 1) }
}

/// Overwritten with null through a `&mut` alias: DISCHARGED before the fix.
pub fn escaped(fd: c_int) -> isize {
    //~^ ERROR Trust Level 0 safety verification incomplete for `ffi_std_qpath_and_nonnull_cast::escaped`: 4 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_and_nonnull_cast::escaped`: 4 obligation(s) were not fully verified
    let x = 0u8;
    let mut p: *const u8 = &raw const x;
    let r = &mut p;
    *r = core::ptr::null();
    unsafe { write(fd, p as *const c_void, 1) }
}
