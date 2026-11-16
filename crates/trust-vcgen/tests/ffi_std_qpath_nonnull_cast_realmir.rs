//! Trust (2026-10-25): the FFI lane's two false rows on claude-code-alab's strict gate,
//! end to end through `generate_vcs` on REAL extracted MIR (`-Ztrust-dump=mir:<dir>`,
//! atpkg Trust 15698, `trustc 1.99.0-dev (20565c325 2026-10-19)`), fixtures under
//! `tests/fixtures/vcgen_recognizer_anchor/{ffiqpath,nncast}_*_mir.json`.
//!
//! * FFI-STD-QPATH-1 (`ffi_vcgen::is_extern_call`, pattern 2b): a safe std call whose
//!   std ffi type sits in a qualified-path header or a generic argument
//!   (`<std::ffi::os_str::OsString as core::ops::deref::Deref>::deref`,
//!   `<alloc::vec::Vec<std::ffi::os_str::OsString> as core::clone::Clone>::clone`) was
//!   routed into the FFI lane and failed closed as `unmodeled FFI call: no summary`,
//!   because the std exemption read only `starts_with("std::")`. A callee naming a USER
//!   `ffi` module anywhere keeps its row.
//! * FFI-NONNULL-CAST-1 (`generate::container_len::ffi_nonnull_locals`): a non-null
//!   pointer retyped by `<*const T>::cast` / `<*mut T>::cast` (a CALL in MIR) lost its
//!   non-null fact, so `write(fd, (&raw const byte).cast(), 1)` kept `FFI write:
//!   parameter 1 must be non-null`; and the old scan admitted a local on ANY non-null
//!   write, so a pointer reassigned to null on a path, or overwritten through a `&mut`
//!   alias, discharged the same row.
//!
//! Sources: `qpath.rs` and `nncast.rs`, quoted at each test. The BEFORE column of
//! each assertion was measured on the atpkg compiler's own JSON results for the same
//! sources; the fixtures are that compiler's dumps of those functions.

use trust_types::{Terminator, VcKind, VerifiableFunction};

fn fixture(name: &str) -> VerifiableFunction {
    let path = format!(
        "{}/tests/fixtures/vcgen_recognizer_anchor/{name}_mir.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("the captured MIR fixture must deserialize")
}

/// The `(callee, desc)` of every `FfiBoundaryViolation` row `generate_vcs` emits.
fn ffi_rows(name: &str) -> Vec<(String, String)> {
    let func = fixture(name);
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            trust_vcgen::generate_vcs(&func)
                .into_iter()
                .filter_map(|vc| match vc.kind {
                    VcKind::FfiBoundaryViolation { callee, desc } => Some((callee, desc)),
                    _ => None,
                })
                .collect::<Vec<_>>()
        })
        .expect("spawn generation thread")
        .join()
        .expect("generation thread must not panic")
}

/// The fixture's calls whose rendered callee contains `needle`, with their
/// `is_foreign` flag.
fn calls_containing(name: &str, needle: &str) -> Vec<(String, bool)> {
    fixture(name)
        .body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func, is_foreign, .. } if func.contains(needle) => {
                Some((func.clone(), *is_foreign))
            }
            _ => None,
        })
        .collect()
}

// ── FFI-STD-QPATH-1 ─────────────────────────────────────────────────────────────

/// ```text
/// pub fn std_deref(s: &OsString) -> &OsStr { s }
/// pub fn std_args(v: &Vec<OsString>) -> usize {
///     let w = v.clone(); let mut n = 0usize;
///     for a in w.into_iter() { if a == "--version" { n = 1; } }
///     n
/// }
/// // inside `pub mod my_sys { pub mod ffi { … } }`:
/// impl Tr for std::ffi::OsString { fn m(&self) -> usize { self.len() } }
/// ```
/// BEFORE: `deref` (1 row), `clone`/`into_iter`/`next`/`eq` (4 rows), `deref` (1 row),
/// each `unmodeled FFI call: no summary, cannot prove safe`.
#[test]
fn a_std_ffi_type_in_a_qualified_path_mints_no_ffi_row() {
    for name in ["ffiqpath_std_deref", "ffiqpath_std_args", "ffiqpath_user_ffi_impl_body"] {
        // Positive control on the instrument: the fixture really calls safe std
        // callees whose spelling contains `::ffi::` (so the name fallback is what
        // decides), and none of them is a foreign item.
        let calls = calls_containing(name, "::ffi::");
        assert!(!calls.is_empty(), "{name}: the fixture no longer calls a `::ffi::` callee");
        assert!(calls.iter().all(|(_, foreign)| !foreign), "{name}: a foreign call: {calls:?}");
        assert!(
            calls.iter().any(|(c, _)| c.starts_with('<')),
            "{name}: no qualified path: {calls:?}"
        );
        let rows = ffi_rows(name);
        assert!(rows.is_empty(), "{name}: a safe std call was routed into the FFI lane: {rows:?}");
    }
}

/// ```text
/// pub mod my_sys { pub mod ffi {
///     pub struct Handle(pub i32);
///     pub trait Tr { fn m(&self) -> usize; }
///     pub fn f() -> i32 { 7 }
/// } }
/// impl Convert for Handle { fn convert(&self) -> i32 { self.0 } }
/// pub fn user_free() -> i32 { my_sys::ffi::f() }
/// pub fn user_self(h: &Handle) -> i32 { <Handle as Convert>::convert(h) }
/// pub fn user_trait(s: &OsString) -> usize { <OsString as Tr>::m(s) }
/// pub fn user_in_std_generic(v: Vec<Handle>) -> usize {
///     let mut n = 0usize; for h in v.into_iter() { n = n.wrapping_add(h.0 as usize); } n
/// }
/// ```
/// BEFORE and AFTER: each user `ffi` callee keeps its `unmodeled FFI call` row — the
/// head (`qpath::my_sys::ffi::f`), the qualified `Self` type
/// (`<qpath::my_sys::ffi::Handle as qpath::Convert>::convert`), the trait over a std
/// type (`<std::ffi::os_str::OsString as qpath::my_sys::ffi::Tr>::m`), and a generic
/// argument of a std `Self` (`<alloc::vec::Vec<qpath::my_sys::ffi::Handle> as …>::into_iter`).
#[test]
fn a_user_ffi_module_anywhere_in_the_callee_keeps_its_ffi_row() {
    for (name, callees) in [
        ("ffiqpath_user_free", &["f"][..]),
        ("ffiqpath_user_self", &["convert"][..]),
        ("ffiqpath_user_trait", &["m"][..]),
        ("ffiqpath_user_in_std_generic", &["into_iter", "next"][..]),
    ] {
        let rows = ffi_rows(name);
        for callee in callees {
            assert!(
                rows.iter().any(|(c, d)| c == callee && d.contains("unmodeled FFI call")),
                "{name}: the user ffi callee `{callee}` left the FFI lane: {rows:?}"
            );
        }
    }
}

/// FFI-STD-QPATH-1 review, finding 2 (2026-10-26). A dependency built verify-off whose
/// crate NAME is `std` (here a `#![no_std]` file `std.rs`, passed as
/// `--extern fakestd=libstd.rlib`), with
/// ```text
/// pub mod ffi {
///     unsafe extern "C" { fn write(fd: c_int, buf: *const c_void, n: usize) -> isize; }
///     pub struct Handle(pub i32);
///     impl Clone for Handle { fn clone(&self) -> Self {
///         unsafe { write(1, core::ptr::null(), 1) }; Handle(self.0) } }
/// }
/// ```
/// and the caller (`spoof.rs`; dumps from the stage 1 of `fix/ffi-std-qpath-20261025`,
/// version identity `003c01d50` — the extractor is unchanged by this branch):
/// ```text
/// pub fn fake_qpath(h: &fakestd::ffi::Handle) -> fakestd::ffi::Handle { h.clone() }
/// pub fn fake_generic_in_real_std(v: &Vec<fakestd::ffi::Handle>) -> Vec<fakestd::ffi::Handle> { v.clone() }
/// pub fn real_qpath(s: &OsString) -> OsString { s.clone() }
/// pub fn real_generic(v: &Vec<OsString>) -> Vec<OsString> { v.clone() }
/// ```
/// The forged crate's types render as plain `std::ffi::Handle` inside the qualified
/// header and the generic argument — the extractor stamps only a path's ROOT — and the
/// producer writes the duplicate-crate-name argument fingerprint instead. The first
/// version of the exemption read past it and dropped both FFI rows; a fingerprinted
/// callee now keeps its row. In this graph `std`'s NAME is shared, so the real
/// `OsString` calls are fingerprinted too and also keep it (the decline costs precision
/// only in a graph holding a same-named crate; `a_std_ffi_type_in_a_qualified_path_mints_no_ffi_row`
/// is the ordinary-graph control).
#[test]
fn a_fingerprinted_callee_keeps_its_ffi_row() {
    for name in [
        "ffiqpath_spoofstd_fake_qpath",
        "ffiqpath_spoofstd_fake_generic",
        "ffiqpath_spoofstd_real_qpath",
        "ffiqpath_spoofstd_real_generic",
    ] {
        // Instrument controls: the fixture calls a `::ffi::` callee that is not a
        // foreign item, carries NO root stamp (so the stamp rule is not what decides),
        // and DOES carry the producer's fingerprint.
        let calls = calls_containing(name, "::ffi::");
        assert_eq!(calls.len(), 1, "{name}: {calls:?}");
        let (callee, foreign) = &calls[0];
        assert!(!foreign, "{name}: {callee}");
        assert!(!trust_types::path_has_unauthenticated_crate_stamp(callee), "{name}: {callee}");
        assert!(trust_types::args_display_may_name_a_same_named_crate(callee), "{name}: {callee}");
        let rows = ffi_rows(name);
        assert!(
            // The row names the callee's last `::` segment, which for a tagged
            // callee is the fingerprint group itself.
            rows.iter()
                .any(|(c, d)| callee.ends_with(c.as_str()) && d.contains("unmodeled FFI call")),
            "{name}: a fingerprinted callee read a possibly forged std ffi type and left \
             the FFI lane: {callee} {rows:?}"
        );
    }
}

// ── FFI-NONNULL-CAST-1 ──────────────────────────────────────────────────────────

fn nonnull_rows(name: &str) -> Vec<(String, String)> {
    ffi_rows(name).into_iter().filter(|(_, d)| d.contains("must be non-null")).collect()
}

/// ```text
/// unsafe extern "C" { fn write(fd: c_int, buf: *const c_void, n: usize) -> isize;
///                     fn read(fd: c_int, buf: *mut c_void, n: usize) -> isize; }
/// pub fn cast_call(fd: c_int, byte: u8) -> isize {
///     unsafe { write(fd, (&raw const byte).cast(), 1) } }
/// pub fn read_cast(fd: c_int) -> isize {
///     let mut buf = [0u8; 64]; unsafe { read(fd, buf.as_mut_ptr().cast(), buf.len()) } }
/// pub fn as_cast(fd: c_int, byte: u8) -> isize {
///     unsafe { write(fd, &raw const byte as *const c_void, 1) } }
/// ```
/// BEFORE: `cast_call` and `read_cast` kept `parameter 1 must be non-null`; `as_cast`
/// (the control) had it discharged. AFTER: all three discharged.
#[test]
fn std_ptr_cast_carries_the_nonnull_fact_to_the_ffi_argument() {
    for (name, item) in [("nncast_cast_call", "ConstPtrCast"), ("nncast_read_cast", "MutPtrCast")] {
        // The fixture's retype IS std's keyed `cast` call.
        let func = fixture(name);
        assert!(
            func.body.blocks.iter().any(|b| matches!(&b.terminator,
                Terminator::Call { callee_key: Some(k), .. }
                    if k.sysroot_item.is_some_and(|i| format!("{i:?}") == item))),
            "{name}: no `{item}` call in the fixture"
        );
        let rows = nonnull_rows(name);
        assert!(
            rows.is_empty(),
            "{name}: a non-null pointer lost its fact through `cast`: {rows:?}"
        );
    }
    assert!(nonnull_rows("nncast_as_cast").is_empty(), "the `as` control lost its fact");
    // A reference parameter reborrowed raw (`b as *const u8` lowers to
    // `&raw const (*b)`): discharged before and after, by the reference's validity.
    //   pub fn ref_param(fd: c_int, b: &u8) -> isize {
    //       unsafe { write(fd, b as *const u8 as *const c_void, 1) } }
    assert!(nonnull_rows("nncast_ref_param").is_empty(), "a reference parameter lost its fact");
}

/// ```text
/// pub trait MyCast { fn cast(self) -> *const c_void; }
/// impl MyCast for *const u8 { fn cast(self) -> *const c_void { core::ptr::null() } }
/// pub fn cast_of_param(fd: c_int, p: *const u8) -> isize { unsafe { write(fd, p.cast(), 1) } }
/// pub fn user_cast(fd: c_int, byte: u8) -> isize {
///     unsafe { write(fd, MyCast::cast(&raw const byte), 1) } }
/// pub fn reassigned(fd: c_int, c: bool) -> isize {
///     let x = 0u8; let mut p: *const u8 = &raw const x;
///     if c { p = core::ptr::null(); } unsafe { write(fd, p.cast(), 1) } }
/// pub fn reassigned_as(fd: c_int, c: bool) -> isize {
///     let x = 0u8; let mut p: *const u8 = &raw const x;
///     if c { p = core::ptr::null(); } unsafe { write(fd, p as *const c_void, 1) } }
/// pub fn escaped(fd: c_int) -> isize {
///     let x = 0u8; let mut p: *const u8 = &raw const x; let r = &mut p;
///     *r = core::ptr::null(); unsafe { write(fd, p as *const c_void, 1) } }
/// ```
/// Every one can hand `write` a null pointer. BEFORE: `cast_of_param`, `user_cast` and
/// `reassigned` kept the row; `reassigned_as` and `escaped` had it DISCHARGED (the old
/// scan admitted `p` on its `&raw` write and never looked at the null one). AFTER: all
/// five keep it.
#[test]
fn a_pointer_that_may_be_null_keeps_the_ffi_nonnull_row() {
    for name in [
        "nncast_cast_of_param",
        "nncast_user_cast",
        "nncast_reassigned",
        "nncast_reassigned_as",
        "nncast_escaped",
    ] {
        let rows = nonnull_rows(name);
        assert!(
            rows.iter().any(|(c, _)| c == "write"),
            "{name}: a possibly-null pointer reached `write` with its non-null row discharged"
        );
    }
}
