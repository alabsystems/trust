//@ needs-trust-verify
//@ edition: 2024
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//! G1 (2026-10-27): MIR `CastKind::FnPtrToPtr` to a thin raw pointer (the
//! `handler as *const ()` half of the `sighandler_t` idiom) lowers to a cast that every
//! vcgen lane models as an OPAQUE CODE ADDRESS: a fresh value, never identity with the
//! fn pointer, no allocation (`trust_vcgen::is_fn_pointer_to_code_address_cast`). It
//! used to be an `unsupported CastKind::FnPtrToPtr` row on every function that took a
//! handler's address.
//!
//! `code_address` has no obligation left (nothing is reported for it). A read through the
//! code address keeps its separation null / allocation / alignment rows and rustc's
//! `CheckNull` assert row (`read_code_address`, 4 rows). The expose to an integer
//! (`fn as usize`, `PointerExposeProvenance`) stays an opaque scalar, which is a
//! separate disclosure and unchanged.

extern "C" fn handler(_sig: i32) {}

/// The cast alone: proves.
pub fn code_address() -> *const () {
    handler as extern "C" fn(i32) as *const ()
}

/// A read through the code address: refused.
pub fn read_code_address() -> u8 {
    //~^ NOTE Trust verification: 0 proved, 3 failed, 1 unknown, 0 timed out, 0 runtime-checked out of 4 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `fn_ptr_to_ptr_code_address::read_code_address`: 4 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `fn_ptr_to_ptr_code_address::read_code_address`: 4 obligation(s) were not fully verified
    let p = handler as extern "C" fn(i32) as *const u8;
    // SAFETY: deliberately reads code as data (negative control).
    unsafe { *p }
}
