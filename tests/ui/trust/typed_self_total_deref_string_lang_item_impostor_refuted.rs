//@ needs-trust-verify
//@ aux-build: no_std_string_lang_item_deref_impostor_dep.rs
//@ revisions: certify strict
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[strict] compile-flags: -Ztrust-policy=strict
//@ rustc-env:TRUST_PF_MATCH_TRACE=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//@ forbid-output: arm=typed-self-total
//~? RAW fn=typed_self_total_deref_string_lang_item_impostor_refuted::victim arm=NONE
//! THE PLANTED REFUTATION FOR THE R43 `<String as Deref>::deref` ARM of
//! `typed_self_total_std_call` (trust_verify.rs) — the S1 x S2 cross shape.
//!
//! The trait here is core's REAL `Deref`, so this isolates the `Self` anchor:
//! the arm admitted `Self` when it was `tcx.lang_items().string()` and not
//! local. A lang item is a source ATTRIBUTE, and this crate is `#![no_std]` and
//! never loads `alloc`, so the auxiliary crate's `#[lang = "String"] struct
//! FakeString` is uncontested and IS the `String` lang item; it is not local
//! here. Its `Deref::deref` panics on every call (a `#![no_std]` binary built
//! around this call exits 134 at run time — measured). MEASURED on stage-1
//! `trustc` at `d06cc05bc12`, before the fix, in both lanes below:
//!
//! ```text
//! [PF_ZEROGATE] fn=…::victim arm=typed-self-total callee=<…_dep::FakeString as …::Deref>::deref
//! ```
//!
//! The build still failed closed, but ONLY because the bridge's own residency
//! check kept the row. The fix requires the ADT's crate to be the compiler's own
//! resident sysroot crate (`is_real_sysroot_crate`).
//!
//! Pinned as in `typed_self_total_to_string_trait_diagnostic_item_impostor_refuted.rs`:
//! the compiler-side credit is forbidden, the gate is shown to have run and
//! declined, and the call keeps its may-panic obligation end to end. Fix the
//! compiler, not this file.
#![no_std]

extern crate no_std_string_lang_item_deref_impostor_dep;

use core::ops::Deref;
use no_std_string_lang_item_deref_impostor_dep::FakeString;

pub fn victim(s: &FakeString) -> u8 {
    //~^ ERROR Trust strict verification failed for `typed_self_total_deref_string_lang_item_impostor_refuted::victim`
    //[certify]~| ERROR Trust Level 0 safety verification incomplete for `typed_self_total_deref_string_lang_item_impostor_refuted::victim`
    *s.deref()
}
