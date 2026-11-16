//@ needs-trust-verify
//@ aux-build: no_std_to_string_trait_diagnostic_item_impostor_dep.rs
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
//~? RAW fn=typed_self_total_to_string_trait_diagnostic_item_impostor_refuted::victim arm=NONE
//! THE PLANTED REFUTATION FOR S1: the `ToString` arm of
//! `typed_self_total_std_call` (trust_verify.rs), which feeds the
//! zero-obligation gate's `typed-self-total` arm.
//!
//! That arm identified the TRAIT by its diagnostic NAME (`ToString`) plus
//! `!is_local()`. A diagnostic item is a source ATTRIBUTE, and this crate is
//! `#![no_std]` and never loads `alloc`, so the auxiliary crate's
//! `#[rustc_diagnostic_item = "ToString"]` on a trait of its own is uncontested
//! and IS that name; the trait is not local here. Its `impl ToString for str`
//! panics on every call (a `#![no_std]` binary built around this call exits 134
//! at run time — measured). MEASURED on stage-1 `trustc` at `d06cc05bc12`, before
//! the fix, in both lanes below:
//!
//! ```text
//! [PF_ZEROGATE] fn=…::victim arm=typed-self-total callee=<str as …_dep::ToString>::to_string
//! ```
//!
//! The build still failed closed (one runtime-checked row), but ONLY because the
//! bridge's own residency check kept the row: the compiler-side identity layer
//! had already credited the impostor. The fix requires the trait's crate to be
//! the compiler's own resident sysroot crate (`is_real_sysroot_crate`, the R2
//! discipline in `trust-mir-extract/src/convert.rs`).
//!
//! BOTH halves are pinned, per revision:
//!  * `forbid-output` — the gate must never credit this call `typed-self-total`
//!    again (the compiler-side decision; a regression there turns this red even
//!    while the bridge still holds);
//!  * the `RAW` line — the gate DID run on `victim` and declined, so the
//!    `forbid-output` is not satisfied vacuously by a gate that never ran;
//!  * the `ERROR`s — end to end, the call keeps its honest may-panic obligation.
//!
//! IF EITHER REVISION EVER COMPILES CLEAN, or the forbidden line reappears, the
//! trait is being identified by an attribute again. Fix the compiler, not this
//! file.
#![no_std]

extern crate no_std_to_string_trait_diagnostic_item_impostor_dep;

use no_std_to_string_trait_diagnostic_item_impostor_dep::ToString;

pub fn victim(s: &str) -> u8 {
    //~^ ERROR Trust strict verification failed for `typed_self_total_to_string_trait_diagnostic_item_impostor_refuted::victim`
    //[certify]~| ERROR Trust Level 0 safety verification incomplete for `typed_self_total_to_string_trait_diagnostic_item_impostor_refuted::victim`
    s.to_string()
}
