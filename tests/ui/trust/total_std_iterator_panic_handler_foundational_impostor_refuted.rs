//@ needs-trust-verify
//@ aux-build: no_std_panic_handler_foundational_impostor_dep.rs
//@ revisions: certify strict
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[strict] compile-flags: -Ztrust-policy=strict
//@ rustc-env:TRUST_PF_MATCH_TRACE=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//@ forbid-output: arm=registry callee=<no_std_panic_handler_foundational_impostor_dep::
//@ forbid-output: arm=bridge-total callee=<no_std_panic_handler_foundational_impostor_dep::
//~? RAW fn=total_std_iterator_panic_handler_foundational_impostor_refuted::victim arm=NONE
//! THE PLANTED REFUTATION FOR S3: the `panic_impl` arm of
//! `crate_is_authentic_std`, and through it `crate_is_authentic_foundational`
//! (trust_verify.rs), measured IN ISOLATION.
//!
//! The auxiliary crate declares NO `#[lang]` attribute and enables no feature;
//! its only sysroot-shaped anchor is the `#[panic_handler]` every `#![no_std]`
//! binary needs some crate to provide. That attribute IS the `panic_impl` lang
//! item, and in a graph that never loads `std` its owner is the crate that
//! declares it, so the predicate graded the dependency `std` and
//! `total_std_iterator_ty` admitted its panicking `slice::Iter` (a `#![no_std]`
//! binary draining it exits 134 at run time — measured). MEASURED on stage-1
//! `trustc` at `d06cc05bc12`, before the fix, in both lanes below:
//!
//! ```text
//! [PF_ZEROGATE] fn=…::victim arm=registry callee=<…_dep::slice::Iter as …IntoIterator>::into_iter
//! [PF_ZEROGATE] fn=…::victim arm=registry callee=<…_dep::slice::Iter as …::Iterator>::next
//! ```
//!
//! Only the bridge's own residency check kept the row. The fix makes residency
//! (`is_real_sysroot_crate`) the identity and leaves `panic_impl` ownership only
//! to say WHICH sysroot crate an already-resident crate is. The same conjunct
//! also denies the grade to a LOCAL crate that supplies the handler (it can
//! authenticate only under the command-line sysroot-build declaration).
//!
//! Pinned per revision as in
//! `total_std_iterator_lang_item_foundational_impostor_refuted.rs`. Fix the
//! compiler, not this file.
#![no_std]

extern crate no_std_panic_handler_foundational_impostor_dep;

pub fn victim() {
    //~^ ERROR Trust strict verification failed for `total_std_iterator_panic_handler_foundational_impostor_refuted::victim`
    //[certify]~| ERROR Trust Level 0 safety verification incomplete for `total_std_iterator_panic_handler_foundational_impostor_refuted::victim`
    let it = no_std_panic_handler_foundational_impostor_dep::slice::Iter { n: 3 };
    for _x in it {}
}
