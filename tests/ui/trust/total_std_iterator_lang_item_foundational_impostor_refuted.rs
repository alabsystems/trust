//@ needs-trust-verify
//@ aux-build: no_std_lang_item_foundational_impostor_dep.rs
//@ revisions: certify strict
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[strict] compile-flags: -Ztrust-policy=strict
//@ rustc-env:TRUST_PF_MATCH_TRACE=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//@ forbid-output: arm=registry callee=<no_std_lang_item_foundational_impostor_dep::
//@ forbid-output: arm=bridge-total callee=<no_std_lang_item_foundational_impostor_dep::
//~? RAW fn=total_std_iterator_lang_item_foundational_impostor_refuted::victim arm=NONE
//! THE PLANTED REFUTATION FOR S2: `crate_is_authentic_foundational`
//! (trust_verify.rs) deciding core/alloc/std identity by LANG-ITEM OWNERSHIP,
//! here through its `string` disjunct and its `total_std_iterator_ty` consumer.
//!
//! This crate is `#![no_std]` and never loads `alloc`, so the auxiliary crate's
//! `#[lang = "String"]` is uncontested and it OWNS the `String` lang item. The
//! predicate graded it alloc, and `total_std_iterator_ty` then admitted its
//! `slice::Iter` (item name + `slice` module segment inside an "authentic"
//! crate) as a total std iterator — whose `next` panics on every call (a
//! `#![no_std]` binary draining it exits 134 at run time — measured). MEASURED on
//! stage-1 `trustc` at `d06cc05bc12`, before the fix, in both lanes below:
//!
//! ```text
//! [PF_ZEROGATE] fn=…::victim arm=registry callee=<…_dep::slice::Iter as …IntoIterator>::into_iter
//! [PF_ZEROGATE] fn=…::victim arm=registry callee=<…_dep::slice::Iter as …::Iterator>::next
//! ```
//!
//! The build still failed closed (one runtime-checked row), but ONLY because the
//! bridge's own residency check kept the row. The fix conjoins every predicate of
//! the `crate_is_authentic_*` family with artifact residency
//! (`is_real_sysroot_crate`, the R2 discipline), so every one of its consumers
//! inherits it, not just this one.
//!
//! Pinned per revision: the compiler-side credit is forbidden (either credit arm
//! naming the dependency), the gate is shown to have run and declined (`RAW`, so
//! the `forbid-output` is not vacuous), and the drain keeps its may-panic
//! obligation end to end. Fix the compiler, not this file.
#![no_std]

extern crate no_std_lang_item_foundational_impostor_dep;

pub fn victim() {
    //~^ ERROR Trust strict verification failed for `total_std_iterator_lang_item_foundational_impostor_refuted::victim`
    //[certify]~| ERROR Trust Level 0 safety verification incomplete for `total_std_iterator_lang_item_foundational_impostor_refuted::victim`
    let it = no_std_lang_item_foundational_impostor_dep::slice::Iter { n: 3 };
    for _x in it {}
}
