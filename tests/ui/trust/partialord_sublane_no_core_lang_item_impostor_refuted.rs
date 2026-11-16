//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: no_core_partial_ord_impostor_dep.rs
//@ revisions: certify strict
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[strict] compile-flags: -Ztrust-policy=strict
//@ rustc-env:TRUST_PARTIALORD_SUBLANE=1
//@ rustc-env:TRUST_BUNDLE_MEMBERS=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//@ forbid-output: as no_core_partial_ord_impostor_dep::PartialOrd>::lt
//@ forbid-output: as no_core_partial_ord_impostor_dep::Ord>::cmp
//@ forbid-output: as no_core_partial_ord_impostor_dep::Ord>::max
//@ forbid-output: this function has no obligation of its own
//~? RAW [BUNDLE_ROOT] root=partialord_sublane_no_core_lang_item_impostor_refuted::victim_lt members=1
//~? RAW [BUNDLE_ROOT] root=partialord_sublane_no_core_lang_item_impostor_refuted::victim_cmp members=1
//~? RAW [BUNDLE_ROOT] root=partialord_sublane_no_core_lang_item_impostor_refuted::victim_max members=1
//! THE PLANTED REFUTATION for `native_trust_ir_partialord_default_comparator_instances`
//! (trust_verify.rs, the `TRUST_PARTIALORD_SUBLANE` sub-lane) deciding "this is
//! core's `PartialOrd`/`Ord`" from SOURCE-DECLARABLE anchors only: the
//! `partial_ord` lang item and the `Ord` diagnostic item.
//!
//! This crate is `#![no_core]`, so the auxiliary crate's `#[lang = "partial_ord"]`
//! and `#[rustc_diagnostic_item = "Ord"]` are uncontested and it OWNS both. The
//! sub-lane took its default comparators for core's and bundled their bodies
//! into the caller's closure for inline verification (`[BUNDLE_MEMBER] …
//! def_path=<…::L as no_core_partial_ord_impostor_dep::PartialOrd>::lt`, and the
//! `Ord` `cmp`/`max` twins). What it grants is inline verification, not a
//! credit, so no false proof was observed: every bundle was refused for its
//! panicking member. The fix requires the trait's crate to be AUTHENTIC core
//! (`crate_is_authentic_core`: owner of `Sized` AND resident in this compiler's
//! own sysroot, the R2 discipline), so an impostor's comparator is never taken
//! for core's and the call keeps the absent-callee refusal instead.
//!
//! MEASURED: see the commit that adds this file. Pinned per revision: no member
//! of the impostor is bundled (`forbid-output`), the bundle trace is shown to
//! have run (`RAW [BUNDLE_ROOT]`, so the forbid is not vacuous), and each call
//! keeps its may-panic refusal. The honest control is
//! `partialord_sublane_resident_core_keeps_bundling.rs`. Fix the compiler, not
//! this file.
#![feature(no_core)]
#![no_core]

extern crate no_core_partial_ord_impostor_dep;

use no_core_partial_ord_impostor_dep::{Copy, Ord, PartialOrd};

pub struct L(pub u8);
impl PartialOrd for L {
    fn partial_cmp(&self, _o: &L) -> u8 {
        0
    }
}

pub struct M(pub u8);
impl Ord for M {}
impl Copy for M {}

pub fn victim_lt(a: &L, b: &L) -> bool {
    //~^ ERROR Trust strict verification failed for `partialord_sublane_no_core_lang_item_impostor_refuted::victim_lt`
    //[certify]~| ERROR Trust Level 0 safety verification incomplete for `partialord_sublane_no_core_lang_item_impostor_refuted::victim_lt`
    a.lt(b)
}

pub fn victim_cmp(a: &M, b: &M) -> u8 {
    //~^ ERROR Trust strict verification failed for `partialord_sublane_no_core_lang_item_impostor_refuted::victim_cmp`
    //[certify]~| ERROR Trust Level 0 safety verification incomplete for `partialord_sublane_no_core_lang_item_impostor_refuted::victim_cmp`
    a.cmp(b)
}

pub fn victim_max(a: M, b: M) -> M {
    //~^ ERROR Trust strict verification failed for `partialord_sublane_no_core_lang_item_impostor_refuted::victim_max`
    //[certify]~| ERROR Trust Level 0 safety verification incomplete for `partialord_sublane_no_core_lang_item_impostor_refuted::victim_max`
    a.max(b)
}

// ZERO-ROW-GATE (2026-10-10): this rail must refuse for its OWN reason; a refusal by the
// zero-row gate (whose note is forbidden here) would mean the gate under test regressed
// into discharging and the zero-row gate masked it.
