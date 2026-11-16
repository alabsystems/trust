//@ needs-trust-verify
//@ edition: 2021
//@ aux-crate: core=typed_arm_impostor/core.rs
//@ revisions: certify strict
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[strict] compile-flags: -Ztrust-policy=strict
//@ rustc-env:TRUST_PF_MATCH_TRACE=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//@ forbid-output: arm=cell-set-typed
//@ forbid-output: arm=moved-value-nodrop
//@ forbid-output: arm=registry
//~? RAW fn=typed_call_arms_core_substitution_impostor_refuted::cell_victim arm=NONE
//~? RAW fn=typed_call_arms_core_substitution_impostor_refuted::unwrap_or_victim arm=NONE
//~? RAW fn=typed_call_arms_core_substitution_impostor_refuted::ok_or_victim arm=NONE
//~? RAW fn=typed_call_arms_core_substitution_impostor_refuted::result_unwrap_or_victim arm=NONE
//~? RAW fn=typed_call_arms_core_substitution_impostor_refuted::result_ok_victim arm=NONE
//~? RAW fn=typed_call_arms_core_substitution_impostor_refuted::into_iter_victim arm=NONE
//! THE PLANTED REFUTATION for three typed call-credit identities in
//! `trust_verify.rs` that decided "this is core's type/trait" from a DIAGNOSTIC
//! ITEM plus `!is_local()` only:
//!
//! * `cell_set_call_payload_needs_no_drop` (`sym::Cell`) -> the zero-obligation
//!   gate's `cell-set-typed` arm;
//! * `moved_value_arg_call_operands_need_no_drop` (`sym::Option`/`sym::Result`)
//!   -> the `moved-value-nodrop` arm of both panic-freedom call gates;
//! * `callee_is_total_std_into_iter` (`sym::IntoIterator`, slice/array receiver)
//!   -> `type_total_std_callees`, spent by the `registry` arm. That arm checked
//!   neither locality nor crate identity.
//!
//! This crate is `#![no_core]`. The auxiliary is a whole-`core` substitute
//! (`auxiliary/typed_arm_impostor/core.rs`, crate name `core`, verify-off,
//! `--extern core=`) that owns all four diagnostic items, and every method called
//! below panics on every call. No real `core` is loaded, so rustc's duplicate
//! checks never fire.
//!
//! MEASURED on stage-1 `trustc` at `978840fe007` (origin/main), without the fix,
//! both revisions: `[PF_ZEROGATE] fn=…::cell_victim arm=cell-set-typed
//! callee=__trust_crate@…::core::cell::Cell::<u32>::set`, `arm=moved-value-nodrop`
//! for `Option::{unwrap_or, ok_or}` and `Result::{unwrap_or, ok}`, and
//! `arm=registry callee=__trust_crate@…::<&[u32] as core::iter::IntoIterator>::into_iter`.
//! Every function still failed closed, but only because an INDEPENDENT layer
//! kept a row: the bridge's own recognizers match a rendered `core::` path and
//! refuse the `__trust_crate@` stamp the extractor puts on a non-resident `core`,
//! so each call kept its absent-callee panic-freedom row, which did not prove
//! (1 runtime-checked row per function). The fix conjoins
//! `crate_is_authentic_core` (lang-item owner AND artifact residency) on the ADT
//! or trait, so the credit itself refuses a non-resident `core`.
//!
//! Pinned per revision: no typed arm credits anything here (`forbid-output`;
//! every call in this crate targets the substitute), the zero-obligation gate is
//! shown to have run and declined for each function (`RAW … arm=NONE`, so the
//! forbids are not vacuous), and every function keeps its refusal. The honest
//! control is `typed_call_arms_resident_core_keeps_credit.rs`. Fix the compiler,
//! not this file.
#![feature(no_core)]
#![no_core]

extern crate core;

use core::cell::Cell;
use core::option::Option;
use core::result::Result;

pub fn cell_victim(c: &Cell<u32>) {
    //~^ ERROR Trust strict verification failed for `typed_call_arms_core_substitution_impostor_refuted::cell_victim`
    //[certify]~| ERROR Trust Level 0 safety verification incomplete for `typed_call_arms_core_substitution_impostor_refuted::cell_victim`
    c.set(1);
}

pub fn unwrap_or_victim(o: Option<u32>) -> u32 {
    //~^ ERROR Trust strict verification failed for `typed_call_arms_core_substitution_impostor_refuted::unwrap_or_victim`
    //[certify]~| ERROR Trust Level 0 safety verification incomplete for `typed_call_arms_core_substitution_impostor_refuted::unwrap_or_victim`
    o.unwrap_or(7)
}

pub fn ok_or_victim(o: Option<u32>) -> Result<u32, u32> {
    //~^ ERROR Trust strict verification failed for `typed_call_arms_core_substitution_impostor_refuted::ok_or_victim`
    //[certify]~| ERROR Trust Level 0 safety verification incomplete for `typed_call_arms_core_substitution_impostor_refuted::ok_or_victim`
    o.ok_or(3)
}

pub fn result_unwrap_or_victim(r: Result<u32, u32>) -> u32 {
    //~^ ERROR Trust strict verification failed for `typed_call_arms_core_substitution_impostor_refuted::result_unwrap_or_victim`
    //[certify]~| ERROR Trust Level 0 safety verification incomplete for `typed_call_arms_core_substitution_impostor_refuted::result_unwrap_or_victim`
    r.unwrap_or(5)
}

pub fn result_ok_victim(r: Result<u32, u32>) -> Option<u32> {
    //~^ ERROR Trust strict verification failed for `typed_call_arms_core_substitution_impostor_refuted::result_ok_victim`
    //[certify]~| ERROR Trust Level 0 safety verification incomplete for `typed_call_arms_core_substitution_impostor_refuted::result_ok_victim`
    r.ok()
}

pub fn into_iter_victim(s: &[u32]) {
    //~^ ERROR Trust strict verification failed for `typed_call_arms_core_substitution_impostor_refuted::into_iter_victim`
    //[certify]~| ERROR Trust Level 0 safety verification incomplete for `typed_call_arms_core_substitution_impostor_refuted::into_iter_victim`
    let _it = core::iter::IntoIterator::into_iter(s);
}
