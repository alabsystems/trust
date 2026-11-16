//@ needs-trust-verify
//@ edition: 2021
//@ aux-crate: core=member_tolerance_impostor/core.rs
//@ revisions: strict default
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-bundle-foreign-crate=core
//@[strict] compile-flags: -Ztrust-policy=strict
//@ rustc-env:TRUST_NATIVE_DEBUG=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//@ forbid-output: Trust verification advisory
//@ forbid-output: trust-std-member-runtime-check
//~? RAW refused Assert-bearing member `__trust_crate@
//! CONTROL (refused before and after) for the IDENTITY half of the bundled
//! std-member runtime-checked disposition (2026-09-29): only a member whose
//! RESOLVED body belongs to an AUTHENTIC sysroot crate
//! (`crate_is_authentic_foundational`: lang-item owner AND compiler-resident) may
//! be kept with its refused Assert published as a `runtime_checked` row.
//!
//! This crate is `#![no_core]`; the auxiliary is a whole-`core` impostor
//! (`auxiliary/member_tolerance_impostor/core.rs`, crate name `core`, verify-off,
//! `-Zalways-encode-mir`, passed as `--extern core=` and declared bundlable with
//! `-Ztrust-bundle-foreign-crate=core`) whose `bump` carries an `Overflow(Add)`
//! Assert — the admission lane's `AssertKindOutsideLane` class, exactly the class
//! the disposition keeps for real core. Both of the impostor's bodies ARE bundled
//! (so the refusal is reached, which the `RAW` pin shows), and the bundle is
//! refused, with no advisory and no runtime-checked row (the `forbid-output`s).
//!
//! Why a control: MEASURED on stage-1 `f6773df328e` (origin/main, m3 debug std),
//! the removed string-keyed tolerance also refused it — the member renders as
//! `__trust_crate@<hash>::core::bump`, which its `core::` prefix test did not
//! accept. That protection was an accident of the extractor's disambiguator; the
//! disposition now decides on the body's crate identity, never its spelling.
#![feature(no_core)]
#![no_core]

extern crate core;

pub fn victim(x: u32) -> u32 {
    //~^ ERROR Trust full verification failed for `std_member_tolerance_identity_impostor_refuted::victim`: native typed-TrustIr lowering did not complete
    let y = core::bump(x);
    core::boom(y)
}
