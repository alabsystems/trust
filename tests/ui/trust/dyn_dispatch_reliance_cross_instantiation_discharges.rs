//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ rustc-env:TRUST_DYN_RELIANCE_PROBE=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW ::call_mut => DISCHARGED
//~? RAW ::call => DISCHARGED
//@ forbid-output: => kept
//! One bundle, two instantiations of the same `Fn`-family trait pedigree: the
//! `std::env` shape (a closure coerced to `dyn Fn(&CStr)`, mirrored here as
//! `&CStr2`) next to the `Once` shape (a `<dyn FnMut(&OnceState)>::call_mut`
//! site, mirrored as `&OnceState2`). Every site must DISCHARGE.
//!
//! Under `DefId`-keyed candidate buckets this exact pair ICEd selection
//! (`SignatureMismatch` in `codegen_select_candidate` — proc-macro2's
//! `build.rs`, any crate mixing an env read with `process::exit`), and after
//! the resolve-time guard stopped the ICE it still VETOED the `FnMut` site:
//! the `dyn Fn(&CStr2)` closure sat first in the shared `FnMut` bucket, its
//! guaranteed-failing resolution short-circuited the case split, and the
//! provable `init` closure was never consulted. Keying `coerced` by the full
//! region-erased instantiation is what this file pins: the `call_mut` site's
//! bucket holds ONLY the `(&OnceState2,)` closure, so its obligation actually
//! discharges — measured on the pre-fix compiler as `::call_mut => kept`
//! (`forbid-output` above) and post-fix as `::call_mut => DISCHARGED`.
//!
//! The by-value pair pins the keying fix alone; the by-reference pair
//! additionally pins the candidate guard's binder handling (a `for<'a>` sig
//! skipped, not erased, declined every reference-taking closure — even the
//! matching one).
//!
//! `detonator` fails verification under BOTH keyings, so this file's
//! `check-fail` status never depends on how much the dyn rule discharges; the
//! probe patterns above carry the whole differential. They are matched against
//! the RAW probe stderr, never against a structured diagnostic (compiletest
//! rejects `error-pattern` on those), and no probe line can appear unless the
//! verifier actually ran — which is what keeps this test non-vacuous.
#![no_std]
#![allow(dead_code)]

/// Mirror of `core::ffi::CStr` in the `getenv` closure's signature.
pub struct CStr2 {
    len: u16,
}

/// Mirror of `std::sync::OnceState` in `Once::call`'s `&mut dyn FnMut` init.
pub struct OnceState2 {
    poisoned: bool,
}

pub fn run_both_by_value() -> u16 {
    let read = |s: CStr2| s.len;
    let f: &dyn Fn(CStr2) -> u16 = &read;
    let n = (*f)(CStr2 { len: 3 });

    let mut ran = 0u16;
    let mut init = |s: OnceState2| {
        ran = ran.wrapping_add(s.poisoned as u16);
    };
    let g: &mut dyn FnMut(OnceState2) = &mut init;
    (*g)(OnceState2 { poisoned: false });
    n.wrapping_add(ran)
}

pub fn run_both_by_ref() -> u16 {
    let read = |s: &CStr2| s.len;
    let f: &dyn Fn(&CStr2) -> u16 = &read;
    let n = (*f)(&CStr2 { len: 3 });

    let mut ran = 0u16;
    let mut init = |s: &OnceState2| {
        ran = ran.wrapping_add(s.poisoned as u16);
    };
    let g: &mut dyn FnMut(&OnceState2) = &mut init;
    (*g)(&OnceState2 { poisoned: false });
    n.wrapping_add(ran)
}

/// A reachable division-by-caller-controlled-zero: fails verification under
/// both the old and new keying, pinning `check-fail` independent of the rule.
pub fn detonator(x: u16) -> u16 {
    255 / x
}
