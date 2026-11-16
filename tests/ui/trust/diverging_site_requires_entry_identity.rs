//@ revisions: default certify memsafe
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: diverging_trait_method_dep.rs
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[memsafe] compile-flags: -Ztrust-policy=memory-safe
//@ check-fail
//@ dont-check-compiler-stderr
//! A core TRAIT method is not a panic entry point, whatever its `Self` is named
//! (DIVERGE-ENTRY-1).
//!
//! DIVERGE-ANCHOR-1 made the diverging-site encoding (`Assert(false)` + a
//! `PanicFreedom` row + `Unreachable`, which REPLACES the absent-callee row and is
//! `runtime_checked`, so accepted, under the default policy) require a callee
//! defined in a real sysroot crate, but kept the panic NAME test on the call's
//! rendering. A call to a core trait method carries the TRAIT's DefId, so its key
//! says `core`, and its rendering carries the user's `Self`:
//! `<dep::panicking::V as core::convert::From<*mut u32>>::from` contains
//! `::panicking::`. Each `v_panicking_*` below reaches a verify-off dependency's
//! segfaulting impl at `x == 5` through `From`, `Default` and core's blanket `Into`;
//! each `v_m_*` is the same call into the identical `dep::m::V`, the control.
//!
//! BEFORE (stage 1 of `4463aeeb6d`, `scratchpad/stage1-w13`, each revision's flags
//! with `--emit=metadata`, 2026-10-04): under default the three `v_panicking_*`
//! victims printed only warnings (their one row `panic freedom ... is reachable`,
//! runtime_checked) and were ACCEPTED; under certify and memory-safe they were
//! refused. Every `v_m_*` control was refused in every revision (an unsupported
//! diverging trait-method call). Linking the default-accepted library and calling
//! `v(5)` from a verify-off `main` exits 139 (SIGSEGV); `v(7)` returns 7.
//!
//! AFTER: the diverging-site encoding needs the extractor's `diverging_entry` stamp on
//! the call's `callee_key`, minted from the callee's DefId alone (a real sysroot
//! crate, NOT a trait item, and the name predicates on the GENERIC-FREE definition
//! path, here `core::convert::From::from`), and the extractor routes on the same
//! function. So every victim takes its control's path. The annotations are what the
//! BEFORE compiler prints for a twin of this file, line for line, whose `panicking`
//! calls are renamed to `m`: exactly the path the fix leaves. Measured on the stage 1
//! of `fe8e01f195` (2026-10-04, `x.py test --stage 1`): every annotation fires in every
//! revision and nothing else is reported; on BEFORE the default and certify revisions
//! mismatch (the victims print the advisory and strict wording, not the unsupported
//! terminator's), and memory-safe matches.

#![allow(unreachable_code, unused_variables)]

extern crate diverging_trait_method_dep as dep;

pub fn v_panicking_from(x: u32) -> u32 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_entry_identity::v_panicking_from`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust full verification failed for `diverging_site_requires_entry_identity::v_panicking_from`: native typed-TrustIr lowering did not complete, so the panic-freedom of an unmodeled construct could not be established
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_entry_identity::v_panicking_from`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_entry_identity::v_panicking_from`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        match dep::panicking::V::from(core::ptr::null_mut()) {}
    }
    x
}

pub fn v_panicking_default(x: u32) -> u32 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_entry_identity::v_panicking_default`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust full verification failed for `diverging_site_requires_entry_identity::v_panicking_default`: native typed-TrustIr lowering did not complete, so the panic-freedom of an unmodeled construct could not be established
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_entry_identity::v_panicking_default`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_entry_identity::v_panicking_default`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        match <dep::panicking::V as Default>::default() {}
    }
    x
}

pub fn v_panicking_into(x: u32) -> u32 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_entry_identity::v_panicking_into`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust full verification failed for `diverging_site_requires_entry_identity::v_panicking_into`: native typed-TrustIr lowering did not complete, so the panic-freedom of an unmodeled construct could not be established
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_entry_identity::v_panicking_into`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_entry_identity::v_panicking_into`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        let v: dep::panicking::V = core::ptr::null_mut::<u32>().into();
        match v {}
    }
    x
}

pub fn v_m_from(x: u32) -> u32 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_entry_identity::v_m_from`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust full verification failed for `diverging_site_requires_entry_identity::v_m_from`: native typed-TrustIr lowering did not complete, so the panic-freedom of an unmodeled construct could not be established
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_entry_identity::v_m_from`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_entry_identity::v_m_from`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        match dep::m::V::from(core::ptr::null_mut()) {}
    }
    x
}

pub fn v_m_default(x: u32) -> u32 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_entry_identity::v_m_default`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust full verification failed for `diverging_site_requires_entry_identity::v_m_default`: native typed-TrustIr lowering did not complete, so the panic-freedom of an unmodeled construct could not be established
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_entry_identity::v_m_default`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_entry_identity::v_m_default`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        match <dep::m::V as Default>::default() {}
    }
    x
}

pub fn v_m_into(x: u32) -> u32 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_entry_identity::v_m_into`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust full verification failed for `diverging_site_requires_entry_identity::v_m_into`: native typed-TrustIr lowering did not complete, so the panic-freedom of an unmodeled construct could not be established
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_entry_identity::v_m_into`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_entry_identity::v_m_into`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        let v: dep::m::V = core::ptr::null_mut::<u32>().into();
        match v {}
    }
    x
}
