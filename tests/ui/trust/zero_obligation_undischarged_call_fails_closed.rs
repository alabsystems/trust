//~ NOTE "kind":"native-verification-gap","description":"native typed verification did not produce a complete obligation inventory","outcome":"unknown"
//@ revisions: u32_default u32_strict u32_certify u32_ms u32_advisory
//@ revisions: u128_strict u128_certify u128_ms
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json
//@ compile-flags: -Copt-level=0 --crate-type lib
//@[u32_strict] compile-flags: -Ztrust-policy=strict
//@[u32_certify] compile-flags: -Ztrust-policy=certify
//@[u32_ms] compile-flags: -Ztrust-policy=memory-safe
//@[u32_advisory] compile-flags: -Ztrust-policy=advisory
//@[u128_strict] compile-flags: -Ztrust-policy=strict
//@[u128_certify] compile-flags: -Ztrust-policy=certify
//@[u128_ms] compile-flags: -Ztrust-policy=memory-safe
//@[u32_default] check-fail
//@[u32_strict] check-fail
//@[u32_certify] check-fail
//@[u32_ms] check-fail
//@[u32_advisory] check-pass
//@[u128_strict] check-fail
//@[u128_certify] check-fail
//@[u128_ms] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: HELP
//! ZERO-ROW-GATE (docs/DECISION_QUEUE.md; docs/KNOWN_HAZARDS.md "EMPTY bridged
//! inventory"): trustc's EXIT STATUS for a body with zero bridged obligations must
//! agree with the row it publishes.
//!
//! Each body below has no obligation of its own, and its one call is a primitive
//! integer `wrapping_pow`. The native lane lowers it with no panic row (it is total), but no
//! authenticated panic-freedom registry discharges it
//! (`zero_obligation_undischarged_call_funcs` records the body). So the publisher
//! calls the body NOT vacuously clean and publishes one `unknown`
//! `native-verification-gap` row, which `targo trust check` already grades
//! Inconclusive.
//!
//! BEFORE: the first early return of `abort_on_full_verification_failure` asked
//! `native_run_is_vacuously_clean` but not the publisher's `calls_undischarged`, and
//! never read its `published_rows`; memory-safe's zero-row branch asked the same
//! narrower question. So each body published the `unknown` row and trustc exited 0
//! under strict (the default), certify and memory-safe. MEASURED 2026-10-10 on stage
//! 1 of this branch with `RUSTC_LOG=rustc_mir_transform::trust_verify=info`: both
//! bodies log `publisher_vacuously_clean=Some(false) published_unknown=1
//! otherwise_accepted=true`, and `otherwise_accepted` is the pre-fix accept verbatim.
//!
//! AFTER: the gates read the publisher's own verdict
//! (`zero_obligation_native_vacuously_clean`), so the default, strict, certify and
//! memory-safe lanes refuse; advisory still reports and passes. The claim is true (a
//! wrapping power is total); what is missing is a lane that AUTHENTICATES it, and until one
//! does, a fail-closed policy does not exit 0 on an `unknown` row.
//!
//! The shapes first reported for this hole, `i32::wrapping_add` and
//! `u128::wrapping_mul`, no longer reach it on this main: both publish the proved
//! `no_obligations` row (`all_calls_proven=true`, measured the same day), so they are
//! not witnesses here. The control `zero_obligation_vacuous_body_still_passes.rs` pins
//! that a genuinely vacuous body is unaffected.
//!
//! Trust (POISON-EVICTION-FALSE-PROOF-1, 2026-11-12): the witness was `rotate_left`
//! (u32) and `rotate_right` (u128). Their bundled std bodies call the absent
//! intrinsics `core::intrinsics::rotate_left::<u32>` and `rotate_right::<u128>`, so the
//! poison loop used to evict them and the caller's call fell back to the bridge's
//! total-method name list: no row, and this gate refused. The loop no longer evicts a
//! member that a retained call still names, so the rotate caller now publishes the kept
//! body's `[trust-absent-callee-assumption]` row (runtime-checked under the default
//! policy) and is no longer a zero-obligation body;
//! `slice_mutator_fnitem_element.rs#int_rotate` pins that outcome. `wrapping_pow` is the
//! same gate shape with no eviction involved: with `TRUST_MEMBER_PANIC_CENSUS=1` its
//! bundle is the root alone (`members=1`) and no poison pass runs. MEASURED on this
//! branch's stage 1 at `-Copt-level=0`: `wrapping_pow` on u32, u64, i32 and u128 each
//! refuse with this note under the default policy.

#[cfg(any(u32_default, u32_strict, u32_certify, u32_advisory))]
pub fn f(x: u32, n: u32) -> u32 {
    //[u32_default,u32_strict,u32_certify]~^ ERROR Trust strict verification failed for `zero_obligation_undischarged_call_fails_closed::f`
    //[u32_default,u32_strict,u32_certify]~| NOTE this function has no obligation of its own, but it is not vacuously verified
    x.wrapping_pow(n)
}

#[cfg(u32_ms)]
pub fn f(x: u32, n: u32) -> u32 {
    //[u32_ms]~^ ERROR Trust memory-safe verification failed for `zero_obligation_undischarged_call_fails_closed::f`
    //[u32_ms]~| NOTE this function has no obligation of its own, but it is not vacuously verified
    x.wrapping_pow(n)
}

#[cfg(any(u128_strict, u128_certify))]
pub fn g(x: u128, n: u32) -> u128 {
    //[u128_strict,u128_certify]~^ ERROR Trust strict verification failed for `zero_obligation_undischarged_call_fails_closed::g`
    //[u128_strict,u128_certify]~| NOTE this function has no obligation of its own, but it is not vacuously verified
    x.wrapping_pow(n)
}

#[cfg(u128_ms)]
pub fn g(x: u128, n: u32) -> u128 {
    //[u128_ms]~^ ERROR Trust memory-safe verification failed for `zero_obligation_undischarged_call_fails_closed::g`
    //[u128_ms]~| NOTE this function has no obligation of its own, but it is not vacuously verified
    x.wrapping_pow(n)
}

