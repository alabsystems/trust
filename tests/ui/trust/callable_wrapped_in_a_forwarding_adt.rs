//@ revisions: ext_aus ext_aus_strict ext_aus_certify ext_aus_aus_certify ext_box_aus
//@ revisions: ext_box_aus_strict ext_aus_then_certify
//@ revisions: reqfree_aus_certify ensures_aus_certify closure_aus closure_aus_strict
//@ revisions: guarded_closure_aus ext_opaque_aus_certify ext_aus_ref_certify
//@ revisions: reqfree_aus reqfree_aus_strict ensures_aus
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[ext_aus_strict] compile-flags: -Ztrust-policy=strict
//@[ext_aus_certify] compile-flags: -Ztrust-policy=certify
//@[ext_aus_aus_certify] compile-flags: -Ztrust-policy=certify
//@[ext_box_aus_strict] compile-flags: -Ztrust-policy=strict
//@[ext_aus_then_certify] compile-flags: -Ztrust-policy=certify
//@[reqfree_aus_certify] compile-flags: -Ztrust-policy=certify
//@[ensures_aus_certify] compile-flags: -Ztrust-policy=certify
//@[reqfree_aus_strict] compile-flags: -Ztrust-policy=strict
//@[closure_aus_strict] compile-flags: -Ztrust-policy=strict
//@[ext_opaque_aus_certify] compile-flags: -Ztrust-policy=certify
//@[ext_aus_ref_certify] compile-flags: -Ztrust-policy=certify
//@[ext_aus] check-fail
//@[ext_aus_strict] check-fail
//@[ext_aus_certify] check-fail
//@[ext_aus_aus_certify] check-fail
//@[ext_box_aus] check-fail
//@[ext_box_aus_strict] check-fail
//@[ext_aus_then_certify] check-fail
//@[ext_opaque_aus_certify] check-fail
//@[ext_aus_ref_certify] check-fail
//@[reqfree_aus_certify] check-fail
//@[ensures_aus_certify] check-fail
//@[reqfree_aus] check-pass
//@[reqfree_aus_strict] check-pass
//@[ensures_aus] check-pass
//@[closure_aus] check-pass
//@[closure_aus_strict] check-pass
//@[guarded_closure_aus] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A callable handed to std INSIDE a type that forwards `Fn`-family calls to what
//! it wraps — `AssertUnwindSafe<F>`'s `impl FnOnce<()>` — must be asked exactly
//! as the same callable handed bare.
//!
//! `callable_type_arg_is_unresolved` peeled `&`, `&mut` and `Box` only; the type
//! argument `AssertUnwindSafe<fn() -> u32 {trust_probe_boom0}>` is an ADT and
//! fell to `_ => false` ("resolved").
//!
//! BEFORE (stage 1 of origin/main `486460dbe77`, m3, release-like std):
//! `o.unwrap_or_else(AssertUnwindSafe(trust_probe_boom0))`, where
//! `trust_probe_boom0` is a `safe fn` of a local `unsafe extern "Rust"` block
//! whose body is a verify-off `#[no_mangle]` function dividing by zero, built
//! exit 0 under the default policy, `-Ztrust-policy=strict` AND
//! `-Ztrust-policy=certify`; a verify-off `main` calling `p(None)` panicked
//! (exit 101). `ext_box_aus` / `ext_box_aus_strict`
//! (`Box::new(AssertUnwindSafe(..))`) built exit 0 under the default policy and
//! strict and panicked the same way (certify refused them), and
//! `ext_aus_aus_certify` (the wrapper nested) built exit 0 under certify — each of
//! these six revisions fails on that compiler with "ui test did not emit an
//! error". The bare spelling `o.unwrap_or_else(trust_probe_boom0)` was refused on
//! all three. `ext_opaque_aus_certify` (the wrapper returned as an opaque
//! `impl FnOnce`) and `ext_aus_ref_certify` (`AssertUnwindSafe(&item)`) were
//! found by review on the same compiler: each built exit 0 under certify (and
//! default/strict) and panicked at run time. `ext_aus_then_certify` (`bool::then`) was already refused there by
//! another row; it is kept as a pin.
//!
//! AFTER: `forwarded_callables` OPENS a callable ADT of this crate or of the
//! sysroot and asks each of its type arguments in its place, so the extern
//! declaration is asked as `local_fn_item_is_verified_unconditionally` asks it
//! bare (it names no body this crate verifies): refused on every lane.
//!
//! Controls (each measured the same before and after): a requires-free item and
//! an `ensures`-only item wrapped, default and strict; a local closure wrapped,
//! default and strict (certify refuses `unwrap_or_else(AssertUnwindSafe(|| 7))` on
//! main and here, unchanged); a closure that calls a `requires` item with a literal
//! that meets it.
//!
//! Trust (W4 ITER-HOF, 2026-10-02): `reqfree_aus_certify` / `ensures_aus_certify`
//! (the requires-free / `ensures`-only item wrapped, under certify) were check-pass
//! controls and are now REFUSED, exactly as the closure spelling above is. MEASURED
//! on stage 1 of origin/main `a3be88bbde` (`TRUST_VANILLA_DEBUG=1`,
//! `-Ztrust-verify-output=both`): those passes were not proofs. The `unwrap_or_else`
//! callee was `vanilla=false`, `p`'s native lowering did not complete, its ONLY row
//! was a `native-verification-gap` UNKNOWN ("the function was not proved"), the crate
//! summary counted 3 of 4 functions verified, and certify exited 0 with no diagnostic:
//! the "EMPTY bridged inventory" hazard at the top of `docs/KNOWN_HAZARDS.md`. On the
//! W4 stage 1 (`f578bffa9f`, `TRUST_NATIVE_DEBUG=1`) `p`'s lowering completes — W4
//! reads a fn item's `->` as text where the bundle reaches its `FnOnce` shim
//! (`arrow_neutral`) — and `p` carries the surfaced panic-freedom obligation of the
//! closure-consumer arm, the row its closure twin carries: runtime-checked, which
//! certify refuses and default/strict report. The
//! controls' own question (does opening the wrapper refuse a requires-free item?)
//! moved to `reqfree_aus`, `reqfree_aus_strict` and `ensures_aus`, which pass on
//! main and with W4 alike.
//! Companions: `callable_handed_to_std_through_a_reference.rs`,
//! `local_item_naming_no_verified_body_as_value.rs`.

use std::panic::AssertUnwindSafe;

#[cfg(any(
    ext_aus,
    ext_aus_strict,
    ext_aus_certify,
    ext_aus_aus_certify,
    ext_box_aus,
    ext_box_aus_strict,
    ext_aus_then_certify,
    ext_opaque_aus_certify,
    ext_aus_ref_certify
))]
unsafe extern "Rust" {
    safe fn trust_probe_boom0() -> u32;
}

#[cfg(any(ext_aus, ext_aus_strict, ext_aus_certify))]
pub fn p(o: Option<u32>) -> u32 {
    //[ext_aus,ext_aus_strict,ext_aus_certify]~^ ERROR Trust strict verification failed for `callable_wrapped_in_a_forwarding_adt::p`
    o.unwrap_or_else(AssertUnwindSafe(trust_probe_boom0))
}

#[cfg(ext_aus_aus_certify)]
pub fn p(o: Option<u32>) -> u32 {
    //[ext_aus_aus_certify]~^ ERROR Trust strict verification failed for `callable_wrapped_in_a_forwarding_adt::p`
    o.unwrap_or_else(AssertUnwindSafe(AssertUnwindSafe(trust_probe_boom0)))
}

#[cfg(any(ext_box_aus, ext_box_aus_strict))]
pub fn p(o: Option<u32>) -> u32 {
    //[ext_box_aus,ext_box_aus_strict]~^ ERROR Trust strict verification failed for `callable_wrapped_in_a_forwarding_adt::p`
    o.unwrap_or_else(Box::new(AssertUnwindSafe(trust_probe_boom0)))
}

#[cfg(ext_aus_then_certify)]
pub fn p(b: bool) -> Option<u32> {
    //[ext_aus_then_certify]~^ ERROR Trust strict verification failed for `callable_wrapped_in_a_forwarding_adt::p`
    b.then(AssertUnwindSafe(trust_probe_boom0))
}

#[cfg(ext_opaque_aus_certify)]
fn mk() -> impl FnOnce() -> u32 {
    AssertUnwindSafe(trust_probe_boom0)
}
#[cfg(ext_opaque_aus_certify)]
pub fn p(o: Option<u32>) -> u32 {
    //[ext_opaque_aus_certify]~^ ERROR Trust strict verification failed for `callable_wrapped_in_a_forwarding_adt::p`
    o.unwrap_or_else(mk())
}

#[cfg(ext_aus_ref_certify)]
pub fn p(o: Option<u32>) -> u32 {
    //[ext_aus_ref_certify]~^ ERROR Trust strict verification failed for `callable_wrapped_in_a_forwarding_adt::p`
    o.unwrap_or_else(AssertUnwindSafe(&trust_probe_boom0))
}

// ---- controls ----

#[cfg(any(reqfree_aus, reqfree_aus_strict, reqfree_aus_certify))]
pub fn d() -> u32 {
    7
}
#[cfg(any(ensures_aus, ensures_aus_certify))]
pub fn d() -> u32 ensures result == 7 {
    7
}
#[cfg(any(reqfree_aus, reqfree_aus_strict, ensures_aus))]
pub fn p(o: Option<u32>) -> u32 {
    o.unwrap_or_else(AssertUnwindSafe(d))
}
#[cfg(any(reqfree_aus_certify, ensures_aus_certify))]
pub fn p(o: Option<u32>) -> u32 {
    //[reqfree_aus_certify,ensures_aus_certify]~^ ERROR Trust strict verification failed
    o.unwrap_or_else(AssertUnwindSafe(d))
}

#[cfg(any(closure_aus, closure_aus_strict))]
pub fn p(o: Option<u32>) -> u32 {
    o.unwrap_or_else(AssertUnwindSafe(|| 7))
}

#[cfg(guarded_closure_aus)]
pub fn d(x: u32) -> u32 requires x != 0 {
    100 / x
}
#[cfg(guarded_closure_aus)]
pub fn p(o: Option<u32>) -> u32 {
    o.unwrap_or_else(AssertUnwindSafe(|| d(5)))
}
