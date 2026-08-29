//! Trust: `#[trust::invariant(..)]` is refused with verification OFF too.
//!
//! THIS IS THE HALF THAT WAS ALMOST MISSED, and it is the more important half.
//!
//! The compiler-side refusal (`ExpandTrustInvariant`, pinned by
//! `trust-spec-invariant-refused.rs`) is installed by the resolver's
//! spec-contract hook, and that hook returns early unless
//! `Session::trust_verification_enabled()`. So it covers `-Z trust-verify=on`
//! and NOTHING ELSE. MEASURED while building this lane: compiletest runs the
//! whole `ui` suite with `-Z trust-verify=off`, and with only the compiler-side
//! refusal in place a bare `#[trust::invariant(x > 0)]` still compiled clean
//! with exit status 0 — the erasure was fully intact in every vanilla build.
//!
//! That is why `trust-spec`'s `invariant` is a `compile_error!` rather than a
//! passthrough. `requires` and `ensures` can safely stay passthroughs in this
//! mode because they have a real meaning that IS checked when verification is
//! on; `invariant` has no verified meaning on any lane, so a mode in which it is
//! silently accepted is a mode in which a guarantee-shaped annotation means
//! nothing.
//!
//! THE PROPERTY THIS FILE STATES: whether the annotation is refused must not
//! depend on a build-mode flag. A developer who only ever runs vanilla builds
//! must not be able to accumulate `invariant` annotations that a later
//! verification run would reject wholesale.
//@ compile-flags: -Z trust-verify=off
//@ proc-macro: trust.rs
//@ edition: 2021

#![allow(dead_code)]

#[trust::invariant(x > 0)]
//~^ ERROR `trust::invariant` is not a verified contract surface
fn annotated_fn(x: i32) -> i32 {
    x + 1
}

#[trust::invariant(self.value >= 0)]
//~^ ERROR `trust::invariant` is not a verified contract surface
struct Counter {
    value: i32,
}

// `requires`/`ensures` MUST still pass through untouched in this mode — that is
// the entire purpose of the compatibility shim, and the refusal above must not
// have collateral. If this stops compiling, the refusal over-reached.
#[trust::requires(x > 0)]
#[trust::ensures(move |r: &i32| *r > 0)]
fn still_supported(x: i32) -> i32 {
    x
}

fn main() {}
