//@ edition: 2021
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! **std-call-summaries P2 negatives: the panic-freedom-only intrinsic stamp is
//! not a name, and it is panic-freedom ONLY.**
//!
//! 1. A NAME is not the stamp. A local function named `maximum_number_nsz_f64`
//!    with the intrinsic's signature that really panics keeps its own panic row,
//!    and so does a caller that reaches it. If either starts verifying, the
//!    extractor has started stamping by name.
//! 2. No value fact. The stamped call's result is a fresh havoc, so a caller's
//!    own arithmetic panics on that result are still CHECKED: an integer
//!    division or remainder by a divisor derived from `maximum_number_nsz_f64`
//!    or `maximumf64` keeps its division-by-zero row (the `nsz` sign of zero
//!    is nondeterministic and no value fact is exported for any entry;
//!    nothing about the value may be assumed).
//!
//! The positive twin is `panic_free_intrinsic_native_total.rs`. The facet half (a
//! facet-gated function calling `maximum_number_nsz_f64` is still refused as
//! nondeterministic) is pinned unit-level, in `trust_types::facet_inference`
//! (`a_panic_free_only_intrinsic_stamp_grants_no_facet`) and `trust_vcgen::facets`
//! (`panic_free_only_intrinsic_stamp_grants_no_facet`): at this level every float
//! local is outside the E6 v1 scalar fragment, so a UI citation is refused for that
//! reason before the callee is ever read (measured on the stage 1 of this change:
//! "local _3 has type Float { width: 64 }, outside the v1 scalar fragment").

#![feature(core_intrinsics)]
#![allow(internal_features)]

pub fn maximum_number_nsz_f64(x: f64, y: f64) -> f64 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    if x == 7.0 {
        panic!("not the core intrinsic");
    }
    if y <= x { y } else { x }
}

pub fn calls_the_lookalike(x: f64, y: f64) -> f64 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    maximum_number_nsz_f64(x, y)
}

pub fn divides_by_the_max(x: f64, y: f64, n: i64) -> i64 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE Trust verification: 0 proved, 2 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2
    n / (std::intrinsics::maximum_number_nsz_f64(x, y) as i64)
}

pub fn remainder_by_the_maximum(x: f64, y: f64, n: i64) -> i64 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE Trust verification: 0 proved, 2 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2
    n % (std::intrinsics::maximumf64(x, y) as i64)
}
