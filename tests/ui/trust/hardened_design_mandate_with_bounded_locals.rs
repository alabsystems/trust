//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-profile=unix_hardened --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify -Cpanic=abort
//@[default] check-pass
//@[certify] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! G3 (2026-10-27): a hardened DESIGN MANDATE stays a mandate in a function
//! that has bounded integer or slice locals.
//!
//! A mandate (`Result::ok` discarding an error under `unix_hardened` here) is a
//! `HardenedBoundary` row whose violation formula is the literal `Bool(true)`.
//! The compiler recognises it only by that exact formula: the policy-B
//! tolerance skip, the transport's `design_mandate` bit and
//! `hardened_obligation_is_design_mandate` all test `Formula::Bool(true)`.
//! `augment_vc_with_abstract_state` conjoined the function's interval
//! environment onto every solver VC, so in any function with a bounded local
//! (`int_param`'s `u32`, the `&str`/`&[u8]` slice lengths) the row reached the
//! engines as `(and (>= s__slice_len 0) true)`: trust-mc refuted it, the
//! refutation was demoted to `Unknown`, tolerance was denied (`RowHasNoFallback`)
//! and the function was a compile error. `no_param` (no bounded local, a Top
//! environment) was the only advisory one.
//!
//! Measured before the fix (stage 1 of main `723f9ec299`, these flags): the
//! `default` revision fails with `Trust strict verification failed` for
//! `plain`, `guarded`, `int_param`, `slice_param` and
//! `with_closure::{closure#0}`. After: every function is advisory under the
//! default policy, and `certify`, which requires full discharge
//! (`requires_full_discharge`), still fails every one of them: the exemption
//! keeps a mandate a mandate and never turns it into a proof.
//!
//! Soundness of the exemption (crates/trust-vcgen/src/abstract_interp/discharge.rs):
//! a closed constant mentions no variable, and a reachable environment is a
//! satisfiable conjunction of per-variable bounds, so `And([env, c])` is
//! satisfiable exactly when `c` is `true`. An unreachable environment still
//! conjoins (`And([false, true])`, proved by unreachability). The exemption is
//! for a mandate only (`VcKind::is_hardened_design_mandate`, an L1 profile rule):
//! an L0 unsafe/FFI `Bool(true)` modelling gap keeps its augmentation and is not
//! a mandate anywhere (negative control: `hardened_ffi_gap_is_not_a_design_mandate.rs`).

pub fn plain(s: &str) -> Option<u32> {
    //[default]~^ WARN Trust verification advisory
    //[certify]~^^ ERROR Trust strict verification failed
    s.parse().ok()
}

pub fn with_closure(v: &[&str]) -> Option<u32> {
    let f = |s: &str| s.parse::<u32>().ok();
    //[default]~^ WARN Trust verification advisory
    //[certify]~^^ ERROR Trust strict verification failed
    f(v.first().copied().unwrap_or("0"))
}

pub fn guarded(s: &str) -> Option<u64> {
    //[default]~^ WARN Trust verification advisory
    //[certify]~^^ ERROR Trust strict verification failed
    if s.bytes().all(|b| b.is_ascii_digit()) { s.parse().ok() } else { None }
}

pub fn int_param(x: u32) -> Option<u8> {
    //[default]~^ WARN Trust verification advisory
    //[certify]~^^ ERROR Trust strict verification failed
    u8::try_from(x).ok()
}

pub fn no_param() -> Option<u32> {
    //[default]~^ WARN Trust verification advisory
    //[certify]~^^ ERROR Trust strict verification failed
    "5".parse().ok()
}

pub fn slice_param(v: &[u8]) -> Option<u32> {
    //[default]~^ WARN Trust verification advisory
    //[certify]~^^ ERROR Trust strict verification failed
    core::str::from_utf8(v).ok().and_then(|_| None)
}
