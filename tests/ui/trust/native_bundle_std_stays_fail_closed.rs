//@ needs-trust-verify
//@ revisions: default certify
//@ compile-flags: -Ztrust-verify=on
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[default] check-pass
//@[certify] check-fail
//! UPDATED 2026-09-14 — policy B as ruled, on the default lane. The rule this
//! file guards is unchanged: the foreign-body lane must PROVE or DECLINE, never
//! assume, and none of the callees below has become total. What changed is the
//! DISPOSITION of a declined row under the default policy: `str::find::<char>` is
//! a sysroot routine instantiated at foundational types, so its absent-callee row
//! is a completeness gap with vanilla Rust semantics (std's own defined
//! behaviour, no user code reachable) and the 2026-07-25 ruling says it is
//! REPORTED and the build succeeds — `[assert] runtime-checked`, `0 proved`, a
//! `Level 0 safety verification incomplete` WARNING on `probe_find`. It is not
//! proved, it is not assumed total, and `-Ztrust-policy=certify` (the `certify`
//! revision) still refuses it. So the soundness content of this pin now reads:
//! default = WARN with the row still unproved; certify = ERROR. If `probe_find`
//! ever compiles under `certify`, or the default lane stops emitting the warning
//! while claiming `proved`, some callee here became total without an audited
//! model — read THAT as the soundness regression. (`leading_zeros` and
//! `saturating_sub` were already green on the default lane before this change,
//! through audited intrinsic models; the paragraph below predates them.)
//!
//! The foreign-body lane must PROVE or DECLINE — never assume.
//!
//! This is the guard for `native_trust_ir_monomorphic_foreign_callees`. That
//! lane bundles real std bodies so their callers' panic-freedom obligations are
//! discharged by proof; the standing temptation is to close the remaining gap
//! the cheap way, by declaring the leftover std callees total. A totality model
//! is a promise that a function cannot panic for ANY input, and a wrong entry
//! manufactures false proofs in every crate downstream — strictly worse than
//! leaving the obligation open.
//!
//! So the callees below are the ones the lane deliberately does NOT admit, and
//! each must still be a hard error under the fail-closed default:
//!
//!   * `str::find` bottoms out in pattern machinery and `core::panicking`;
//!   * `u32::leading_zeros` bottoms out in the `ctlz` INTRINSIC — no MIR body
//!     exists to lower, for any input, ever;
//!   * `u32::saturating_sub` bottoms out in `saturating_sub`, likewise an
//!     intrinsic.
//!
//! Intrinsics, drop glue, fn-trait shims and virtual dispatch have no source
//! body, so they are the irreducible floor no amount of body-lowering reaches.
//! Recording them as audited assumptions is a legitimate separate decision; what
//! this test forbids is that decision being made SILENTLY, by widening the
//! bundling lane until "unsupported" quietly starts meaning "assume true".
//!
//! If this fixture ever starts passing, some callee here became total without an
//! audited model behind it — read that as a soundness regression, not progress.

pub fn probe_find(s: &str) -> Option<usize> {
    //[default]~^ WARN Trust Level 0 safety verification incomplete
    //[certify]~^^ ERROR Trust strict verification failed
    s.find('x')
}

pub fn probe_leading_zeros(x: u32) -> u32 {
    x.leading_zeros()
}

pub fn probe_saturating_sub(a: u32, b: u32) -> u32 {
    a.saturating_sub(b)
}

fn main() {}
