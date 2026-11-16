//@ needs-trust-verify
//@ edition: 2021
//@ revisions: strict_o2 strict_o2_ofc advisory_o2 advisory_o2_ofc vanilla_o2
//@[strict_o2] compile-flags: -Ztrust-verify=on -Copt-level=2
//@[strict_o2_ofc] compile-flags: -Ztrust-verify=on -Copt-level=2 -Coverflow-checks=off
//@[advisory_o2] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Copt-level=2
//@[advisory_o2_ofc] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Copt-level=2 -Coverflow-checks=off
//@[vanilla_o2] compile-flags: -Ztrust-verify=off -Copt-level=2
//@[strict_o2] run-fail
//@[strict_o2_ofc] run-fail
//@[advisory_o2] run-fail
//@[advisory_o2_ofc] run-pass
//@[vanilla_o2] run-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (-O parity, ruling R2, 2026-09-25): IN A VERIFYING SESSION A RELEASE
//! BUILD KEEPS ITS OVERFLOW CHECKS UNLESS THEY ARE TURNED OFF EXPLICITLY.
//!
//! `g` adds through `&i32`, i.e. core's `<&i32 as Add<i32>>::add`, whose
//! `#[rustc_inherit_overflow_checks]` arithmetic takes THIS crate's
//! `-Coverflow-checks`. Policy B accepts that member's internal overflow `Assert`
//! as a runtime-checked completeness gap (`foundational_member_qualified_path.rs`)
//! only because the check is kept in the binary. So `g(&i32::MAX)` must PANIC in
//! every verifying lane that claims it, and may wrap only where the checks were
//! turned off on purpose or nothing is verified.
//!
//! * `strict_o2`: the default policy. Verified (the tolerance applies at `-O` now
//!   that the MIR inliner no longer exposes the add), and the check panics.
//! * `strict_o2_ofc`: strict and certify already canonicalize overflow checks
//!   AND debug assertions ON before the `Session` exists, over an explicit
//!   `-Coverflow-checks=off` too (`rustc_driver_impl::canonicalize_trust_options`,
//!   pre-existing). Still panics.
//! * `advisory_o2`: R2 proper. Advisory does not canonicalize, so before R2 its
//!   `-O` build had `debug_assertions` off and therefore no overflow checks: the
//!   add wrapped. The verifying-session default is now ON.
//! * `advisory_o2_ofc`: an explicit `-Coverflow-checks=off` is honored where no
//!   canonicalization overrides it; advisory claims nothing, so the wrap is not
//!   a false proof.
//! * `vanilla_o2`: the vanilla lane keeps upstream's `debug_assertions` default.
//!
//! Every revision prints nothing on success; a run-pass revision that panicked,
//! or a run-fail revision that returned, fails the test.

#[inline(never)]
fn g(x: &i32) -> i32 {
    x + 1
}

fn main() {
    let v = [i32::MAX];
    let r = g(&v[0]);
    // Reached only when the addition wrapped.
    let _ = r;
}
