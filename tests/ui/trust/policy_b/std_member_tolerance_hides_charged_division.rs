//@ needs-trust-verify
//@ revisions: strict default certify nocount
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@ compile-flags: -Copt-level=0 --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@[nocount] compile-flags: -Ztrust-policy=strict
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ regex-error-pattern: "typed_kind":"DivisionByZero","description":"division by zero","location":\{[^{}]*\},"outcome":"failed"
//@ check-fail
//! REFUTED 2026-09-29 — the exit-code proof for the bundled std-member
//! runtime-checked disposition (`trust_verify/runtime_checked_std_member.rs`).
//!
//! `v.iter().filter(..).count()` bundles core's `<usize as Sum>::sum::{closure#0}`,
//! whose `count + 1` is an `#[rustc_inherit_overflow_checks]` `Overflow(Add)`
//! Assert — present with a release std and with a std built with debug
//! assertions. The admission lane refuses it (`AssertKindOutsideLane`). Before
//! this change that refusal DISCARDED THE WHOLE BUNDLE, including the caller-side
//! `d != 0` charge that `c.wrapping_div(d)` owes, and the policy-B
//! lowering-failure tolerance then called the count's Assert the only
//! undischarged obligation: strict and default built exit 0, the crate summary
//! read `functions_verified` 2 of 2, and a verify-off `main` calling
//! `p(Tag::A, &[1, 2, 3], 7, 0)` panicked "attempt to divide by zero" (exit 101).
//! MEASURED on stage-1 `trustc` at `f6773df328e` (origin/main), both with m3's
//! debug std and with a release-like std (`debug-assertions-std = false`,
//! `overflow-checks-std = false`).
//!
//! The bundle is now KEPT (the count closure's Assert is published as a
//! `runtime_checked` row), so the division's charge survives and `p` is refused
//! with exactly the error the `nocount` revision — the same function without
//! `count()`, which never lost its bundle — already gives. `certify` also names
//! the runtime-checked member. `nocount` is the control: check-fail before and
//! after.
pub enum Tag {
    A,
    B,
}

#[cfg(not(nocount))]
pub fn p(t: Tag, v: &[u32; 3], c: u32, d: u32) -> u32 {
    let k = v.iter().filter(|x| **x > 1).count();
    let b = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    if k == 7 {
        return b;
    }
    c.wrapping_div(d)
}

#[cfg(nocount)]
pub fn p(t: Tag, c: u32, d: u32) -> u32 {
    let b = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    if b == 7 {
        return b;
    }
    c.wrapping_div(d)
}

// Re-pinned 2026-10-15 (the merge of 2026-10-14): the counted panic-freedom aggregate now
// carries the bundled member's Assert as a second unproved row (`runtime_checked`) beside
// the division's FAILED charge, so every revision counts 2, and no member is recorded under
// the runtime-checked disposition (certify's named line is gone). The refusal this file
// exists for is the division's charge, and it is pinned directly.
//~? RAW error: Trust strict verification failed for `std_member_tolerance_hides_charged_division::p`: 2 obligation(s) were not fully verified
// The original VC snapshot may occur between `kind` and `typed_kind`; the
// row-scoped regex above still requires the exact typed division row to FAIL.
//~? RAW "kind":"divzero"
//[certify]~? RAW error: Trust Level 0 safety verification incomplete for `std_member_tolerance_hides_charged_division::p`
