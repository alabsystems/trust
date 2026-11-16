//@ needs-trust-verify
//@ edition: 2021
//@ aux-build:xcrate_member_unsafe_dep.rs
//@ revisions: extend noop_unsafe plain undeclared_plain
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[extend] compile-flags: -Ztrust-bundle-foreign-crate=xcunsafe_dep
//@[noop_unsafe] compile-flags: -Ztrust-bundle-foreign-crate=xcunsafe_dep
//@[plain] compile-flags: -Ztrust-bundle-foreign-crate=xcunsafe_dep
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[extend] check-fail
//@[noop_unsafe] check-fail
//@[plain] check-pass
//@[undeclared_plain] check-fail
//! D4 increment A (2026-09-24) — a DECLARED dependency's function that carries
//! user `unsafe` source is not bundled as a member of a verifying root
//! (`trust_verify/foreign_rederivation.rs`,
//! `foreign_body_carries_user_unsafe_source`, called from the B-lane member
//! drain). Its call site keeps the fail-closed absent-callee row, exactly as
//! with the crate undeclared.
//!
//! `extend` and `noop_unsafe` MUST STAY REFUSED. Fix the compiler, never this
//! file.
//!
//! # The false accept this closes (pre-existing, found under D4-A)
//!
//! Measured on the stage-1 snapshot at `4e9fe36bf` (current main without this
//! change), through a compiletest-equivalent harness: `extend` — a lifetime-only
//! `transmute::<&u32, &'static u32>` in the dependency — built rc=0 with the
//! crate declared (one tolerated runtime-checked row), while the byte-identical
//! LOCAL function is refused ("1 obligation(s) were not proved": the HIR half of
//! `validity_transmute` charges it). InstSimplify erases that transmute from the
//! encoded MIR, and a bundled member is judged from MIR alone, so a dependency
//! body cleared a weaker bar than the same local body. A re-derived D4-A root
//! reaches its callees through this same drain, so the member lane has to be
//! held to the same source fact as the root.
//!
//! # The revisions
//!
//! * `extend` — declared, the erased transmute: refused on the absent-callee row.
//! * `noop_unsafe` — declared, an `unsafe` block around a safe expression: the
//!   MIR has no unsafe operation, so only the source fact declines it (the
//!   deliberate completeness cost: any user `unsafe` declines).
//! * `plain` — declared, the same body without `unsafe`: still bundled and
//!   verified (the control; without it the two refusals prove nothing).
//! * `undeclared_plain` — the control's body, crate undeclared: the
//!   absent-callee row the declined members fall back to.
//!
//! BEFORE (same snapshot): `extend` rc=0, `noop_unsafe` rc=0, `plain` rc=0,
//! `undeclared_plain` refused.
extern crate xcunsafe_dep;

#[cfg(extend)]
pub fn f() -> u32 {
    //[extend]~^ ERROR Trust strict verification failed
    //[extend]~| NOTE an unproven panic-freedom obligation for a call to an absent callee
    let x = 5u32;
    xcunsafe_dep::extend(&x)
}

#[cfg(noop_unsafe)]
pub fn f() -> u32 {
    //[noop_unsafe]~^ ERROR Trust strict verification failed
    //[noop_unsafe]~| NOTE an unproven panic-freedom obligation for a call to an absent callee
    xcunsafe_dep::noop_unsafe(std::hint::black_box(9))
}

#[cfg(any(plain, undeclared_plain))]
pub fn f() -> u32 {
    //[undeclared_plain]~^ ERROR Trust strict verification failed
    //[undeclared_plain]~| NOTE an unproven panic-freedom obligation for a call to an absent callee
    xcunsafe_dep::plain(std::hint::black_box(9))
}
