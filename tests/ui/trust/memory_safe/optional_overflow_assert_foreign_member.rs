//@ revisions: ms adv ms_on path_ms path_adv
//@ needs-trust-verify
//@ aux-build:optional_overflow_assert_foreign_dep.rs
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@[ms] compile-flags: -Ztrust-policy=memory-safe -Coverflow-checks=off
//@[ms] compile-flags: -Ztrust-bundle-foreign-crate=optional_overflow_assert_foreign_dep
//@[adv] compile-flags: -Ztrust-policy=advisory -Coverflow-checks=off -Ztrust-verify-output=json
//@[adv] compile-flags: --error-format=human
//@[adv] compile-flags: -Ztrust-bundle-foreign-crate=optional_overflow_assert_foreign_dep
//@[ms_on] compile-flags: -Ztrust-policy=memory-safe -Coverflow-checks=on
//@[ms_on] compile-flags: -Ztrust-bundle-foreign-crate=optional_overflow_assert_foreign_dep
//@[path_ms] compile-flags: -Ztrust-policy=memory-safe -Coverflow-checks=off
//@[path_ms] compile-flags: -Ztrust-bundle-foreign-crate=optional_overflow_assert_foreign_dep
//@[path_adv] compile-flags: -Ztrust-policy=advisory -Coverflow-checks=off -Ztrust-verify-output=json
//@[path_adv] compile-flags: --error-format=human
//@[path_adv] compile-flags: -Ztrust-bundle-foreign-crate=optional_overflow_assert_foreign_dep
//@[ms] check-fail
//@[ms_on] check-fail
//@[path_ms] check-fail
//@[adv] check-pass
//@[path_adv] check-pass
//@[adv] forbid-output: "outcome":"proved"
//@[path_adv] forbid-output: "outcome":"proved"
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! **A checks-off caller must not erase the overflow assert of a body another
//! crate codegens** (OVF-ASSERT-XCRATE-1, direction 1; docs/KNOWN_HAZARDS.md,
//! docs/DECISION_QUEUE.md).
//!
//! EVERY `check-fail` REVISION MUST STAY REFUSED, and no `adv` revision may
//! publish a `proved` row. One going green is a possible FALSE ACCEPT until shown
//! otherwise: fix the compiler, never this file.
//!
//! The dependency (`auxiliary/optional_overflow_assert_foreign_dep.rs`) is built
//! verify-off with overflow checks ON, so its own code panics at the edge
//! (`optional_overflow_assert_foreign_member_run.rs`). This crate verifies with
//! `-Coverflow-checks=off` (honored only under memory-safe and advisory; every
//! fail-closed policy canonicalizes checks on) and declares the dependency in its
//! bundling scope, so the callee is bundled as a MEMBER of the caller's proof.
//!
//! # Before (the stage 1 of `4ccd862830`, `scratchpad/stage1-w18b`, measured
//! 2026-10-06 with exactly these revisions' flags and `--cfg <revision>`, outside
//! compiletest, aux crates built with their own headers by the same compiler)
//!
//! OVF-ASSERT-ERASED-1 erased every optional overflow assert of a checks-off
//! EXTRACTING session, including the members' — although the dependency's code,
//! not this crate's, runs them.
//!
//! * `ms` built rc=0 and `adv` rc=0. Each reported `use_inc`'s one row (`vc:…:
//!   assertion:panic-freedom:0`) `proved` (trust-full-verifier, "1 proved").
//! * `path_ms` built rc=0 and `path_adv` rc=0, with `use_outer`'s row `proved`:
//!   the dependency's exported `outer` runs ITS copy of the `#[inline]` `inner`,
//!   while the bundle held one `inner`, erased.
//! * `ms_on` (checks on; the control) was refused, rc=1, "Trust memory-safe
//!   verification failed for `…::use_inc`".
//!
//! On the stage 1 of `0ac7a96d9f` (`scratchpad/stage1-w18`, before
//! OVF-ASSERT-ERASED-1; same day, same flags) every revision read as this file
//! expects: `ms`, `ms_on` and `path_ms` rc=1 ("Trust memory-safe verification
//! failed for"), `adv` and `path_adv` rc=0 with no `proved` row. The member kept
//! its assert there, and the bundled-member assert gate refused it.
//!
//! # After (PREDICTED, not built: no stage 1 of this change exists yet)
//!
//! `trust-mir-extract` erases an optional overflow assert only in a body THIS
//! session codegens. A foreign member's keeps its panic edge with the unsupported
//! condition `optional-overflow-assert-codegen-session`. The bundled-member assert
//! gate judges an assert by its message (`Overflow(Add)` is outside its lane), so
//! the member is refused as on the stage 1 of `0ac7a96d9f` and as `ms_on`'s is:
//! every check-fail revision is refused ("verification failed for"), and no adv
//! revision publishes a `proved` row. The local-body shapes of
//! `optional_overflow_assert_checks_off.rs` are unchanged.

extern crate optional_overflow_assert_foreign_dep as dep;

#[cfg(any(ms, adv, ms_on))]
pub fn use_inc(x: u32) -> u32 {
    //[ms]~^ ERROR verification failed for
    //[ms_on]~^^ ERROR verification failed for
    dep::inc(x)
}
//[adv]~? RAW "function":"optional_overflow_assert_foreign_member::use_inc"

#[cfg(any(path_ms, path_adv))]
pub fn use_outer(x: u32) -> u32 {
    //[path_ms]~^ ERROR verification failed for
    dep::outer(x)
}
//[path_adv]~? RAW "function":"optional_overflow_assert_foreign_member::use_outer"
