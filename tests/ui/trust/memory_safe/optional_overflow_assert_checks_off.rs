//@ revisions: inherit_off inherit_on
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@[inherit_off] compile-flags: -Ztrust-policy=memory-safe -Coverflow-checks=off
//@[inherit_on] compile-flags: -Ztrust-policy=memory-safe -Coverflow-checks=on
//@[inherit_off] check-fail
//@[inherit_on] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! **With overflow checks OFF, an optional overflow `Assert` in MIR is not a check**
//! (OVF-ASSERT-ERASED-1; docs/KNOWN_HAZARDS.md, docs/DECISION_QUEUE.md).
//!
//! rustc's codegen compiles every `Assert` whose message is an OPTIONAL overflow
//! check (`OverflowNeg`, `Overflow(Add | Sub | Mul | Shl | Shr)`) as if it always
//! succeeds when the session has overflow checks off, whichever crate the MIR came
//! from (`rustc_codegen_ssa/src/mir/block.rs`, `codegen_assert_terminator`). Such
//! an assert reaches a checks-off body from MIR built with checks on: a
//! `#[rustc_inherit_overflow_checks]` body (`inherit_off`), or core's `abs`,
//! `Add::add` and `Neg::neg` pulled in by the MIR inliner (`inline_adv`). The
//! binary then wraps (`optional_overflow_assert_checks_off_run.rs`), while every
//! verification lane read the assert's success edge as "no overflow".
//!
//! # Before (stage 1 of `0ac7a96d9f`, `integ/wave18`, measured 2026-10-06 with
//! exactly these revisions' flags and `--cfg <revision>`, outside compiletest)
//!
//! `inherit_off` built rc=0: every postcondition row of `abs_like` and `add1` PROVED
//! (trust-exact-source-clause-discharge, trust-full-verifier) although
//! `abs_like(i32::MIN)` returns `i32::MIN` and `add1(i32::MAX)` returns `i32::MIN`.
//! `inline_adv` built rc=0 with every postcondition row of `inline_abs`,
//! `inline_add` and `inline_neg` PROVED (no `[postcond] UNKNOWN` note), and each
//! returns `MIN` at its edge. `inherit_on` built rc=0 with every row proved.
//!
//! # After (measured 2026-10-06 on the stage 1 of this change)
//!
//! `trust-mir-extract` extracts an optional overflow assert of a checks-off session
//! as the `Goto` codegen emits. `inherit_off` is refused on both liars;
//! `inline_adv` builds with each liar's postcondition rows UNKNOWN (fail-closed,
//! not a refutation); `inherit_on` (checks on: the assert is real, `-MIN` and
//! `MAX + 1` panic before they return) still proves every row.

#![cfg_attr(any(inherit_off, inherit_on), feature(rustc_attrs))]
#![cfg_attr(any(inherit_off, inherit_on), allow(internal_features))]

#[cfg(any(inherit_off, inherit_on))]
#[rustc_inherit_overflow_checks]
pub fn abs_like(x: i32) -> i32
//[inherit_off]~^ ERROR Trust memory-safe verification failed for `optional_overflow_assert_checks_off::abs_like`
    ensures result >= 0
{
    if x < 0 { -x } else { x }
}

#[cfg(any(inherit_off, inherit_on))]
#[rustc_inherit_overflow_checks]
pub fn add1(x: i32) -> i32
//[inherit_off]~^ ERROR Trust memory-safe verification failed for `optional_overflow_assert_checks_off::add1`
    ensures result > x
{
    x + 1
}
