//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: HELP
//! LITERAL-PAIR-WIDTH-1 (2026-10-13): an operation over TWO width-less signed
//! literals was checked at i64.
//!
//! A signed literal reaches trust-vcgen as `ConstValue::Int`, with no width, and
//! `operand_ty` types it i64 (i128 when the value does not fit i64). `int_op_type`
//! recovers an operation's width from its NON-constant operand, so for two literals
//! it answered the fabricated i64. `core::intrinsics::unchecked_div(i8::MIN, -1)`
//! lowers to a bare `_0 = Div(const -128, const -1)` into `_0: i8`, with NO assert, so
//! the statement-lane overflow row is the function's only obligation; at i64 it read
//! `-128 == i64::MIN` (UNSAT). The function was VERIFIED, its one row clean-kernel
//! `Certified` under the closed false hypothesis `h_0 : -128 = -9223372036854775808`,
//! and every call is UB (stock CTFE: "overflow in signed division (dividing MIN by
//! -1)"; native runs print values that change with the optimisation level). The
//! stable `i8::MAX.unchecked_add(1)` and `100i8.unchecked_mul(2)` read
//! `unchecked_overflow:*` PROVED and certified the same way, beside their FAILED
//! `[unsafe:unmodeled-call]` row. The rows now read the operation's DESTINATION width
//! (trust-vcgen `checked_vcs.rs` `literal_pair_int_type`, `panic_calls.rs`
//! `v2_overflow_call_body`).
//!
//! Each function is pinned by its human-format `Trust verification:` count, and each
//! that the fix moves also by its `summary:` note (printed once a row fails) and, for a
//! ground row, its guaranteed-violation error; both revisions print the same. No JSON
//! `forbid-output`: compiletest keeps only the first 512 KiB of a test's output.
//!
//! BEFORE (stage1-w25f, integ7's stage 1 of wave 25 at `a971311ee2`; each revision's
//! flags plus `--cfg <revision> -Zui-testing -Zdeduplicate-diagnostics=no -A unused
//! --emit=metadata`; both revisions read the same): exit 1 (the `unchecked_*` calls'
//! `[unsafe:unmodeled-call]` rows and the controls). `ud8`, `ud16`, `ud32`, `ud128` and
//! `ur8` each read `1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of
//! 1 obligation(s)`, `of which 1 kernel-certified by the clean CIC kernel`, and no
//! summary (nothing failed); `ua8` and `um8` read `1 proved, 1 failed, 0 unknown, 0
//! timed out, 1 runtime-checked out of 3 obligation(s)` and `summary: 0 trusted, 1
//! certified, 1 failed, 0 unknown, 1 runtime-checked`. No pin on those seven matches
//! BEFORE. The controls read as pinned: `ud64` and `ud_px` `0 proved, 1 failed` with
//! "1 guaranteed Level 0 safety violation(s)", `ud_py` `0 proved, 2 failed` (its
//! `divzero` row too), `ok_ud32` `1 proved`, `ok_ua8` `1 proved, 1 failed, 1
//! runtime-checked`.
//!
//! AFTER (FIX PREPARED 2026-10-13, not built; predicted): each intrinsic's one row is
//! FAILED at the destination width, and, ground, reported as a guaranteed violation
//! exactly as `ud64`'s already is. Each `unchecked_*` call's row, now SAT at `i8`, can
//! no longer be certified, and no in-process backend refutes an
//! `UncheckedArithmeticOverflow` row, so it reads `unknown`, as `x.unchecked_add(1)`
//! (`x: i8`) already reads on stage1-w25f; it is not an escalated kind, so no
//! guaranteed-violation error. The controls (`ud64`: the widths coincide; `ud_px`, `ud_py`: a place carries
//! the width; `ok_ud32`, `ok_ua8`: nothing to refute) do not move.
#![feature(core_intrinsics)]
#![allow(internal_features)]

use std::intrinsics::{unchecked_div, unchecked_rem};

pub fn ud8() -> i8 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    //~| NOTE summary: 0 trusted, 0 certified, 1 failed, 0 unknown,
    //~| ERROR 1 guaranteed Level 0 safety violation(s)
    unsafe { unchecked_div(i8::MIN, -1) }
}

pub fn ud16() -> i16 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    //~| NOTE summary: 0 trusted, 0 certified, 1 failed, 0 unknown,
    //~| ERROR 1 guaranteed Level 0 safety violation(s)
    unsafe { unchecked_div(i16::MIN, -1) }
}

pub fn ud32() -> i32 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    //~| NOTE summary: 0 trusted, 0 certified, 1 failed, 0 unknown,
    //~| ERROR 1 guaranteed Level 0 safety violation(s)
    unsafe { unchecked_div(i32::MIN, -1) }
}

pub fn ud128() -> i128 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    //~| NOTE summary: 0 trusted, 0 certified, 1 failed, 0 unknown,
    //~| ERROR 1 guaranteed Level 0 safety violation(s)
    unsafe { unchecked_div(i128::MIN, -1) }
}

pub fn ur8() -> i8 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    //~| NOTE summary: 0 trusted, 0 certified, 1 failed, 0 unknown,
    //~| ERROR 1 guaranteed Level 0 safety violation(s)
    unsafe { unchecked_rem(i8::MIN, -1) }
}

// Stable, no attributes: the `unchecked_*` METHOD call, whose row the call arm builds.
pub fn ua8() -> i8 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 1 unknown, 0 timed out, 1 runtime-checked out of 3 obligation(s)
    //~| NOTE summary: 0 trusted, 0 certified, 1 failed, 1 unknown, 1 runtime-checked
    unsafe { i8::MAX.unchecked_add(1) }
}

pub fn um8() -> i8 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 1 unknown, 0 timed out, 1 runtime-checked out of 3 obligation(s)
    //~| NOTE summary: 0 trusted, 0 certified, 1 failed, 1 unknown, 1 runtime-checked
    unsafe { 100i8.unchecked_mul(2) }
}

// ---- controls: unchanged by the fix ----

pub fn ud64() -> i64 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    unsafe { unchecked_div(i64::MIN, -1) }
}

pub fn ud_px(x: i8) -> i8 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    unsafe { unchecked_div(x, -1) }
}

pub fn ud_py(y: i8) -> i8 {
    //~^ NOTE Trust verification: 0 proved, 2 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2 obligation(s)
    unsafe { unchecked_div(-128, y) }
}

pub fn ok_ud32() -> i32 {
    //~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    unsafe { unchecked_div(100i32, 7) }
}

pub fn ok_ua8() -> i8 {
    //~^ NOTE Trust verification: 1 proved, 1 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 3 obligation(s)
    unsafe { 100i8.unchecked_add(27) }
}
