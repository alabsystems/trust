//@ revisions: lit ok
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@[lit] check-fail
//@[ok] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! ABS-LIT-WIDTH-1: `abs` of a signed-LITERAL receiver gets its negation row at the
//! OWNER's width.
//!
//! `trust_vcgen`'s `signed_abs_panic_body` read the row's width from
//! `crate::operand_ty` of the receiver, which types a width-less signed literal
//! (`ConstValue::Int`) as i64. `i32::MIN.abs()`, `let m = i32::MIN; m.abs()` and
//! `const M: i32 = i32::MIN; M.abs()` all reach the call as the constant `-2^31`, so the
//! row asked whether `-2^31 == i64::MIN`. That is UNSAT, so the row was published
//! `negation overflow (Int { width: 64, signed: true })` PROVED, with clean-kernel
//! `Certified` evidence (`KernelRechecked`): the kernel re-checked a goal built at the
//! wrong width. Each call panics "attempt to negate with overflow"
//! (`abs_signed_literal_receiver_run.rs`).
//!
//! BEFORE (a pre-fix stage 1, `scratchpad/stage1-w22probe`, measured 2026-10-11 with
//! this header's flags plus `--cfg <revision> --emit=metadata`): `lit` exits 0. Each
//! function has its negation row proved at width 64 and only WARNINGS ("incomplete: 1
//! obligation(s) were not proved", which is the bundled `core::num::<impl iN>::abs`
//! member's runtime-checked row). `ok` exits 0. As controls in the same build,
//! `i64::MIN.abs()` and an `x: i32` guarded by `x == i32::MIN` were refuted ("found 1
//! guaranteed Level 0 safety violation(s)").
//!
//! AFTER (measured 2026-10-11 on the stage 1 of `618d7bd287`, `integ/wave22`; before that
//! build, predicted): each `lit` function's row is built at its owner's width and is
//! refuted, with the three errors below, the same as `i64::MIN.abs()` before the fix.
//! `ok` stays green: `(-5i32).abs()`, `(i32::MIN + 1).abs()` and `(-7i16).abs()` cannot
//! panic, and their rows stay proved.

// ---- lit: each call panics ----

#[cfg(lit)]
pub fn a32() -> i32 {
    //[lit]~^ ERROR Trust Level 0 safety verification incomplete for `abs_signed_literal_receiver::a32`
    //[lit]~^^ ERROR Trust strict verification failed for `abs_signed_literal_receiver::a32`
    //[lit]~^^^ ERROR Trust verification found 1 guaranteed Level 0 safety violation(s) in `abs_signed_literal_receiver::a32`
    i32::MIN.abs()
}

#[cfg(lit)]
pub fn a16() -> i16 {
    //[lit]~^ ERROR Trust Level 0 safety verification incomplete for `abs_signed_literal_receiver::a16`
    //[lit]~^^ ERROR Trust strict verification failed for `abs_signed_literal_receiver::a16`
    //[lit]~^^^ ERROR Trust verification found 1 guaranteed Level 0 safety violation(s) in `abs_signed_literal_receiver::a16`
    i16::MIN.abs()
}

#[cfg(lit)]
pub fn a8() -> i8 {
    //[lit]~^ ERROR Trust Level 0 safety verification incomplete for `abs_signed_literal_receiver::a8`
    //[lit]~^^ ERROR Trust strict verification failed for `abs_signed_literal_receiver::a8`
    //[lit]~^^^ ERROR Trust verification found 1 guaranteed Level 0 safety violation(s) in `abs_signed_literal_receiver::a8`
    (-128i8).abs()
}

// The constant reaches the call as the same `ConstValue::Int` operand.
#[cfg(lit)]
pub fn loc() -> i32 {
    //[lit]~^ ERROR Trust Level 0 safety verification incomplete for `abs_signed_literal_receiver::loc`
    //[lit]~^^ ERROR Trust strict verification failed for `abs_signed_literal_receiver::loc`
    //[lit]~^^^ ERROR Trust verification found 1 guaranteed Level 0 safety violation(s) in `abs_signed_literal_receiver::loc`
    let m = i32::MIN;
    m.abs()
}

#[cfg(lit)]
pub fn cst() -> i32 {
    //[lit]~^ ERROR Trust Level 0 safety verification incomplete for `abs_signed_literal_receiver::cst`
    //[lit]~^^ ERROR Trust strict verification failed for `abs_signed_literal_receiver::cst`
    //[lit]~^^^ ERROR Trust verification found 1 guaranteed Level 0 safety violation(s) in `abs_signed_literal_receiver::cst`
    const M: i32 = i32::MIN;
    M.abs()
}

// ---- ok: none of these can panic ----

#[cfg(ok)]
pub fn lit_ok() -> i32 {
    (-5i32).abs()
}

#[cfg(ok)]
pub fn lit_ok2() -> i32 {
    (i32::MIN + 1).abs()
}

#[cfg(ok)]
pub fn lit_ok16() -> i16 {
    (-7i16).abs()
}
