//@ check-fail
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ forbid-output: REFUSED at crate assembly
//@ forbid-output: did not fully lower
//@ forbid-output: final Trust-IR module validation failed
//@ forbid-output: UnsignableRustAbiDeclaration
//! Trust (thir-generic-instance-callee, 2026-09-29): a call edge to a generic std INSTANCE
//! whose parameter is a REFERENCE TO A POINTER (`&&str`, `&&u32`, `&&String`, `&&i32`) is
//! SIGNED, so the body that mints it lowers and splices.
//!
//! Every body here was refused under `-Ztrust-ir-lower=strict` before, each for the same
//! reason: `UnsignableRustAbiDeclaration(<callee>)` — "the instance carries generic
//! arguments …, so this instance has neither a lowered body to link nor an instantiated
//! signature to record". The signature WAS instantiated (an extern callee is always read at
//! its resolved instance); what refused it was the DROPPED-BORROW GUARD in
//! `recover_callee_param_tys`, which declined any parameter `&P` whose pointee `P` is itself
//! a pointer. That guard stood in for a call-site defect — a value-for-pointer carrier lane
//! passing `P` where `&P` was due — which is now closed where it happens
//! (`ref_arg_pointee_may_be_pointer`), so the parameter is signed as what `map_ty` gives the
//! argument: a thin `ptr`. The module is validated with those signatures in place, so every
//! argument below is checked against a real parameter list, not the vacuous vararg one.
//!
//! One function per shape of the class, as measured on the inventory's census
//! (`~/scratch.noindex/handoff/lowering-classes-2026-09-29.json`):
//!   * `format!("{y}")` / `format!("{y:?}")` over a `&str` — `Argument::new_display::<&str>` /
//!     `new_debug::<&str>`, parameter `&&str`;
//!   * `==` / `!=` / `>=` on two references — `<&A as PartialEq<&B>>::eq` / `ne`,
//!     `<&A as PartialOrd<&B>>::ge`, parameters `&&A`, `&&B` (thin `&u32` / `&String` pointees
//!     and fat `&str` ones alike);
//!   * `String == &str` through a reference — `<&String as PartialEq<&str>>::eq`;
//!   * `.clone()` of a `&i32` — `<&T as Clone>::clone`, parameter `&&i32`;
//!   * `std::mem::size_of_val(&r)` on a reference — parameter `&&u8`.
//!
//! MEASURED 2026-10-15 on the stage 1 of this change: every body here lowers and splices with
//! no producer refusal (the run-make twin `tests/run-make/trust-ir-ref-to-pointer-declarations`
//! asserts it on the sidecar, and that each `==` edge is passed SLOT addresses). Under strict,
//! the three `format!` bodies then meet a DIFFERENT, later gate, so this file is `check-fail`
//! with exactly those three errors: the effect-conservation check refuses a body whose direct
//! trust-ir abstracts an enum held by value, and the `format_args!` expansion holds
//! `core::fmt::rt::Argument` values whose `ArgumentType` field the producer spells as the opaque
//! `()` placeholder. That is not this class (the `forbid-output` lines keep this class closed);
//! when the `fmt::rt` enum is modelled, the three annotations go and the file is `check-pass`.
//! compiletest fails on any unannotated error, so every other body is pinned to lower.

pub fn fmt_display_str(y: &str) -> String {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir of this body is not the program
    format!("{y}")
}

pub fn fmt_debug_str(y: &str) -> String {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir of this body is not the program
    format!("{y:?}")
}

pub fn fmt_mixed(x: u32, y: &str) -> String {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir of this body is not the program
    format!("{x} {y}")
}

pub fn eq_str(a: &str, b: &str) -> bool {
    a == b
}

pub fn ne_str(a: &str, b: &str) -> bool {
    a != b
}

pub fn eq_ref_u32(a: &u32, b: &u32) -> bool {
    a == b
}

pub fn ge_ref_u64(a: &u64, b: &u64) -> bool {
    a >= b
}

pub fn eq_string(a: &String, b: &String) -> bool {
    a == b
}

pub fn string_eq_lit(s: &String) -> bool {
    s == "0"
}

pub fn clone_ref(r: &i32) -> i32 {
    let c: &i32 = Clone::clone(&r);
    *c
}

pub fn size_of_ref(r: &u8) -> usize {
    std::mem::size_of_val(&r)
}
