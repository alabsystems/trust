//@ check-fail
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Ztrust-verify-level=2 -Ztrust-verify-profile=unix_hardened -Ztrust-verify-include-dependencies=yes -Ztrust-ir-lower=strict --crate-type=lib
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ forbid-output: REFUSED at crate assembly
//@ forbid-output: did not fully lower
//@ forbid-output: UnsignableRustAbiDeclaration
//! Trust (thir-generic-instance-callee): the class's inventory repro under ay's checked-in
//! posture argv, verbatim (certify, level 2, unix_hardened, dependencies included, strict
//! lowering).
//!
//! Measured on origin/main 9641bc6352 (stage1 built from it) this file failed with exactly one
//! error, and not a verification one — its one obligation was PROVED:
//!
//! ```text
//! error: -Ztrust-ir-lower=strict: this body was REFUSED at crate assembly, so the producer did
//!        not fully lower it: UnsignableRustAbiDeclaration(!trust_bodyless_instance::core::fmt::
//!        rt::Argument::<'_>::new_display::…)
//! ```
//!
//! `format!("{x} {y}")` mints `Argument::new_display::<&str>(x: &&str)`, whose declaration the
//! producer refused to sign (the dropped-borrow guard: a reference to a pointer). It is signed
//! now and the body lowers and splices, so that error is gone and the `forbid-output` lines keep
//! it gone.
//!
//! RE-PINNED 2026-10-15 to `check-fail`, measured on the stage 1 of this change: the body now
//! meets the NEXT gate, a different one. The effect-conservation check refuses it under strict
//! because the `format_args!` expansion holds `core::fmt::rt::Argument` values whose
//! `ArgumentType` enum field the producer spells as the opaque `()` placeholder (`struct
//! @"core::fmt::rt::Argument<'_>" { ty: () }`), so the direct trust-ir abstracts an enum held by
//! value. That refusal is the honest answer for an abstracted value, not this class; when the
//! `fmt::rt` enum is modelled, the annotation below goes and this file is `check-pass`, with
//! certify still required to PROVE every obligation.

pub fn show(x: u32, y: &str) -> String {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir of this body is not the program
    format!("{x} {y}")
}
