//@ revisions: sym_certify sym_twin_certify sym_dep_strict
//@ needs-trust-verify
//@ needs-asm-support
//@ edition: 2021
//@ aux-build: assume_total_requires_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[sym_certify] compile-flags: -Ztrust-policy=certify
//@[sym_twin_certify] compile-flags: -Ztrust-policy=certify
//@[sym_certify] check-fail
//@[sym_dep_strict] check-fail
//@[sym_twin_certify] check-fail
//@ rustc-env:TRUST_VANILLA_DEBUG=1
//@[sym_twin_certify] forbid-output: into a value that no call site charges
//@[sym_twin_certify] forbid-output: [MINTED_VALUE]
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The minting-site seam's rule 6 for module-level assembly (docs/DECISION_QUEUE.md,
//! AT-REQ-2): a `global_asm!` `sym` operand hands the assembly a function it can call
//! with any argument, and no call site is charged a `requires` the function carries.
//! `mir_keys` never holds a `global_asm!` body and no verification pass reads one, so
//! the seam types each `sym` operand from the item's `typeck` results, as the mono
//! collector does, and refuses a `requires`-carrying function there.
//!
//! The operand names a VERIFIED DEPENDENCY's `add1`, whose overflow check is elided
//! under its clause. A LOCAL `requires` function is no witness here: a crate with any
//! `global_asm!` item refuses every local function with a panic path at its own
//! `UnmodeledThreadSpawnEffect` row on strict, certify and memory-safe — `sym add1`,
//! a `sym` of another function, and an operand-free template alike (MEASURED 2026-10-03
//! on a stage 1 of `782780ea0d`) — so that route was closed before the seam, by the
//! spawn census, and this crate defines no function.
//!
//! BEFORE (MEASURED 2026-10-03, stage 1 of `782780ea0d`): `sym_certify` and
//! `sym_dep_strict` (the default policy) compile exit 0 — nothing reads the operand and
//! no local function exists for the spawn census to refuse. AFTER (MEASURED on the
//! seam's stage 1; docs/KNOWN_HAZARDS.md names it): refused at the operand, one error
//! (two since the link-level rule below).
//! `sym_twin_certify`, the same with the `requires`-free `add1_wrapping`, compiled exit
//! 0 before and after the seam: the seam leaves it alone (the `forbid-output` lines).
//! No revision reaches codegen, so the template is never assembled.
//!
//! Every revision ALSO carries the link-level refusal of the `global_asm!` item itself
//! (`link_level_code`, docs/KNOWN_HAZARDS.md "CLOSED 2026-10-01 — `global_asm!` and
//! `#[link_section]` ran unverified code without a Rust call"): a verifying build under a
//! fail-closed policy refuses any `global_asm!` item, an operand-free template included,
//! because assembly can define a symbol a linked crate imports or fill a constructor
//! table. So the twin is check-fail at that one error, and the seam's own error must not
//! appear beside it (every ERROR here is annotated).

extern crate assume_total_requires_dep as dep;

#[cfg(any(sym_certify, sym_dep_strict))]
core::arch::global_asm!("/* {} */", sym dep::add1);
//[sym_certify,sym_dep_strict]~^ ERROR Trust verification failed for a `global_asm!` `sym` operand
//[sym_certify,sym_dep_strict]~| ERROR Trust verification cannot accept global assembly

#[cfg(sym_twin_certify)]
core::arch::global_asm!("/* {} */", sym dep::add1_wrapping);
//[sym_twin_certify]~^ ERROR Trust verification cannot accept global assembly

//[sym_certify,sym_dep_strict]~? RAW [MINTED_VALUE] `assume_total_requires_dep::add1` owes its caller a `requires` and becomes a value in a `global_asm!` `sym` operand
