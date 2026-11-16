//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ needs-trust-verify
//@ only-aarch64
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-ASM, the NEGATIVE pin for gate G4 ALONE): `no operands`.
//!
//! `trust_ir_lower_asm_refuses.rs`'s operand body names its operand from the
//! template (`"/* {0} */"`), so its `{0}` placeholder is a template piece and G3
//! (an empty template) refuses it first: deleting G4 would leave that file green.
//! This body passes G1 (`asm!`), G2 (`noreturn`) and G3 (the template is `""`,
//! zero pieces) and fails ONLY G4: an explicit-register operand is never named in
//! the template, yet it still evaluates `x` and writes it into `x0` before the
//! block runs. If G4 were dropped the body would lower to a bare `Unreachable`,
//! erasing the operand, and this file would go red.
//!
//! Explicit registers are per-architecture, hence `only-aarch64`.

use std::arch::asm;

pub fn operand_only(x: u64) -> ! {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    unsafe { asm!("", in("x0") x, options(noreturn)) }
}
