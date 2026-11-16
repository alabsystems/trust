//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ needs-trust-verify
//@ needs-asm-support
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-ASM, the NEGATIVE pin): inline assembly has no representation in
//! trust-ir, so every `asm!` the wave-ASM arm cannot show to be "falls through into
//! UB at once" must stay REFUSED. Each body here fails exactly one of that arm's
//! gates; erasing any of them would drop a real effect from a body the flip lane
//! may substitute into codegen.

use std::arch::asm;

// G2: not `noreturn`. An empty `asm!("")` is the canonical compiler BARRIER; it
// returns to the next statement and its whole purpose is the side effect.
pub fn barrier(x: u32) -> u32 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    unsafe { asm!("") }
    x
}

// G3: a non-empty template. `nop` emits an instruction, so whether control falls
// through into the UB depends on what the template does.
pub fn one_instruction() -> ! {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    unsafe { asm!("nop", options(noreturn)) }
}

// G3 AND G4: an operand named from the template. The `{0}` placeholder is a
// template piece, so G3 refuses this body before G4 is consulted; it does NOT
// isolate G4. The body that fails G4 ALONE (an empty template with an
// explicit-register operand, which no template names) is architecture-specific
// and lives in `trust_ir_lower_asm_refuses_operand_only.rs`.
pub fn with_operand(x: u32) -> ! {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    unsafe { asm!("/* {0} */", in(reg) x, options(noreturn)) }
}
