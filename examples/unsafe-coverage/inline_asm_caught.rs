// Inline assembly is unconditionally unsafe and unmodeled, so Trust must CATCH
// it fail-closed — never silently pass it (the completeness guarantee).
//   trustc -Z trust-verify-output=human --crate-type lib inline_asm_caught.rs
#![allow(dead_code)]

use std::arch::asm;

pub fn double_via_asm(x: u64) -> u64 {
    let out: u64;
    // SAFETY (developer's claim): a pure register add with no memory effects.
    // Trust has no semantic model of arbitrary asm, so it is caught regardless.
    unsafe {
        asm!("lsl {out}, {inp}, #1", out = out(reg) out, inp = in(reg) x);
    }
    out
}
