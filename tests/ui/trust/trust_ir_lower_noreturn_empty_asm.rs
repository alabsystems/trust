//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ needs-trust-verify
//@ needs-asm-support
//@ dont-require-annotations: NOTE
//! Trust (wave-ASM, the POSITIVE pin): an `asm!` block with an EMPTY template, NO
//! operands and `options(noreturn)` lowers to `Inst::Unreachable`. Falling through
//! the end of a `noreturn` asm block is undefined behaviour, and an empty template
//! falls through at once, so reaching the statement IS the UB — `Unreachable` is its
//! exact meaning, not an approximation. Under `strict` with verification on, so a
//! regression (the body falling back to the `InlineAsm` catch-all tag) is a compile
//! error. The shapes the arm must keep REFUSING are pinned by
//! `trust_ir_lower_asm_refuses.rs` and `trust_ir_lower_asm_refuses_operand_only.rs`.
//!
//! WHAT THE `WARN`s BELOW DO AND DO NOT SHOW. They are the MIR lane's
//! "Trust Level 0 safety verification incomplete" warning: that lane reads the
//! built body's own `InlineAsm` terminator (1 failed structural unsafe demand +
//! 1 unknown "opaque MIR terminator `InlineAsm` cannot be soundly lowered", of 2
//! obligations, per body, measured 2026-09-29) and NEVER the direct module this
//! arm writes. The same warning fires for a provably DEAD asm
//! (`if x < 1 && x > 5 { asm!(...) }`). So requiring it pins only that the MIR
//! lane's shipped verdict on these bodies stays "not proved"; it is NO evidence
//! that the arm charges the reachable asm rather than erasing or assuming it
//! away. Measured: with the seal erased, or replaced by `assume(false)`, this
//! file stays green.
//!
//! The arm's own output is pinned where it lands, in
//! `tests/run-make/trust-ir-noreturn-empty-asm` (the `-Ztrust-dump=ir` module):
//! one `unreachable` charge on each asm's own line, reached on exactly `x == 0`
//! in `guarded` and on no input in a dead-path control. No verifier reads that
//! module today (no native verification requests, no proof authority), so
//! neither charge is proved or refuted by a shipped lane.

use std::arch::asm;

// The whole body is the asm block: the fn's `!` return is the block's own type.
pub fn diverge() -> ! {
    //~^ WARN Trust Level 0 safety verification incomplete for `trust_ir_lower_noreturn_empty_asm::diverge`
    unsafe { asm!("", options(noreturn)) }
}

// The asm block in one arm of a join: the arm seals with `Unreachable` and the join
// takes only the fall-through edge.
pub fn guarded(x: u32) -> u32 {
    //~^ WARN Trust Level 0 safety verification incomplete for `trust_ir_lower_noreturn_empty_asm::guarded`
    if x == 0 {
        unsafe { asm!("", options(noreturn)) }
    }
    x
}
