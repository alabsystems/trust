//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ needs-asm-support
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (F1, 2026-09-29): the REFUSAL half of `trust_ir_lower_diverging_call_arg.rs`.
//!
//! wave-DA let a call argument that SEALED the cursor stop the call with no tag, on the belief
//! that a sealed cursor means the argument diverged, and it `truncate`d the argument's tags to
//! get there. A seal is not a divergence: fail-closed arms seal too. `capture_arm` tags an arm
//! that produced no value and seals it `Unreachable`; a block keeps lowering past a statement
//! that failed and a later `return` seals it. The truncate erased the only record of either,
//! and the body was SPLICED with `unsupported == []`:
//!
//!   * `arm_declined` — `condbr c; then: unreachable; else: ret 0`. rustc computes the asm's
//!     value and calls `consume`; the spliced body executes `unreachable`.
//!   * `stmt_declined` — `ret 7` with the refused statement simply gone.
//!
//! Measured on the pre-fix driver (fbb9fa383d, `-Ztrust-dump=ir`): both rows `lowered`,
//! `spliced`, `unsupported: []`. Under `strict` both must now be refused, and the three genuine
//! divergences below must still lower with no error at all — a `return`, a `break` and a
//! `!`-typed call push no tag, so keeping the argument's tags costs them nothing.

#![allow(unreachable_code, unused_variables)]

#[inline(never)]
pub fn consume(x: u64) -> u64 {
    x
}

// (a) a declined VALUE in one arm, a genuine divergence in the other.
pub fn arm_declined(c: bool) -> u64 { //~ ERROR could not fully lower
    consume(if c {
        let r: u64;
        unsafe { core::arch::asm!("mov {}, 7", out(reg) r) };
        r
    } else {
        return 0
    })
}

// (b) a declined STATEMENT, then a genuine divergence.
pub fn stmt_declined(c: bool) -> u64 { //~ ERROR could not fully lower
    if c {
        consume({
            unsafe { core::arch::asm!("nop") };
            return 7
        })
    } else {
        1
    }
}

// Controls: genuine divergence in argument position. NOT errors.
pub fn ctl_return(c: bool) -> u64 {
    if c { consume(return 3) } else { 7 }
}

pub fn ctl_panic(c: bool) -> u64 {
    if c { consume(panic!()) } else { 7 }
}

pub fn ctl_break() -> u64 {
    let mut n = 0;
    loop {
        n += 1;
        consume(break);
    }
    n
}

fn main() {}
