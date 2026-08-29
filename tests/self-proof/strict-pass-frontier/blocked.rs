#![no_std]
//! FRONTIER MARKER — this is correct, fully guarded code that CANNOT pass.
//!
//! `a + b` under the guards below cannot overflow, and the interval solver
//! agrees: the `[arithmetic_overflow_add]` row is PROVED. The build still fails
//! because the default `unix_hardened` profile emits a SECOND, separately
//! adjudicated row — `[hardened_panic_boundary] mir_assert::Overflow(Add)`.
//!
//! CORRECTED 2026-08-27 (this file previously said the twin "`ay-in-process`
//! does not discharge from the same guards" — that names the wrong mechanism,
//! and reading it as "the engines disagree" sends the next reader after a
//! refutation that does not exist):
//!
//!   * NO ENGINE REFUTES ANYTHING HERE. Every run reports `0 failed`. The
//!     interval solver reports **Proved for BOTH rows**; the twin's Proved is
//!     then DOWNGRADED, which `targo` hides and `trustc` prints verbatim:
//!     `[hardened_panic_boundary] UNKNOWN (interval): Proved label lacked exact
//!     kernel/native proof authority`.
//!   * The two rows are NOT the same formula. Both are violation formulas and
//!     both are UNSAT (z3 4.x agrees on both; a guard-widened mutant turns both
//!     SAT with the same witness `a = 147483648, b = 2000000000` that
//!     `ay-in-process` reports, so the refuting lane is live and correct). They
//!     differ only in how the out-of-range core is SPELLED:
//!         primary  `Or([Lt(a+b, i32::MIN), Gt(a+b, i32::MAX)])`
//!         twin     `Not(And([Le(i32::MIN, a+b), Le(a+b, i32::MAX)]))`
//!     `certify_disjunctive_contradiction` keys on `Formula::Or`, so the De
//!     Morgan dual never reaches the recognizer and the kernel certifies
//!     nothing it was never handed. Rewriting ONLY that node makes the twin
//!     certify — pinned, with its false-PROVE safety control, in
//!     `crates/trust-certify/tests/hardened_overflow_twin_certification.rs`.
//!
//! Scope of the measured boundary — all seven re-measured on the AUTHENTICATED
//! `targo trust check` lane, because a direct `trustc` invocation routes some of
//! them differently and reported a PASS that the authenticated lane does not
//! reproduce (a struct-field read of the same add certifies under bare `trustc`
//! and is `ay-in-process` UNKNOWN under `targo`; do not quote the bare-`trustc`
//! numbers). On the authenticated lane, exit 0: `Overflow(Shl)` under an
//! `s >= 32` guard, a guarded `BoundsCheck`, `DivisionByZero` (`pass.rs`), and
//! the widened `(a as u16) + (b as u16)` (`widen_add.rs`). Exit non-zero:
//! `Overflow(Add|Sub|Mul)` on direct integer parameters under `if` guards,
//! signed and unsigned alike.
//!
//! Measured 2026-08-27: exit 101, `Gate: FAIL [strict lane, exit 101]`, while
//! the published transport reads `Summary: 1 proved, 0 failed, 0 unknown,
//! 0 runtime-checked (1 total)` with `Coverage: 1/1 (complete)`. The compiler
//! reports "2 obligation(s) were not fully verified"; the transport publishes
//! only 1 of the 2. READING THE SUMMARY LINE ALONE SAYS THIS CRATE PASSED.
//!
//! When the hardened Overflow(*) twin's violation reaches a recognizer that can
//! refute it, this file must start passing — and that is the whole reason it is
//! checked in. Until then it pins the boundary.
pub fn add_guarded(a: i32, b: i32) -> i32 {
    if a > 1_000_000 { return 0; }
    if a < -1_000_000 { return 0; }
    if b > 1_000_000 { return 0; }
    if b < -1_000_000 { return 0; }
    a + b
}
