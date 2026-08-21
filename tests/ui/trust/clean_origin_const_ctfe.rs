//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **I5 CONTROL 3 — THE CONST FIXTURE (CTFE COVERAGE).**
//! (`docs/design/2026-08-04-two-language-compiler-architecture.md` §7.)
//!
//! The increment's acceptance criterion, verbatim:
//!
//! > **the const fixture** — `const X: u64 = f();` must traverse the gate.
//!
//! WHY A CONST, AND NOT JUST A CALL. The design places the faithfulness gate in
//! `clean_origin_mir(def)` as the **sole constructor** of a Clean-origin `Body`,
//! called by BOTH the `optimized_mir` and `mir_for_ctfe` provider arms,
//! precisely so that:
//!
//!   * compile-time evaluation is covered — a `const` never reaches
//!     `optimized_mir`, so a gate installed only there would be bypassed by
//!     every constant in the program, and the value would still be baked into
//!     the binary;
//!   * **no verification switch can disable it.** The gate is a
//!     compilation-correctness check on emitted code, not an obligation. This
//!     file is compiled with `-Z trust-verify=off` ON PURPOSE: when I5 lands,
//!     the gate must still run here. A gate that vanishes under
//!     `-Z trust-verify=off` is not a gate, it is a lint.
//!
//! ============================================================================
//! **GREEN AS OF 2026-08-19.** Was RED BY DESIGN; the tilde-ERROR annotation is
//! DELETED and `-Z trust-verify=off` is RETAINED, which is the whole point of
//! the file. It is now `run-pass`, so the const is not merely accepted — it is
//! evaluated at compile time and its value observed at runtime.
//!
//! The load-bearing measurement: `X` is `6`, the FIRST argument of `f(6, 7)`.
//! A gate that had admitted the wrong projection would produce `7` and this
//! file would still compile, so the assertion below — not the exit code — is
//! what pins CTFE to the declaration's meaning.
//!
//! The gate ran with verification OFF. That is the claim this fixture owns: the
//! faithfulness gate is a compilation-correctness check on emitted code, not an
//! obligation, so no verification switch can disable it. A gate that vanished
//! under `-Z trust-verify=off` would be a lint.
//!
//! THE SHAPE HERE IS NOT ARBITRARY — it was RETARGETED (2026-08-19) after the
//! fragment was measured. This fixture used to read `def f : UInt64 := 6` with
//! `const X: u64 = f();`, a nullary constant. That shape is the one the kernel
//! **refuses**: `tests/e6-fragment-probe/` runs the same comparison in the
//! opposite direction and records every `ConstantUint` probe as
//! `defeq-rejected` (f06-f09) or `unproved` (f04), while `Projection`
//! discharges (d01-d05, d08, d09). A const fixture written on the constant
//! shape would therefore have failed the gate for a reason that has nothing to
//! do with CTFE, and would have been "fixed" by weakening the gate. It is a
//! two-parameter projection called with constant arguments instead: the CTFE
//! coverage this fixture owns is unchanged, and the shape is one the kernel
//! demonstrably admits.
//! ============================================================================

mod m {
    clean {
        def f (a : UInt64) (b : UInt64) : UInt64 := a
    }
}

// MUST traverse the faithfulness gate at CTFE time, with verification OFF.
// Trust (#65, R2/C4 housekeeping): a DIRECT const call, restored — the mint
// plants `Visibility::Public` and feeds constness `Const`, so the earlier
// same-module `const fn` wrapper (added against a then-measured E0603) is
// gone; see clean_origin_call_parity.rs for the parity rationale.
const X: u64 = crate::m::f(6, 7);

fn main() {
    println!("{X}");
    // `6`, not `7`: the first projection argument. See the header — a gate that
    // admitted the wrong projection would still compile this file.
    assert_eq!(X, 6, "CTFE must evaluate the projection the Clean `def` denotes");
}
