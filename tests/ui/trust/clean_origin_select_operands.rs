//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **§6f LANDING 3 — THE GENERAL SELECT EMISSION, RUN.**
//! (`CleanOriginShape::SelectOperands`; `crates/trust-clean-origin/src/emit.rs`,
//! emitted by `build_select_operands_body` in
//! `compiler/rustc_mir_transform/src/clean_origin_mir.rs`.)
//!
//! This is the shape landing 2 ranked SECOND on its MISS list and refused, on
//! the correct reading that a constant arm was unrepresentable in the frozen
//! `trust-spec-elab` producers' signatures. Landing 3 owned that crate and
//! added `admit_select_operands_function` BESIDE them — the frozen routes are
//! untouched — after measuring the shape first at the kernel, against side A
//! taken from the REAL island elaborator
//! (`crates/trust-clean-origin/tests/landing3_selection_probes.rs`).
//!
//! What this fixture pins that the fast lane cannot:
//!
//! * `clampz(a, b)` — the arms are now DIFFERENT INSTRUCTIONS (a parameter
//!   copy in one block, an inline scalar in the other), so a real compilation
//!   is the only place the emitted diamond's two arm blocks, its `SwitchInt`
//!   polarity and the extractor's read-back of an arm CONSTANT are exercised
//!   together. Every fast-lane control hands `admit_lowering` a hand-built
//!   `VerifiableFunction`.
//! * `bothc(a, b)` — BOTH arms constant, so the emitted body reads no parameter
//!   at all in either arm while still being a two-parameter function.
//! * `clamp10z(a, b)` — a constant arm UNDER R2/C9's literal comparison, which
//!   composes the two widenings: the Nat-reduced decidability instance on side
//!   A and the numeral arm on side B, in one tree.
//! * `nz(a)` — arity 1, where a de Bruijn inversion that arity 2 hides would
//!   show, and the constant is in the THEN arm rather than the ELSE arm.
//! * `C`/`CN` — CTFE goes through `mir_for_ctfe`, whose only source of a
//!   Clean-origin body is the GATED emission.
//!
//! The polarity trap is what the runtime assertions are really for: a swapped
//! `SwitchTargets` emits the arms the other way round, and with one arm a
//! parameter and the other a numeral that is a visibly different function on
//! every input — so these `assert_eq!`s fail loudly rather than coincidentally
//! agreeing.
//!
//! `-Z trust-verify=off` is the point, not a convenience: the faithfulness
//! gate is a compilation-correctness check, deliberately NOT behind any
//! verification switch, and this fixture would be worthless if the flag could
//! disable the machinery it measures.

mod m {
    clean {
        def clampz (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else 0
        def bothc (a : UInt64) (b : UInt64) : UInt64 := if a < b then 1 else 0
        def clamp10z (a : UInt64) (b : UInt64) : UInt64 := if a < 10 then a else 0
        def nz (a : UInt64) : UInt64 := if a < 1 then 7 else a
    }
}

const C: u64 = crate::m::clampz(3, 9);
const CN: u64 = crate::m::nz(0);

fn main() {
    // The TRUE arm returns the parameter, the FALSE arm the numeral.
    assert_eq!(m::clampz(3, 9), 3, "a < b: the then arm is the parameter");
    assert_eq!(m::clampz(9, 3), 0, "a >= b: the else arm is the numeral");
    assert_eq!(m::clampz(5, 5), 0, "the comparison is strict `<`");

    // Both arms constant: a two-parameter function that reads neither in
    // either arm.
    assert_eq!(m::bothc(1, 2), 1);
    assert_eq!(m::bothc(2, 1), 0);

    // A constant arm under a literal comparison — the two widenings composed.
    assert_eq!(m::clamp10z(4, 77), 4, "a < 10: the parameter");
    assert_eq!(m::clamp10z(10, 77), 0, "a == 10 is NOT < 10: the numeral");
    assert_eq!(m::clamp10z(u64::MAX, 77), 0);

    // Arity 1, constant in the THEN arm.
    assert_eq!(m::nz(0), 7, "0 < 1: the then arm is the numeral");
    assert_eq!(m::nz(1), 1, "1 is not < 1: the else arm is the parameter");
    assert_eq!(m::nz(u64::MAX), u64::MAX);

    assert_eq!(C, 3, "CTFE must agree with the runtime value");
    assert_eq!(CN, 7, "…including the arity-1, constant-then-arm case");
}
