//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **§6f LANDING 7 — THE RAW-BINOP EMISSION, RUN.**
//! (`CleanOriginShape::RawBinOp`; `crates/trust-clean-origin/src/emit.rs`.)
//!
//! Every other emittable shape has a run fixture — `clean_origin_call_parity`
//! (`Projection`), `clean_origin_wrapping_binop` (`WrappingBinOp`),
//! `clean_origin_constant`, `clean_origin_run_select{,_literal}`,
//! `clean_origin_select_operands`, `clean_origin_composed`,
//! `clean_origin_structural_rec`, `clean_origin_wf_rec`. Landing 7 shipped
//! `RawBinOp` without one, so `&`/`|`/`/`/`%` were measured everywhere except
//! in a running binary. This is that fixture, led by `%`.
//!
//! # EVERY VALUE BELOW DISTINGUISHES SOMETHING
//!
//! A fixture that only proved a call linked would be worthless, so each assert
//! separates the emitted body from a specific plausible mistranslation:
//!
//! * `rem7(u64::MAX) == 1` — **the width witness.** A body emitted at u32
//!   instead of u64 is a valid `fn(u32) -> u32` remainder that passes every
//!   structural check, and it returns `3` here
//!   (`u32::MAX % 7 == 3` against `u64::MAX % 7 == 1`). This is the runtime
//!   counterpart of `control_15::half_7`, where only the kernel comparison
//!   catches it at gate time.
//! * `rem7(7) == 0` and `rem7(6) == 6` — AT and BELOW the divisor. An
//!   off-by-one in the emitted divisor flips exactly these two.
//! * `div7(u64::MAX) == 2635249153387078802` — `/` and `%` are different
//!   `Nat` recursions, and this pins that the two rows did not get crossed.
//! * `bmod(255) == 5` — a NARROWER carrier (u8), so the width is read from the
//!   signature rather than assumed to be 64.
//! * `mask(255) == 15` / `setlow(240) == 255` — the bitwise pair, whose operands
//!   have no divisor rule; they share the shape's single-statement
//!   realization and would break with it.
//! * `R == 2` — CTFE traverses the faithfulness gate AND interprets the
//!   emitted bare `Rvalue::BinaryOp`, so the const lane is measured, not
//!   assumed.
//!
//! # THE DIVISOR IS A POSITIVE LITERAL IN EVERY DEF HERE, AND THAT IS THE RULE
//!
//! `UInt{N}.mod` is TOTAL and Rust's `%` PANICS, so this shape emits `/` and
//! `%` only at a statically nonzero divisor, where the two semantics agree on
//! every input — which is why there is no `Assert` terminator in the emitted
//! body and why nothing below can panic. `def r (a b : UInt64) := a % b` does
//! not compile at all (`landing7_selection_probes::l7_p8`), and that refusal is
//! a soundness boundary, not a missing feature: a symbolic divisor needs a real
//! `b != 0` obligation discharged before emission, and a MIR `if b == 0` guard
//! does not supply one (`l7_p6` — at an open `b` the scrutinee is stuck, so the
//! guarded body is not definitionally equal to the declaration).
//!
//! `-Z trust-verify=off` is the point, not a convenience: the faithfulness gate
//! is a compilation-correctness check, deliberately NOT behind any verification
//! switch, and this fixture would be worthless if the flag could disable the
//! machinery it measures.

mod m {
    clean {
        def rem7 (a : UInt64) : UInt64 := a % 7
        def div7 (a : UInt64) : UInt64 := a / 7
        def bmod (a : UInt8) : UInt8 := a % 10
        def mask (a : UInt64) : UInt64 := a &&& 15
        def setlow (a : UInt64) : UInt64 := a ||| 15
    }
}

// CTFE: the const lane goes through `mir_for_ctfe`, whose only source of a
// Clean-origin body is the gated emission.
const R: u64 = crate::m::rem7(100);

fn main() {
    // ── `%`, the operator this fixture is led by ───────────────────────────
    assert_eq!(m::rem7(0), 0, "0 % 7");
    assert_eq!(m::rem7(6), 6, "BELOW the divisor: `%` is the identity there");
    assert_eq!(m::rem7(7), 0, "AT the divisor: an off-by-one divisor flips this");
    assert_eq!(m::rem7(8), 1, "just above the divisor");
    assert_eq!(
        m::rem7(u64::MAX),
        1,
        "THE WIDTH WITNESS: a u32-truncated emission returns 3 here, not 1"
    );

    // ── `/`, so the two division rows cannot be crossed ────────────────────
    assert_eq!(m::div7(u64::MAX), 2_635_249_153_387_078_802, "`/` is not `%`");
    assert_eq!(m::div7(6), 0, "truncating division below the divisor");

    // ── a narrower carrier ─────────────────────────────────────────────────
    assert_eq!(m::bmod(255), 5, "u8: 255 % 10, with the width read from the signature");
    assert_eq!(m::bmod(9), 9, "u8, below the divisor");

    // ── the bitwise pair, which shares the realization ─────────────────────
    assert_eq!(m::mask(255), 15, "`&&&` masks the low nibble");
    assert_eq!(m::mask(240), 0, "`&&&` with no overlap");
    assert_eq!(m::setlow(240), 255, "`|||` sets the low nibble");

    assert_eq!(R, 2, "CTFE of the emitted BinaryOp must agree with the runtime value");
}
