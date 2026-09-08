//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ known-bug: unimplemented
//@ failure-status: 1
//! THE SEQUENCE-LOWERING GAP, as two lines instead of a paragraph.
//!
//! Typed-TrustIr lowering does not model sequences, so any body touching one is
//! refused with
//!
//!     error: Trust full verification failed for `...`: native typed-TrustIr
//!     lowering did not complete, so the panic-freedom of an unmodeled construct
//!     could not be established
//!
//! It surfaces as `BridgeError::UnsupportedType` in
//! `crates/trust-ir-bridge/src/lower.rs:251` (33 call sites), reported as
//! `unsupported type: Seq { elem: Int { width: 8, signed: false } }` for
//! `Vec<u8>`/`&str`/`&[u8]`. This is the dominant obligation-debt class across
//! the whole constellation — measured: 1006 notes on a single trust-ir crate,
//! 370 of 651 errors on nn.
//!
//! WHAT THIS FILE PINS, and why it is worth its own test: a struct is poisoned
//! merely by CONTAINING sequence fields. Measured on trust f70ce6054 —
//!
//!     struct with Vec<f32> fields + constructor   -> exit 1 (this file)
//!     the SAME struct with the Vec fields removed  -> exit 0
//!     a bare `fn make() -> Vec<f32>`               -> exit 1, same error
//!
//! — which is why it reaches whole systems rather than isolated functions. nn's
//! tensor buffers and ny's `GeluPrecomputeTables { d_lower_right: Vec<f32>, ... }`
//! are both this, and both repos fail their verified build because of it.
//!
//! WHAT IT DOES NOT PIN — CORRECTED 2026-09-07. This file previously claimed the
//! case does NOT produce the #189-family
//! `OperandTypeMismatch`/`ReturnTypeMismatch { expected: "struct.N", actual: "()" }`.
//! That was wrong, and the reason is worth keeping: it was concluded from a run
//! under `-Ztrust-verify=on`, where #189 is MASKED because the per-body verifier
//! raises a fatal before `trust_ir_crate_finalize` ever validates the module. Under
//! `-Ztrust-verify=off -Ztrust-ir-lower=on` the same shape reproduces #189 in two
//! lines. A strict-policy run proves nothing about module validation.
//!
//! #189 is now FIXED (`fix(#189)`, the foreach carrier-havoc refusal) and pinned by
//! `trust_ir_lower_foreach_carrier_havoc.rs`. What remains here is the sequence gap
//! itself, which is a separate and larger defect: this file still fails because
//! lowering cannot model `Vec<T>`, not because of a type mismatch.
//!
//! WHEN THIS STARTS PASSING, that is the win — delete the `known-bug` header,
//! turn it into a `check-pass`, and re-measure nn and ny, which are the two
//! repos waiting on it.

pub struct SequenceFields {
    pub scale: f32,
    pub lower: Vec<f32>,
    pub upper: Vec<f32>,
}

pub fn build() -> SequenceFields {
    SequenceFields { scale: 0.01, lower: vec![1.0], upper: vec![2.0] }
}
