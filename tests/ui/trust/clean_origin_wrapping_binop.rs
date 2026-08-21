//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **I5 — THE WRAPPING-BINOP EMISSION, RUN.**
//! (`CleanOriginShape::WrappingBinOp`, the second emittable Clean-origin body
//! shape; `crates/trust-clean-origin/src/emit.rs`.)
//!
//! `clean_origin_call_parity.rs` runs the Projection emission; this file runs
//! the arithmetic one. Every value asserted below DISTINGUISHES wrapping from
//! either checked or saturating arithmetic, so a green run pins the emitted
//! semantics and not merely that a call linked:
//!
//! * `wsum(u64::MAX, 1) == 0` — u64 wrap-around at the top;
//! * `wdec(0) == u64::MAX` — u64 wrap-around at the bottom, through a NUMERAL
//!   operand (the case the fast-lane probes a4–a6 put to the kernel first);
//! * `bsum(200, 100) == 44` — the u8 witness `200 + 100 = 300 ≡ 44 (mod 256)`,
//!   the same known counterexample the checked-pair rows pin in docs/TCB.md;
//! * `W == 13` — CTFE traverses the gate AND interprets the emitted Call
//!   (`wrapping_add` is `const fn` in core), so the const lane is measured,
//!   not assumed.
//!
//! `-Z trust-verify=off` is the point, not a convenience: the faithfulness
//! gate is a compilation-correctness check, deliberately NOT behind any
//! verification switch, and this fixture would be worthless if the flag could
//! disable the machinery it measures.

mod m {
    clean {
        def wsum (a : UInt64) (b : UInt64) : UInt64 := a + b
        def wdec (a : UInt64) : UInt64 := a - 1
        def bsum (a : UInt8) (b : UInt8) : UInt8 := a + b
    }
}

// CTFE: the const lane goes through `mir_for_ctfe`, whose only source of a
// Clean-origin body is the gated emission.
const W: u64 = crate::m::wsum(6, 7);

fn main() {
    assert_eq!(m::wsum(2, 3), 5, "unwrapped addition must still be addition");
    assert_eq!(m::wsum(u64::MAX, 1), 0, "WRAPPED: the emitted `+` must be wrapping_add");
    assert_eq!(m::wdec(0), u64::MAX, "WRAPPED, numeral operand: `a - 1` at a = 0");
    assert_eq!(m::bsum(200, 100), 44, "WRAPPED at u8: 200 + 100 = 300 = 44 mod 256");
    assert_eq!(W, 13, "CTFE of the emitted Call must agree with the runtime value");
}
