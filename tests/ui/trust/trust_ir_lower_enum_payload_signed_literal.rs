//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on
//@ edition: 2021
//@ dont-check-compiler-stderr
//@ check-pass
#![crate_type = "lib"]
//! An enum payload's LITERAL pattern constant is sign-extended like every other literal.
//!
//! `const_pat_int` returns the RAW bit pattern (its `signed`/`bits` parameters are unused),
//! so every caller must pass it through `integer_constant_from_bits`. The wave-LP enum
//! payload literal test cast it directly, `Constant::Int(v as i128)`: a `-3` payload for an
//! `i32` field became 4294967293, which `int_value_fits_ty` rejects, and the crate module
//! failed final validation:
//!
//!     trust-ir-lower semantic finalization failed: final Trust-IR module validation
//!     failed [ConstTypeMismatch]: ConstTypeMismatch { location: "function 'f' bb1",
//!     expected: "i32", actual: "int" }
//!
//! First reported by ay's release gate on 2026-09-12 (seal line b2c42b6b19); still
//! reproduced on the sealed `trust-7d5533b2` (main as of 2026-09-23) with the `i32` face
//! below. Under this flag posture the refusal is a spanless WARN, and this file fails on it
//! because the `dont-require-annotations: WARN` waiver is deliberately absent.
//!
//! The wrap is width-independent (`i8`/`i32`/`i64` all failed); a POSITIVE literal, a bare
//! scalar `matches!(x, -3)` and a struct field literal never did. The same cast gave a
//! `u128` payload above `i128::MAX` a negative constant, which is the unsigned face.

pub enum E32 {
    V(i32),
    W,
}

pub fn i32_face(e: &E32) -> bool {
    matches!(e, E32::V(-3))
}

pub enum E8 {
    V(i8),
    W,
}

pub fn i8_face(e: &E8) -> bool {
    matches!(e, E8::V(-128))
}

pub enum E64 {
    V(i64),
    W,
}

pub fn i64_face(e: &E64) -> bool {
    matches!(e, E64::V(-1))
}

pub enum U128 {
    V(u128),
    W,
}

pub fn u128_above_i128_max_face(e: &U128) -> bool {
    matches!(e, U128::V(340_282_366_920_938_463_463_374_607_431_768_211_455))
}

// ── controls: these never failed and must keep lowering ───────────────────────────────

pub fn positive_literal_control(e: &E32) -> bool {
    matches!(e, E32::V(3))
}

pub fn bare_scalar_control(x: i32) -> bool {
    matches!(x, -3)
}
