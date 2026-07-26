// trust-types/bitvector: Bitvector theory types for fixed-width integer operations
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
#![allow(clippy::double_must_use)]

use serde::{Deserialize, Serialize};
use thiserror::Error;

/// A concrete bitvector value with fixed width.
///
/// Values are stored as `u128` and masked to `width` bits.
/// Supports widths from 1 to 128.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BitVector {
    /// Bit width (1..=128).
    width: u32,
    /// Value masked to `width` bits.
    value: u128,
}

/// Bitvector arithmetic/bitwise operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BvOp {
    Add,
    Sub,
    Mul,
    UDiv,
    SDiv,
    URem,
    SRem,
    Shl,
    LShr,
    AShr,
    And,
    Or,
    Xor,
    Not,
}

/// Bitvector comparison operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BvComparison {
    /// Unsigned less-than.
    Ult,
    /// Unsigned less-or-equal.
    Ule,
    /// Unsigned greater-than.
    Ugt,
    /// Unsigned greater-or-equal.
    Uge,
    /// Signed less-than.
    Slt,
    /// Signed less-or-equal.
    Sle,
    /// Signed greater-than.
    Sgt,
    /// Signed greater-or-equal.
    Sge,
}

/// Errors from bitvector operations.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum BvError {
    #[error("width mismatch: left={left}, right={right}")]
    WidthMismatch { left: u32, right: u32 },
    #[error("invalid width {0}: must be 1..=128")]
    InvalidWidth(u32),
    #[error("bitvector op {0:?} is unary-only and cannot be evaluated in the binary path")]
    UnsupportedBinaryOp(BvOp),
    #[error("division by zero (width={0})")]
    DivisionByZero(u32),
    #[error("extract high={high} must be >= low={low} and < width={width}")]
    InvalidExtract { high: u32, low: u32, width: u32 },
    #[error("concat would exceed 128 bits: {left_width} + {right_width}")]
    ConcatOverflow { left_width: u32, right_width: u32 },
    #[error("target width {target} must be >= current width {current}")]
    ExtendNarrowing { target: u32, current: u32 },
}

impl BitVector {
    /// Create a new bitvector, masking `value` to `width` bits.
    pub fn new(width: u32, value: u128) -> Result<Self, BvError> {
        if width == 0 || width > 128 {
            return Err(BvError::InvalidWidth(width));
        }
        Ok(Self { width, value: mask(value, width) })
    }

    /// Bit width.
    #[must_use]
    pub fn width(&self) -> u32 {
        self.width
    }

    /// Unsigned value.
    #[must_use]
    pub fn value(&self) -> u128 {
        self.value
    }

    /// Interpret the value as a signed integer (sign-extended to i128).
    #[must_use]
    pub fn signed_value(&self) -> i128 {
        let sign_bit = 1u128 << (self.width - 1);
        if self.value & sign_bit != 0 {
            // Negative: sign-extend by filling upper bits with 1s.
            (self.value | !mask_all(self.width)) as i128
        } else {
            self.value as i128
        }
    }

    /// Create a zero bitvector of the given width.
    pub fn zero(width: u32) -> Result<Self, BvError> {
        Self::new(width, 0)
    }

    /// Create an all-ones bitvector of the given width.
    pub fn ones(width: u32) -> Result<Self, BvError> {
        if width == 0 || width > 128 {
            return Err(BvError::InvalidWidth(width));
        }
        Ok(Self { width, value: mask_all(width) })
    }
}

/// Mask a value to `width` bits.
fn mask(value: u128, width: u32) -> u128 {
    if width >= 128 { value } else { value & ((1u128 << width) - 1) }
}

/// All-ones mask for `width` bits.
fn mask_all(width: u32) -> u128 {
    if width >= 128 { u128::MAX } else { (1u128 << width) - 1 }
}

/// Validate that two bitvectors have the same width.
pub fn bv_width_check(a: &BitVector, b: &BitVector) -> Result<(), BvError> {
    if a.width() != b.width() {
        Err(BvError::WidthMismatch { left: a.width(), right: b.width() })
    } else {
        Ok(())
    }
}

/// Evaluate a bitvector operation concretely.
///
/// For unary ops (`Not`), only `lhs` is used; `rhs` is ignored.
/// For binary ops, widths must match.
pub fn bv_eval(op: BvOp, lhs: &BitVector, rhs: &BitVector) -> Result<BitVector, BvError> {
    let w = lhs.width();

    // Not is unary — skip width check.
    if matches!(op, BvOp::Not) {
        let result = !lhs.value();
        return BitVector::new(w, result);
    }

    bv_width_check(lhs, rhs)?;

    let a = lhs.value();
    let b = rhs.value();

    let result = match op {
        BvOp::Add => a.wrapping_add(b),
        BvOp::Sub => a.wrapping_sub(b),
        BvOp::Mul => a.wrapping_mul(b),
        BvOp::UDiv => {
            if b == 0 {
                return Err(BvError::DivisionByZero(w));
            }
            a / b
        }
        BvOp::SDiv => {
            if b == 0 {
                return Err(BvError::DivisionByZero(w));
            }
            let sa = lhs.signed_value();
            let sb = rhs.signed_value();
            // Wrap: signed division can overflow (e.g., MIN / -1).
            sa.wrapping_div(sb) as u128
        }
        BvOp::URem => {
            if b == 0 {
                return Err(BvError::DivisionByZero(w));
            }
            a % b
        }
        BvOp::SRem => {
            if b == 0 {
                return Err(BvError::DivisionByZero(w));
            }
            let sa = lhs.signed_value();
            let sb = rhs.signed_value();
            sa.wrapping_rem(sb) as u128
        }
        BvOp::Shl => {
            let shift = b as u32;
            if shift >= w { 0 } else { a << shift }
        }
        BvOp::LShr => {
            let shift = b as u32;
            if shift >= w { 0 } else { a >> shift }
        }
        BvOp::AShr => {
            let shift = b as u32;
            let sa = lhs.signed_value();
            if shift >= w {
                if sa < 0 { mask_all(w) } else { 0 }
            } else {
                // Perform arithmetic shift on the sign-extended value,
                // then mask back to width.
                (sa >> shift) as u128
            }
        }
        BvOp::And => a & b,
        BvOp::Or => a | b,
        BvOp::Xor => a ^ b,
        BvOp::Not => return Err(BvError::UnsupportedBinaryOp(BvOp::Not)),
    };

    BitVector::new(w, result)
}

/// Evaluate a bitvector comparison. Widths must match.
#[must_use]
pub fn bv_compare(cmp: BvComparison, lhs: &BitVector, rhs: &BitVector) -> Result<bool, BvError> {
    bv_width_check(lhs, rhs)?;

    let a = lhs.value();
    let b = rhs.value();
    let sa = lhs.signed_value();
    let sb = rhs.signed_value();

    Ok(match cmp {
        BvComparison::Ult => a < b,
        BvComparison::Ule => a <= b,
        BvComparison::Ugt => a > b,
        BvComparison::Uge => a >= b,
        BvComparison::Slt => sa < sb,
        BvComparison::Sle => sa <= sb,
        BvComparison::Sgt => sa > sb,
        BvComparison::Sge => sa >= sb,
    })
}

/// Zero-extend a bitvector to a wider width (pads with 0s).
pub fn zero_extend(bv: &BitVector, target_width: u32) -> Result<BitVector, BvError> {
    if target_width == 0 || target_width > 128 {
        return Err(BvError::InvalidWidth(target_width));
    }
    if target_width < bv.width() {
        return Err(BvError::ExtendNarrowing { target: target_width, current: bv.width() });
    }
    BitVector::new(target_width, bv.value())
}

/// Sign-extend a bitvector to a wider width (replicates sign bit).
pub fn sign_extend(bv: &BitVector, target_width: u32) -> Result<BitVector, BvError> {
    if target_width == 0 || target_width > 128 {
        return Err(BvError::InvalidWidth(target_width));
    }
    if target_width < bv.width() {
        return Err(BvError::ExtendNarrowing { target: target_width, current: bv.width() });
    }
    // The signed_value() already has proper sign extension to i128.
    // Mask to target width to get the correct representation.
    BitVector::new(target_width, bv.signed_value() as u128)
}

/// Extract bits `[high:low]` (inclusive) from a bitvector.
///
/// Returns a new bitvector of width `high - low + 1`.
pub fn extract(bv: &BitVector, high: u32, low: u32) -> Result<BitVector, BvError> {
    if high < low || high >= bv.width() {
        return Err(BvError::InvalidExtract { high, low, width: bv.width() });
    }
    let new_width = high - low + 1;
    let shifted = bv.value() >> low;
    BitVector::new(new_width, shifted)
}

/// Concatenate two bitvectors: `lhs` becomes the high bits, `rhs` the low bits.
///
/// Result width = `lhs.width() + rhs.width()`.
pub fn concat(lhs: &BitVector, rhs: &BitVector) -> Result<BitVector, BvError> {
    let new_width = lhs.width() + rhs.width();
    if new_width > 128 {
        return Err(BvError::ConcatOverflow { left_width: lhs.width(), right_width: rhs.width() });
    }
    let combined = (lhs.value() << rhs.width()) | rhs.value();
    BitVector::new(new_width, combined)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bitvector_new_masks_value() {
        let bv = BitVector::new(8, 0x1FF).expect("valid width");
        assert_eq!(bv.width(), 8);
        assert_eq!(bv.value(), 0xFF);
    }

    #[test]
    fn test_bitvector_invalid_width_zero() {
        assert!(matches!(BitVector::new(0, 0), Err(BvError::InvalidWidth(0))));
    }

    #[test]
    fn test_bitvector_invalid_width_over_128() {
        assert!(matches!(BitVector::new(129, 0), Err(BvError::InvalidWidth(129))));
    }

    #[test]
    fn test_bitvector_signed_value_negative() {
        // 8-bit 0xFF = -1 signed
        let bv = BitVector::new(8, 0xFF).expect("valid");
        assert_eq!(bv.signed_value(), -1);
    }

    #[test]
    fn test_bitvector_signed_value_positive() {
        let bv = BitVector::new(8, 127).expect("valid");
        assert_eq!(bv.signed_value(), 127);
    }

    #[test]
    fn test_bv_eval_add_wrapping() {
        let a = BitVector::new(8, 200).expect("valid");
        let b = BitVector::new(8, 100).expect("valid");
        let r = bv_eval(BvOp::Add, &a, &b).expect("ok");
        // 200 + 100 = 300, masked to 8 bits = 44
        assert_eq!(r.value(), 44);
        assert_eq!(r.width(), 8);
    }

    #[test]
    fn test_bv_eval_sub() {
        let a = BitVector::new(16, 10).expect("valid");
        let b = BitVector::new(16, 3).expect("valid");
        let r = bv_eval(BvOp::Sub, &a, &b).expect("ok");
        assert_eq!(r.value(), 7);
    }

    #[test]
    fn test_bv_eval_mul() {
        let a = BitVector::new(8, 15).expect("valid");
        let b = BitVector::new(8, 17).expect("valid");
        let r = bv_eval(BvOp::Mul, &a, &b).expect("ok");
        // 15 * 17 = 255
        assert_eq!(r.value(), 255);
    }

    #[test]
    fn test_bv_eval_udiv_and_div_by_zero() {
        let a = BitVector::new(32, 100).expect("valid");
        let b = BitVector::new(32, 7).expect("valid");
        let r = bv_eval(BvOp::UDiv, &a, &b).expect("ok");
        assert_eq!(r.value(), 14); // 100 / 7 = 14

        let zero = BitVector::new(32, 0).expect("valid");
        assert!(matches!(bv_eval(BvOp::UDiv, &a, &zero), Err(BvError::DivisionByZero(32))));
    }

    /// Fidelity for the trust-mc self-verification arm `build_trust_types_bv_eval_div`
    /// (soundness_oracle.rs) + the `self_verification_suite`: the REAL `bv_eval(UDiv)` is TOTAL —
    /// `b == 0` returns `Err(DivisionByZero)` (a value, NOT a panic) and for `b != 0` the `a / b`
    /// cannot divide-by-zero — which is exactly what Trust's discharge PROVES of the model. The
    /// grid includes `b == 0`, the panic boundary the guard protects.
    #[test]
    fn bv_eval_udiv_model_matches_and_is_total() {
        let width = 32;
        let grid = [0u128, 1, 2, 7, 100, 255, 1000, (1u128 << 32) - 1];
        for &av in &grid {
            for &bv in &grid {
                let a = BitVector::new(width, av).expect("valid");
                let b = BitVector::new(width, bv).expect("valid");
                // Executing the real evaluator must NEVER panic, regardless of `b` (incl. b == 0).
                match bv_eval(BvOp::UDiv, &a, &b) {
                    Ok(r) => {
                        // Reached only when b != 0, so `a / b` is itself total here.
                        assert_ne!(bv, 0, "Ok result implies a non-zero divisor");
                        assert_eq!(r.value(), av / bv, "b != 0 ⇒ result is a / b");
                    }
                    Err(BvError::DivisionByZero(w)) => {
                        assert_eq!((w, bv), (width, 0), "DivisionByZero only at b == 0");
                    }
                    Err(other) => panic!("unexpected error from bv_eval(UDiv): {other:?}"),
                }
            }
        }
    }

    #[test]
    fn test_bv_eval_sdiv() {
        // -6 / 2 = -3 in 8-bit signed
        let a = BitVector::new(8, 0xFA).expect("valid"); // -6
        let b = BitVector::new(8, 2).expect("valid");
        let r = bv_eval(BvOp::SDiv, &a, &b).expect("ok");
        assert_eq!(r.signed_value(), -3);
    }

    #[test]
    fn test_bv_eval_shifts() {
        let a = BitVector::new(8, 0x0F).expect("valid");
        let shift = BitVector::new(8, 4).expect("valid");

        let left = bv_eval(BvOp::Shl, &a, &shift).expect("ok");
        assert_eq!(left.value(), 0xF0);

        let right = bv_eval(BvOp::LShr, &a, &shift).expect("ok");
        assert_eq!(right.value(), 0x00);
    }

    #[test]
    fn test_bv_eval_ashr_negative() {
        // 8-bit 0xF0 = -16 signed, AShr by 2 = -4 = 0xFC
        let a = BitVector::new(8, 0xF0).expect("valid");
        let shift = BitVector::new(8, 2).expect("valid");
        let r = bv_eval(BvOp::AShr, &a, &shift).expect("ok");
        assert_eq!(r.value(), 0xFC);
        assert_eq!(r.signed_value(), -4);
    }

    #[test]
    fn test_bv_eval_bitwise() {
        let a = BitVector::new(8, 0xAA).expect("valid");
        let b = BitVector::new(8, 0x55).expect("valid");

        let and = bv_eval(BvOp::And, &a, &b).expect("ok");
        assert_eq!(and.value(), 0x00);

        let or = bv_eval(BvOp::Or, &a, &b).expect("ok");
        assert_eq!(or.value(), 0xFF);

        let xor = bv_eval(BvOp::Xor, &a, &b).expect("ok");
        assert_eq!(xor.value(), 0xFF);
    }

    #[test]
    fn test_bv_eval_not() {
        let a = BitVector::new(8, 0xAA).expect("valid");
        let dummy = BitVector::new(1, 0).expect("valid"); // unused for Not
        let r = bv_eval(BvOp::Not, &a, &dummy).expect("ok");
        assert_eq!(r.value(), 0x55);
    }

    #[test]
    fn test_bv_width_mismatch() {
        let a = BitVector::new(8, 1).expect("valid");
        let b = BitVector::new(16, 1).expect("valid");
        assert!(matches!(
            bv_eval(BvOp::Add, &a, &b),
            Err(BvError::WidthMismatch { left: 8, right: 16 })
        ));
    }

    #[test]
    fn test_bv_compare_unsigned() {
        let a = BitVector::new(8, 200).expect("valid");
        let b = BitVector::new(8, 100).expect("valid");
        assert!(bv_compare(BvComparison::Ugt, &a, &b).expect("ok"));
        assert!(bv_compare(BvComparison::Uge, &a, &b).expect("ok"));
        assert!(bv_compare(BvComparison::Ult, &b, &a).expect("ok"));
        assert!(bv_compare(BvComparison::Ule, &b, &a).expect("ok"));
    }

    #[test]
    fn test_bv_compare_signed() {
        // 200 unsigned in 8-bit = -56 signed; 100 = 100 signed
        let a = BitVector::new(8, 200).expect("valid");
        let b = BitVector::new(8, 100).expect("valid");
        // Signed: -56 < 100
        assert!(bv_compare(BvComparison::Slt, &a, &b).expect("ok"));
        assert!(bv_compare(BvComparison::Sle, &a, &b).expect("ok"));
        assert!(bv_compare(BvComparison::Sgt, &b, &a).expect("ok"));
        assert!(bv_compare(BvComparison::Sge, &b, &a).expect("ok"));
    }

    #[test]
    fn test_zero_extend() {
        let bv = BitVector::new(8, 0xFF).expect("valid");
        let ext = zero_extend(&bv, 16).expect("ok");
        assert_eq!(ext.width(), 16);
        assert_eq!(ext.value(), 0x00FF);
    }

    #[test]
    fn test_sign_extend() {
        // 8-bit 0xFF = -1, sign-extended to 16-bit = 0xFFFF
        let bv = BitVector::new(8, 0xFF).expect("valid");
        let ext = sign_extend(&bv, 16).expect("ok");
        assert_eq!(ext.width(), 16);
        assert_eq!(ext.value(), 0xFFFF);
    }

    #[test]
    fn test_sign_extend_positive() {
        // 8-bit 0x7F = 127, sign-extended to 16-bit = 0x007F
        let bv = BitVector::new(8, 0x7F).expect("valid");
        let ext = sign_extend(&bv, 16).expect("ok");
        assert_eq!(ext.width(), 16);
        assert_eq!(ext.value(), 0x007F);
    }

    #[test]
    fn test_extend_narrowing_error() {
        let bv = BitVector::new(16, 0).expect("valid");
        assert!(matches!(
            zero_extend(&bv, 8),
            Err(BvError::ExtendNarrowing { target: 8, current: 16 })
        ));
        assert!(matches!(
            sign_extend(&bv, 8),
            Err(BvError::ExtendNarrowing { target: 8, current: 16 })
        ));
    }

    #[test]
    fn test_extract_bits() {
        // 16-bit 0xABCD, extract [11:4] = 0xBC
        let bv = BitVector::new(16, 0xABCD).expect("valid");
        let ex = extract(&bv, 11, 4).expect("ok");
        assert_eq!(ex.width(), 8);
        assert_eq!(ex.value(), 0xBC);
    }

    #[test]
    fn test_extract_invalid() {
        let bv = BitVector::new(8, 0xFF).expect("valid");
        assert!(matches!(extract(&bv, 8, 0), Err(BvError::InvalidExtract { .. })));
        assert!(matches!(extract(&bv, 2, 5), Err(BvError::InvalidExtract { .. })));
    }

    #[test]
    fn test_concat() {
        let hi = BitVector::new(8, 0xAB).expect("valid");
        let lo = BitVector::new(8, 0xCD).expect("valid");
        let cat = concat(&hi, &lo).expect("ok");
        assert_eq!(cat.width(), 16);
        assert_eq!(cat.value(), 0xABCD);
    }

    #[test]
    fn test_concat_overflow() {
        let a = BitVector::new(64, 0).expect("valid");
        let b = BitVector::new(65, 0).expect("valid");
        assert!(matches!(concat(&a, &b), Err(BvError::ConcatOverflow { .. })));
    }

    #[test]
    fn test_bitvector_128bit_width() {
        let bv = BitVector::new(128, u128::MAX).expect("valid");
        assert_eq!(bv.width(), 128);
        assert_eq!(bv.value(), u128::MAX);
    }

    #[test]
    fn test_bitvector_1bit_width() {
        let bv = BitVector::new(1, 3).expect("valid");
        assert_eq!(bv.value(), 1); // masked to 1 bit
    }

    /// RUNG 3 (Trust self-verification) — execution-fidelity half. Trust's own discharge
    /// PROVES the guarded shift in `mask_all` panic-free (trust-mc
    /// soundness_oracle::rung3_trust_types_low_mask_guarded_shift_proven_safe, enabled by
    /// the shift-overflow obligation). That proof is about the REAL function only if the
    /// model is faithful — so this runs the actual `mask_all` over a grid INCLUDING the
    /// shift-panic boundary (width == 128) and the u32 extremes, asserting (a) it never
    /// panics (the `width >= 128` guard dominates the `1u128 << width` that would otherwise
    /// trap), and (b) its guard structure matches the model: width >= 128 → all-ones,
    /// width < 128 → `(1<<width) - 1`. Trust proving a real arm of its own verifier crate.
    #[test]
    fn low_mask_model_matches_and_is_total() {
        for width in [0u32, 1, 7, 31, 32, 63, 64, 100, 126, 127, 128, 129, 200, 255, u32::MAX] {
            // The REAL function — must be TOTAL for every width (no shift-overflow panic).
            let got = mask_all(width);
            if width >= 128 {
                assert_eq!(got, u128::MAX, "mask_all guard arm (width>=128) at width={width}");
            } else {
                assert_eq!(
                    got,
                    (1u128 << width) - 1,
                    "mask_all shift arm (width<128) at width={width}"
                );
            }
        }
    }
}
