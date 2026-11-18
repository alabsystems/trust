// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Lean Nat bit operations. Counts are naturals, not truncated machine words.

use alloc::vec::Vec;

use crate::Nat;

impl Nat {
    /// Bitwise conjunction, with the shorter operand zero-extended.
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn land(&self, other: &Self) -> Self {
        Self::from_limbs(self.limbs.iter().zip(&other.limbs).map(|(a, b)| a & b).collect())
    }

    /// Bitwise disjunction, with both operands zero-extended.
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn lor(&self, other: &Self) -> Self {
        Self::from_limbs(
            (0..self.limbs.len().max(other.limbs.len()))
                .map(|i| {
                    self.limbs.get(i).copied().unwrap_or(0)
                        | other.limbs.get(i).copied().unwrap_or(0)
                })
                .collect(),
        )
    }

    /// Bitwise exclusive disjunction, with both operands zero-extended.
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn xor(&self, other: &Self) -> Self {
        Self::from_limbs(
            (0..self.limbs.len().max(other.limbs.len()))
                .map(|i| {
                    self.limbs.get(i).copied().unwrap_or(0)
                        ^ other.limbs.get(i).copied().unwrap_or(0)
                })
                .collect(),
        )
    }

    /// Multiply by `2 ^ amount`, with an arbitrary-precision natural count.
    ///
    /// There is no kernel-reduction bit ceiling here. A nonzero result that
    /// cannot fit addressable allocation storage fails, rather than wrapping
    /// the count or returning a different natural. Zero needs no allocation
    /// regardless of the size of the count.
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn shift_left(&self, amount: &Self) -> Self {
        if self.is_zero() {
            return Self::ZERO;
        }
        let (words, bits) = shift_parts(amount)
            .expect("Nat::shift_left: result exceeds addressable allocation storage");
        let extra = usize::from(bits != 0 && self.limbs.last().unwrap() >> (64 - bits) != 0);
        let capacity = words
            .checked_add(self.limbs.len())
            .and_then(|len| len.checked_add(extra))
            .expect("Nat::shift_left: result exceeds addressable allocation storage");
        let mut limbs = Vec::with_capacity(capacity);
        limbs.resize(words, 0);
        if bits == 0 {
            limbs.extend_from_slice(&self.limbs);
        } else {
            let mut carry = 0;
            for &limb in &self.limbs {
                limbs.push((limb << bits) | carry);
                carry = limb >> (64 - bits);
            }
            if carry != 0 {
                limbs.push(carry);
            }
        }
        Self::from_limbs(limbs)
    }

    /// Divide by `2 ^ amount`, rounding down, with a natural-valued count.
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn shift_right(&self, amount: &Self) -> Self {
        let Some((words, bits)) = shift_parts(amount) else {
            // The WORD count exceeds usize::MAX, hence every possible Vec
            // length. This is not a truncation of the natural shift amount.
            return Self::ZERO;
        };
        if words >= self.limbs.len() {
            return Self::ZERO;
        }
        let mut limbs = Vec::with_capacity(self.limbs.len() - words);
        for i in words..self.limbs.len() {
            let upper = if bits == 0 {
                0
            } else {
                self.limbs.get(i + 1).copied().unwrap_or(0) << (64 - bits)
            };
            limbs.push((self.limbs[i] >> bits) | upper);
        }
        Self::from_limbs(limbs)
    }
}

/// Split the NATURAL count into whole limbs and remaining bits. Only the
/// quotient by 64 must fit usize; the original count need not fit u64/usize.
/// Checked binary accumulation also works on a 32-bit usize without a cast.
fn shift_parts(amount: &Nat) -> Option<(usize, u32)> {
    let bits = (amount.limbs.first().copied().unwrap_or(0) & 63) as u32;
    let mut words = 0usize;
    for (i, &limb) in amount.limbs.iter().enumerate().rev() {
        let first_bit = if i == 0 { 6 } else { 0 };
        for bit in (first_bit..64).rev() {
            words = words.checked_mul(2)?.checked_add(((limb >> bit) & 1) as usize)?;
        }
    }
    Some((words, bits))
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use super::*;

    #[test]
    fn bit_operations_zero_extend_and_canonicalize() {
        let a = Nat::from_limbs(vec![0xF0, 1]);
        let b = Nat::from_u64(0xCC);
        assert_eq!(a.land(&b).limbs(), &[0xC0]);
        assert_eq!(a.lor(&b).limbs(), &[0xFC, 1]);
        assert_eq!(a.xor(&b).limbs(), &[0x3C, 1]);
        assert_eq!(a.xor(&a), Nat::ZERO);
    }

    #[test]
    fn shifts_cross_words_without_machine_shift_masking() {
        let a = Nat::from_limbs(vec![u64::MAX, 1]);
        assert_eq!(a.shift_left(&Nat::from_u64(1)).limbs(), &[u64::MAX - 1, 3]);
        assert_eq!(a.shift_right(&Nat::from_u64(64)), Nat::from_u64(1));
        assert_eq!(a.shift_left(&Nat::from_u64(64)).limbs(), &[0, u64::MAX, 1]);
        assert_eq!(a.shift_right(&Nat::from_u64(65)), Nat::ZERO);
        for bits in 0..128 {
            let value = 0x1234_5678_9ABC_DEF0u128;
            let n = Nat::from_u64(value as u64);
            let amount = Nat::from_u64(bits);
            let expected = value >> bits;
            assert_eq!(n.shift_right(&amount), Nat::from_u64(expected as u64));
        }
    }

    #[test]
    fn counts_above_u64_are_not_truncated_and_zero_stays_zero() {
        let huge = Nat::from_limbs(vec![0, 1]);
        assert_eq!(Nat::from_u64(7).shift_right(&huge), Nat::ZERO);
        assert_eq!(Nat::ZERO.shift_left(&huge), Nat::ZERO);
        assert_eq!(Nat::ZERO.shift_right(&huge), Nat::ZERO);
        assert_eq!(shift_parts(&huge), usize::try_from(1u64 << 58).ok().map(|n| (n, 0)));
        assert!(shift_parts(&Nat::from_limbs(vec![0, 0, 1])).is_none());
    }

    #[test]
    fn runtime_shifts_have_no_kernel_reduction_ceiling() {
        let shifted = Nat::one().shift_left(&Nat::from_u64(2048));
        let mut expected = vec![0; 32];
        expected.push(1);
        assert_eq!(shifted.limbs(), expected);
        assert_eq!(shifted.shift_right(&Nat::from_u64(2048)), Nat::one());
    }
}
