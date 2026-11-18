// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::Nat;

impl Nat {
    /// Natural exponentiation, with `0 ^ 0 = 1` as in Lean's Nat.pow.
    ///
    /// The exponent is not converted to a machine word and the kernel's
    /// reduction budget is not a runtime limit. Allocation failure remains a
    /// resource failure, never a wrapped exponent or an invented result.
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn pow(&self, exponent: &Self) -> Self {
        if exponent.is_zero() {
            return Self::one();
        }
        if self.is_zero() {
            return Self::ZERO;
        }
        if self.to_u64() == Some(1) {
            return Self::one();
        }
        let mut result = Self::one();
        let mut power = self.clone();
        for (i, &limb) in exponent.limbs.iter().enumerate() {
            let last = i + 1 == exponent.limbs.len();
            let width = if last { 64 - limb.leading_zeros() } else { 64 };
            for bit in 0..width {
                if limb & (1u64 << bit) != 0 {
                    result = result.mul(&power);
                }
                // Do not square after the last exponent bit: that would
                // allocate an unused, potentially much larger natural.
                if !last || bit + 1 < width {
                    power = power.mul(&power);
                }
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use super::*;

    #[test]
    fn powers_agree_with_u128_where_it_is_an_independent_oracle() {
        for base in 0u64..20 {
            for exponent in 0u32..12 {
                let expected = u128::from(base).pow(exponent);
                assert_eq!(
                    Nat::from_u64(base).pow(&Nat::from_u64(u64::from(exponent))),
                    Nat::from_limbs(vec![expected as u64, (expected >> 64) as u64]),
                );
            }
        }
    }

    #[test]
    fn trivial_bases_accept_natural_exponents_above_u64() {
        let huge = Nat::from_limbs(vec![0, 1]);
        assert_eq!(Nat::ZERO.pow(&Nat::ZERO), Nat::one());
        assert_eq!(Nat::ZERO.pow(&huge), Nat::ZERO);
        assert_eq!(Nat::one().pow(&huge), Nat::one());
    }

    #[test]
    fn runtime_power_has_no_kernel_reduction_ceiling() {
        let mut expected = vec![0; 16];
        expected.push(1);
        assert_eq!(Nat::from_u64(2).pow(&Nat::from_u64(1024)).limbs(), expected);
    }
}
