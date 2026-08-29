// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Arithmetic modulo the group order
//! `L = 2^252 + 27742317777372353535851937790883648493`.
//!
//! `L` is fixed by **RFC 8032 §5.1 Table 1** ("order of edwards25519 in
//! [RFC7748]"). Three operations are needed and no more:
//!
//! * **`s mod L` for a 512-bit `s`** — RFC 8032 §5.1.5 step 1 and §5.1.6 steps
//!   2 and 4 all reduce a SHA-512 digest, i.e. a 64-octet little-endian
//!   integer, into `Z/LZ`.
//! * **`(r + k·s) mod L`** — RFC 8032 §5.1.6 step 5, the `S` half of the
//!   signature.
//! * **`s < L`** — RFC 8032 §5.1.7, which requires `S` to decode "as an
//!   integer in the range `0 <= s < L`" and calls the signature invalid
//!   otherwise. This is the malleability check.
//!
//! # Why bitwise long division rather than Montgomery or Barrett
//!
//! The fast reductions mod `L` (Montgomery with 52-bit limbs, or Barrett with
//! a precomputed `floor(2^512 / L)`) each carry a precomputed magic constant
//! and a correctness argument that has to be reproduced, not read. This module
//! reduces by restoring long division instead: 512 iterations of "shift one bit
//! in, conditionally subtract `L`". It is the textbook algorithm, its
//! invariant (`0 <= r < L` at every step) is checkable by inspection, it needs
//! no constant beyond `L` itself, and it is constant time without effort
//! because the conditional subtract is a masked select.
//!
//! The cost is real and bounded: about 512 × 4 word operations per reduction,
//! three reductions per signature. That is nowhere near the scalar
//! multiplication that dominates either operation.
//!
//! # Constant time
//!
//! Every routine here is constant time in its inputs. `s` (the secret scalar)
//! and `r` (the per-signature nonce) both flow through [`Scalar::mul_add`], so
//! this is not optional. The one exception is
//! [`Scalar::from_canonical_bytes`], which returns an `Option` and whose input
//! — the `S` half of a candidate signature — is public.

/// `L = 2^252 + 27742317777372353535851937790883648493`, little-endian 64-bit
/// limbs. RFC 8032 §5.1 Table 1.
pub(crate) const L: [u64; 4] =
    [0x5812_631a_5cf5_d3ed, 0x14de_f9de_a2f7_9cd6, 0x0000_0000_0000_0000, 0x1000_0000_0000_0000];

/// An integer in `[0, L)`.
#[derive(Copy, Clone)]
pub(crate) struct Scalar(pub(crate) [u64; 4]);

/// `a - b` over four limbs, returning the difference and the final borrow.
/// The difference is only meaningful when the borrow is 0.
fn sub_borrow(a: &[u64; 4], b: &[u64; 4]) -> ([u64; 4], u64) {
    let mut out = [0u64; 4];
    let mut borrow = 0u64;
    for i in 0..4 {
        let (d, b1) = a[i].overflowing_sub(b[i]);
        let (d, b2) = d.overflowing_sub(borrow);
        out[i] = d;
        borrow = (b1 as u64) | (b2 as u64);
    }
    (out, borrow)
}

impl Scalar {
    /// Reduce a 512-bit little-endian integer modulo `L`.
    ///
    /// Restoring long division, most significant bit first. The remainder `r`
    /// satisfies `0 <= r < L < 2^253` at the top of each iteration, so
    /// `2r + bit < 2^254` and the shift cannot carry out of four limbs — the
    /// `debug_assert` records that, and it is the only place the bound matters.
    pub(crate) fn reduce_wide(x: &[u64; 8]) -> Scalar {
        let mut r = [0u64; 4];
        for i in (0..512).rev() {
            let bit = (x[i / 64] >> (i % 64)) & 1;

            // r <- 2r + bit
            let mut carry = bit;
            for limb in r.iter_mut() {
                let next = *limb >> 63;
                *limb = (*limb << 1) | carry;
                carry = next;
            }
            debug_assert_eq!(carry, 0, "remainder exceeded 2^255; L bound violated");

            // r <- r - L if r >= L. borrow == 0 means the subtraction held.
            let (diff, borrow) = sub_borrow(&r, &L);
            let mask = borrow.wrapping_sub(1);
            for k in 0..4 {
                r[k] = (r[k] & !mask) | (diff[k] & mask);
            }
        }
        Scalar(r)
    }

    /// Reduce a 64-octet little-endian integer modulo `L`.
    ///
    /// This is the `interpret the 64-octet digest as a little-endian integer
    /// and reduce modulo L` step of RFC 8032 §5.1.5 (step 1) and §5.1.6
    /// (steps 2 and 4).
    pub(crate) fn from_bytes_mod_order_wide(bytes: &[u8; 64]) -> Scalar {
        let mut limbs = [0u64; 8];
        for (i, limb) in limbs.iter_mut().enumerate() {
            let mut chunk = [0u8; 8];
            chunk.copy_from_slice(&bytes[8 * i..8 * i + 8]);
            *limb = u64::from_le_bytes(chunk);
        }
        Scalar::reduce_wide(&limbs)
    }

    /// Decode 32 octets as an integer in `[0, L)`, or `None` if it is `>= L`.
    ///
    /// RFC 8032 §5.1.7: "Decode the second half as an integer S, in the range
    /// `0 <= s < L`. [...] If any of the decodings fail (including S being out
    /// of range), the signature is invalid."
    pub(crate) fn from_canonical_bytes(bytes: &[u8; 32]) -> Option<Scalar> {
        let mut limbs = [0u64; 4];
        for (i, limb) in limbs.iter_mut().enumerate() {
            let mut chunk = [0u8; 8];
            chunk.copy_from_slice(&bytes[8 * i..8 * i + 8]);
            *limb = u64::from_le_bytes(chunk);
        }
        let (_, borrow) = sub_borrow(&limbs, &L);
        // borrow == 1 means limbs < L.
        if borrow == 1 { Some(Scalar(limbs)) } else { None }
    }

    /// `(a·b + c) mod L`. RFC 8032 §5.1.6 step 5: `S = (r + k·s) mod L`.
    ///
    /// `a·b` is formed exactly as a 512-bit schoolbook product and `c` is added
    /// into it before a single reduction, so no intermediate is itself reduced
    /// — `a·b + c < L² + L < 2^505` cannot overflow the 512-bit accumulator.
    ///
    /// `a` is permitted to be an unreduced 256-bit integer: the caller passes
    /// the *clamped* secret scalar, which RFC 8032 §5.1.5 defines as a 255-bit
    /// value that may exceed `L`. The product bound still holds:
    /// `2^255 · L + L < 2^508`.
    pub(crate) fn mul_add(a: &[u64; 4], b: &Scalar, c: &Scalar) -> Scalar {
        // Operand scanning. The accumulator step is
        // `w[i+j] + a[i]·b[j] + carry`, whose maximum is exactly `2^128 - 1`
        // (`(2^64-1) + (2^64-1)² + (2^64-1)`), so a `u128` holds it with no
        // slack and no second carry word. Column-summing the products first
        // would NOT fit: four products of `(2^64-1)²` overflow a `u128`.
        let mut wide = [0u64; 8];
        for i in 0..4 {
            let mut carry = 0u128;
            for j in 0..4 {
                let t = (wide[i + j] as u128) + (a[i] as u128) * (b.0[j] as u128) + carry;
                wide[i + j] = t as u64;
                carry = t >> 64;
            }
            // Untouched by rows 0..i, so this is a write, not an accumulate.
            wide[i + 4] = carry as u64;
        }

        // wide += c
        let mut add_carry = 0u64;
        for i in 0..8 {
            let addend = if i < 4 { c.0[i] } else { 0 };
            let (s1, o1) = wide[i].overflowing_add(addend);
            let (s2, o2) = s1.overflowing_add(add_carry);
            wide[i] = s2;
            add_carry = (o1 as u64) | (o2 as u64);
        }
        debug_assert_eq!(add_carry, 0, "512-bit accumulator overflowed on add");

        Scalar::reduce_wide(&wide)
    }

    /// The little-endian 32-octet encoding. Always canonical, because the type
    /// invariant is `< L`.
    pub(crate) fn to_bytes(self) -> [u8; 32] {
        let mut out = [0u8; 32];
        for (i, limb) in self.0.iter().enumerate() {
            out[8 * i..8 * i + 8].copy_from_slice(&limb.to_le_bytes());
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `L` itself, `L-1`, `L+1` and `2^512-1` — the values a reduction is most
    /// likely to be wrong on.
    #[test]
    fn boundary_values_reduce_correctly() {
        let mut l_bytes = [0u8; 64];
        for (i, limb) in L.iter().enumerate() {
            l_bytes[8 * i..8 * i + 8].copy_from_slice(&limb.to_le_bytes());
        }

        // L mod L == 0
        assert_eq!(Scalar::from_bytes_mod_order_wide(&l_bytes).to_bytes(), [0u8; 32]);

        // (L - 1) mod L == L - 1
        let mut lm1 = l_bytes;
        lm1[0] -= 1;
        assert_eq!(&Scalar::from_bytes_mod_order_wide(&lm1).to_bytes()[..], &lm1[..32]);

        // (L + 1) mod L == 1
        let mut lp1 = l_bytes;
        lp1[0] += 1;
        let mut one = [0u8; 32];
        one[0] = 1;
        assert_eq!(Scalar::from_bytes_mod_order_wide(&lp1).to_bytes(), one);

        // 2L mod L == 0
        let mut two_l = [0u64; 8];
        let mut carry = 0u64;
        for i in 0..4 {
            two_l[i] = (L[i] << 1) | carry;
            carry = L[i] >> 63;
        }
        two_l[4] = carry;
        assert_eq!(Scalar::reduce_wide(&two_l).to_bytes(), [0u8; 32]);

        // The all-ones 512-bit integer must still land in [0, L).
        let max = Scalar::reduce_wide(&[u64::MAX; 8]);
        let (_, borrow) = sub_borrow(&max.0, &L);
        assert_eq!(borrow, 1, "reduce_wide(2^512-1) is not < L");
    }

    /// The **high half** of the 512-bit input actually participates.
    ///
    /// Every other assertion in this module uses values whose top limbs are
    /// zero, or only checks that the result is in range — and "in range" stays
    /// true if the reduction silently ignores high bits. Measured: shortening
    /// `reduce_wide`'s bit loop from 512 to 511 left every other scalar test
    /// passing, and was caught only by the RFC vectors and the differential.
    /// These two values are computed independently in Python's
    /// arbitrary-precision integers, so they share no code with this crate.
    #[test]
    fn reduce_wide_uses_the_whole_input() {
        // 2^511 mod L. Non-zero, so a dropped top bit turns this into 0.
        let two_511 = Scalar::reduce_wide(&[0, 0, 0, 0, 0, 0, 0, 1 << 63]);
        assert_ne!(two_511.to_bytes(), [0u8; 32], "the top bit of the input was dropped");
        assert_eq!(
            two_511.to_bytes(),
            [
                0x77, 0xf1, 0xc8, 0xd0, 0x7e, 0x3a, 0x0c, 0xfe, 0x0e, 0x98, 0xbe, 0x05, 0xc3, 0x8a,
                0x76, 0xf2, 0x32, 0xdf, 0xfa, 0x0b, 0xe9, 0x39, 0x76, 0xe7, 0x1e, 0x4d, 0x18, 0xbe,
                0x8d, 0xa0, 0xcc, 0x09,
            ],
            "2^511 mod L"
        );

        // (2^512 - 1) mod L.
        assert_eq!(
            Scalar::reduce_wide(&[u64::MAX; 8]).to_bytes(),
            [
                0x00, 0x0f, 0x9c, 0x44, 0xe3, 0x11, 0x06, 0xa4, 0x47, 0x93, 0x85, 0x68, 0xa7, 0x1b,
                0x0e, 0xd0, 0x65, 0xbe, 0xf5, 0x17, 0xd2, 0x73, 0xec, 0xce, 0x3d, 0x9a, 0x30, 0x7c,
                0x1b, 0x41, 0x99, 0x03,
            ],
            "(2^512-1) mod L"
        );
    }

    /// `mul_add` with operands that fill every limb, cross-checked against an
    /// independent computation.
    ///
    /// `a = 2^255 - 1` is deliberately larger than `L` — the caller passes the
    /// clamped secret scalar, which is unreduced — so this also pins the
    /// documented precondition that `a` need not be in `[0, L)`.
    #[test]
    fn mul_add_matches_an_independent_computation_at_full_width() {
        let a = [u64::MAX, u64::MAX, u64::MAX, u64::MAX >> 1]; // 2^255 - 1
        let mut b = L;
        b[0] -= 1; // L - 1
        let mut c = L;
        c[0] -= 2; // L - 2
        assert_eq!(
            Scalar::mul_add(&a, &Scalar(b), &Scalar(c)).to_bytes(),
            [
                0x67, 0x9f, 0xae, 0xe7, 0xd2, 0x18, 0x93, 0xc0, 0xb2, 0xe6, 0xbc, 0x17, 0xf5, 0xce,
                0xf7, 0xa6, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00,
            ],
            "((2^255-1)(L-1) + (L-2)) mod L"
        );
    }

    #[test]
    fn from_canonical_bytes_is_the_malleability_gate() {
        let mut l_bytes = [0u8; 32];
        for (i, limb) in L.iter().enumerate() {
            l_bytes[8 * i..8 * i + 8].copy_from_slice(&limb.to_le_bytes());
        }
        // L is rejected; L-1 is accepted.
        assert!(Scalar::from_canonical_bytes(&l_bytes).is_none());
        let mut lm1 = l_bytes;
        lm1[0] -= 1;
        assert!(Scalar::from_canonical_bytes(&lm1).is_some());
        // 2^255-ish values with the top bits set are rejected.
        assert!(Scalar::from_canonical_bytes(&[0xff; 32]).is_none());
        assert!(Scalar::from_canonical_bytes(&[0u8; 32]).is_some());
    }

    #[test]
    fn mul_add_matches_schoolbook_on_small_values() {
        // (a·b + c) for small a, b, c is just a·b + c, no reduction.
        for a in 0u64..8 {
            for b in 0u64..8 {
                for c in 0u64..8 {
                    let got = Scalar::mul_add(
                        &[a, 0, 0, 0],
                        &Scalar([b, 0, 0, 0]),
                        &Scalar([c, 0, 0, 0]),
                    );
                    let mut want = [0u8; 32];
                    want[..8].copy_from_slice(&(a * b + c).to_le_bytes());
                    assert_eq!(got.to_bytes(), want, "{a}·{b}+{c}");
                }
            }
        }
    }

    #[test]
    fn mul_add_reduces_at_the_boundary() {
        // (L-1)·1 + 1 ≡ 0 (mod L).
        let mut lm1 = L;
        lm1[0] -= 1;
        let one = Scalar([1, 0, 0, 0]);
        let got = Scalar::mul_add(&lm1, &one, &one);
        assert_eq!(got.to_bytes(), [0u8; 32]);

        // L·anything + c ≡ c.
        let c = Scalar([12345, 0, 0, 0]);
        let got = Scalar::mul_add(&L, &Scalar([7, 0, 0, 0]), &c);
        assert_eq!(got.to_bytes(), c.to_bytes());
    }
}
