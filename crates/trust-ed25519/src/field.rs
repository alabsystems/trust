// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Arithmetic in the prime field GF(p), `p = 2^255 - 19`.
//!
//! The field is fixed by **RFC 8032 §5.1 Table 1** ("p of edwards25519 in
//! [RFC7748], i.e. 2^255 - 19") and **RFC 7748 §4.1**.
//!
//! # Why 5 limbs of 51 bits
//!
//! An element is `l0 + l1·2^51 + l2·2^102 + l3·2^153 + l4·2^204`, five `u64`
//! limbs. The alternative usually considered is 10 limbs of 25.5 bits, which
//! exists so that a 32-bit machine can hold every partial product in a `u64`.
//! We do not need that: Rust guarantees `u128` on every target, so the 51-bit
//! radix is available portably and it is the better choice here for two
//! reasons that both bear on *correctness*, not speed:
//!
//! 1. **Half as many carry chains.** Carry propagation is the step where a
//!    hand-written field implementation silently breaks, and near the modulus
//!    is exactly where it breaks. Five limbs means one carry chain of five
//!    steps per multiply instead of ten, and the 10x25.5 representation's
//!    alternating 26/25-bit limb widths are an additional off-by-one surface
//!    that the uniform 51-bit layout does not have.
//! 2. **The headroom is provable by inspection.** Every limb is `< 2^52` on
//!    entry to and exit from every operation here (see [`FieldElement`]'s
//!    invariant), and the bound calculations in each function show the largest
//!    intermediate. With 13 bits of slack above 51 in a `u64` and 18 bits of
//!    slack above 110 in a `u128`, no operation is close to its limit.
//!
//! The cost is that a 32-bit target compiles `u128` multiplication into a
//! libcall. That is a performance argument, and this crate is not on a hot
//! path — `trust-proof-cert` signs and verifies certificates.
//!
//! # The representation is redundant, deliberately
//!
//! Limbs are *not* canonical: many limb vectors denote the same field element
//! (`p` and `0`, for instance, are both representable). That is what makes the
//! carry chains cheap. Canonicality is imposed at exactly one place,
//! [`FieldElement::to_bytes`], which is therefore the only function here whose
//! correctness the boundary tests can observe directly — hence
//! `boundary_values_reduce_canonically` below drives `p-1`, `p`, `p+1` and
//! `2p-1` through it.
//!
//! # Constant time
//!
//! Every function in this module is constant time with respect to the *values*
//! of its inputs: no branch and no memory index depends on a limb. [`pow`] is
//! constant time with respect to its base; its schedule depends on the
//! exponent, which is always one of the two public compile-time constants in
//! this file.

/// `2^51 - 1`, the limb mask.
const LOW_51: u64 = (1u64 << 51) - 1;

/// `16·p`, limb by limb, used by [`FieldElement::sub`] to keep the subtraction
/// from underflowing. `16·p ≡ 0 (mod p)`, and every limb of it exceeds `2^54`,
/// which is the loosest input this module ever produces (see the type
/// invariant), so `a_i + 16p_i - b_i` cannot wrap.
const SIXTEEN_P: [u64; 5] = [
    36028797018963664, // 16·(2^51 - 19) = 2^55 - 304
    36028797018963952, // 16·(2^51 -  1) = 2^55 -  16
    36028797018963952,
    36028797018963952,
    36028797018963952,
];

/// `p - 2`, the inversion exponent (RFC 8032 §5.1.1: "for inversion modulo p,
/// it is recommended to use the identity `x^-1 = x^(p-2) (mod p)`").
/// Little-endian 64-bit limbs of `2^255 - 21`.
const P_MINUS_2: [u64; 4] =
    [0xffff_ffff_ffff_ffeb, 0xffff_ffff_ffff_ffff, 0xffff_ffff_ffff_ffff, 0x7fff_ffff_ffff_ffff];

/// `(p - 5) / 8 = 2^252 - 3`, the square-root exponent for `p ≡ 5 (mod 8)`
/// (RFC 8032 §5.1.1: "first compute the candidate root `x = a^((p+3)/8)`",
/// which this crate evaluates in the `u·v³·(u·v⁷)^((p-5)/8)` form of §5.1.3).
const P_MINUS_5_DIV_8: [u64; 4] =
    [0xffff_ffff_ffff_fffd, 0xffff_ffff_ffff_ffff, 0xffff_ffff_ffff_ffff, 0x0fff_ffff_ffff_ffff];

/// An element of GF(2^255 - 19).
///
/// # Invariant
///
/// Every limb of every `FieldElement` produced by this module is `< 2^52`.
/// Each operation states the largest intermediate it forms and re-establishes
/// the invariant before returning; the invariant is what lets [`mul`] bound its
/// `u128` accumulators without a further reduction step.
///
/// [`mul`]: FieldElement::mul
#[derive(Copy, Clone)]
pub(crate) struct FieldElement(pub(crate) [u64; 5]);

impl FieldElement {
    pub(crate) const ZERO: FieldElement = FieldElement([0, 0, 0, 0, 0]);
    pub(crate) const ONE: FieldElement = FieldElement([1, 0, 0, 0, 0]);

    /// `p - 1`, i.e. `-1`. Test-only: the implementation reaches `-1` through
    /// [`FieldElement::neg`], never through a table.
    #[cfg(test)]
    pub(crate) const MINUS_ONE: FieldElement = FieldElement([
        0x7ffffffffffec,
        0x7ffffffffffff,
        0x7ffffffffffff,
        0x7ffffffffffff,
        0x7ffffffffffff,
    ]);

    /// One carry pass with the `2^255 ≡ 19 (mod p)` fold.
    ///
    /// Precondition: every limb `< 2^59`. (Callers here stay under `2^56`.) The
    /// pass carries limb `i` into limb `i+1`, folds the carry out of limb 4
    /// back into limb 0 multiplied by 19, and carries that once more, so on
    /// return limbs 0, 2, 3, 4 are `< 2^51` and limb 1 is `< 2^51 + 2^8` —
    /// comfortably inside the type invariant.
    fn carry_pass(mut l: [u64; 5]) -> FieldElement {
        l[1] += l[0] >> 51;
        l[0] &= LOW_51;
        l[2] += l[1] >> 51;
        l[1] &= LOW_51;
        l[3] += l[2] >> 51;
        l[2] &= LOW_51;
        l[4] += l[3] >> 51;
        l[3] &= LOW_51;
        // 2^255 ≡ 19 (mod p): the bits above limb 4 re-enter at limb 0 × 19.
        l[0] += 19 * (l[4] >> 51);
        l[4] &= LOW_51;
        l[1] += l[0] >> 51;
        l[0] &= LOW_51;
        FieldElement(l)
    }

    /// Field addition.
    ///
    /// Inputs satisfy the invariant (`< 2^52`), so each sum is `< 2^53` and one
    /// carry pass restores it.
    pub(crate) fn add(&self, rhs: &FieldElement) -> FieldElement {
        let (a, b) = (&self.0, &rhs.0);
        Self::carry_pass([a[0] + b[0], a[1] + b[1], a[2] + b[2], a[3] + b[3], a[4] + b[4]])
    }

    /// Field subtraction, as `a + 16p - b`.
    ///
    /// `16p` is added first so the limb-wise difference cannot underflow: every
    /// limb of `16p` is `> 2^54` and every limb of `b` is `< 2^52`. The largest
    /// intermediate is `2^52 + 2^55 < 2^56`, inside `carry_pass`'s precondition.
    pub(crate) fn sub(&self, rhs: &FieldElement) -> FieldElement {
        let (a, b) = (&self.0, &rhs.0);
        Self::carry_pass([
            a[0] + SIXTEEN_P[0] - b[0],
            a[1] + SIXTEEN_P[1] - b[1],
            a[2] + SIXTEEN_P[2] - b[2],
            a[3] + SIXTEEN_P[3] - b[3],
            a[4] + SIXTEEN_P[4] - b[4],
        ])
    }

    /// Field negation.
    pub(crate) fn neg(&self) -> FieldElement {
        FieldElement::ZERO.sub(self)
    }

    /// Field multiplication.
    ///
    /// Schoolbook over five limbs with the `2^255 ≡ 19` fold applied to the
    /// five high columns, so the product lands back in five limbs directly.
    ///
    /// # Bounds
    ///
    /// With every input limb `< 2^52`, each `a_i·b_j < 2^104`. The widest
    /// column is `c0 = a0b0 + 19(a1b4 + a2b3 + a3b2 + a4b1)`, i.e. at most
    /// `77·2^104 < 2^111` — 17 bits of `u128` headroom. The sequential carry
    /// chain then leaves `carry = c4 >> 51 < 2^56`, so `19·carry < 2^60` fits
    /// the `u64` accumulator in `out[0]`, and the final short carry restores
    /// the type invariant.
    pub(crate) fn mul(&self, rhs: &FieldElement) -> FieldElement {
        const M: u128 = (1u128 << 51) - 1;

        let a: [u128; 5] = [
            self.0[0] as u128,
            self.0[1] as u128,
            self.0[2] as u128,
            self.0[3] as u128,
            self.0[4] as u128,
        ];
        let b: [u128; 5] = [
            rhs.0[0] as u128,
            rhs.0[1] as u128,
            rhs.0[2] as u128,
            rhs.0[3] as u128,
            rhs.0[4] as u128,
        ];

        let c0 = a[0] * b[0] + 19 * (a[1] * b[4] + a[2] * b[3] + a[3] * b[2] + a[4] * b[1]);
        let mut c1 = a[0] * b[1] + a[1] * b[0] + 19 * (a[2] * b[4] + a[3] * b[3] + a[4] * b[2]);
        let mut c2 = a[0] * b[2] + a[1] * b[1] + a[2] * b[0] + 19 * (a[3] * b[4] + a[4] * b[3]);
        let mut c3 = a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0] + 19 * (a[4] * b[4]);
        let mut c4 = a[0] * b[4] + a[1] * b[3] + a[2] * b[2] + a[3] * b[1] + a[4] * b[0];

        let mut out = [0u64; 5];
        out[0] = (c0 & M) as u64;
        c1 += c0 >> 51;
        out[1] = (c1 & M) as u64;
        c2 += c1 >> 51;
        out[2] = (c2 & M) as u64;
        c3 += c2 >> 51;
        out[3] = (c3 & M) as u64;
        c4 += c3 >> 51;
        out[4] = (c4 & M) as u64;

        out[0] += 19 * ((c4 >> 51) as u64);
        out[1] += out[0] >> 51;
        out[0] &= LOW_51;
        FieldElement(out)
    }

    /// Field squaring.
    ///
    /// Deliberately *not* a specialised routine. A dedicated square saves about
    /// a third of the partial products, and it is a second, differently-shaped
    /// carry chain to get right. On this crate's paths (a few hundred squarings
    /// per signature) that trade is not worth an independent correctness
    /// obligation.
    pub(crate) fn square(&self) -> FieldElement {
        self.mul(self)
    }

    /// `self^exp`, square-and-multiply, most-significant bit first.
    ///
    /// `exp` is always a public compile-time constant in this crate
    /// ([`P_MINUS_2`] or [`P_MINUS_5_DIV_8`]), so the schedule leaks nothing;
    /// the multiply is nevertheless unconditional and selected, so the trace is
    /// identical for every exponent of the same length.
    fn pow(&self, exp: &[u64; 4]) -> FieldElement {
        let mut acc = FieldElement::ONE;
        for i in (0..256).rev() {
            acc = acc.square();
            let bit = ((exp[i / 64] >> (i % 64)) & 1) as u64;
            let prod = acc.mul(self);
            acc = FieldElement::conditional_select(&acc, &prod, bit);
        }
        acc
    }

    /// Multiplicative inverse, `x^(p-2)` (RFC 8032 §5.1.1).
    ///
    /// `0.invert() == 0`, which is what the exponentiation yields. RFC 8032
    /// notes inverting zero "should never happen"; the only caller here is
    /// point compression, whose `Z` is never zero.
    pub(crate) fn invert(&self) -> FieldElement {
        self.pow(&P_MINUS_2)
    }

    /// The square root of `u/v`, per **RFC 8032 §5.1.1 / §5.1.3**.
    ///
    /// Returns `(1, r)` when `r² · v == u`, and `(0, r)` — with `r` meaningless
    /// — when `u/v` is not a square. Since `p ≡ 5 (mod 8)`, the candidate root
    /// is `(u/v)^((p+3)/8)`, evaluated without an inversion as
    /// `u·v³·(u·v⁷)^((p-5)/8)`; if that candidate squares to `-u/v` instead,
    /// multiplying by `sqrt(-1)` corrects it, which is exactly the three-case
    /// analysis §5.1.1 spells out.
    ///
    /// Both branches are taken and one is selected, so no timing signal depends
    /// on which case held.
    pub(crate) fn sqrt_ratio(
        u: &FieldElement,
        v: &FieldElement,
        sqrt_m1: &FieldElement,
    ) -> (u64, FieldElement) {
        let v2 = v.square();
        let v3 = v2.mul(v);
        let v6 = v3.square();
        let v7 = v6.mul(v);

        let uv7 = u.mul(&v7);
        let mut r = u.mul(&v3).mul(&uv7.pow(&P_MINUS_5_DIV_8));

        let check = v.mul(&r.square());
        let correct = check.ct_eq(u);
        let flipped = check.ct_eq(&u.neg());

        let r_times_i = r.mul(sqrt_m1);
        r = FieldElement::conditional_select(&r, &r_times_i, flipped);

        (correct | flipped, r)
    }

    /// `b` if `choice == 1`, `a` if `choice == 0`. `choice` must be 0 or 1.
    pub(crate) fn conditional_select(
        a: &FieldElement,
        b: &FieldElement,
        choice: u64,
    ) -> FieldElement {
        let mask = 0u64.wrapping_sub(choice);
        let mut out = [0u64; 5];
        for i in 0..5 {
            out[i] = a.0[i] ^ (mask & (a.0[i] ^ b.0[i]));
        }
        FieldElement(out)
    }

    /// Negate in place when `choice == 1`.
    pub(crate) fn conditional_negate(&mut self, choice: u64) {
        *self = FieldElement::conditional_select(self, &self.neg(), choice);
    }

    /// `1` if the two elements denote the same field element, else `0`.
    ///
    /// Compares canonical encodings, because the limb representation is
    /// redundant — a limb-wise comparison would report `p != 0`.
    pub(crate) fn ct_eq(&self, other: &FieldElement) -> u64 {
        let (x, y) = (self.to_bytes(), other.to_bytes());
        let mut diff = 0u8;
        for i in 0..32 {
            diff |= x[i] ^ y[i];
        }
        // diff == 0  ->  1,  otherwise  ->  0
        (((diff as u64).wrapping_sub(1)) >> 63) & 1
    }

    /// `1` when the element is zero.
    pub(crate) fn is_zero(&self) -> u64 {
        self.ct_eq(&FieldElement::ZERO)
    }

    /// The sign bit of **RFC 8032 §5.1.2**: "the least significant bit of the
    /// x-coordinate", i.e. bit 0 of the *canonical* little-endian encoding.
    pub(crate) fn is_negative(&self) -> u64 {
        (self.to_bytes()[0] & 1) as u64
    }

    /// Decode 32 octets as a field element, **masking bit 255**.
    ///
    /// RFC 8032 §5.1.2 spends the top bit of the encoding on the sign of `x`,
    /// so a `y` decoder must ignore it. This function does *not* reject
    /// `y >= p`; the canonicality check RFC 8032 §5.1.3 requires
    /// ("if the resulting value is >= p, decoding fails") lives in
    /// [`is_canonical_encoding`], which the point decoder calls.
    ///
    /// [`is_canonical_encoding`]: FieldElement::is_canonical_encoding
    pub(crate) fn from_bytes(bytes: &[u8; 32]) -> FieldElement {
        let load8 = |i: usize| -> u64 {
            let mut v = 0u64;
            for k in 0..8 {
                v |= (bytes[i + k] as u64) << (8 * k);
            }
            v
        };
        // The five 51-bit windows of a 256-bit little-endian integer.
        let l0 = load8(0) & LOW_51;
        let l1 = (load8(6) >> 3) & LOW_51;
        let l2 = (load8(12) >> 6) & LOW_51;
        let l3 = (load8(19) >> 1) & LOW_51;
        let l4 = (load8(24) >> 12) & LOW_51;
        FieldElement([l0, l1, l2, l3, l4])
    }

    /// `1` when `bytes` (bit 255 masked off) is the canonical encoding of a
    /// field element, i.e. when the 255-bit value is `< p`. RFC 8032 §5.1.3.
    pub(crate) fn is_canonical_encoding(bytes: &[u8; 32]) -> u64 {
        let mut masked = *bytes;
        masked[31] &= 0x7f;
        let round_trip = FieldElement::from_bytes(&masked).to_bytes();
        let mut diff = 0u8;
        for i in 0..32 {
            diff |= masked[i] ^ round_trip[i];
        }
        (((diff as u64).wrapping_sub(1)) >> 63) & 1
    }

    /// The canonical 32-octet little-endian encoding, `0 <= value < p`
    /// (RFC 8032 §5.1.2, "255-bit little-endian encoding of {0, 1, ..., p-1}").
    ///
    /// # Why two carry passes then a conditional subtract
    ///
    /// The limb representation is redundant, so the value here can be anything
    /// in `[0, 2p)`. Two carry passes bring every limb below `2^51 + 1`, hence
    /// the value below `2^255 + 2^51 < 2p`; one subtraction of `p` therefore
    /// suffices. `h >= p` iff `h + 19` carries out of bit 254, so `q` — the
    /// number of `p`s to subtract — is that carry, and `h - qp = h + 19q` with
    /// bit 255 discarded.
    pub(crate) fn to_bytes(&self) -> [u8; 32] {
        let mut l = FieldElement::carry_pass(FieldElement::carry_pass(self.0).0).0;

        // q = 1 exactly when the value is >= p.
        let mut q = (l[0] + 19) >> 51;
        q = (l[1] + q) >> 51;
        q = (l[2] + q) >> 51;
        q = (l[3] + q) >> 51;
        q = (l[4] + q) >> 51;

        l[0] += 19 * q;
        l[1] += l[0] >> 51;
        l[0] &= LOW_51;
        l[2] += l[1] >> 51;
        l[1] &= LOW_51;
        l[3] += l[2] >> 51;
        l[2] &= LOW_51;
        l[4] += l[3] >> 51;
        l[3] &= LOW_51;
        // Discarding this carry is the `- q·2^255` half of `- q·p`.
        l[4] &= LOW_51;

        let mut out = [0u8; 32];
        for (i, byte) in out.iter_mut().enumerate() {
            let bit = i * 8;
            let limb = bit / 51;
            let shift = bit % 51;
            let mut v = l[limb] >> shift;
            // A byte can straddle two limbs; splice the next limb's low bits in.
            if shift > 51 - 8 && limb < 4 {
                v |= l[limb + 1] << (51 - shift);
            }
            *byte = (v & 0xff) as u8;
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The four boundary values the field is most likely to be wrong on.
    /// Built from raw limbs, because `from_bytes` cannot express `p` or larger.
    fn boundary_limbs() -> [(&'static str, [u64; 5], [u8; 32]); 4] {
        let mut p_minus_1 = [0u8; 32];
        p_minus_1[0] = 0xec;
        for b in p_minus_1.iter_mut().skip(1) {
            *b = 0xff;
        }
        p_minus_1[31] = 0x7f;

        let mut one = [0u8; 32];
        one[0] = 1;

        [
            // p - 1 encodes as itself.
            ("p-1", [0x7ffffffffffec, LOW_51, LOW_51, LOW_51, LOW_51], p_minus_1),
            // p ≡ 0.
            ("p", [0x7ffffffffffed, LOW_51, LOW_51, LOW_51, LOW_51], [0u8; 32]),
            // p + 1 ≡ 1.
            ("p+1", [0x7ffffffffffee, LOW_51, LOW_51, LOW_51, LOW_51], one),
            // 2p - 1 = 2^256 - 39 ≡ p - 1. Note limb 4 is 2^52-1 here, the
            // loosest input `to_bytes` must accept.
            ("2p-1", [0x7ffffffffffd9, LOW_51, LOW_51, LOW_51, (1 << 52) - 1], p_minus_1),
        ]
    }

    #[test]
    fn boundary_values_reduce_canonically() {
        for (name, limbs, expected) in boundary_limbs() {
            let got = FieldElement(limbs).to_bytes();
            assert_eq!(got, expected, "{name} did not reduce to its canonical encoding");
        }
    }

    #[test]
    fn boundary_values_survive_arithmetic() {
        // p ≡ 0, so p + 1 ≡ 1 and (p-1) + 1 ≡ 0, computed through `add`.
        let p = FieldElement([0x7ffffffffffed, LOW_51, LOW_51, LOW_51, LOW_51]);
        let p_minus_1 = FieldElement([0x7ffffffffffec, LOW_51, LOW_51, LOW_51, LOW_51]);
        assert_eq!(p.add(&FieldElement::ONE).to_bytes(), FieldElement::ONE.to_bytes());
        assert_eq!(p_minus_1.add(&FieldElement::ONE).to_bytes(), FieldElement::ZERO.to_bytes());
        assert_eq!(p.mul(&FieldElement::ONE).to_bytes(), FieldElement::ZERO.to_bytes());
        // (p-1)² = p² - 2p + 1 ≡ 1.
        assert_eq!(p_minus_1.square().to_bytes(), FieldElement::ONE.to_bytes());
        // 0 - 1 ≡ p - 1.
        assert_eq!(FieldElement::ZERO.sub(&FieldElement::ONE).to_bytes(), p_minus_1.to_bytes());
        assert_eq!(FieldElement::MINUS_ONE.to_bytes(), p_minus_1.to_bytes());
    }

    #[test]
    fn from_bytes_masks_bit_255_and_flags_non_canonical() {
        // 0xff.. has bit 255 set AND is >= p once masked.
        let all_ff = [0xffu8; 32];
        assert_eq!(FieldElement::is_canonical_encoding(&all_ff), 0);
        // Masked, it is 2^255 - 1 = p + 18, so it reduces to 18.
        let mut eighteen = [0u8; 32];
        eighteen[0] = 18;
        assert_eq!(FieldElement::from_bytes(&all_ff).to_bytes(), eighteen);

        // p - 1 with the sign bit set is canonical as a y-coordinate.
        let mut p_minus_1_signed = [0xffu8; 32];
        p_minus_1_signed[0] = 0xec;
        p_minus_1_signed[31] = 0xff;
        assert_eq!(FieldElement::is_canonical_encoding(&p_minus_1_signed), 1);
    }

    #[test]
    fn byte_round_trip_over_every_bit_position() {
        // A single set bit at each of the 255 positions exercises every limb
        // boundary in both `from_bytes` and `to_bytes`.
        for bit in 0..255 {
            let mut b = [0u8; 32];
            b[bit / 8] = 1 << (bit % 8);
            assert_eq!(FieldElement::from_bytes(&b).to_bytes(), b, "bit {bit}");
        }
    }

    #[test]
    fn inverse_and_sqrt_agree_with_their_definitions() {
        // A deterministic spread of elements, including 1 and p-1.
        for seed in 1u64..64 {
            let mut b = [0u8; 32];
            b[..8].copy_from_slice(&seed.wrapping_mul(0x9e37_79b9_7f4a_7c15).to_le_bytes());
            b[8] = 0x37;
            b[31] = 0x3f;
            let x = FieldElement::from_bytes(&b);
            assert_eq!(x.mul(&x.invert()).to_bytes(), FieldElement::ONE.to_bytes(), "inv {seed}");
        }
        assert_eq!(FieldElement::MINUS_ONE.invert().to_bytes(), FieldElement::MINUS_ONE.to_bytes());
    }

    #[test]
    fn ct_eq_sees_through_the_redundant_representation() {
        let p = FieldElement([0x7ffffffffffed, LOW_51, LOW_51, LOW_51, LOW_51]);
        assert_eq!(p.ct_eq(&FieldElement::ZERO), 1);
        assert_eq!(p.is_zero(), 1);
        assert_eq!(FieldElement::ONE.ct_eq(&FieldElement::ZERO), 0);
        assert_eq!(FieldElement::ONE.is_negative(), 1);
        assert_eq!(FieldElement::ZERO.is_negative(), 0);
        assert_eq!(FieldElement::MINUS_ONE.is_negative(), 0);
    }
}
