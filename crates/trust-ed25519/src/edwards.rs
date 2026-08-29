// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The twisted Edwards curve `edwards25519` and its group law.
//!
//! **RFC 8032 §5.1**: `-x² + y² = 1 + d·x²·y²` over GF(2^255 - 19), with
//! `a = -1`, `d = -121665/121666`, base point `B` of prime order
//! `L = 2^252 + 27742317777372353535851937790883648493`, and cofactor 8.
//!
//! # Coordinates
//!
//! Points are held in **extended twisted Edwards coordinates** `(x : y : z : t)`
//! with `X = x/z`, `Y = y/z` and `X·Y = t/z` (Hisil, Wong, Carter and Dawson,
//! *Twisted Edwards Curves Revisited*, ASIACRYPT 2008). The affine addition law
//! RFC 8032 §5.1.4 states is division-heavy; the extended form evaluates the
//! same law with no inversion at all, and the single inversion this module
//! performs is in [`EdwardsPoint::compress`], on the way out.
//!
//! # Completeness — why there are no special cases in the group law
//!
//! For a twisted Edwards curve, the addition law used by [`EdwardsPoint::add`]
//! is *complete* — correct for every pair of inputs, including `P + P`,
//! `P + (-P)` and anything involving the identity — precisely when `a` is a
//! square and `d` is a non-square in the field. Here `a = -1`, which is a
//! square because `p ≡ 1 (mod 4)`, and `d` is a non-square (that is the same
//! fact that lets [`decompress`] fail on half of all `y` values). So the group
//! law needs no exceptional branch, and the scalar multiplication below is free
//! to add the identity out of its precomputed table without a special case —
//! which is what makes a constant-time window possible in the first place.
//!
//! The `addition_law_has_no_exceptional_cases` test below exercises exactly
//! those would-be exceptions.
//!
//! [`decompress`]: EdwardsPoint::decompress

use crate::field::FieldElement;

/// `d = -121665/121666` (RFC 8032 §5.1 Table 1).
///
/// Derived, not remembered: the `constants_are_derivable` test below recomputes
/// it as `(-121665) · 121666^-1` in this crate's own field arithmetic. RFC 8032
/// §5.1 Table 1 also prints it in decimal as
/// `3709570593466943934313808350875456518954211387984321901638878553308594028\
/// 3555`.
pub(crate) const EDWARDS_D: FieldElement = FieldElement([
    0x34dca135978a3,
    0x1a8283b156ebd,
    0x5e7a26001c029,
    0x739c663a03cbb,
    0x52036cee2b6ff,
]);

/// `2·d`, the `k` of the Hisil-Wong-Carter-Dawson addition law.
pub(crate) const EDWARDS_D2: FieldElement = FieldElement([
    0x69b9426b2f159,
    0x35050762add7a,
    0x3cf44c0038052,
    0x6738cc7407977,
    0x2406d9dc56dff,
]);

/// `sqrt(-1) = 2^((p-1)/4) (mod p)`, the correction factor of the three-case
/// square root in RFC 8032 §5.1.1.
pub(crate) const SQRT_M1: FieldElement = FieldElement([
    0x61b274a0ea0b0,
    0x0d5a5fc8f189d,
    0x7ef5e9cbd0c60,
    0x78595a6804c9e,
    0x2b8324804fc1d,
]);

/// `B.x` — RFC 8032 §5.1 Table 1 prints the decimal
/// `15112221349535400772501151409588531511454012693041857206046113283949847762202`.
const B_X: FieldElement = FieldElement([
    0x62d608f25d51a,
    0x412a4b4f6592a,
    0x75b7171a4b31d,
    0x1ff60527118fe,
    0x216936d3cd6e5,
]);

/// `B.y = 4/5` — RFC 8032 §5.1 Table 1 prints the decimal
/// `46316835694926478169428394003475163141307993866256225615783033603165251855960`.
const B_Y: FieldElement = FieldElement([
    0x6666666666658,
    0x4cccccccccccc,
    0x1999999999999,
    0x3333333333333,
    0x6666666666666,
]);

/// `B.x · B.y`, the extended coordinate `t` of the base point at `z = 1`.
const B_T: FieldElement = FieldElement([
    0x68ab3a5b7dda3,
    0x00eea2a5eadbb,
    0x2af8df483c27e,
    0x332b375274732,
    0x67875f0fd78b7,
]);

/// A point on edwards25519, in extended coordinates.
#[derive(Copy, Clone)]
pub(crate) struct EdwardsPoint {
    x: FieldElement,
    y: FieldElement,
    z: FieldElement,
    t: FieldElement,
}

impl EdwardsPoint {
    /// The neutral element `(0, 1)`.
    pub(crate) const IDENTITY: EdwardsPoint = EdwardsPoint {
        x: FieldElement::ZERO,
        y: FieldElement::ONE,
        z: FieldElement::ONE,
        t: FieldElement::ZERO,
    };

    /// The base point `B` of RFC 8032 §5.1 Table 1.
    pub(crate) const BASEPOINT: EdwardsPoint =
        EdwardsPoint { x: B_X, y: B_Y, z: FieldElement::ONE, t: B_T };

    /// The group law, `add-2008-hwcd-3` for `a = -1`.
    ///
    /// ```text
    ///   A = (y1-x1)(y2-x2)      E = B-A      x3 = E·F
    ///   B = (y1+x1)(y2+x2)      F = D-C      y3 = G·H
    ///   C = 2d·t1·t2            G = D+C      t3 = E·H
    ///   D = 2·z1·z2             H = B+A      z3 = F·G
    /// ```
    ///
    /// Complete — see the module header. No input is special-cased.
    pub(crate) fn add(&self, rhs: &EdwardsPoint) -> EdwardsPoint {
        let a = self.y.sub(&self.x).mul(&rhs.y.sub(&rhs.x));
        let b = self.y.add(&self.x).mul(&rhs.y.add(&rhs.x));
        let c = self.t.mul(&EDWARDS_D2).mul(&rhs.t);
        let dd = self.z.mul(&rhs.z);
        let dd = dd.add(&dd);

        let e = b.sub(&a);
        let f = dd.sub(&c);
        let g = dd.add(&c);
        let h = b.add(&a);

        EdwardsPoint { x: e.mul(&f), y: g.mul(&h), t: e.mul(&h), z: f.mul(&g) }
    }

    /// Doubling, `dbl-2008-hwcd` for `a = -1`.
    ///
    /// ```text
    ///   A = x1²                 E = (x1+y1)² - A - B     x3 = E·F
    ///   B = y1²                 G = D + B                y3 = G·H
    ///   C = 2·z1²               F = G - C                t3 = E·H
    ///   D = -A                  H = D - B                z3 = F·G
    /// ```
    ///
    /// Doubling `P` through [`add`] gives the same answer (the law is
    /// complete); this is the cheaper route, and `addition_law_has_no_exceptional_cases`
    /// pins the agreement.
    ///
    /// [`add`]: EdwardsPoint::add
    pub(crate) fn double(&self) -> EdwardsPoint {
        let a = self.x.square();
        let b = self.y.square();
        let zz = self.z.square();
        let c = zz.add(&zz);
        let d = a.neg();

        let e = self.x.add(&self.y).square().sub(&a).sub(&b);
        let g = d.add(&b);
        let f = g.sub(&c);
        let h = d.sub(&b);

        EdwardsPoint { x: e.mul(&f), y: g.mul(&h), t: e.mul(&h), z: f.mul(&g) }
    }

    /// `-P = (-x : y : z : -t)`.
    pub(crate) fn neg(&self) -> EdwardsPoint {
        EdwardsPoint { x: self.x.neg(), y: self.y, z: self.z, t: self.t.neg() }
    }

    /// `b` if `choice == 1`, `a` if `choice == 0`. `choice` must be 0 or 1.
    fn conditional_select(a: &EdwardsPoint, b: &EdwardsPoint, choice: u64) -> EdwardsPoint {
        EdwardsPoint {
            x: FieldElement::conditional_select(&a.x, &b.x, choice),
            y: FieldElement::conditional_select(&a.y, &b.y, choice),
            z: FieldElement::conditional_select(&a.z, &b.z, choice),
            t: FieldElement::conditional_select(&a.t, &b.t, choice),
        }
    }

    /// `[k]P` for a 256-bit little-endian scalar, in constant time.
    ///
    /// # Why this shape
    ///
    /// A fixed 4-bit window: sixty-four nibbles, most significant first, four
    /// doublings and one addition each, against a table of `[0]P .. [15]P`.
    ///
    /// * **No secret-dependent branch.** The loop trip count and the operation
    ///   sequence are fixed by the scalar's *length*, which is always 32 bytes.
    /// * **No secret-dependent memory index.** [`select`] reads all sixteen
    ///   table entries every time and keeps one with a mask. An `table[nibble]`
    ///   index would leak the nibble through the cache, which is the classic
    ///   break of a windowed scalar multiplication.
    /// * **No exceptional case to branch on.** `[0]P` is the identity, and the
    ///   addition law is complete, so a zero nibble needs no special handling.
    ///
    /// This is used for the *secret* scalar (RFC 8032 §5.1.6 step 1's `s`, and
    /// the nonce `r`) and, unchanged, for the public scalars in verification.
    /// Verification could use a faster variable-time ladder; running one
    /// routine for both is the deliberate choice, because it means the
    /// constant-time property cannot be lost by a caller picking the wrong
    /// entry point.
    ///
    /// [`select`]: EdwardsPoint::select
    pub(crate) fn mul(&self, scalar: &[u8; 32]) -> EdwardsPoint {
        let mut table = [EdwardsPoint::IDENTITY; 16];
        table[1] = *self;
        for i in 2..16 {
            table[i] = table[i - 1].add(self);
        }

        let mut q = EdwardsPoint::IDENTITY;
        for i in (0..64).rev() {
            for _ in 0..4 {
                q = q.double();
            }
            let nibble = (scalar[i / 2] >> (4 * (i % 2))) & 0x0f;
            q = q.add(&Self::select(&table, nibble));
        }
        q
    }

    /// Constant-time table read: touches every entry, keeps one.
    fn select(table: &[EdwardsPoint; 16], index: u8) -> EdwardsPoint {
        let mut out = EdwardsPoint::IDENTITY;
        for (i, entry) in table.iter().enumerate() {
            // 1 exactly when i == index, with no branch.
            let diff = (i as u8) ^ index;
            let choice = (((diff as u64).wrapping_sub(1)) >> 63) & 1;
            out = EdwardsPoint::conditional_select(&out, entry, choice);
        }
        out
    }

    /// Encode per **RFC 8032 §5.1.2**: the 255-bit little-endian encoding of
    /// `y`, with the least significant bit of `x` copied into the most
    /// significant bit of the final octet.
    pub(crate) fn compress(&self) -> [u8; 32] {
        let z_inv = self.z.invert();
        let x = self.x.mul(&z_inv);
        let y = self.y.mul(&z_inv);
        let mut out = y.to_bytes();
        out[31] |= (x.is_negative() as u8) << 7;
        out
    }

    /// Decode per **RFC 8032 §5.1.3**, rejecting every encoding the section
    /// says to reject.
    ///
    /// 1. `y` is the low 255 bits; `x_0` is bit 255.
    /// 2. **"If the resulting value is >= p, decoding fails."** — the
    ///    non-canonical case.
    /// 3. `x² = (y²-1)/(d·y²+1)`. **"If there is no such square root, decoding
    ///    fails."**
    /// 4. **"If x = 0 and x_0 = 1, decoding fails."**
    /// 5. Otherwise `x` is the root whose least significant bit is `x_0`.
    ///
    /// Note that `d·y²+1` is never zero, so step 3 has no division by zero:
    /// `v = 0` would need `y² = -1/d`, and `-1/d` is a non-square while `y²` is
    /// a square.
    ///
    /// This is deliberately **stricter than ed25519-dalek's**, which omits
    /// steps 2 and 4 — see the crate-level `Deliberate deviations` section.
    pub(crate) fn decompress(bytes: &[u8; 32]) -> Option<EdwardsPoint> {
        if FieldElement::is_canonical_encoding(bytes) != 1 {
            return None; // step 2
        }
        let sign = (bytes[31] >> 7) as u64;
        let y = FieldElement::from_bytes(bytes);

        let yy = y.square();
        let u = yy.sub(&FieldElement::ONE); // y² - 1
        let v = yy.mul(&EDWARDS_D).add(&FieldElement::ONE); // d·y² + 1

        let (is_square, mut x) = FieldElement::sqrt_ratio(&u, &v, &SQRT_M1);
        if is_square != 1 {
            return None; // step 3
        }
        if x.is_zero() == 1 && sign == 1 {
            return None; // step 4
        }
        x.conditional_negate(x.is_negative() ^ sign); // step 5

        Some(EdwardsPoint { x, y, z: FieldElement::ONE, t: x.mul(&y) })
    }

    /// `1` when the two points are equal as group elements.
    ///
    /// Compares canonical encodings rather than coordinates, because the
    /// projective representation is redundant.
    #[cfg(test)]
    pub(crate) fn ct_eq(&self, other: &EdwardsPoint) -> u64 {
        let (a, b) = (self.compress(), other.compress());
        let mut diff = 0u8;
        for i in 0..32 {
            diff |= a[i] ^ b[i];
        }
        (((diff as u64).wrapping_sub(1)) >> 63) & 1
    }

    /// `1` when the point satisfies `-x² + y² = 1 + d·x²·y²` (RFC 8032 §5.1),
    /// checked projectively as `(-x² + y²)z² = z⁴ + d·x²·y²`, and when the
    /// extended coordinate is consistent (`x·y = t·z`).
    #[cfg(test)]
    pub(crate) fn is_on_curve(&self) -> u64 {
        let xx = self.x.square();
        let yy = self.y.square();
        let zz = self.z.square();
        let lhs = yy.sub(&xx).mul(&zz);
        let rhs = zz.square().add(&EDWARDS_D.mul(&xx).mul(&yy));
        let curve = lhs.ct_eq(&rhs);
        let extended = self.x.mul(&self.y).ct_eq(&self.t.mul(&self.z));
        curve & extended
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fe(v: u64) -> FieldElement {
        FieldElement([v, 0, 0, 0, 0])
    }

    /// Re-derive every curve constant from the RFC 8032 §5.1 Table 1
    /// *definitions* rather than trusting the limbs above.
    ///
    /// This shares the field arithmetic with the implementation, so it is not
    /// an independent check of `field.rs`; it is an independent check that the
    /// hand-entered limb tables denote the numbers the RFC names, which is the
    /// error this file is actually exposed to.
    #[test]
    fn constants_are_derivable() {
        // d = -121665 / 121666
        let d = fe(121665).neg().mul(&fe(121666).invert());
        assert_eq!(d.to_bytes(), EDWARDS_D.to_bytes(), "EDWARDS_D");
        // and the defining relation, in the other direction
        assert_eq!(EDWARDS_D.mul(&fe(121666)).add(&fe(121665)).to_bytes(), [0u8; 32]);

        assert_eq!(EDWARDS_D.add(&EDWARDS_D).to_bytes(), EDWARDS_D2.to_bytes(), "EDWARDS_D2");
        assert_eq!(SQRT_M1.square().to_bytes(), FieldElement::MINUS_ONE.to_bytes(), "SQRT_M1");

        // B.y = 4/5
        assert_eq!(fe(4).mul(&fe(5).invert()).to_bytes(), B_Y.to_bytes(), "B_Y");
        assert_eq!(B_X.mul(&B_Y).to_bytes(), B_T.to_bytes(), "B_T");

        // B.x is the even root of B.y, so B compresses with a clear sign bit —
        // and decompressing that encoding must return B.x, which exercises the
        // whole of §5.1.3 against a value the RFC states independently.
        assert_eq!(B_X.is_negative(), 0, "B.x should be even");
        let b_encoded = EdwardsPoint::BASEPOINT.compress();
        assert_eq!(b_encoded[31] >> 7, 0);
        let round = EdwardsPoint::decompress(&b_encoded).expect("B decompresses");
        assert_eq!(round.compress(), b_encoded);
        assert_eq!(EdwardsPoint::BASEPOINT.is_on_curve(), 1, "B on curve");
    }

    /// The cases a non-complete addition law would get wrong.
    #[test]
    fn addition_law_has_no_exceptional_cases() {
        let b = EdwardsPoint::BASEPOINT;
        let id = EdwardsPoint::IDENTITY;

        assert_eq!(id.add(&id).ct_eq(&id), 1, "0 + 0");
        assert_eq!(b.add(&id).ct_eq(&b), 1, "P + 0");
        assert_eq!(id.add(&b).ct_eq(&b), 1, "0 + P");
        assert_eq!(b.add(&b.neg()).ct_eq(&id), 1, "P + (-P)");
        assert_eq!(id.double().ct_eq(&id), 1, "2·0");
        assert_eq!(b.add(&b).ct_eq(&b.double()), 1, "P + P == 2P");

        // The doubling chain and the addition chain must agree for a while.
        let mut by_add = b;
        let mut by_dbl = b;
        for i in 1..8 {
            by_add = by_add.add(&by_add);
            by_dbl = by_dbl.double();
            assert_eq!(by_add.ct_eq(&by_dbl), 1, "2^{i}·B");
            assert_eq!(by_add.is_on_curve(), 1, "2^{i}·B on curve");
        }
    }

    /// `[k]B` by window against `[k]B` by naive double-and-add, and the small
    /// multiples against repeated addition.
    #[test]
    fn scalar_mul_matches_repeated_addition() {
        let b = EdwardsPoint::BASEPOINT;
        let mut acc = EdwardsPoint::IDENTITY;
        for k in 0u8..40 {
            let mut s = [0u8; 32];
            s[0] = k;
            assert_eq!(b.mul(&s).ct_eq(&acc), 1, "[{k}]B");
            acc = acc.add(&b);
        }

        // A scalar that spans several nibbles and both bytes of a window.
        let mut s = [0u8; 32];
        s[0] = 0xf3;
        s[1] = 0x01;
        let mut want = EdwardsPoint::IDENTITY;
        for _ in 0..0x01f3 {
            want = want.add(&b);
        }
        assert_eq!(b.mul(&s).ct_eq(&want), 1, "[0x1f3]B");
    }

    /// `L·B = 0`: the base point has exactly the order RFC 8032 Table 1 names.
    #[test]
    fn basepoint_has_order_l() {
        let mut l_bytes = [0u8; 32];
        for (i, limb) in crate::scalar::L.iter().enumerate() {
            l_bytes[8 * i..8 * i + 8].copy_from_slice(&limb.to_le_bytes());
        }
        assert_eq!(
            EdwardsPoint::BASEPOINT.mul(&l_bytes).ct_eq(&EdwardsPoint::IDENTITY),
            1,
            "[L]B is not the identity"
        );
        // L-1 times B is -B, so adding B once more lands on the identity.
        l_bytes[0] -= 1;
        assert_eq!(
            EdwardsPoint::BASEPOINT
                .mul(&l_bytes)
                .add(&EdwardsPoint::BASEPOINT)
                .ct_eq(&EdwardsPoint::IDENTITY),
            1,
            "[L-1]B + B is not the identity"
        );
    }

    /// Encoding round-trips, and the two encodings §5.1.3 must reject.
    #[test]
    fn decompress_rejects_what_the_rfc_says_to_reject() {
        // Non-canonical y: 0xff.. masks to 2^255-1 = p+18, which is >= p.
        assert!(EdwardsPoint::decompress(&[0xff; 32]).is_none(), "non-canonical y accepted");

        // x = 0 with the sign bit set: y = 1 is the identity's encoding.
        let mut ident_signed = [0u8; 32];
        ident_signed[0] = 1;
        ident_signed[31] = 0x80;
        assert!(EdwardsPoint::decompress(&ident_signed).is_none(), "x=0, x_0=1 accepted");
        // Without the sign bit it is the identity.
        let mut ident = [0u8; 32];
        ident[0] = 1;
        assert_eq!(
            EdwardsPoint::decompress(&ident)
                .expect("identity decompresses")
                .ct_eq(&EdwardsPoint::IDENTITY),
            1
        );

        // Roughly half of arbitrary y values are not on the curve.
        let mut rejected = 0;
        for k in 0u16..256 {
            let mut b = [0u8; 32];
            b[0] = k as u8;
            b[1] = (k >> 8) as u8;
            b[2] = 0x5a;
            match EdwardsPoint::decompress(&b) {
                None => rejected += 1,
                Some(p) => assert_eq!(p.is_on_curve(), 1, "decompressed off-curve point at k={k}"),
            }
        }
        assert!((64..192).contains(&rejected), "implausible rejection rate: {rejected}/256");
    }

    /// The 8-torsion subgroup, derived here and cross-checked against the
    /// **independent** derivation in `tests/data/derive_edge_vectors.py`.
    ///
    /// The two computations share nothing: that script works in Python
    /// arbitrary-precision integers with the affine addition law of RFC 8032
    /// §5.1.4, this one works in 5×51-bit limbs with the extended
    /// `add-2008-hwcd-3` law. Agreement on all eight encodings is therefore
    /// evidence about both, and it is what lets `tests/kat_edge_cases.rs`
    /// treat the file's `small_order` records as trustworthy inputs.
    ///
    /// Nothing is transcribed. Every curve point `Q` satisfies `[8L]Q = 0`, so
    /// `[L]Q` always lands in the 8-torsion; taking small `y` until `[L]Q` has
    /// full order 8 yields a generator, and its multiples are the subgroup.
    #[test]
    fn eight_torsion_matches_the_derivation() {
        const EDGE_VECTORS: &str = include_str!("../tests/data/edge_vectors.txt");

        let mut l_bytes = [0u8; 32];
        for (i, limb) in crate::scalar::L.iter().enumerate() {
            l_bytes[8 * i..8 * i + 8].copy_from_slice(&limb.to_le_bytes());
        }

        // The exact order of a point already known to lie in the 8-torsion.
        let order_of = |p: &EdwardsPoint| -> u32 {
            let mut acc = *p;
            for order in 1..=8u32 {
                if acc.ct_eq(&EdwardsPoint::IDENTITY) == 1 {
                    return order;
                }
                acc = acc.add(p);
            }
            0
        };

        let mut generator = None;
        for y in 2u16..200 {
            let mut encoded = [0u8; 32];
            encoded[0] = y as u8;
            encoded[1] = (y >> 8) as u8;
            if let Some(q) = EdwardsPoint::decompress(&encoded) {
                let t = q.mul(&l_bytes);
                if order_of(&t) == 8 {
                    generator = Some(t);
                    break;
                }
            }
        }
        let generator = generator.expect("no point of order 8 found in the 8-torsion");

        let mut ours = [[0u8; 32]; 8];
        let mut acc = EdwardsPoint::IDENTITY;
        for slot in ours.iter_mut() {
            assert_eq!(acc.is_on_curve(), 1, "8-torsion member is not on the curve");
            *slot = acc.compress();
            acc = acc.add(&generator);
        }
        // [8]T must close the cycle.
        assert_eq!(acc.ct_eq(&EdwardsPoint::IDENTITY), 1, "the generator does not have order 8");
        ours.sort_unstable();
        // Eight DISTINCT points, or the comparison below could pass on repeats.
        for pair in ours.windows(2) {
            assert_ne!(pair[0], pair[1], "the derived 8-torsion has a repeat");
        }

        let mut theirs = [[0u8; 32]; 8];
        let mut found = 0;
        for line in EDGE_VECTORS.lines() {
            let mut f = line.split('|');
            if f.next() != Some("small_order") {
                continue;
            }
            let hex = f.nth(1).expect("small_order record has an encoding");
            assert_eq!(hex.len(), 64, "small_order encoding is not 32 octets");
            assert!(found < 8, "more than eight small_order records");
            for i in 0..32 {
                theirs[found][i] =
                    u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).expect("hex digit");
            }
            found += 1;
        }
        assert_eq!(found, 8, "expected eight small_order records in edge_vectors.txt");
        theirs.sort_unstable();

        assert_eq!(
            ours, theirs,
            "this crate's 8-torsion disagrees with derive_edge_vectors.py's. Two independent \
             implementations of RFC 8032 §5.1 do not agree on the curve's torsion subgroup."
        );
    }

    /// Every decompressible encoding must re-compress to itself. This is the
    /// totality property `trust-proof-cert`'s `TrustAnchorPolicy` relies on.
    #[test]
    fn compress_decompress_round_trips() {
        let mut found = 0;
        for k in 0u16..512 {
            let mut b = [0u8; 32];
            b[0] = k as u8;
            b[1] = (k >> 8) as u8;
            b[2] = 0xc3;
            b[31] = ((k & 1) as u8) << 7;
            if let Some(p) = EdwardsPoint::decompress(&b) {
                assert_eq!(p.compress(), b, "round trip failed at k={k}");
                found += 1;
            }
        }
        assert!(found > 100, "only {found} decompressible encodings; test is not exercising much");
    }
}
