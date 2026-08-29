// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **Edge-case known-answer tests: the encodings RFC 8032 says to REJECT.**
//!
//! `kat_rfc8032.rs` covers the five published §7.1 vectors, all of which are
//! valid. RFC 8032 publishes no vector for any case a verifier is likely to get
//! *wrong*, and those are the interesting ones: a non-canonical `y`, an
//! encoding that is not a curve point, a malleated `S`, a small-order key.
//!
//! # Provenance
//!
//! Every vector here is **DERIVED**, and derived by
//! `tests/data/derive_edge_vectors.py` rather than by this crate — that script
//! implements RFC 8032 §5.1.3 and §5.1.7 in Python's arbitrary-precision
//! integers, with the *affine* addition law of §5.1.4, so it shares neither
//! the 5×51 limb representation nor the extended-coordinate group law with the
//! implementation under test. `tests/data/PROVENANCE.md` records the split
//! between published and derived material; nothing here came from
//! `ed25519-dalek`.
//!
//! # Why this file exists separately from the differential
//!
//! `differential_ed25519.rs` covers some of the same ground, but only for as
//! long as `ed25519-dalek` is in the dependency graph — and removing it is the
//! entire point of this crate. These tests outlive the incumbent, because they
//! compare against a *specification*, not against another implementation.

const EDGE_VECTORS: &str = include_str!("data/edge_vectors.txt");

use trust_ed25519::{Signature, Signer, SigningKey, Verifier, VerifyingKey};

fn unhex(s: &str) -> Vec<u8> {
    assert!(s.len() % 2 == 0, "odd-length hex: {} chars", s.len());
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).expect("hex digit"))
        .collect()
}

fn key32(s: &str) -> [u8; 32] {
    unhex(s).try_into().expect("32-octet value")
}

/// Records of one kind, as their remaining pipe-separated fields.
///
/// The data file is an input, not a fixture: a caller that asks for a kind the
/// file does not carry gets a panic, not an empty loop that passes vacuously.
fn records(kind: &str) -> Vec<Vec<String>> {
    let out: Vec<Vec<String>> = EDGE_VECTORS
        .lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
        .filter_map(|l| {
            let mut f = l.split('|');
            (f.next() == Some(kind)).then(|| f.map(str::to_string).collect())
        })
        .collect();
    assert!(!out.is_empty(), "no `{kind}` records in tests/data/edge_vectors.txt");
    out
}

/// `L`, little-endian, from **RFC 8032 §5.1 Table 1**: "order of edwards25519
/// in [RFC7748] (i.e., 2^252+27742317777372353535851937790883648493)".
///
/// Written as the RFC's decimal, converted here rather than transcribed as
/// hex, so the constant can be read against the RFC without a calculator.
fn l_le() -> [u8; 32] {
    // 2^252 + 27742317777372353535851937790883648493, built by long addition
    // on the decimal digits of the low term.
    const LOW: &str = "27742317777372353535851937790883648493";
    let mut bytes = [0u8; 32];
    // Horner over the decimal digits, little-endian byte accumulator.
    for digit in LOW.bytes().map(|b| (b - b'0') as u32) {
        let mut carry = digit;
        for byte in bytes.iter_mut() {
            let v = (*byte as u32) * 10 + carry;
            *byte = v as u8;
            carry = v >> 8;
        }
        assert_eq!(carry, 0, "L's low term overflowed 32 octets");
    }
    // + 2^252
    bytes[31] |= 0x10;
    bytes
}

// ---------------------------------------------------------------------------
// RFC 8032 §5.1.3 step 1 — "If the resulting value is >= p, decoding fails."
// ---------------------------------------------------------------------------

/// **Exhaustive.** There are exactly nineteen 255-bit values `>= p`, namely
/// `p .. 2^255-1`, and each is tested with both settings of the sign bit.
///
/// Exhaustiveness is what makes this worth writing: a random sweep over
/// 32-octet strings hits this class with probability 19/2^255, so the
/// differential's 2048-sample key sweep can never reach it.
#[test]
fn every_non_canonical_y_is_rejected() {
    let rows = records("noncanonical_y");
    assert_eq!(rows.len(), 19, "expected the 19 values in [p, 2^255)");

    for row in &rows {
        let (name, bytes) = (&row[0], key32(&row[1]));
        for sign in [0u8, 0x80] {
            let mut encoding = bytes;
            encoding[31] = (encoding[31] & 0x7f) | sign;
            assert!(
                VerifyingKey::from_bytes(&encoding).is_err(),
                "non-canonical y ({name}, sign bit {}) was accepted as a key; \
                 RFC 8032 §5.1.3 step 1 requires decoding to fail",
                sign >> 7
            );
        }
    }
}

/// The other side of the same boundary: `p-1` is the largest canonical `y`,
/// and it *is* a curve point, so it must be **accepted**.
///
/// Without this, `every_non_canonical_y_is_rejected` would still pass in an
/// implementation that rejected every key with a large `y` — or every key at
/// all. It pins that the check is `>= p`, not `>= p - something`.
#[test]
fn p_minus_1_is_canonical_and_accepted() {
    let mut p_minus_1 = [0xffu8; 32];
    p_minus_1[0] = 0xec;
    p_minus_1[31] = 0x7f;

    // Cross-check against the derivation: p-1 is the order-2 point's encoding.
    let order_2: Vec<[u8; 32]> =
        records("small_order").iter().filter(|r| r[0] == "order=2").map(|r| key32(&r[1])).collect();
    assert_eq!(order_2, vec![p_minus_1], "p-1 is not the derived order-2 point");

    let key = VerifyingKey::from_bytes(&p_minus_1).expect("p-1 is a canonical curve point");
    assert_eq!(key.to_bytes(), p_minus_1, "accepted key did not round-trip");

    // With the sign bit set it must be rejected, but for a *different* reason:
    // this point has x = 0, so RFC 8032 §5.1.3 step 4 applies, not step 1.
    let mut signed = p_minus_1;
    signed[31] |= 0x80;
    assert!(
        VerifyingKey::from_bytes(&signed).is_err(),
        "x = 0 with x_0 = 1 was accepted; RFC 8032 §5.1.3 step 4 requires decoding to fail"
    );
}

// ---------------------------------------------------------------------------
// RFC 8032 §5.1.3 step 3.3 — "no square root exists ... decoding fails."
// ---------------------------------------------------------------------------

/// Canonical `y` values that are simply not on the curve.
///
/// A distinct rejection path from the one above: these are `< p`, so they
/// clear step 1 and die at the square root. The values are the smallest such
/// `y`, derived independently.
#[test]
fn off_curve_encodings_are_rejected() {
    let rows = records("off_curve_y");
    assert!(rows.len() >= 8, "expected at least 8 off-curve y values");

    for row in &rows {
        let (name, bytes) = (&row[0], key32(&row[1]));
        for sign in [0u8, 0x80] {
            let mut encoding = bytes;
            encoding[31] = (encoding[31] & 0x7f) | sign;
            assert!(
                VerifyingKey::from_bytes(&encoding).is_err(),
                "off-curve encoding ({name}, sign bit {}) was accepted as a key; \
                 RFC 8032 §5.1.3 step 3 requires decoding to fail",
                sign >> 7
            );
        }
    }

    // Positive control: y = 1 and y = 0 ARE curve points, and they differ from
    // the values above only in being on the curve. So the test above is not
    // passing merely because small y values are rejected wholesale.
    let mut y1 = [0u8; 32];
    y1[0] = 1;
    assert!(VerifyingKey::from_bytes(&y1).is_ok(), "y = 1 (the identity) should decode");
    assert!(VerifyingKey::from_bytes(&[0u8; 32]).is_ok(), "y = 0 should decode");
}

// ---------------------------------------------------------------------------
// RFC 8032 §5.1.7 step 1 — "an integer S, in the range 0 <= s < L ...
// If any of the decodings fail (including S being out of range), the
// signature is invalid."
// ---------------------------------------------------------------------------

/// **The malleability KAT, and it is deliberately non-vacuous.**
///
/// `(R, S+L)` is not merely an out-of-range signature: because `B` has order
/// `L`, `[S+L]B = [S]B`, so it satisfies the §5.1.7 group equation *exactly as
/// the published signature does*. The range check is therefore the only thing
/// in the specification that can reject it.
///
/// That claim is not taken on faith. `derive_edge_vectors.py` evaluates
/// `[S+L]B == R + [k]A` in Python bignums for every one of the five RFC
/// vectors and refuses to emit a record unless it holds — so if the algebra
/// were wrong, this file would not exist rather than silently testing nothing.
///
/// This matters because the weaker version of this test was measured to be
/// vacuous: deleting the range check from `Scalar::from_canonical_bytes` left
/// a malleability test built on arbitrary out-of-range `S` values **passing**,
/// since each of those also failed the equation and would have been rejected
/// by an implementation with no range check at all.
#[test]
fn malleated_s_plus_l_is_rejected() {
    let rows = records("malleated_sig");
    assert_eq!(rows.len(), 5, "expected one malleation per RFC 8032 §7.1 vector");

    for row in &rows {
        let (name, public, message, malleated) = (&row[0], key32(&row[1]), unhex(&row[2]), &row[3]);
        let key = VerifyingKey::from_bytes(&public).expect("RFC public key decodes");
        let sig_bytes = unhex(malleated);
        assert_eq!(sig_bytes.len(), 64);

        // The signature parses — the rejection must come from verification,
        // not from a length check.
        let sig = Signature::from_slice(&sig_bytes).expect("64 octets");
        assert!(
            key.verify(&message, &sig).is_err(),
            "MALLEABILITY, TEST {name}: (R, S+L) verified. It satisfies the RFC 8032 §5.1.7 \
             group equation — that is checked independently by derive_edge_vectors.py — so \
             the only thing that can reject it is the `0 <= S < L` range check, and it did not."
        );

        // Positive control: the same R with the ORIGINAL S must verify. This
        // rules out the rejection coming from a broken R, a broken key, or a
        // `verify` that rejects everything.
        let mut original = sig_bytes.clone();
        let s_plus_l = &sig_bytes[32..];
        let mut s = [0u8; 32];
        let mut borrow = 0i16;
        let l = l_le();
        for i in 0..32 {
            let v = s_plus_l[i] as i16 - l[i] as i16 - borrow;
            s[i] = v as u8;
            borrow = i16::from(v < 0);
        }
        assert_eq!(borrow, 0, "TEST {name}: S+L - L borrowed out");
        original[32..].copy_from_slice(&s);
        assert!(
            key.verify(&message, &Signature::from_slice(&original).unwrap()).is_ok(),
            "TEST {name}: the un-malleated signature did not verify, so the malleation test \
             above proves nothing"
        );
        assert_ne!(original, sig_bytes, "TEST {name}: S+L equals S");
    }
}

/// The rest of the out-of-range space — and it is built to be **non-vacuous**,
/// which the obvious version of this test is not.
///
/// `S = L`, `S = L+1` and `S = 2^256-1` are the natural cases to reach for, and
/// on their own they prove nothing: each *also* fails the group equation, so an
/// implementation with no range check at all rejects them anyway. Measured —
/// an earlier draft of this test used exactly those three values and **did not
/// fail** under a mutation that deleted `Scalar::from_canonical_bytes`'s range
/// check.
///
/// The fix is the same trick `malleated_s_plus_l_is_rejected` uses, extended:
/// since `B` has order `L`, **every** `S + m·L` satisfies the group equation,
/// for every `m`. So `m = 2` and `m = 3` are out-of-range signatures that the
/// equation accepts, and only the `0 ≤ S < L` check can reject them. The
/// boundary values are still tested, but they are now riding alongside cases
/// that carry the actual evidence.
#[test]
fn out_of_range_s_is_rejected_across_the_whole_class() {
    let l = l_le();

    // 32-octet little-endian add, asserting no overflow out of the top.
    let add_l = |x: &[u8; 32]| -> [u8; 32] {
        let mut out = [0u8; 32];
        let mut carry = 0u16;
        for i in 0..32 {
            let v = x[i] as u16 + l[i] as u16 + carry;
            out[i] = v as u8;
            carry = v >> 8;
        }
        assert_eq!(carry, 0, "S + m·L overflowed 32 octets");
        out
    };

    for row in records("malleated_sig") {
        let (name, public, message) = (&row[0], key32(&row[1]), unhex(&row[2]));
        let key = VerifyingKey::from_bytes(&public).expect("RFC public key decodes");
        let malleated = unhex(&row[3]);
        let r_half: [u8; 32] = malleated[..32].try_into().unwrap();
        let s_plus_1l: [u8; 32] = malleated[32..].try_into().unwrap();

        let build = |s: &[u8; 32]| {
            let mut bytes = [0u8; 64];
            bytes[..32].copy_from_slice(&r_half);
            bytes[32..].copy_from_slice(s);
            Signature::from_slice(&bytes).expect("64 octets")
        };

        // THE EVIDENCE-BEARING CASES. S + 2L and S + 3L satisfy the group
        // equation exactly as the published signature does.
        let s_plus_2l = add_l(&s_plus_1l);
        let s_plus_3l = add_l(&s_plus_2l);
        for (m, s) in [(2u8, &s_plus_2l), (3, &s_plus_3l)] {
            assert!(
                key.verify(&message, &build(s)).is_err(),
                "MALLEABILITY, TEST {name}: (R, S+{m}L) verified. [S+{m}L]B = [S]B because B \
                 has order L, so it satisfies RFC 8032 §5.1.7's equation and only the \
                 `0 ≤ S < L` range check can reject it."
            );
        }

        // The boundary values. Weaker — each also fails the equation — but they
        // pin that the cut is at L exactly.
        let mut l_plus_1 = l;
        l_plus_1[0] += 1;
        for (label, s) in [("L", &l), ("L+1", &l_plus_1), ("2^256-1", &[0xffu8; 32])] {
            assert!(
                key.verify(&message, &build(s)).is_err(),
                "TEST {name}: out-of-range S = {label} was accepted"
            );
        }

        // In range, wrong value: rejected by the equation, not the range check.
        let mut l_minus_1 = l;
        l_minus_1[0] -= 1;
        assert!(
            key.verify(&message, &build(&l_minus_1)).is_err(),
            "TEST {name}: S = L-1 with a wrong value was accepted"
        );
        assert!(l_minus_1 < l && l < l_plus_1, "l_le() is not ordered as expected");
    }
}

// ---------------------------------------------------------------------------
// Small-order and all-zero keys.
// ---------------------------------------------------------------------------

/// **What this asserts, and why.**
///
/// All eight points of the 8-torsion subgroup — including the all-zeros
/// encoding and the identity — are canonical curve points, and **RFC 8032
/// §5.1.3 gives no reason to reject any of them**. So this crate accepts them,
/// and asserting rejection here would be asserting a spec violation. That is
/// also what `ed25519-dalek`'s `verify` path does, so it is not a deviation;
/// `dalek`'s stricter `verify_strict` rejects them, and nothing in this tree
/// calls it.
///
/// The subgroup is *derived*, not transcribed: `derive_edge_vectors.py`
/// computes `[L]Q` for small `y` until it finds a point of order 8, then takes
/// its multiples. `src/edwards.rs`'s `eight_torsion_matches_the_derivation`
/// re-derives the same set inside this crate and asserts the two agree.
///
/// The security consequence is pinned separately, by
/// `identity_key_accepts_a_universal_forgery` below.
#[test]
fn small_order_keys_decode_and_do_not_verify_foreign_signatures() {
    let rows = records("small_order");
    assert_eq!(rows.len(), 8, "the 8-torsion has eight points");

    let signer = SigningKey::from_bytes(&[7u8; 32]);
    let message = b"a message signed by a real key";
    let signature = signer.sign(message);

    let mut orders: Vec<&str> = Vec::new();
    for row in &rows {
        let (name, bytes) = (row[0].as_str(), key32(&row[1]));
        orders.push(name);

        let key = VerifyingKey::from_bytes(&bytes).unwrap_or_else(|_| {
            panic!("small-order point {name} was rejected; RFC 8032 §5.1.3 gives no ground to")
        });
        assert_eq!(key.to_bytes(), bytes, "{name}: key did not round-trip");

        // A signature by a genuine key must not transfer to a small-order one.
        assert!(
            key.verify(message, &signature).is_err(),
            "{name}: a signature made under a different key verified"
        );
    }

    // The derivation claims a specific order profile; if the file ever changes
    // shape this test should stop rather than silently test eight copies of
    // the identity.
    orders.sort_unstable();
    assert_eq!(
        orders,
        ["order=1", "order=2", "order=4", "order=4", "order=8", "order=8", "order=8", "order=8"],
        "the small-order set is not the 8-torsion"
    );

    // The all-zeros encoding is one of them: y = 0 gives x² = -1, so x = ±i,
    // which is NOT zero — §5.1.3 step 4 does not apply and the key decodes.
    assert!(
        rows.iter().any(|r| key32(&r[1]) == [0u8; 32]),
        "the all-zeros encoding should be an order-4 point"
    );
    assert!(
        VerifyingKey::from_bytes(&[0u8; 32]).is_ok(),
        "the all-zeros public key should decode (y = 0, x = sqrt(-1))"
    );
}

/// **A forged signature this implementation accepts — correctly.**
///
/// Under the identity public key, `(R = identity, S = 0)` satisfies
/// `[S]B = R + [k]A` for *every* `k`, hence for every message, because both
/// sides are the identity whatever `k` is. No secret is involved. RFC 8032
/// §5.1.7 says the signature is valid, and a cofactorless verifier that
/// follows §5.1.7 must accept it.
///
/// This test exists to make that a **stated, tested** property rather than a
/// latent surprise: it is the reason `trust-proof-cert` must never accept a
/// small-order key as a trust anchor, and it is exactly the check
/// `dalek::verify_strict` adds.
///
/// If a future change adds small-order rejection, this test fails. That is the
/// intended behaviour — it forces the decision to be deliberate and to be
/// recorded, rather than quietly changing the accept boundary of a signature
/// scheme.
#[test]
fn identity_key_accepts_a_universal_forgery() {
    let row = &records("identity_forgery")[0];
    let (public, forged) = (key32(&row[1]), unhex(&row[2]));
    assert_eq!(forged.len(), 64);

    let mut identity = [0u8; 32];
    identity[0] = 1;
    assert_eq!(public, identity, "the forgery's key should be the identity point");

    let key = VerifyingKey::from_bytes(&public).expect("the identity encoding decodes");
    let sig = Signature::from_slice(&forged).expect("64 octets");

    // "Universal" means it does not depend on the message. Include the RFC
    // messages and a spread of lengths.
    let mut messages: Vec<Vec<u8>> = vec![Vec::new(), b"x".to_vec(), b"forge me".to_vec()];
    messages.push(vec![0xab; 1023]);
    for row in records("malleated_sig") {
        messages.push(unhex(&row[2]));
    }

    for message in &messages {
        assert!(
            key.verify(message, &sig).is_ok(),
            "the identity-key forgery was REJECTED for a {}-octet message. If small-order \
             key rejection was added deliberately, update this test and the crate docs; \
             if not, verification has changed in a way RFC 8032 §5.1.7 does not sanction.",
            message.len()
        );
    }

    // A real key must NOT accept it — otherwise the test above would pass in
    // an implementation whose `verify` returns `Ok` unconditionally.
    let real = SigningKey::from_bytes(&[3u8; 32]).verifying_key();
    assert!(
        real.verify(b"x", &sig).is_err(),
        "the all-zeros-S forgery verified under an ordinary key; `verify` accepts everything"
    );

    // And the forgery is specific to S = 0 with R = A = identity: perturbing
    // any octet of it must break it.
    for i in 0..64 {
        let mut bytes: [u8; 64] = forged.clone().try_into().unwrap();
        bytes[i] ^= 1;
        let perturbed = Signature::from_slice(&bytes).expect("64 octets");
        assert!(
            key.verify(b"x", &perturbed).is_err(),
            "forgery with octet {i} perturbed still verified"
        );
    }
}

/// The all-zeros signature under an ordinary key: always rejected.
#[test]
fn all_zero_signature_is_parsed_and_rejected_by_a_real_key() {
    // Parsing checks only the length, matching the incumbent, so the rejection
    // has to come from verification.
    let zero_sig = Signature::from_slice(&[0u8; 64]).expect("length is the only check");

    let real = SigningKey::from_bytes(&[11u8; 32]).verifying_key();
    for message in [b"".as_slice(), b"m", b"another", &[0u8; 128]] {
        assert!(
            real.verify(message, &zero_sig).is_err(),
            "the all-zeros signature was accepted by an ordinary key"
        );
    }
}

/// **The all-zeros KEY with the all-zeros SIGNATURE — a per-message answer.**
///
/// This is the case that must not be guessed at, and the first draft of this
/// file guessed wrong. The all-zeros encoding is `y = 0`, whose `x` is
/// `±sqrt(-1)`; that is a point `A` of **order 4**, not the identity. With
/// `R = A` and `S = 0`, RFC 8032 §5.1.7's equation
///
/// ```text
///     [S]B = R + [k]A     <=>     identity = [k+1]A
/// ```
///
/// holds exactly when `k ≡ 3 (mod 4)`. `k` is a SHA-512 digest reduced mod
/// `L`, so **about a quarter of all messages are accepted, correctly**, and an
/// implementation that rejected all of them would be violating §5.1.7.
///
/// So the known answer here is a per-message verdict, derived by
/// `derive_edge_vectors.py` — which evaluates the full group equation in
/// Python bignums *and* cross-checks it against the `k ≡ 3 (mod 4)` shortcut,
/// refusing to emit anything if the two disagree. Of the 33 sampled messages
/// it accepts 8, so this test discriminates in both directions: an
/// implementation that always accepted, and one that always rejected, would
/// each fail it.
///
/// The security reading is the same as `identity_key_accepts_a_universal_forgery`:
/// a small-order public key gives no guarantee at all, and `trust-proof-cert`
/// must not accept one as a trust anchor. This is not a defect in this crate.
#[test]
fn all_zero_key_accepts_the_all_zero_signature_for_exactly_the_derived_messages() {
    let zero_sig = Signature::from_slice(&[0u8; 64]).expect("length is the only check");
    let zero_key = VerifyingKey::from_bytes(&[0u8; 32]).expect("y = 0 is an order-4 curve point");

    let rows = records("zero_key_zero_sig");
    let (mut expected_ok, mut expected_err) = (0, 0);

    for row in &rows {
        let message = unhex(&row[0]);
        let expected = match row[1].as_str() {
            "1" => true,
            "0" => false,
            other => panic!("bad verdict field {other:?}"),
        };
        let k_mod_4: u8 = row[2].parse().expect("k mod 4");
        assert_eq!(expected, k_mod_4 == 3, "the data file is internally inconsistent");

        let got = zero_key.verify(&message, &zero_sig).is_ok();
        assert_eq!(
            got,
            expected,
            "all-zeros key, all-zeros signature, message {:?}: got accept={got}, derived \
             accept={expected} (k mod 4 = {k_mod_4}). RFC 8032 §5.1.7 accepts exactly when \
             k ≡ 3 (mod 4) for this key.",
            core::str::from_utf8(&message).unwrap_or("<non-utf8>")
        );
        if expected { expected_ok += 1 } else { expected_err += 1 }
    }

    // Non-vacuity: the sample must contain both outcomes, or a constant-verdict
    // implementation would pass.
    assert!(expected_ok > 0, "no accepted message in the sample");
    assert!(expected_err > 0, "no rejected message in the sample");
}
