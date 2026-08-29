// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **The differential acceptance gate for replacing `ed25519-dalek`.**
//!
//! This file compares `trust-ed25519` against `ed25519-dalek 2.2.0` while both
//! are in the graph. It is the evidence the swap is gated on, and it must be
//! deleted — not disabled — on the day the incumbent leaves.
//!
//! # What agreement means, and where it deliberately stops
//!
//! On everything a conforming signer produces, the two implementations must be
//! **octet-identical**: same public key from a seed, same signature from a key
//! and message, same accept/reject verdict on a candidate signature. Those are
//! the tests that would catch a real defect.
//!
//! On two classes of *malformed input* the two deliberately disagree, and this
//! file **asserts the disagreement** rather than skipping it:
//!
//! * **D1** — a verifying key whose `y` is `>= p`. There are exactly nineteen
//!   such encodings per sign bit (`p .. 2^255-1`), and `non_canonical_keys`
//!   enumerates all of them. RFC 8032 §5.1.3 says decoding fails; dalek
//!   accepts, silently reducing `y` mod `p`.
//! * **D2** — an encoding with `x = 0` and the sign bit set, i.e. the identity
//!   and the order-2 point with a spurious sign. RFC 8032 §5.1.3 says decoding
//!   fails; dalek accepts.
//!
//! A deviation that is not tested is a deviation nobody knows about, and the
//! failure mode of "skip the cases where we differ" is that a *new*, unintended
//! difference lands in the same skipped region. So both are pinned, in both
//! directions: this crate must reject, and the incumbent's behaviour is
//! recorded so that a change in it is also a test failure.
//!
//! # Coverage
//!
//! | Lane | Extent |
//! |---|---|
//! | key derivation | 512 pseudorandom seeds + the three degenerate ones |
//! | signing | **every** message length 0..=600, plus 4 MiB / 4 MiB+1 / 12 MiB+113 |
//! | cross-verification | both directions at every length 0..=600 |
//! | corrupted signature | all 512 single-bit flips at four lengths, + 12 structural substitutions |
//! | corrupted message | 1841 cases: single-bit flips, ±1-octet length changes, whole-message substitution |
//! | wrong public key | all 256 ordered pairs from 16 keys (16 must verify, 240 must not) |
//! | `S >= L` | `S + nL` for n=1..8 (these satisfy the equation), 256 random out-of-range `S`, and the `L-1`/`L` boundary |
//! | key parsing | 2048 pseudorandom encodings, both verdicts exercised |
//! | deviations D1/D2 | exhaustive |
//!
//! Sweeps that compare accept/reject verdicts route through [`Census`], which
//! collects **every** disagreement with its exact input and both verdicts
//! rather than dying on the first — a differential's job is to characterise a
//! disagreeing set, not to announce that one exists. Each census also asserts
//! a floor on the number of cases it examined, because a sweep whose filter
//! excluded everything reports the same green as one that found nothing.
//!
//! # Every test here has been seen to fail
//!
//! Eight mutations, applied one at a time to a byte-identical isolated copy of
//! the crate, each reverted with a SHA-256 check. Results are in the report
//! that accompanied this file; the two that are load-bearing for the design of
//! this file are recorded where they apply:
//!
//! * **MD3** (message truncated at 256 octets in sign and verify) fails
//!   `signatures_agree_over_every_length_to_600` while a 0..=256 control sweep
//!   still passes — so the extension past 256 is load-bearing, not decoration.
//! * **MD2** (one bit of the `R` comparison masked out) is caught by nothing,
//!   for a structural reason recorded on
//!   `corrupted_signature_every_single_bit_flip_is_rejected`.

use ed25519_dalek as dalek;
use ed25519_dalek::{Signer as DalekSigner, Verifier as DalekVerifier};
use trust_ed25519 as trust;
use trust_ed25519::{Signer as TrustSigner, Verifier as TrustVerifier};

/// A deterministic byte source. Not cryptographic and not meant to be — it
/// only has to make the sweep reproducible, so a failure can be re-run.
struct Xorshift(u64);

impl Xorshift {
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn fill(&mut self, out: &mut [u8]) {
        for chunk in out.chunks_mut(8) {
            let v = self.next_u64().to_le_bytes();
            let n = chunk.len();
            chunk.copy_from_slice(&v[..n]);
        }
    }
}

/// `p = 2^255 - 19`, little-endian, for the canonicality classification below.
const P_LE: [u8; 32] = [
    0xed, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f,
];

/// `L`, little-endian.
const L_LE: [u8; 32] = [
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
];

// ---------------------------------------------------------------------------
// The agreement half: everything a conforming signer produces.
// ---------------------------------------------------------------------------

/// Key derivation (RFC 8032 §5.1.5) is octet-identical across 512 seeds.
#[test]
fn public_keys_agree() {
    let mut rng = Xorshift(0x243f_6a88_85a3_08d3);
    for i in 0..512 {
        let mut seed = [0u8; 32];
        rng.fill(&mut seed);
        let ours = trust::SigningKey::from_bytes(&seed).verifying_key().to_bytes();
        let theirs = dalek::SigningKey::from_bytes(&seed).verifying_key().to_bytes();
        assert_eq!(ours, theirs, "seed {i}: derived public keys differ");
    }
    // The degenerate seeds too.
    for seed in [[0u8; 32], [0xffu8; 32], [0x01u8; 32]] {
        let ours = trust::SigningKey::from_bytes(&seed).verifying_key().to_bytes();
        let theirs = dalek::SigningKey::from_bytes(&seed).verifying_key().to_bytes();
        assert_eq!(ours, theirs, "degenerate seed {seed:02x?}");
    }
}

/// Signing (§5.1.6) is octet-identical over **every** message length 0..=600.
///
/// Ed25519 is deterministic — §5.1.6 derives the nonce `r` from `prefix || M`,
/// with no randomness anywhere — so "the signatures differ" is never a valid
/// variant. Any difference at any length is a defect in one of the two.
///
/// # Why 600, and why every length rather than a sample
///
/// The message is absorbed by SHA-512 **twice, at two different offsets**:
/// once behind the 32-octet `prefix`, and once behind the 64 octets of
/// `R || A`. SHA-512's block is 128 octets, and its padding needs an extra
/// block once the final fragment reaches 112. So the two hashes hit their
/// interesting lengths at *different* message lengths — `M ≡ 96 (mod 128)` for
/// the first and `M ≡ 64 (mod 128)` for the second — and the padding-overflow
/// boundaries interleave between them. A sampled sweep chosen for one hash's
/// boundaries systematically misses the other's. 0..=600 is 4.7 blocks: it
/// crosses every residue class of both hashes at least four times, so no
/// boundary is represented only once.
#[test]
fn signatures_agree_over_every_length_to_600() {
    let mut rng = Xorshift(0x1359_5c66_f28a_bcde);
    let mut seed = [0u8; 32];
    rng.fill(&mut seed);
    let ours = trust::SigningKey::from_bytes(&seed);
    let theirs = dalek::SigningKey::from_bytes(&seed);

    let mut message = Vec::new();
    for len in 0..=600usize {
        message.resize(len, 0);
        rng.fill(&mut message);
        let a = ours.sign(&message).to_bytes();
        let b = theirs.sign(&message).to_bytes();
        assert_eq!(
            hex(&a),
            hex(&b),
            "message length {len}: signatures differ\n    seed:    {}\n    message: {}",
            hex(&seed),
            hex(&message)
        );
    }
}

/// Signing agrees across many *keys* as well as many messages.
#[test]
fn signatures_agree_across_keys() {
    let mut rng = Xorshift(0x9e37_79b9_7f4a_7c15);
    for i in 0..128 {
        let mut seed = [0u8; 32];
        rng.fill(&mut seed);
        let mut message = [0u8; 96];
        rng.fill(&mut message);
        let n = (i % 96) + 1;
        let msg = &message[..n];
        let a = trust::SigningKey::from_bytes(&seed).sign(msg).to_bytes();
        let b = dalek::SigningKey::from_bytes(&seed).sign(msg).to_bytes();
        assert_eq!(a, b, "key {i}: signatures differ on a {n}-octet message");
    }
}

/// Each implementation verifies the other's signatures, and rejects the same
/// perturbations.
///
/// Signing agreement alone would not catch a verifier that accepts too much:
/// this is the direction that would hide a broken verification equation.
#[test]
fn verification_agrees_including_cross_verification() {
    let mut rng = Xorshift(0xc2b2_ae3d_27d4_eb4f);
    for i in 0..128 {
        let mut seed = [0u8; 32];
        rng.fill(&mut seed);
        let mut message = [0u8; 64];
        rng.fill(&mut message);

        let ours = trust::SigningKey::from_bytes(&seed);
        let theirs = dalek::SigningKey::from_bytes(&seed);
        let our_vk = ours.verifying_key();
        let their_vk = theirs.verifying_key();

        let our_sig = ours.sign(&message);
        let their_sig = theirs.sign(&message);

        // Cross-verification, both directions.
        assert!(their_vk.verify(&message, &their_sig).is_ok(), "{i}: dalek rejects its own");
        assert!(
            their_vk
                .verify(&message, &dalek::Signature::from_slice(&our_sig.to_bytes()).unwrap())
                .is_ok(),
            "{i}: dalek rejected our signature"
        );
        assert!(
            our_vk
                .verify(&message, &trust::Signature::from_slice(&their_sig.to_bytes()).unwrap())
                .is_ok(),
            "{i}: we rejected dalek's signature"
        );

        // And both must reject the same perturbations, verdict for verdict.
        for bit in [0u32, 1, 7, 128, 255, 256, 300, 380, 511] {
            let mut bytes = our_sig.to_bytes();
            bytes[(bit / 8) as usize] ^= 1 << (bit % 8);
            let a = our_vk.verify(&message, &trust::Signature::from_slice(&bytes).unwrap()).is_ok();
            let b =
                their_vk.verify(&message, &dalek::Signature::from_slice(&bytes).unwrap()).is_ok();
            assert_eq!(a, b, "{i}: verdicts differ on signature bit {bit} flipped");
            assert!(!a, "{i}: perturbed signature accepted");
        }
    }
}

/// `Signature::from_slice` accepts and rejects exactly the same slices.
#[test]
fn signature_parsing_agrees() {
    for len in 0..80usize {
        let bytes = vec![0x5au8; len];
        let a = trust::Signature::from_slice(&bytes).is_ok();
        let b = dalek::Signature::from_slice(&bytes).is_ok();
        assert_eq!(a, b, "length {len}: from_slice verdicts differ");
        assert_eq!(a, len == 64, "length {len}: unexpected verdict {a}");
    }
    // 64 zero octets parse — the s-range check is deferred to verification,
    // in both implementations.
    assert!(trust::Signature::from_slice(&[0u8; 64]).is_ok());
    assert!(dalek::Signature::from_slice(&[0u8; 64]).is_ok());
}

/// `S >= L` is rejected by both — the malleability check of §5.1.7.
#[test]
fn out_of_range_s_is_rejected_by_both() {
    let mut rng = Xorshift(0x0123_4567_89ab_cdef);
    let mut seed = [0u8; 32];
    rng.fill(&mut seed);
    let ours = trust::SigningKey::from_bytes(&seed);
    let theirs = dalek::SigningKey::from_bytes(&seed);
    let message = b"malleability";
    let valid = ours.sign(message).to_bytes();
    assert_eq!(valid, theirs.sign(message).to_bytes());

    let our_vk = ours.verifying_key();
    let their_vk = theirs.verifying_key();
    assert!(our_vk.verify(message, &trust::Signature::from_slice(&valid).unwrap()).is_ok());

    // THE MALLEATED SIGNATURE — the case this test exists for.
    //
    // `[S + L]B = [S]B`, because B has order L. So `(R, S+L)` satisfies the
    // verification *equation* exactly as `(R, S)` does, and the ONLY thing
    // that rejects it is the range check. Every other out-of-range case below
    // also fails the equation, so each of them would still be rejected by an
    // implementation with no range check at all — they cannot, on their own,
    // show that the check is present.
    //
    // (This was measured: deleting `Scalar::from_canonical_bytes`'s range test
    // left every other assertion in this function passing.)
    let mut malleated = valid;
    let mut s_plus_l = [0u8; 32];
    let mut carry = 0u16;
    for i in 0..32 {
        let v = valid[32 + i] as u16 + L_LE[i] as u16 + carry;
        s_plus_l[i] = v as u8;
        carry = v >> 8;
    }
    assert_eq!(carry, 0, "S + L overflowed 32 octets");
    malleated[32..].copy_from_slice(&s_plus_l);
    assert_ne!(malleated, valid, "S + L must differ from S");

    let a = our_vk.verify(message, &trust::Signature::from_slice(&malleated).unwrap()).is_ok();
    let b = their_vk.verify(message, &dalek::Signature::from_slice(&malleated).unwrap()).is_ok();
    assert_eq!(a, b, "malleated (R, S+L): verdicts differ");
    assert!(
        !a,
        "MALLEABILITY: (R, S+L) verified. It satisfies the verification equation, so only \
         the S < L range check of RFC 8032 §5.1.7 can reject it, and it did not."
    );

    // S = L exactly, S = L+1, S with the three high bits set, S = 2^256-1.
    let mut cases: Vec<[u8; 32]> = Vec::new();
    cases.push(L_LE);
    let mut l_plus_1 = L_LE;
    l_plus_1[0] += 1;
    cases.push(l_plus_1);
    let mut high = [0u8; 32];
    high[31] = 0xe0;
    cases.push(high);
    cases.push([0xff; 32]);

    for (i, s) in cases.iter().enumerate() {
        let mut bytes = valid;
        bytes[32..].copy_from_slice(s);
        let a = our_vk.verify(message, &trust::Signature::from_slice(&bytes).unwrap()).is_ok();
        let b = their_vk.verify(message, &dalek::Signature::from_slice(&bytes).unwrap()).is_ok();
        assert_eq!(a, b, "out-of-range S case {i}: verdicts differ");
        assert!(!a, "out-of-range S case {i} was accepted");
    }

    // L-1 is in range: both must reach the equation and both must reject it,
    // which is a different code path from the range check.
    let mut in_range = valid;
    let mut l_minus_1 = L_LE;
    l_minus_1[0] -= 1;
    in_range[32..].copy_from_slice(&l_minus_1);
    let a = our_vk.verify(message, &trust::Signature::from_slice(&in_range).unwrap()).is_ok();
    let b = their_vk.verify(message, &dalek::Signature::from_slice(&in_range).unwrap()).is_ok();
    assert_eq!(a, b, "in-range but wrong S: verdicts differ");
    assert!(!a);
}

/// `VerifyingKey::from_bytes` agrees on every *canonical* encoding.
///
/// Roughly half of arbitrary 32-octet strings are not curve points, so this
/// sweeps both verdicts. Non-canonical encodings are excluded here and covered
/// exhaustively by `non_canonical_keys` below — random strings essentially
/// never hit them (19 encodings out of 2^255).
#[test]
fn key_parsing_agrees_on_canonical_encodings() {
    let mut rng = Xorshift(0xdead_beef_cafe_f00d);
    let (mut accepted, mut rejected) = (0, 0);
    for i in 0..2048 {
        let mut bytes = [0u8; 32];
        rng.fill(&mut bytes);
        if is_non_canonical(&bytes) || is_zero_x_with_sign(&bytes) {
            continue;
        }
        let a = trust::VerifyingKey::from_bytes(&bytes).is_ok();
        let b = dalek::VerifyingKey::from_bytes(&bytes).is_ok();
        assert_eq!(a, b, "key {i} ({bytes:02x?}): parse verdicts differ");
        if a { accepted += 1 } else { rejected += 1 }
    }
    assert!(accepted > 500, "only {accepted} accepted; sweep is not exercising the accept path");
    assert!(rejected > 500, "only {rejected} rejected; sweep is not exercising the reject path");
}

/// Round-tripping a key through `to_bytes`/`from_bytes` is total in both.
///
/// `trust-proof-cert`'s `TrustAnchorPolicy::from_verifying_keys` `.expect()`s
/// this, so a failure here is a panic in production, not an error.
#[test]
fn key_round_trip_is_total() {
    let mut rng = Xorshift(0xfeed_face_0000_1234);
    for i in 0..256 {
        let mut seed = [0u8; 32];
        rng.fill(&mut seed);
        let ours = trust::SigningKey::from_bytes(&seed).verifying_key();
        let theirs = dalek::SigningKey::from_bytes(&seed).verifying_key();
        assert_eq!(ours.to_bytes(), theirs.to_bytes(), "key {i}");
        assert!(trust::VerifyingKey::from_bytes(&ours.to_bytes()).is_ok(), "key {i} round trip");
        assert!(dalek::VerifyingKey::from_bytes(&theirs.to_bytes()).is_ok(), "key {i} round trip");
    }
}

// ---------------------------------------------------------------------------
// The deviation half: the two places we deliberately reject more.
// ---------------------------------------------------------------------------

/// **D1, exhaustively.** The nineteen non-canonical `y` values, both sign bits.
///
/// A 255-bit encoding is non-canonical exactly when it denotes a value in
/// `[p, 2^255)`, and there are nineteen of those. This enumerates every one.
#[test]
fn non_canonical_keys() {
    let mut ours_rejected = 0;
    let mut theirs_accepted = 0;

    for offset in 0..19u16 {
        for sign in [0u8, 0x80] {
            // p + offset, little-endian, with the sign bit applied.
            let mut bytes = P_LE;
            let mut carry = offset as u32;
            for b in bytes.iter_mut() {
                let v = *b as u32 + (carry & 0xff);
                *b = v as u8;
                carry = (carry >> 8) + (v >> 8);
            }
            assert!(is_non_canonical(&bytes), "offset {offset} was not classified non-canonical");
            bytes[31] |= sign;

            assert!(
                trust::VerifyingKey::from_bytes(&bytes).is_err(),
                "D1: p+{offset} (sign {sign:#x}) was accepted; RFC 8032 §5.1.3 says decoding fails"
            );
            ours_rejected += 1;
            if dalek::VerifyingKey::from_bytes(&bytes).is_ok() {
                theirs_accepted += 1;
            }
        }
    }

    assert_eq!(ours_rejected, 38, "expected 19 non-canonical values x 2 sign bits");
    // The deviation must be REAL: if the incumbent rejected all of these too,
    // this test would be pinning a difference that does not exist, and the
    // crate docs would be wrong. Measured against ed25519-dalek 2.2.0.
    assert!(
        theirs_accepted > 0,
        "the incumbent rejected every non-canonical key; deviation D1 no longer exists \
         and the crate documentation must be corrected"
    );
}

/// **D2.** `x = 0` with the sign bit set: the identity and the order-2 point.
#[test]
fn zero_x_with_sign_bit_keys() {
    // y = 1 (the identity) and y = p-1 (the order-2 point (0, -1)) are the only
    // two y values whose x is zero.
    let mut identity = [0u8; 32];
    identity[0] = 1;
    let mut order_two = P_LE;
    order_two[0] -= 1;

    let mut theirs_accepted = 0;
    for base in [identity, order_two] {
        // Without the sign bit both accept: x = 0 is a legitimate coordinate.
        assert!(
            trust::VerifyingKey::from_bytes(&base).is_ok(),
            "x=0 with a clear sign bit must decode"
        );
        assert!(dalek::VerifyingKey::from_bytes(&base).is_ok());

        // With it, RFC 8032 §5.1.3 says decoding fails.
        let mut signed = base;
        signed[31] |= 0x80;
        assert!(is_zero_x_with_sign(&signed), "classifier missed a D2 case");
        assert!(
            trust::VerifyingKey::from_bytes(&signed).is_err(),
            "D2: x=0 with x_0=1 was accepted; RFC 8032 §5.1.3 says decoding fails"
        );
        if dalek::VerifyingKey::from_bytes(&signed).is_ok() {
            theirs_accepted += 1;
        }
    }
    assert!(
        theirs_accepted > 0,
        "the incumbent rejected every x=0/sign-set key; deviation D2 no longer exists \
         and the crate documentation must be corrected"
    );
}

// ---------------------------------------------------------------------------
// Classifiers, shared by the sweeps above.
// ---------------------------------------------------------------------------

/// `y >= p` once bit 255 is masked off.
fn is_non_canonical(bytes: &[u8; 32]) -> bool {
    let mut masked = *bytes;
    masked[31] &= 0x7f;
    // Little-endian compare from the top.
    for i in (0..32).rev() {
        if masked[i] != P_LE[i] {
            return masked[i] > P_LE[i];
        }
    }
    true // equal to p is itself non-canonical
}

/// The sign bit is set and `y` is one of the two values whose `x` is zero.
fn is_zero_x_with_sign(bytes: &[u8; 32]) -> bool {
    if bytes[31] & 0x80 == 0 {
        return false;
    }
    let mut masked = *bytes;
    masked[31] &= 0x7f;
    let mut identity = [0u8; 32];
    identity[0] = 1;
    let mut order_two = P_LE;
    order_two[0] -= 1;
    masked == identity || masked == order_two
}

/// Lowercase hex.
///
/// Every assertion below prints the octets it disagreed on, not an index into
/// a sweep: a differential failure has to be reproducible from the failure
/// message alone, because the sweep that produced it is seeded and long and
/// nobody re-derives case 4718 by hand.
fn hex(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        let _ = write!(s, "{b:02x}");
    }
    s
}

/// `ACCEPT` / `REJECT`, so a report reads as verdicts rather than booleans.
fn verdict(ok: bool) -> &'static str {
    if ok { "ACCEPT" } else { "REJECT" }
}

/// Collects **every** accept/reject disagreement instead of dying on the first.
///
/// The brief for this file is explicit that a semantic disagreement is a
/// *finding* to be reported with its exact input and both verdicts — not
/// something to paper over, and not something to learn about one case at a
/// time. A first-failure `assert_eq!` answers "is there a disagreement"; it
/// does not answer "what is the shape of the disagreeing set", which is the
/// question that decides whether a difference is a bug or a documented
/// deviation like D1/D2 above.
///
/// `checked` is asserted against a floor by [`Census::finish`] for the reason
/// in `MEMORY.md`'s "a SILENT instrument reads as a clean result": a sweep
/// whose filter excluded everything reports the same green as a sweep that
/// examined thousands of cases and found nothing.
#[derive(Default)]
struct Census {
    checked: usize,
    ours_accepted: usize,
    theirs_accepted: usize,
    disagreements: Vec<String>,
}

impl Census {
    /// Record one comparison. `label` must identify the exact input.
    fn check(&mut self, label: &str, ours: bool, theirs: bool) {
        self.checked += 1;
        if ours {
            self.ours_accepted += 1;
        }
        if theirs {
            self.theirs_accepted += 1;
        }
        if ours != theirs {
            self.disagreements.push(format!(
                "  {label}\n      trust-ed25519: {}\n      ed25519-dalek: {}",
                verdict(ours),
                verdict(theirs)
            ));
        }
    }

    /// Fail if anything disagreed, or if the sweep examined too little.
    fn finish(&self, what: &str, min_checked: usize) {
        // Printed so `--nocapture` shows the size of each sweep. A differential
        // that silently shrank still reports "ok".
        println!(
            "  [census] {what}: {} cases compared, {} accepted by trust-ed25519, \
             {} by ed25519-dalek, {} disagreements",
            self.checked,
            self.ours_accepted,
            self.theirs_accepted,
            self.disagreements.len()
        );
        assert!(
            self.checked >= min_checked,
            "{what}: only {} cases examined, expected at least {min_checked} — the sweep \
             is not exercising what it claims to",
            self.checked
        );
        assert!(
            self.disagreements.is_empty(),
            "{what}: {} of {} cases DISAGREED between trust-ed25519 and ed25519-dalek\n{}",
            self.disagreements.len(),
            self.checked,
            self.disagreements.join("\n")
        );
    }
}

// ---------------------------------------------------------------------------
// Multi-megabyte messages.
// ---------------------------------------------------------------------------

/// Signatures agree octet-for-octet on multi-megabyte messages.
///
/// # What this covers that the 0..=600 sweep does not
///
/// SHA-512's length field is the message length in **bits**, and everything
/// under 600 octets lives in the low 13 bits of it. A defect in how the length
/// is encoded, a 32-bit block counter, or an `as u32` on a byte count is
/// invisible to every other test in this crate and to `trust-sha2`'s own
/// suite. The largest case here is 12 MiB — over 2^26 bits — so the length
/// field's fourth octet is non-zero and the block counter has passed 2^16.
///
/// It also exercises the streaming `update` path at a scale where a
/// buffer-carry defect between calls has somewhere to hide: `try_sign` feeds
/// the message as one `update` behind a 32-octet prefix, so every internal
/// block boundary falls at a *non-zero offset within the caller's slice*.
///
/// # Cost, measured
///
/// 20 MiB of message across three cases, absorbed eight times over (each side
/// signs with two passes and verifies twice), is ~2.0 s in the debug profile.
/// The same test at a quarter of these sizes ran in 0.50 s — the linear
/// scaling is what establishes that the bytes are actually being hashed rather
/// than short-circuited somewhere.
#[test]
fn signatures_agree_on_multi_megabyte_messages() {
    // 12 MiB + 113: the final fragment is 113 octets, one past the point where
    // SHA-512's padding no longer fits in the last block. With the 32-octet
    // prefix the first hash's final fragment is 17 (mod 128) and with the
    // 64-octet `R || A` prefix the second's is 49, so one message exercises
    // both sides of the padding boundary. `(4 << 20) + 1` puts a nearly-empty
    // final block after a whole number of full ones.
    const SIZES: [usize; 3] = [4 << 20, (4 << 20) + 1, 12 * (1 << 20) + 113];

    let mut rng = Xorshift(0x5555_aaaa_1234_5678);
    let mut seed = [0u8; 32];
    rng.fill(&mut seed);
    let ours = trust::SigningKey::from_bytes(&seed);
    let theirs = dalek::SigningKey::from_bytes(&seed);
    let our_vk = ours.verifying_key();
    let their_vk = theirs.verifying_key();

    for size in SIZES {
        let mut message = vec![0u8; size];
        rng.fill(&mut message);

        let a = ours.sign(&message).to_bytes();
        let b = theirs.sign(&message).to_bytes();
        assert_eq!(
            hex(&a),
            hex(&b),
            "{size}-octet message: signatures differ (seed {})",
            hex(&seed)
        );

        // And both verifiers accept, at this size, in both directions.
        assert!(
            our_vk.verify(&message, &trust::Signature::from_slice(&b).unwrap()).is_ok(),
            "{size}-octet message: we rejected dalek's signature {}",
            hex(&b)
        );
        assert!(
            their_vk.verify(&message, &dalek::Signature::from_slice(&a).unwrap()).is_ok(),
            "{size}-octet message: dalek rejected our signature {}",
            hex(&a)
        );

        // A single flipped bit in the middle of a multi-megabyte message must
        // still be caught by both. This is the case a truncated absorb passes.
        let mut corrupted = message.clone();
        corrupted[size / 2] ^= 0x01;
        let mine = our_vk.verify(&corrupted, &trust::Signature::from_slice(&a).unwrap()).is_ok();
        let theirs_ok =
            their_vk.verify(&corrupted, &dalek::Signature::from_slice(&a).unwrap()).is_ok();
        assert_eq!(
            mine,
            theirs_ok,
            "{size}-octet message, bit 0 of octet {} flipped: verdicts differ ({} vs {})",
            size / 2,
            verdict(mine),
            verdict(theirs_ok)
        );
        assert!(!mine, "{size}-octet message: a one-bit corruption at octet {} verified", size / 2);
    }
}

// ---------------------------------------------------------------------------
// Cross-verification, both directions.
// ---------------------------------------------------------------------------

/// Each implementation accepts the other's signatures, at every length 0..=600.
///
/// # What this does and does not prove
///
/// Because signing agrees octet-for-octet (the test above), "dalek verifies
/// our signature" and "dalek verifies its own signature" are statements about
/// the *same 64 octets*. This test is therefore not evidence that two
/// different signature encodings interoperate — there are not two encodings.
///
/// What it is evidence of is the direction signing agreement cannot reach: a
/// verifier that rejects valid input. Signature agreement is a property of the
/// two signers; it says nothing about either verifier. A `verify` that
/// returned `Err` unconditionally would pass every signing test in this file
/// and fail here, at every length.
///
/// The genuinely independent cross-direction — our verifier on signatures no
/// implementation in this graph produced — is `tests/kat_rfc8032.rs`, which
/// verifies the five published RFC 8032 §7.1 signatures.
#[test]
fn cross_verification_in_both_directions() {
    let mut rng = Xorshift(0x7777_3333_dddd_9999);
    let mut seed = [0u8; 32];
    rng.fill(&mut seed);
    let ours = trust::SigningKey::from_bytes(&seed);
    let theirs = dalek::SigningKey::from_bytes(&seed);
    let our_vk = ours.verifying_key();
    let their_vk = theirs.verifying_key();
    assert_eq!(hex(&our_vk.to_bytes()), hex(&their_vk.to_bytes()));

    let mut census = Census::default();
    let mut message = Vec::new();
    for len in 0..=600usize {
        message.resize(len, 0);
        rng.fill(&mut message);

        let our_sig = ours.sign(&message).to_bytes();
        let their_sig = theirs.sign(&message).to_bytes();

        // dalek's verifier on our signature.
        census.check(
            &format!("len {len}: dalek verifies OUR signature {}", hex(&our_sig)),
            true,
            their_vk.verify(&message, &dalek::Signature::from_slice(&our_sig).unwrap()).is_ok(),
        );
        // Our verifier on dalek's signature.
        census.check(
            &format!("len {len}: WE verify dalek's signature {}", hex(&their_sig)),
            our_vk.verify(&message, &trust::Signature::from_slice(&their_sig).unwrap()).is_ok(),
            true,
        );
    }
    census.finish("cross-verification", 1202);
    assert_eq!(
        census.ours_accepted, census.checked,
        "a valid signature was rejected somewhere in the sweep"
    );
}

// ---------------------------------------------------------------------------
// Negative class 1 — corrupted signature.
// ---------------------------------------------------------------------------

/// **Every** single-bit corruption of a signature — all 512 — is rejected by
/// both, at four message lengths.
///
/// Exhaustive rather than sampled because the two halves are checked by
/// completely different code: bits 0..255 are `R`, which is compared as octets
/// after being recomputed, and bits 256..511 are `S`, which is a scalar that
/// first has to pass the `S < L` range check. Within `R`, the top bit is the
/// compressed point's sign; within `S`, the top three bits are always zero in a
/// valid signature, so flipping them lands out of range rather than in the
/// equation. A sampled sweep picks its samples from whichever of those regions
/// the author was thinking about.
///
/// # What exhaustiveness does NOT buy, measured
///
/// This test was written expecting to be strictly more sensitive than the nine
/// hand-picked bit positions in
/// `verification_agrees_including_cross_verification`. **It is not, and the
/// mutation campaign said so.** Mutation MD2 — masking bit 3 of the recomputed
/// `R`'s first octet out of the comparison, a one-character weakening — was
/// caught by *nothing in the crate*, this test included.
///
/// The reason is structural, and it is worth stating because it bounds what
/// any signature-corruption test can prove: `R` is an **input to the hash**
/// that produces `k`, so perturbing one bit of `R` does not perturb one bit of
/// the recomputed point — it changes the recomputed point completely.
/// Weakening the final comparison by `n` bits therefore only accepts a forgery
/// with probability `2^(n-256)`, and no black-box sweep of any size can
/// observe that. MD2 is an *equivalent mutant in practice*, not a missed
/// defect; catching it needs a code-level review of the comparison, which is
/// why the comparison is four lines long and has this note pointing at it.
///
/// What the exhaustive sweep does buy over the sampled one is that its 2048
/// cases span both halves uniformly, so a *severe* truncation of the
/// comparison (MD8: the `R` half not compared at all) is caught with margin
/// rather than by luck.
#[test]
fn corrupted_signature_every_single_bit_flip_is_rejected() {
    let mut rng = Xorshift(0x2718_2818_2845_9045);
    let mut seed = [0u8; 32];
    rng.fill(&mut seed);
    let ours = trust::SigningKey::from_bytes(&seed);
    let theirs = dalek::SigningKey::from_bytes(&seed);
    let our_vk = ours.verifying_key();
    let their_vk = theirs.verifying_key();

    let mut census = Census::default();
    for len in [0usize, 1, 32, 129] {
        let mut message = vec![0u8; len];
        rng.fill(&mut message);
        let valid = ours.sign(&message).to_bytes();
        assert_eq!(hex(&valid), hex(&theirs.sign(&message).to_bytes()));

        for bit in 0..512usize {
            let mut bytes = valid;
            bytes[bit / 8] ^= 1 << (bit % 8);
            let mine = our_vk.verify(&message, &trust::Signature::from_slice(&bytes).unwrap());
            let theirs_r =
                their_vk.verify(&message, &dalek::Signature::from_slice(&bytes).unwrap());
            census.check(
                &format!(
                    "len {len}, signature bit {bit} flipped ({} half): {}",
                    if bit < 256 { "R" } else { "S" },
                    hex(&bytes)
                ),
                mine.is_ok(),
                theirs_r.is_ok(),
            );
        }
    }
    census.finish("single-bit signature corruption", 2048);
    assert_eq!(
        census.ours_accepted, 0,
        "{} corrupted signatures were ACCEPTED; a signature scheme that accepts a \
         one-bit change is forged, not verified",
        census.ours_accepted
    );
    assert_eq!(census.theirs_accepted, 0, "the incumbent accepted a corrupted signature");
}

/// Structural corruptions of a signature that are not single-bit flips.
///
/// A bit flip only ever produces a *nearby* signature. These are the
/// substitutions an attacker would actually reach for: reuse a real `R` with a
/// real `S` from a different signature, zero a half, swap the halves.
#[test]
fn structurally_corrupted_signatures_are_rejected_by_both() {
    let mut rng = Xorshift(0x1414_2135_6237_3095);
    let mut seed = [0u8; 32];
    rng.fill(&mut seed);
    let ours = trust::SigningKey::from_bytes(&seed);
    let theirs = dalek::SigningKey::from_bytes(&seed);
    let our_vk = ours.verifying_key();
    let their_vk = theirs.verifying_key();

    let msg_a = b"the message that was signed".to_vec();
    let msg_b = b"a different message entirely".to_vec();
    let sig_a = ours.sign(&msg_a).to_bytes();
    let sig_b = ours.sign(&msg_b).to_bytes();
    assert_eq!(hex(&sig_a), hex(&theirs.sign(&msg_a).to_bytes()));
    assert_eq!(hex(&sig_b), hex(&theirs.sign(&msg_b).to_bytes()));

    let mut cases: Vec<(String, [u8; 64])> = Vec::new();

    // R from one signature, S from another.
    let mut mixed = sig_a;
    mixed[32..].copy_from_slice(&sig_b[32..]);
    cases.push(("R of sig(msg_a) with S of sig(msg_b)".to_string(), mixed));

    let mut mixed2 = sig_b;
    mixed2[32..].copy_from_slice(&sig_a[32..]);
    cases.push(("R of sig(msg_b) with S of sig(msg_a)".to_string(), mixed2));

    // Halves swapped.
    let mut swapped = [0u8; 64];
    swapped[..32].copy_from_slice(&sig_a[32..]);
    swapped[32..].copy_from_slice(&sig_a[..32]);
    cases.push(("halves of sig(msg_a) swapped".to_string(), swapped));

    // Zeroed halves.
    let mut zero_r = sig_a;
    zero_r[..32].fill(0);
    cases.push(("R zeroed".to_string(), zero_r));
    let mut zero_s = sig_a;
    zero_s[32..].fill(0);
    cases.push(("S zeroed".to_string(), zero_s));

    // R replaced by the identity point's encoding, and by the public key.
    let mut identity_r = sig_a;
    identity_r[..32].fill(0);
    identity_r[0] = 1;
    cases.push(("R replaced by the identity encoding".to_string(), identity_r));
    let mut key_r = sig_a;
    key_r[..32].copy_from_slice(&our_vk.to_bytes());
    cases.push(("R replaced by the public key encoding".to_string(), key_r));

    // Every octet set to the same value (0x00 is also the all-zero signature).
    for fill in [0x00u8, 0x01, 0x7f, 0x80, 0xff] {
        cases.push((format!("every octet = {fill:#04x}"), [fill; 64]));
    }

    let mut census = Census::default();
    for (label, bytes) in &cases {
        let mine = our_vk.verify(&msg_a, &trust::Signature::from_slice(bytes).unwrap()).is_ok();
        let theirs_r =
            their_vk.verify(&msg_a, &dalek::Signature::from_slice(bytes).unwrap()).is_ok();
        census.check(&format!("{label}: {}", hex(bytes)), mine, theirs_r);
    }
    census.finish("structural signature corruption", 12);
    assert_eq!(census.ours_accepted, 0, "a structurally corrupted signature was accepted");
    assert_eq!(census.theirs_accepted, 0, "the incumbent accepted one");

    // The control: the unmodified signature still verifies under both. Without
    // this the whole test would pass with a verifier that rejects everything.
    assert!(our_vk.verify(&msg_a, &trust::Signature::from_slice(&sig_a).unwrap()).is_ok());
    assert!(their_vk.verify(&msg_a, &dalek::Signature::from_slice(&sig_a).unwrap()).is_ok());
}

// ---------------------------------------------------------------------------
// Negative class 2 — corrupted message.
// ---------------------------------------------------------------------------

/// A message that changed after signing is rejected by both, for every
/// single-bit change and for every length change.
///
/// # The three corruption shapes, and why length changes are separate
///
/// * **Substitution** — flip one bit. Both hashes see a different message and
///   `k` changes, so the equation fails.
/// * **Truncation and extension** — the message gets shorter or longer. This
///   is a *different* failure surface: SHA-512 binds the length in its padding,
///   so `M` and `M || 0x00` differ even though one is a prefix of the other.
///   An implementation that fed the message to the hash without its length —
///   or that stopped at a NUL — would pass the substitution cases and fail
///   these.
/// * **Substitution of the whole message** — a signature presented for a
///   different message of the same length.
#[test]
fn corrupted_message_is_rejected_by_both() {
    let mut rng = Xorshift(0x6626_0701_7100_0000);
    let mut seed = [0u8; 32];
    rng.fill(&mut seed);
    let ours = trust::SigningKey::from_bytes(&seed);
    let theirs = dalek::SigningKey::from_bytes(&seed);
    let our_vk = ours.verifying_key();
    let their_vk = theirs.verifying_key();

    let mut census = Census::default();

    for len in [0usize, 1, 2, 31, 32, 63, 64, 96, 127, 128, 129, 191, 192, 255] {
        let mut message = vec![0u8; len];
        rng.fill(&mut message);
        let sig = ours.sign(&message).to_bytes();
        assert_eq!(hex(&sig), hex(&theirs.sign(&message).to_bytes()));

        // Control: the true message verifies. A verifier that rejects
        // everything must not be able to pass this test.
        assert!(
            our_vk.verify(&message, &trust::Signature::from_slice(&sig).unwrap()).is_ok(),
            "len {len}: the unmodified message did not verify"
        );

        // Substitution: every single-bit change, exhaustively, up to 32 octets;
        // beyond that, one bit in every octet (a rotating position, so the
        // sweep as a whole still covers all eight bit positions).
        for bit in 0..(len * 8) {
            if len > 32 && bit % 8 != (bit / 8) % 8 {
                continue;
            }
            let mut corrupted = message.clone();
            corrupted[bit / 8] ^= 1 << (bit % 8);
            let mine =
                our_vk.verify(&corrupted, &trust::Signature::from_slice(&sig).unwrap()).is_ok();
            let theirs_r =
                their_vk.verify(&corrupted, &dalek::Signature::from_slice(&sig).unwrap()).is_ok();
            census.check(
                &format!("len {len}, message bit {bit} flipped: {}", hex(&corrupted)),
                mine,
                theirs_r,
            );
        }

        // Extension by one octet, with three different appended values —
        // including 0x00, the one a length-blind implementation would miss.
        for extra in [0x00u8, 0x01, 0xff] {
            let mut extended = message.clone();
            extended.push(extra);
            let mine =
                our_vk.verify(&extended, &trust::Signature::from_slice(&sig).unwrap()).is_ok();
            let theirs_r =
                their_vk.verify(&extended, &dalek::Signature::from_slice(&sig).unwrap()).is_ok();
            census.check(
                &format!("len {len}, extended with {extra:#04x}: {}", hex(&extended)),
                mine,
                theirs_r,
            );
        }

        // Truncation by one octet.
        if len > 0 {
            let truncated = &message[..len - 1];
            let mine =
                our_vk.verify(truncated, &trust::Signature::from_slice(&sig).unwrap()).is_ok();
            let theirs_r =
                their_vk.verify(truncated, &dalek::Signature::from_slice(&sig).unwrap()).is_ok();
            census.check(
                &format!("len {len}, truncated to {}: {}", len - 1, hex(truncated)),
                mine,
                theirs_r,
            );
        }

        // A wholly different message of the same length.
        let mut other = vec![0u8; len];
        rng.fill(&mut other);
        if other != message {
            let mine = our_vk.verify(&other, &trust::Signature::from_slice(&sig).unwrap()).is_ok();
            let theirs_r =
                their_vk.verify(&other, &dalek::Signature::from_slice(&sig).unwrap()).is_ok();
            census.check(
                &format!("len {len}, unrelated message of the same length: {}", hex(&other)),
                mine,
                theirs_r,
            );
        }
    }

    // 1841 at the time of writing. The floor is a silence detector, not a
    // target: it fails if a future edit narrows the sweep without saying so.
    census.finish("message corruption", 1800);
    assert_eq!(
        census.ours_accepted, 0,
        "a corrupted message verified against a signature over the original"
    );
    assert_eq!(census.theirs_accepted, 0, "the incumbent accepted a corrupted message");
}

// ---------------------------------------------------------------------------
// Negative class 3 — wrong public key.
// ---------------------------------------------------------------------------

/// A signature presented under the wrong public key is rejected by both.
///
/// Every ordered pair from a set of sixteen independently derived keys is
/// tried: 16 correct pairings that must verify, and 240 wrong ones that must
/// not. Both halves are asserted, because "rejects the wrong key" is trivially
/// satisfied by a verifier that rejects everything, and the accept half is the
/// only thing that stops this test from passing in that state.
///
/// A wrong key breaks the equation twice over — it changes `A` in
/// `[S]B = R + [k]A` *and* changes `k`, since §5.1.7 hashes `R || A || M`. So
/// there is no mutation confined to this crate under which a wrong key is
/// accepted while valid signatures still verify: the only way to reach that
/// state is a `verify` that has stopped comparing anything at all. That is
/// what this test detects, and it is worth detecting — it is the shape a
/// refactoring accident takes.
#[test]
fn wrong_public_key_is_rejected_by_both() {
    const KEYS: usize = 16;
    let mut rng = Xorshift(0x3141_5926_5358_9793);

    let mut seeds = [[0u8; 32]; KEYS];
    for seed in seeds.iter_mut() {
        rng.fill(seed);
    }

    let message = b"a message signed by exactly one of these keys";

    let our_keys: Vec<_> = seeds.iter().map(trust::SigningKey::from_bytes).collect();
    let their_keys: Vec<_> = seeds.iter().map(dalek::SigningKey::from_bytes).collect();
    let our_sigs: Vec<[u8; 64]> = our_keys.iter().map(|k| k.sign(message).to_bytes()).collect();
    for (i, k) in their_keys.iter().enumerate() {
        assert_eq!(hex(&our_sigs[i]), hex(&k.sign(message).to_bytes()), "key {i}");
    }

    let mut census = Census::default();
    let (mut correct_accepted, mut wrong_accepted) = (0usize, 0usize);
    for (signer, sig) in our_sigs.iter().enumerate() {
        for verifier in 0..KEYS {
            let our_vk = our_keys[verifier].verifying_key();
            let their_vk = their_keys[verifier].verifying_key();
            let mine = our_vk.verify(message, &trust::Signature::from_slice(sig).unwrap()).is_ok();
            let theirs_r =
                their_vk.verify(message, &dalek::Signature::from_slice(sig).unwrap()).is_ok();
            census.check(
                &format!(
                    "signature by key {signer} ({}) presented under key {verifier} ({})",
                    hex(&our_keys[signer].verifying_key().to_bytes()),
                    hex(&our_vk.to_bytes())
                ),
                mine,
                theirs_r,
            );
            if signer == verifier {
                if mine {
                    correct_accepted += 1;
                }
            } else if mine {
                wrong_accepted += 1;
            }
        }
    }

    census.finish("wrong public key", KEYS * KEYS);
    assert_eq!(
        correct_accepted, KEYS,
        "only {correct_accepted} of {KEYS} signatures verified under their OWN key — this \
         test cannot detect a wrong-key acceptance in that state"
    );
    assert_eq!(
        wrong_accepted, 0,
        "{wrong_accepted} signatures verified under a key that did not produce them"
    );
}

// ---------------------------------------------------------------------------
// Negative class 4 — S >= L, swept rather than enumerated.
// ---------------------------------------------------------------------------

/// `S + nL` for `n = 1..8`, plus a sweep of the out-of-range space.
///
/// `out_of_range_s_is_rejected_by_both` above pins the one case that isolates
/// the range check (`S + L`, which satisfies the verification equation). This
/// sweeps the rest of the space so that "rejected" is a property of the range,
/// not of four hand-picked constants: every `S + nL` that still fits in 32
/// octets is a *valid* signature under the equation and is rejected only by the
/// §5.1.7 range test, and the random out-of-range values check that the
/// comparison against `L` is not off by a limb somewhere in the middle.
#[test]
fn out_of_range_s_swept() {
    let mut rng = Xorshift(0x1618_0339_8874_9895);
    let mut seed = [0u8; 32];
    rng.fill(&mut seed);
    let ours = trust::SigningKey::from_bytes(&seed);
    let theirs = dalek::SigningKey::from_bytes(&seed);
    let our_vk = ours.verifying_key();
    let their_vk = theirs.verifying_key();

    let mut census = Census::default();
    let mut malleable_accepted = 0usize;

    for msg_len in [0usize, 7, 64, 200] {
        let mut message = vec![0u8; msg_len];
        rng.fill(&mut message);
        let valid = ours.sign(&message).to_bytes();
        assert_eq!(hex(&valid), hex(&theirs.sign(&message).to_bytes()));

        // S + nL for as many n as fit in 32 octets. Each of these satisfies
        // [S+nL]B = [S]B, so the equation holds and ONLY the range check can
        // reject them.
        let mut s = [0u8; 32];
        s.copy_from_slice(&valid[32..]);
        for n in 1..=8u16 {
            let mut acc = s;
            let mut overflow = false;
            for _ in 0..n {
                let mut carry = 0u16;
                for i in 0..32 {
                    let v = acc[i] as u16 + L_LE[i] as u16 + carry;
                    acc[i] = v as u8;
                    carry = v >> 8;
                }
                if carry != 0 {
                    overflow = true;
                }
            }
            if overflow {
                continue;
            }
            let mut bytes = valid;
            bytes[32..].copy_from_slice(&acc);
            let mine =
                our_vk.verify(&message, &trust::Signature::from_slice(&bytes).unwrap()).is_ok();
            let theirs_r =
                their_vk.verify(&message, &dalek::Signature::from_slice(&bytes).unwrap()).is_ok();
            census.check(
                &format!("len {msg_len}: MALLEATED S + {n}L (equation holds): {}", hex(&bytes)),
                mine,
                theirs_r,
            );
            if mine {
                malleable_accepted += 1;
            }
        }

        // Random out-of-range S. Bit 255 of a valid S is always zero (L < 2^253),
        // so setting the top three bits guarantees out of range.
        for _ in 0..64 {
            let mut bytes = valid;
            let mut s_bytes = [0u8; 32];
            rng.fill(&mut s_bytes);
            s_bytes[31] |= 0xe0;
            bytes[32..].copy_from_slice(&s_bytes);
            let mine =
                our_vk.verify(&message, &trust::Signature::from_slice(&bytes).unwrap()).is_ok();
            let theirs_r =
                their_vk.verify(&message, &dalek::Signature::from_slice(&bytes).unwrap()).is_ok();
            census.check(
                &format!("len {msg_len}: random out-of-range S: {}", hex(&bytes)),
                mine,
                theirs_r,
            );
        }

        // The boundary itself, from both sides: L-1 is in range (and fails the
        // equation), L is not.
        for (label, delta) in [("L-1 (IN range)", -1i16), ("L (out of range)", 0)] {
            let mut acc = L_LE;
            if delta == -1 {
                acc[0] -= 1;
            }
            let mut bytes = valid;
            bytes[32..].copy_from_slice(&acc);
            let mine =
                our_vk.verify(&message, &trust::Signature::from_slice(&bytes).unwrap()).is_ok();
            let theirs_r =
                their_vk.verify(&message, &dalek::Signature::from_slice(&bytes).unwrap()).is_ok();
            census.check(&format!("len {msg_len}: S = {label}: {}", hex(&bytes)), mine, theirs_r);
        }
    }

    census.finish("out-of-range S", 4 * (8 + 64 + 2) - 8);
    assert_eq!(
        malleable_accepted, 0,
        "MALLEABILITY: {malleable_accepted} signatures of the form (R, S+nL) verified. \
         They satisfy the verification equation, so only the RFC 8032 §5.1.7 range check \
         rejects them, and it did not."
    );
    assert_eq!(census.ours_accepted, 0, "an out-of-range S was accepted");
    assert_eq!(census.theirs_accepted, 0, "the incumbent accepted an out-of-range S");
}
