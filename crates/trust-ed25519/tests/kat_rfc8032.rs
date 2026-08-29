// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **Published known-answer tests: RFC 8032 §7.1.**
//!
//! All five vectors, read from `tests/data/rfc8032_7_1.txt`, which was
//! extracted mechanically from the RFC text — see `tests/data/PROVENANCE.md`
//! for the source URL, its SHA-256, and the extractor. Nothing in this file
//! was typed from memory and nothing was produced by this crate.
//!
//! Each vector pins three separate things, and they fail independently:
//!
//! 1. **Key derivation** — RFC 8032 §5.1.5: the seed expands to the stated
//!    public key. A wrong clamp, a wrong scalar multiplication or a wrong
//!    point encoding all show up here.
//! 2. **Signing** — §5.1.6: the same seed and message produce the stated
//!    signature, octet for octet. Ed25519 signing is deterministic, so this is
//!    a total function's value, not a sample.
//! 3. **Verification** — §5.1.7: the stated signature verifies, and a
//!    perturbed one does not.

const VECTORS: &str = include_str!("data/rfc8032_7_1.txt");

use trust_ed25519::{Signature, Signer, SigningKey, Verifier, VerifyingKey};

fn unhex(s: &str) -> Vec<u8> {
    assert!(s.len() % 2 == 0, "odd-length hex: {} chars", s.len());
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).expect("hex digit"))
        .collect()
}

struct Vector {
    name: String,
    seed: [u8; 32],
    public: [u8; 32],
    message: Vec<u8>,
    signature: [u8; 64],
}

fn vectors() -> Vec<Vector> {
    let out: Vec<Vector> = VECTORS
        .lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
        .map(|line| {
            let f: Vec<&str> = line.split('|').collect();
            assert_eq!(f.len(), 5, "malformed record: {line}");
            Vector {
                name: f[0].to_string(),
                seed: unhex(f[1]).try_into().expect("32-octet secret key"),
                public: unhex(f[2]).try_into().expect("32-octet public key"),
                message: unhex(f[3]),
                signature: unhex(f[4]).try_into().expect("64-octet signature"),
            }
        })
        .collect();
    // The data file is an input, not a fixture the test can shrug off: a
    // truncated or empty file must fail loudly rather than vacuously pass.
    assert_eq!(out.len(), 5, "expected the five RFC 8032 §7.1 vectors");
    out
}

/// §5.1.5 — the seed expands to the stated public key.
#[test]
fn public_keys_match_rfc8032_7_1() {
    for v in vectors() {
        let key = SigningKey::from_bytes(&v.seed);
        assert_eq!(
            key.verifying_key().to_bytes(),
            v.public,
            "TEST {}: derived public key differs from RFC 8032 §7.1",
            v.name
        );
        // The seed round-trips: `to_bytes` returns what `from_bytes` took.
        assert_eq!(key.to_bytes(), v.seed, "TEST {}: seed round trip", v.name);
    }
}

/// §5.1.6 — signing is deterministic and reproduces the stated signature.
#[test]
fn signatures_match_rfc8032_7_1() {
    for v in vectors() {
        let key = SigningKey::from_bytes(&v.seed);
        let sig = key.sign(&v.message);
        assert_eq!(
            sig.to_bytes(),
            v.signature,
            "TEST {} ({} byte message): signature differs from RFC 8032 §7.1",
            v.name,
            v.message.len()
        );
        // Signing twice gives the same answer — no randomness enters §5.1.6.
        assert_eq!(
            key.sign(&v.message).to_bytes(),
            v.signature,
            "TEST {}: not deterministic",
            v.name
        );
    }
}

/// §5.1.7 — the stated signature verifies under the stated key.
#[test]
fn verification_accepts_rfc8032_7_1() {
    for v in vectors() {
        let key = VerifyingKey::from_bytes(&v.public).expect("RFC public key decodes");
        let sig = Signature::from_slice(&v.signature).expect("64 octets");
        assert!(key.verify(&v.message, &sig).is_ok(), "TEST {}: valid signature rejected", v.name);
    }
}

/// The other half of a verification test: everything one octet away must fail.
///
/// Without this, a `verify` that returned `Ok(())` unconditionally would pass
/// the test above.
#[test]
fn verification_rejects_perturbations_of_rfc8032_7_1() {
    for v in vectors() {
        let key = VerifyingKey::from_bytes(&v.public).expect("RFC public key decodes");

        // Every octet of the signature matters. Flipping the low bit of each
        // in turn must break it — including inside R, inside S, and the
        // malleability-relevant high octet of S.
        for i in 0..64 {
            let mut bytes = v.signature;
            bytes[i] ^= 1;
            let sig = Signature::from_slice(&bytes).expect("64 octets");
            assert!(
                key.verify(&v.message, &sig).is_err(),
                "TEST {}: signature with octet {i} perturbed still verified",
                v.name
            );
        }

        // A different message must not verify.
        let mut other = v.message.clone();
        other.push(0);
        let sig = Signature::from_slice(&v.signature).expect("64 octets");
        assert!(
            key.verify(&other, &sig).is_err(),
            "TEST {}: signature verified over a longer message",
            v.name
        );
        if !v.message.is_empty() {
            let mut flipped = v.message.clone();
            flipped[0] ^= 0x80;
            assert!(
                key.verify(&flipped, &sig).is_err(),
                "TEST {}: signature verified over a perturbed message",
                v.name
            );
        }

        // A different key must not verify. (Use the next vector's key; for the
        // last, wrap to the first.)
        let all = vectors();
        for other_v in &all {
            if other_v.public == v.public {
                continue;
            }
            let other_key = VerifyingKey::from_bytes(&other_v.public).expect("decodes");
            assert!(
                other_key.verify(&v.message, &sig).is_err(),
                "TEST {}: signature verified under TEST {}'s key",
                v.name,
                other_v.name
            );
        }
    }
}

/// Cross-vector coherence: signing vector *i*'s message with vector *j*'s key
/// must never coincide with vector *i*'s signature.
///
/// A degenerate implementation that ignored the key would pass every test
/// above that used only one key at a time.
#[test]
fn signatures_depend_on_the_key() {
    let all = vectors();
    for (i, v) in all.iter().enumerate() {
        for (j, w) in all.iter().enumerate() {
            if i == j {
                continue;
            }
            let sig = SigningKey::from_bytes(&w.seed).sign(&v.message);
            assert_ne!(
                sig.to_bytes(),
                v.signature,
                "TEST {}'s signature was reproduced with TEST {}'s key",
                v.name,
                w.name
            );
        }
    }
}
