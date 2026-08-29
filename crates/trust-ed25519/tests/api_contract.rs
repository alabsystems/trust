// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **The API surface the swap depends on, exercised exactly as
//! `trust-proof-cert` exercises it.**
//!
//! `crates/trust-proof-cert/src/signing.rs` is the sole consumer of
//! `ed25519-dalek` in this tree — one import line, ten distinct entry points,
//! fifteen call sites. This file pins those ten so that a change to this
//! crate's surface fails here rather than at the integration step, and so that
//! the *shapes* (by value or by reference, fallible or not) cannot drift.
//!
//! Each test names the `signing.rs` line it stands for.
//!
//! Two shapes are load-bearing and easy to get wrong:
//!
//! * `SigningKey::from_bytes` is **infallible** — no `Result`. The call site
//!   assigns its value directly.
//! * `verifying_key()` returns **by value**, not by reference.

use trust_ed25519::{
    KEY_LENGTH, SIGNATURE_LENGTH, Signature, SignatureError, Signer, SigningKey, Verifier,
    VerifyingKey,
};

const SEED: [u8; 32] = [7u8; 32];

/// `signing.rs:47` — `SigningKey::from_bytes(bytes)`, infallible.
/// `signing.rs:53` — `self.key.to_bytes()`, the seed.
#[test]
fn signing_key_from_bytes_is_infallible_and_round_trips() {
    let key: SigningKey = SigningKey::from_bytes(&SEED);
    let out: [u8; KEY_LENGTH] = key.to_bytes();
    assert_eq!(out, SEED, "to_bytes must return the seed from_bytes took");
    assert_eq!(KEY_LENGTH, 32);
}

/// `signing.rs:63,75` — `self.key.verifying_key()`, by value.
/// `signing.rs:75,104` — `.to_bytes()` on the verifying key.
#[test]
fn verifying_key_is_returned_by_value_and_encodes_to_32_octets() {
    let key = SigningKey::from_bytes(&SEED);
    let vk: VerifyingKey = key.verifying_key();
    let bytes: [u8; KEY_LENGTH] = vk.to_bytes();
    // Deriving twice gives the same key: `verifying_key` is a pure accessor.
    assert_eq!(bytes, key.verifying_key().to_bytes());
    assert_eq!(bytes.len(), 32);
}

/// `signing.rs:91` — `VerifyingKey::from_bytes(bytes)`, fallible, and its
/// error is consumed by `Display` alone.
#[test]
fn verifying_key_from_bytes_is_fallible_and_its_error_displays() {
    let good = SigningKey::from_bytes(&SEED).verifying_key().to_bytes();
    assert!(VerifyingKey::from_bytes(&good).is_ok());

    // An encoding that is not a curve point. (0xff.. is also non-canonical,
    // which this crate rejects too — see the crate docs' deviation D1.)
    let err: SignatureError =
        VerifyingKey::from_bytes(&[0xff; 32]).expect_err("0xff.. is not a valid key");
    // The consumer does `format!("...: {e}")` and nothing else. That is the
    // entire requirement on this type.
    let rendered = format!("{err}");
    assert!(!rendered.is_empty());
    assert_eq!(format!("{err:?}").is_empty(), false);
}

/// `signing.rs:72` — `self.key.sign(&canonical)` via the `Signer` trait.
/// `signing.rs:74` — `sig.to_bytes()` then `.to_vec()`.
#[test]
fn sign_resolves_through_the_signer_trait_and_yields_64_octets() {
    let key = SigningKey::from_bytes(&SEED);
    let sig: Signature = key.sign(b"canonical bytes");
    let bytes: [u8; SIGNATURE_LENGTH] = sig.to_bytes();
    assert_eq!(bytes.to_vec().len(), 64);
    assert_eq!(SIGNATURE_LENGTH, 64);
    // `try_sign` is the primitive; `sign` is its unwrapping wrapper.
    assert_eq!(key.try_sign(b"canonical bytes").unwrap().to_bytes(), bytes);
}

/// `signing.rs:114` — `Signature::from_slice(&sig.signature_bytes)`, fallible.
/// `signing.rs:117` — `self.key.verify(&canonical, &signature)`.
#[test]
fn verify_resolves_through_the_verifier_trait() {
    let key = SigningKey::from_bytes(&SEED);
    let vk = key.verifying_key();
    let message = b"canonical bytes";
    let stored: Vec<u8> = key.sign(message).to_bytes().to_vec();

    let signature = Signature::from_slice(&stored).expect("64 octets");
    assert!(vk.verify(message, &signature).is_ok());

    let err = vk.verify(b"different", &signature).expect_err("wrong message");
    assert!(!format!("{err}").is_empty());

    // A short slice fails to parse, and that failure is also Display-only.
    let err = Signature::from_slice(&stored[..63]).expect_err("63 octets");
    assert!(!format!("{err}").is_empty());
}

/// The derives the consumer's own structs need.
///
/// `CertVerifyingKey` derives `Debug, Clone`, so `VerifyingKey` must offer
/// both. `CertSigningKey` derives nothing, so `SigningKey` needs no trait impl
/// at all — and deliberately has no `Clone`, so a secret is not duplicated by
/// accident.
#[test]
fn required_derives_are_present() {
    let vk = SigningKey::from_bytes(&SEED).verifying_key();
    let cloned: VerifyingKey = vk;
    assert_eq!(format!("{vk:?}"), format!("{cloned:?}"));
    // Debug prints the encoding, not coordinates.
    assert!(format!("{vk:?}").contains(&format!("{:02x}", vk.to_bytes()[0])));

    // Signature is Copy + Debug + Eq, which the consumer does not require but
    // which its tests use freely.
    let sig = SigningKey::from_bytes(&SEED).sign(b"x");
    let copy = sig;
    assert_eq!(sig, copy);
    assert!(!format!("{sig:?}").is_empty());
}

/// The whole `signing.rs` flow, end to end, in the order that file runs it.
#[test]
fn the_consumers_flow_end_to_end() {
    // CertSigningKey::from_bytes
    let key = SigningKey::from_bytes(&SEED);
    // canonical_bytes(..) -> sign -> CertificateSignature { signature_bytes,
    // public_key_bytes }
    let canonical = b"cert|Solver|payload";
    let signature_bytes: Vec<u8> = key.sign(canonical).to_bytes().to_vec();
    let public_key_bytes: Vec<u8> = key.verifying_key().to_bytes().to_vec();

    // CertVerifyingKey::from_bytes, then check_signature_integrity.
    let vk_array: [u8; 32] = public_key_bytes.clone().try_into().expect("32 octets");
    let vk = VerifyingKey::from_bytes(&vk_array).expect("valid key");
    let signature = Signature::from_slice(&signature_bytes).expect("64 octets");
    assert!(vk.verify(canonical, &signature).is_ok());

    // TrustAnchorPolicy::from_verifying_keys round-trips every anchor and
    // `.expect()`s the result. That must be total.
    let anchor: [u8; 32] = vk.to_bytes();
    VerifyingKey::from_bytes(&anchor).expect("existing verifying keys are valid Ed25519 keys");

    // A signature over different canonical bytes must not verify — the
    // `TrustLevel` is inside `canonical`, so this is the check that makes the
    // level binding real.
    let other = b"cert|Root|payload";
    assert!(vk.verify(other, &signature).is_err());
}
