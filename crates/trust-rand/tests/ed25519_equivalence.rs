// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **The differential acceptance gate for the call-site rewrite this crate
//! enables.**
//!
//! # What is being differentiated, and why it is not the entropy
//!
//! You cannot differential-test a random source for equality against another
//! random source: they are supposed to disagree. The rigor bar's "differential
//! against the incumbent while both still exist" therefore has to attach to
//! something deterministic, and here it does — the *rewrite*, not the source.
//!
//! `crates/trust-proof-cert/src/signing.rs:40` currently reads
//!
//! ```text
//! let mut rng = rand::thread_rng();
//! let key = SigningKey::generate(&mut rng);
//! ```
//!
//! and the replacement is
//!
//! ```text
//! let key = SigningKey::from_bytes(&trust_rand::secret_seed_32());
//! ```
//!
//! Those are equal exactly when `SigningKey::generate` is nothing more than
//! "draw 32 bytes, call `from_bytes`". Reading `ed25519-dalek-2.2.0`'s
//! `src/signing.rs:202` says it is:
//!
//! ```text
//! pub fn generate<R: CryptoRngCore + ?Sized>(csprng: &mut R) -> SigningKey {
//!     let mut secret = SecretKey::default();      // SecretKey = [u8; 32]
//!     csprng.fill_bytes(&mut secret);
//!     Self::from_bytes(&secret)
//! }
//! ```
//!
//! but reading source is not evidence that the linked artifact behaves that
//! way. This file supplies a deterministic `RngCore` that emits a fixed 32
//! bytes and asserts byte-identical secret keys, verifying keys, and
//! signatures. That is an exact comparison, and it fails loudly if a future
//! `ed25519-dalek` ever puts a KDF, a rejection loop, or a clamping step
//! between the RNG and `from_bytes`.
//!
//! # Provenance of the vectors
//!
//! * The **RFC 8032 §7.1 TEST 1 / TEST 2 / TEST 3** rows are **PUBLISHED**:
//!   secret key, public key and signature are transcribed from the RFC. They
//!   test `from_bytes` itself against the standard, so the equivalence proved
//!   below is anchored to a specification rather than only to the incumbent's
//!   self-consistency.
//! * The **structured seeds** (all-`0x00`, all-`0xFF`, counter, alternating)
//!   are **DERIVED** — chosen here to hit boundary shapes, with no published
//!   expected output. They are used only for `generate`-vs-`from_bytes`
//!   equality, where the expected value is whatever the incumbent produces on
//!   both sides.
//! * The **random seeds** are **DERIVED at run time from this crate's own
//!   entropy**, so the equality is exercised over inputs nobody chose.
//!
//! When `SigningKey::generate` leaves the tree, delete this file together with
//! the two dev-dependencies in `Cargo.toml`.

use ed25519_dalek::{Signer, SigningKey, Verifier};
use rand_core::{CryptoRng, RngCore};

/// A deterministic "RNG" that hands out a fixed buffer, then refuses.
///
/// It is `CryptoRng` because `SigningKey::generate` demands `CryptoRngCore`,
/// which is `CryptoRng + RngCore`. It is emphatically not cryptographic; it
/// exists only inside this test binary, and the `panic!` arms make sure it can
/// never be used as a general-purpose source by accident.
struct FixedBytes {
    bytes: Vec<u8>,
    position: usize,
}

impl FixedBytes {
    fn new(bytes: &[u8]) -> Self {
        FixedBytes { bytes: bytes.to_vec(), position: 0 }
    }
}

impl RngCore for FixedBytes {
    fn next_u32(&mut self) -> u32 {
        let mut b = [0u8; 4];
        self.fill_bytes(&mut b);
        u32::from_le_bytes(b)
    }

    fn next_u64(&mut self) -> u64 {
        let mut b = [0u8; 8];
        self.fill_bytes(&mut b);
        u64::from_le_bytes(b)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        let end = self.position + dest.len();
        assert!(
            end <= self.bytes.len(),
            "ed25519-dalek asked this fixture for {} bytes at offset {}, but only {} were \
             supplied. That means `SigningKey::generate` no longer consumes exactly one \
             32-byte draw, and the `from_bytes` rewrite is NOT equivalent any more.",
            dest.len(),
            self.position,
            self.bytes.len()
        );
        dest.copy_from_slice(&self.bytes[self.position..end]);
        self.position = end;
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

impl CryptoRng for FixedBytes {}

/// The whole point: for any 32-byte seed, the two spellings agree on the secret
/// key, the public key, and a signature over a message.
fn assert_spellings_agree(seed: &[u8; 32], label: &str) {
    let mut fixture = FixedBytes::new(seed);
    let via_generate = SigningKey::generate(&mut fixture);
    let via_from_bytes = SigningKey::from_bytes(seed);

    assert_eq!(
        fixture.position, 32,
        "{label}: `generate` consumed {} bytes, not 32 — the rewrite is not equivalent",
        fixture.position
    );
    assert_eq!(
        via_generate.to_bytes(),
        via_from_bytes.to_bytes(),
        "{label}: secret keys differ between SigningKey::generate and SigningKey::from_bytes"
    );
    assert_eq!(
        via_generate.verifying_key().to_bytes(),
        via_from_bytes.verifying_key().to_bytes(),
        "{label}: verifying keys differ"
    );

    // Ed25519 is deterministic (RFC 8032 §5.1.6), so signatures are comparable
    // for equality too — a stronger check than key equality, because it also
    // covers the expanded scalar and the hash prefix that `from_bytes` derives.
    let message = b"trust-rand: generate/from_bytes equivalence";
    assert_eq!(
        via_generate.sign(message).to_bytes(),
        via_from_bytes.sign(message).to_bytes(),
        "{label}: signatures differ"
    );

    // And the signature verifies under the public key, so neither spelling
    // produced an internally inconsistent key pair.
    let signature = via_from_bytes.sign(message);
    via_generate
        .verifying_key()
        .verify(message, &signature)
        .unwrap_or_else(|e| panic!("{label}: cross-verification failed: {e}"));
}

#[test]
fn generate_and_from_bytes_agree_on_structured_seeds() {
    // DERIVED (boundary shapes; no published expected output).
    let mut counter = [0u8; 32];
    for (i, b) in counter.iter_mut().enumerate() {
        *b = i as u8;
    }

    assert_spellings_agree(&[0x00; 32], "all-zero seed");
    assert_spellings_agree(&[0xFF; 32], "all-ones seed");
    assert_spellings_agree(&counter, "counter seed");
    assert_spellings_agree(&[0xAA; 32], "alternating-bit seed");
    assert_spellings_agree(&[0x55; 32], "inverse alternating-bit seed");

    let mut one_bit = [0u8; 32];
    one_bit[31] = 0x01;
    assert_spellings_agree(&one_bit, "single low bit");
    let mut high_bit = [0u8; 32];
    high_bit[0] = 0x80;
    assert_spellings_agree(&high_bit, "single high bit");
}

#[test]
fn generate_and_from_bytes_agree_on_published_rfc8032_seeds() {
    // PUBLISHED: RFC 8032 §7.1, the SECRET KEY column of TEST 1, TEST 2 and
    // TEST 3. These are real specification vectors, not values derived here.
    const RFC8032_TEST1_SECRET: [u8; 32] = [
        0x9d, 0x61, 0xb1, 0x9d, 0xef, 0xfd, 0x5a, 0x60, 0xba, 0x84, 0x4a, 0xf4, 0x92, 0xec, 0x2c,
        0xc4, 0x44, 0x49, 0xc5, 0x69, 0x7b, 0x32, 0x69, 0x19, 0x70, 0x3b, 0xac, 0x03, 0x1c, 0xae,
        0x7f, 0x60,
    ];
    const RFC8032_TEST2_SECRET: [u8; 32] = [
        0x4c, 0xcd, 0x08, 0x9b, 0x28, 0xff, 0x96, 0xda, 0x9d, 0xb6, 0xc3, 0x46, 0xec, 0x11, 0x4e,
        0x0f, 0x5b, 0x8a, 0x31, 0x9f, 0x35, 0xab, 0xa6, 0x24, 0xda, 0x8c, 0xf6, 0xed, 0x4f, 0xb8,
        0xa6, 0xfb,
    ];
    const RFC8032_TEST3_SECRET: [u8; 32] = [
        0xc5, 0xaa, 0x8d, 0xf4, 0x3f, 0x9f, 0x83, 0x7b, 0xed, 0xb7, 0x44, 0x2f, 0x31, 0xdc, 0xb7,
        0xb1, 0x66, 0xd3, 0x85, 0x35, 0x07, 0x6f, 0x09, 0x4b, 0x85, 0xce, 0x3a, 0x2e, 0x0b, 0x44,
        0x58, 0xf7,
    ];

    assert_spellings_agree(&RFC8032_TEST1_SECRET, "RFC 8032 TEST 1");
    assert_spellings_agree(&RFC8032_TEST2_SECRET, "RFC 8032 TEST 2");
    assert_spellings_agree(&RFC8032_TEST3_SECRET, "RFC 8032 TEST 3");
}

/// Anchors the equivalence to the **specification**, not only to the
/// incumbent's self-consistency: `from_bytes` on the RFC 8032 §7.1 TEST 1
/// secret key must yield the RFC's public key and the RFC's signature over the
/// RFC's (empty) message.
///
/// PUBLISHED — every byte below is transcribed from RFC 8032 §7.1.
#[test]
fn from_bytes_matches_the_published_rfc8032_test1_vector() {
    const SECRET: [u8; 32] = [
        0x9d, 0x61, 0xb1, 0x9d, 0xef, 0xfd, 0x5a, 0x60, 0xba, 0x84, 0x4a, 0xf4, 0x92, 0xec, 0x2c,
        0xc4, 0x44, 0x49, 0xc5, 0x69, 0x7b, 0x32, 0x69, 0x19, 0x70, 0x3b, 0xac, 0x03, 0x1c, 0xae,
        0x7f, 0x60,
    ];
    const PUBLIC: [u8; 32] = [
        0xd7, 0x5a, 0x98, 0x01, 0x82, 0xb1, 0x0a, 0xb7, 0xd5, 0x4b, 0xfe, 0xd3, 0xc9, 0x64, 0x07,
        0x3a, 0x0e, 0xe1, 0x72, 0xf3, 0xda, 0xa6, 0x23, 0x25, 0xaf, 0x02, 0x1a, 0x68, 0xf7, 0x07,
        0x51, 0x1a,
    ];
    const MESSAGE: &[u8] = b"";
    const SIGNATURE: [u8; 64] = [
        0xe5, 0x56, 0x43, 0x00, 0xc3, 0x60, 0xac, 0x72, 0x90, 0x86, 0xe2, 0xcc, 0x80, 0x6e, 0x82,
        0x8a, 0x84, 0x87, 0x7f, 0x1e, 0xb8, 0xe5, 0xd9, 0x74, 0xd8, 0x73, 0xe0, 0x65, 0x22, 0x49,
        0x01, 0x55, 0x5f, 0xb8, 0x82, 0x15, 0x90, 0xa3, 0x3b, 0xac, 0xc6, 0x1e, 0x39, 0x70, 0x1c,
        0xf9, 0xb4, 0x6b, 0xd2, 0x5b, 0xf5, 0xf0, 0x59, 0x5b, 0xbe, 0x24, 0x65, 0x51, 0x41, 0x43,
        0x8e, 0x7a, 0x10, 0x0b,
    ];

    let key = SigningKey::from_bytes(&SECRET);
    assert_eq!(key.verifying_key().to_bytes(), PUBLIC, "RFC 8032 TEST 1 public key mismatch");
    assert_eq!(key.sign(MESSAGE).to_bytes(), SIGNATURE, "RFC 8032 TEST 1 signature mismatch");

    // And via `generate`, closing the loop: the rewrite reproduces a published
    // specification vector, not merely the incumbent's own output.
    let mut fixture = FixedBytes::new(&SECRET);
    let generated = SigningKey::generate(&mut fixture);
    assert_eq!(generated.verifying_key().to_bytes(), PUBLIC);
    assert_eq!(generated.sign(MESSAGE).to_bytes(), SIGNATURE);
}

/// The same equality over seeds nobody chose — drawn from this crate's own
/// entropy, so the equivalence is exercised on inputs outside any fixture.
#[test]
fn generate_and_from_bytes_agree_on_freshly_drawn_seeds() {
    for i in 0..64 {
        let seed = trust_rand::secret_seed_32();
        assert_spellings_agree(&seed, &format!("drawn seed #{i}"));
    }
}

/// A seed drawn by this crate produces a key pair that actually works —
/// end-to-end evidence that `trust_rand::secret_seed_32` is a usable
/// replacement for `rand::thread_rng()` at the signing call site, and that two
/// draws do not collide into the same key.
#[test]
fn a_drawn_seed_produces_a_working_and_distinct_key_pair() {
    let key_a = SigningKey::from_bytes(&trust_rand::secret_seed_32());
    let key_b = SigningKey::from_bytes(&trust_rand::secret_seed_32());

    assert_ne!(
        key_a.verifying_key().to_bytes(),
        key_b.verifying_key().to_bytes(),
        "two drawn seeds produced the same public key"
    );

    let message = b"a proof certificate record";
    let signature = key_a.sign(message);
    key_a.verifying_key().verify(message, &signature).expect("own signature must verify");
    assert!(
        key_b.verifying_key().verify(message, &signature).is_err(),
        "a signature verified under the WRONG public key"
    );
}
