// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![no_std]
#![forbid(unsafe_code)]

//! **The Trust-owned Ed25519**, per **RFC 8032** (*Edwards-Curve Digital
//! Signature Algorithm (EdDSA)*), §5.1.
//!
//! # Why this crate exists
//!
//! `crates/trust-proof-cert` signs and verifies proof certificates with
//! `ed25519-dalek`, which the verified lane reports as
//! `dependency-policy-excluded`: every proof certificate's authenticity is
//! today conditional on the correctness of a compilation unit Trust does not
//! own — and, transitively, on **34 packages**, of which the `curve25519`
//! family, `sha2`, `digest`, `subtle`, `fiat-crypto`, `der`, `pkcs8`, `spki`
//! and `zeroize` are reachable through no other edge. This crate, together
//! with the `trust-sha2` it is built on, retires all of them.
//!
//! Signature identity is not a place where "probably right" is a coherent
//! position: a signature scheme that disagrees with RFC 8032 on some input
//! class does not fail loudly, it silently declares good certificates bad, or
//! bad ones good. What follows is therefore explicit about which of its
//! behaviours are the RFC's, which are the incumbent's, and where the two
//! differ.
//!
//! # Deliberate deviations from `ed25519-dalek`'s default behaviour
//!
//! `ed25519-dalek 2.2.0`'s `VerifyingKey::verify` is the historical, permissive
//! check. Two of the encodings it accepts, this crate rejects, because
//! RFC 8032 §5.1.3 says to reject them:
//!
//! | # | Encoding | dalek `verify` | here | RFC 8032 |
//! |---|---|---|---|---|
//! | D1 | verifying key whose `y` is `>= p` (non-canonical) | accepts | **rejects** | §5.1.3: "if the resulting value is >= p, decoding fails" |
//! | D2 | encoding with `x = 0` and the sign bit set | accepts (as the identity) | **rejects** | §5.1.3: "if x = 0 and x_0 = 1, decoding fails" |
//!
//! Both are strictly-more-rejecting, both are unreachable for a key any
//! conforming signer produced, and both are pinned by
//! `tests/differential_ed25519.rs`, which asserts the disagreement rather than
//! tolerating it — a deviation nobody tests is a deviation nobody knows about.
//! Everything else matches the incumbent exactly, including the three choices
//! below that a reader would otherwise have to guess at:
//!
//! * **`S >= L` is rejected.** RFC 8032 §5.1.7 requires `S` to decode "as an
//!   integer in the range `0 <= s < L`". This is the malleability check;
//!   without it a third party can produce a second distinct signature that
//!   verifies under the same key and message. dalek does this too (its
//!   non-default `legacy_compatibility` feature is what turns it off).
//! * **The verification equation is cofactorless**, `[S]B = R + [k]A`,
//!   compared by *re-encoding* the computed `R` and comparing octets. This
//!   matches RFC 8032 §5.1.7's first, non-parenthesised form and matches
//!   dalek. The cofactored variant `[8][S]B = [8]R + [8][k]A` that §5.1.7 also
//!   permits accepts strictly more signatures; adopting it would be a
//!   *loosening* relative to the incumbent and is not done.
//! * **Small-order and non-canonical `R` are not specially rejected**, exactly
//!   as in dalek's `verify`. `dalek`'s stricter `verify_strict` is not
//!   replicated because nothing in this tree calls it.
//!
//! # A small-order public key gives NO guarantee — and that is spec-conformant
//!
//! RFC 8032 §5.1.3 gives no ground to reject the eight points of the 8-torsion
//! subgroup, so [`VerifyingKey::from_bytes`] accepts all of them, including
//! the all-zeros encoding and the identity. The consequence is sharp enough to
//! state rather than leave implicit, and `tests/kat_edge_cases.rs` pins both
//! halves of it:
//!
//! * Under the **identity** public key, the 64-octet string
//!   `identity_encoding || 0…0` verifies for **every message**. The §5.1.7
//!   equation becomes `identity = identity + [k]identity`, true for all `k`.
//!   No secret is involved. This is a *universal forgery*, and a verifier
//!   following §5.1.7 must accept it.
//! * Under the **all-zeros** public key — a point of order 4, not the identity
//!   — the all-zeros signature verifies for about a quarter of all messages:
//!   exactly those whose `k ≡ 3 (mod 4)`.
//!
//! Neither is a defect here. Both are reasons `trust-proof-cert` must never
//! accept a small-order key as a trust anchor; that check belongs at the
//! policy layer, where the key is admitted, not in `verify`.
//!
//! # What is constant time, and what is not
//!
//! Constant time — no branch and no memory index depends on the value:
//!
//! * All field arithmetic (`field.rs`), including inversion and the
//!   square-root candidate.
//! * All scalar arithmetic mod `L` (`scalar.rs`): the wide reduction of a
//!   SHA-512 digest, and `(r + k·s) mod L`.
//! * Scalar multiplication (`edwards.rs`), including its windowed table read,
//!   which touches all sixteen entries on every lookup. **This is the one that
//!   matters**: it is the operation applied to the secret scalar.
//! * The final octet comparison in [`Verifier::verify`].
//!
//! Not constant time, deliberately, because the data is public:
//!
//! * [`VerifyingKey::from_bytes`] and point decompression return early on a
//!   malformed encoding. The input is a public key.
//! * [`Signature::from_slice`] branches on the slice length.
//! * The `S >= L` check in verification returns early. `S` is public.
//!
//! Not addressed, and out of scope for a portable implementation: physical
//! side channels, and the compiler's freedom to reintroduce a branch. RFC 8032
//! §8.1 is the relevant advice.
//!
//! # Evidence
//!
//! 1. **Spec derivation, not transcription.** Every curve constant is
//!    re-derived from its RFC 8032 §5.1 Table 1 *definition* in
//!    `edwards.rs`'s `constants_are_derivable`: `d` from `-121665/121666`,
//!    `B.y` from `4/5`, `sqrt(-1)` from `sqrt(-1)² = -1`, and `[L]B` from the
//!    stated group order.
//! 2. **Field boundary tests.** `field.rs` drives `p-1`, `p`, `p+1` and `2p-1`
//!    through canonical encoding and through arithmetic — the inputs on which
//!    a hand-written carry chain silently breaks.
//! 3. **Published known-answer tests.** `tests/kat_rfc8032.rs` carries all
//!    five RFC 8032 §7.1 vectors, *mechanically extracted* from the RFC text
//!    (`tests/data/PROVENANCE.md` records the source URL, its SHA-256, and the
//!    extractor). No vector in this crate was typed from memory.
//! 3b. **Derived edge-case known-answer tests.** RFC 8032 publishes only valid
//!    triples, so `tests/kat_edge_cases.rs` covers what a verifier is likely
//!    to get *wrong*: all nineteen non-canonical `y` values exhaustively, both
//!    sign bits; canonical-but-off-curve encodings; `(R, S+L)` malleation; the
//!    8-torsion; and the two small-order forgeries above. Its vectors come
//!    from `tests/data/derive_edge_vectors.py`, an independent Python
//!    implementation using bignums and the *affine* §5.1.4 addition law — so
//!    it shares neither the limb representation nor the group law with this
//!    crate, and `edwards.rs`'s `eight_torsion_matches_the_derivation` checks
//!    the two agree. Unlike (4), these tests survive the incumbent's removal.
//! 4. **Differential against the incumbent.** `tests/differential_ed25519.rs`
//!    compares key derivation, signing and verification against
//!    `ed25519-dalek 2.2.0` and separately pins the two deviations above. This
//!    is the acceptance gate for the swap. Extent: 512 seeds; **every** message
//!    length from 0 to 600 octets plus 4 MiB, 4 MiB+1 and 12 MiB+113;
//!    cross-verification in both directions at every one of those lengths; and
//!    four negative classes compared verdict-for-verdict — all 512 single-bit
//!    signature corruptions, 1841 message corruptions (bit flips, ±1-octet
//!    length changes, whole-message substitution), all 256 ordered pairs of 16
//!    keys, and `S + nL` for `n = 1..8`, which satisfy the verification
//!    equation and so isolate the §5.1.7 range check. Verdict sweeps report
//!    **every** disagreement with its exact input and both verdicts, not just
//!    the first. The full sweep is 2.1 s.
//! 4b. **The differential's own tests have been seen to fail**, under eight
//!    mutations applied one at a time to an isolated byte-identical copy.
//!    Truncating the message at 256 octets fails the 0..=600 sweep while a
//!    0..=256 control still passes — the extension is load-bearing; truncating
//!    at 65536 fails *only* the multi-megabyte test. **One mutation was caught
//!    by nothing**: masking a single bit of the `R` comparison out of
//!    [`Verifier::verify`]. That is an equivalent mutant rather than a gap —
//!    `R` is an input to the hash that produces `k`, so weakening the
//!    comparison by `n` bits admits a forgery only with probability
//!    `2^(n-256)`, which no black-box sweep can observe. It is recorded here
//!    because "no test covers this" is a fact about the comparison that a
//!    reader of the evidence section should not have to rediscover.
//! 5. **Every test above has been seen to fail.** Eight mutations were applied
//!    one at a time — the field's `2^255 ≡ 19` fold constant, the canonical
//!    reduction's `h >= p` boundary, the group law's `2d`, the scalar
//!    reduction's bit range, the §5.1.5 clamp bit, the §5.1.3 canonicality
//!    rejection, the `S < L` range check, and the sign of `A` in the
//!    verification equation — and each was caught. **Two of the mutations
//!    found a defective test rather than a defective implementation, and both
//!    tests were strengthened:**
//!
//!    * Deleting the `S < L` check left the differential's malleability test
//!      *passing*, because every out-of-range `S` it tried also failed the
//!      verification equation. The test now builds `(R, S+L)`, which satisfies
//!      the equation — so only the range check can reject it.
//!    * Shortening the wide scalar reduction to 511 bits left every scalar
//!      unit test passing, because they all check "is the result in range",
//!      which stays true when high bits are silently dropped.
//!      `reduce_wide_uses_the_whole_input` now pins two values computed
//!      independently.
//!
//!    **Not covered by any test: the constant-time claims.** Nothing here
//!    measures timing or inspects the emitted code, so the section above is a
//!    structural argument, not a measurement. Replacing
//!    `EdwardsPoint::select`'s masked scan with a direct `table[index]` is a
//!    mutation that no test in this crate detects.
//!
//! # Surface
//!
//! Shaped to be a drop-in for `ed25519-dalek` *as `trust-proof-cert` actually
//! uses it* — ten API entry points, no more. See `SigningKey::generate`'s
//! absence, explained on [`SigningKey`].
//!
//! ```
//! use trust_ed25519::{Signer, SigningKey, Verifier, VerifyingKey};
//!
//! // RFC 8032 §7.1 TEST 2.
//! let seed = [
//!     0x4c, 0xcd, 0x08, 0x9b, 0x28, 0xff, 0x96, 0xda, 0x9d, 0xb6, 0xc3, 0x46,
//!     0xec, 0x11, 0x4e, 0x0f, 0x5b, 0x8a, 0x31, 0x9f, 0x35, 0xab, 0xa6, 0x24,
//!     0xda, 0x8c, 0xf6, 0xed, 0x4f, 0xb8, 0xa6, 0xfb,
//! ];
//! let signing_key = SigningKey::from_bytes(&seed);
//! let verifying_key = signing_key.verifying_key();
//! let signature = signing_key.sign(b"\x72");
//!
//! assert!(verifying_key.verify(b"\x72", &signature).is_ok());
//! assert!(verifying_key.verify(b"\x73", &signature).is_err());
//! ```

mod edwards;
mod field;
mod scalar;

use edwards::EdwardsPoint;
use scalar::Scalar;
use trust_sha2::{Digest, Sha512};

/// The length of a `SigningKey` seed, a `VerifyingKey` encoding, in octets.
pub const KEY_LENGTH: usize = 32;

/// The length of a `Signature`, in octets.
pub const SIGNATURE_LENGTH: usize = 64;

/// A signature operation failed, or a signature or key was malformed.
///
/// # Why this carries no detail
///
/// The incumbent's `SignatureError` is likewise opaque by design. More to the
/// point, the sole consumer in this tree never names this type, never matches
/// on it, and reaches it only through `format!("{e}")` into a diagnostic
/// string — so a variant taxonomy would be surface with no reader. Whatever
/// distinguishes "the key did not decompress" from "the equation did not
/// hold" is also a signal a verifier need not hand to whoever supplied the
/// bytes.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SignatureError;

impl core::fmt::Display for SignatureError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("signature error")
    }
}

/// Produces signatures of type `S`.
///
/// Mirrors `signature::Signer`, which `trust-proof-cert` imports by name so
/// that `.sign(..)` resolves. Implementors supply [`try_sign`]; [`sign`] is
/// the provided panicking wrapper.
///
/// [`try_sign`]: Signer::try_sign
/// [`sign`]: Signer::sign
pub trait Signer<S> {
    /// Sign `msg`, panicking on failure.
    ///
    /// Ed25519 signing is total — it has no failure mode for a well-formed key
    /// — so this never panics for [`SigningKey`]. The method exists because the
    /// incumbent's trait has it and the call sites use it.
    fn sign(&self, msg: &[u8]) -> S {
        self.try_sign(msg).expect("ed25519 signing is infallible")
    }

    /// Sign `msg`.
    fn try_sign(&self, msg: &[u8]) -> Result<S, SignatureError>;
}

/// Verifies signatures of type `S`.
///
/// Mirrors `signature::Verifier`.
pub trait Verifier<S> {
    /// `Ok(())` when `signature` is a valid signature by this key over `msg`.
    fn verify(&self, msg: &[u8], signature: &S) -> Result<(), SignatureError>;
}

/// An Ed25519 signature: `R || S`, 64 octets (RFC 8032 §5.1.6).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    bytes: [u8; SIGNATURE_LENGTH],
}

impl Signature {
    /// Decode 64 octets.
    ///
    /// **Only the length is checked here.** Neither half is validated:
    /// RFC 8032 §5.1.7 folds the `R` and `S` checks into verification, and the
    /// incumbent behaves identically (its `Signature::from_slice` accepts
    /// `[0u8; 64]`, which no key will ever verify). Deferring is what keeps
    /// the two implementations' accept boundaries the same.
    pub fn from_slice(bytes: &[u8]) -> Result<Signature, SignatureError> {
        if bytes.len() != SIGNATURE_LENGTH {
            return Err(SignatureError);
        }
        let mut out = [0u8; SIGNATURE_LENGTH];
        out.copy_from_slice(bytes);
        Ok(Signature { bytes: out })
    }

    /// The 64-octet encoding.
    pub fn to_bytes(&self) -> [u8; SIGNATURE_LENGTH] {
        self.bytes
    }
}

/// An Ed25519 signing key.
///
/// # There is no `generate`
///
/// The incumbent's `SigningKey::generate` takes an `&mut impl CryptoRngCore`,
/// a `rand_core` trait. Naming it would put a third-party crate back in this
/// crate's dependency list, which is the whole thing this replacement exists
/// to remove — and `generate` is not an algorithm, it is
/// `fill_bytes(&mut seed); from_bytes(&seed)`. RFC 8032 §5.1.5 agrees: the
/// private key *is* "32 octets of cryptographically secure random data".
///
/// So the randomness stays with the caller, who has an RNG already:
///
/// ```ignore (illustrative)
/// let mut seed = [0u8; 32];
/// rand::thread_rng().fill_bytes(&mut seed);
/// let key = SigningKey::from_bytes(&seed);
/// ```
///
/// This is the one place the swap is not source-compatible. It is a three-line
/// change in one Trust-owned function (`trust-proof-cert`'s
/// `CertSigningKey::generate`), and it confines the RNG question to the `rand`
/// replacement instead of sequencing this crate behind it.
///
/// # Zeroization
///
/// The seed is overwritten on drop. This is best-effort — without `unsafe` it
/// rests on [`core::hint::black_box`] to keep the write from being optimised
/// out — and it does not reach copies the caller made of the value passed to
/// [`from_bytes`] or returned from [`to_bytes`].
///
/// [`from_bytes`]: SigningKey::from_bytes
/// [`to_bytes`]: SigningKey::to_bytes
pub struct SigningKey {
    /// RFC 8032 §5.1.5's private key: 32 octets of secret data.
    seed: [u8; KEY_LENGTH],
    /// The clamped secret scalar `s`, §5.1.5 step 2, as 64-bit limbs.
    scalar: [u64; 4],
    /// The `prefix` of §5.1.6 step 2: the upper half of `SHA-512(seed)`.
    prefix: [u8; 32],
    /// `A = [s]B`, §5.1.5 step 4, already encoded.
    verifying_key: VerifyingKey,
}

impl SigningKey {
    /// Expand a 32-octet seed into a signing key. **RFC 8032 §5.1.5.**
    ///
    /// 1. Hash the seed with SHA-512, giving `h[0], ..., h[63]`.
    /// 2. Prune (`clamp`) the lower half: clear the three lowest bits of
    ///    `h[0]`, clear the highest bit of `h[31]`, set the second-highest bit
    ///    of `h[31]`. The result, little-endian, is the secret scalar `s`.
    /// 3. `A = [s]B`, encoded per §5.1.2.
    ///
    /// The upper half `h[32..64]` is the `prefix` §5.1.6 uses to derive the
    /// per-signature nonce deterministically.
    ///
    /// Infallible: every 32-octet string is a valid seed.
    pub fn from_bytes(seed: &[u8; KEY_LENGTH]) -> SigningKey {
        let h: [u8; 64] = Sha512::digest(seed).into();

        let mut clamped = [0u8; 32];
        clamped.copy_from_slice(&h[..32]);
        clamped[0] &= 248; // clear bits 0,1,2  -> s is a multiple of the cofactor 8
        clamped[31] &= 127; // clear bit 255
        clamped[31] |= 64; // set bit 254      -> s >= 2^254, fixing the ladder length

        let mut prefix = [0u8; 32];
        prefix.copy_from_slice(&h[32..]);

        let a_point = EdwardsPoint::BASEPOINT.mul(&clamped);
        let compressed = a_point.compress();

        let mut scalar = [0u64; 4];
        for (i, limb) in scalar.iter_mut().enumerate() {
            let mut chunk = [0u8; 8];
            chunk.copy_from_slice(&clamped[8 * i..8 * i + 8]);
            *limb = u64::from_le_bytes(chunk);
        }

        SigningKey {
            seed: *seed,
            scalar,
            prefix,
            verifying_key: VerifyingKey { compressed, point: a_point },
        }
    }

    /// The 32-octet seed this key was built from.
    ///
    /// Note this is the **seed**, not the expanded scalar — matching the
    /// incumbent, whose `to_bytes` likewise returns the value `from_bytes`
    /// accepts, so the two are inverse.
    pub fn to_bytes(&self) -> [u8; KEY_LENGTH] {
        self.seed
    }

    /// The corresponding public key `A`.
    pub fn verifying_key(&self) -> VerifyingKey {
        self.verifying_key
    }
}

impl Drop for SigningKey {
    fn drop(&mut self) {
        self.seed.fill(0);
        self.prefix.fill(0);
        self.scalar.fill(0);
        // Best-effort: make the writes observable so they are not elided.
        core::hint::black_box(&self.seed);
        core::hint::black_box(&self.prefix);
        core::hint::black_box(&self.scalar);
    }
}

impl Signer<Signature> for SigningKey {
    /// **RFC 8032 §5.1.6.**
    ///
    /// 2. `r = SHA-512(prefix || M)`, interpreted little-endian and reduced
    ///    mod `L`. The nonce is a deterministic function of the key and the
    ///    message — no randomness enters signing, which is what makes the
    ///    scheme reproducible and removes an RNG from the trusted path.
    /// 3. `R = [r]B`, encoded.
    /// 4. `k = SHA-512(R || A || M)`, reduced mod `L`.
    /// 5. `S = (r + k·s) mod L`.
    /// 6. The signature is `R || S`, 64 octets.
    fn try_sign(&self, msg: &[u8]) -> Result<Signature, SignatureError> {
        let mut hasher = Sha512::new();
        hasher.update(self.prefix);
        hasher.update(msg);
        let r = Scalar::from_bytes_mod_order_wide(&hasher.finalize().into());

        let r_point = EdwardsPoint::BASEPOINT.mul(&r.to_bytes()).compress();

        let mut hasher = Sha512::new();
        hasher.update(r_point);
        hasher.update(self.verifying_key.compressed);
        hasher.update(msg);
        let k = Scalar::from_bytes_mod_order_wide(&hasher.finalize().into());

        let s = Scalar::mul_add(&self.scalar, &k, &r);

        let mut bytes = [0u8; SIGNATURE_LENGTH];
        bytes[..32].copy_from_slice(&r_point);
        bytes[32..].copy_from_slice(&s.to_bytes());
        Ok(Signature { bytes })
    }
}

/// An Ed25519 verifying key `A`.
///
/// Holds both the decompressed point and the octets it came from. Keeping the
/// octets is what makes [`to_bytes`] a total inverse of [`from_bytes`]:
/// `trust-proof-cert`'s `TrustAnchorPolicy::from_verifying_keys` round-trips
/// every anchor through the pair and `.expect()`s it, so a `to_bytes` that
/// could emit something `from_bytes` rejects would be a panic in policy
/// construction rather than an error.
///
/// [`to_bytes`]: VerifyingKey::to_bytes
/// [`from_bytes`]: VerifyingKey::from_bytes
#[derive(Copy, Clone)]
pub struct VerifyingKey {
    compressed: [u8; KEY_LENGTH],
    point: EdwardsPoint,
}

/// Prints the encoding, not the coordinates.
///
/// `Debug` is required — `trust-proof-cert`'s `CertVerifyingKey` derives it —
/// and the projective coordinates are an implementation detail that is also
/// *redundant*: the same key has many coordinate representations, so printing
/// them would make two `Debug` outputs differ for equal keys.
impl core::fmt::Debug for VerifyingKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("VerifyingKey(")?;
        for byte in &self.compressed {
            write!(f, "{byte:02x}")?;
        }
        f.write_str(")")
    }
}

impl VerifyingKey {
    /// Decode a public key. **RFC 8032 §5.1.3.**
    ///
    /// Fails when `y >= p` (non-canonical), when `x² = (y²-1)/(d·y²+1)` has no
    /// square root (the encoding is not a curve point), or when `x = 0` with
    /// the sign bit set. See the crate header for the two of those the
    /// incumbent does not check.
    ///
    /// Note it does **not** reject small-order keys; neither does the
    /// incumbent's `verify` path.
    pub fn from_bytes(bytes: &[u8; KEY_LENGTH]) -> Result<VerifyingKey, SignatureError> {
        let point = EdwardsPoint::decompress(bytes).ok_or(SignatureError)?;
        Ok(VerifyingKey { compressed: *bytes, point })
    }

    /// The 32-octet encoding. Always accepted by [`from_bytes`].
    ///
    /// [`from_bytes`]: VerifyingKey::from_bytes
    pub fn to_bytes(&self) -> [u8; KEY_LENGTH] {
        self.compressed
    }
}

impl Verifier<Signature> for VerifyingKey {
    /// **RFC 8032 §5.1.7.**
    ///
    /// 1. Split the signature into `R` (32 octets) and `S` (32 octets).
    ///    **Decode `S` as an integer `0 <= S < L`, or the signature is
    ///    invalid** — this is the malleability check.
    /// 2. `k = SHA-512(R || A || M)`, reduced mod `L`.
    /// 3. Check `[S]B = R + [k]A`, computed here as `R' = [S]B + [k](-A)` and
    ///    compared by re-encoding `R'` against the signature's `R` octets.
    ///
    /// Cofactorless, matching the incumbent — see the crate header.
    fn verify(&self, msg: &[u8], signature: &Signature) -> Result<(), SignatureError> {
        let mut r_bytes = [0u8; 32];
        r_bytes.copy_from_slice(&signature.bytes[..32]);
        let mut s_bytes = [0u8; 32];
        s_bytes.copy_from_slice(&signature.bytes[32..]);

        let s = Scalar::from_canonical_bytes(&s_bytes).ok_or(SignatureError)?;

        let mut hasher = Sha512::new();
        hasher.update(r_bytes);
        hasher.update(self.compressed);
        hasher.update(msg);
        let k = Scalar::from_bytes_mod_order_wide(&hasher.finalize().into());

        let recomputed = EdwardsPoint::BASEPOINT
            .mul(&s.to_bytes())
            .add(&self.point.neg().mul(&k.to_bytes()))
            .compress();

        let mut diff = 0u8;
        for i in 0..32 {
            diff |= recomputed[i] ^ r_bytes[i];
        }
        if diff == 0 { Ok(()) } else { Err(SignatureError) }
    }
}
