// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![no_std]

//! **The Trust-owned HMAC**, per **RFC 2104** (*HMAC: Keyed-Hashing for Message
//! Authentication*) and **FIPS PUB 198-1** (*The Keyed-Hash Message
//! Authentication Code*).
//!
//! # The construction
//!
//! RFC 2104 §2 defines, for a hash `H` with block size `B` bytes and output
//! size `L` bytes, and key `K`:
//!
//! ```text
//!     HMAC(K, text) = H(K0 XOR opad || H(K0 XOR ipad || text))
//!
//!     ipad = the byte 0x36 repeated B times
//!     opad = the byte 0x5C repeated B times
//! ```
//!
//! where `K0` is `K` normalized to exactly `B` bytes (FIPS 198-1 §3, step 1-3):
//!
//! * `len(K) == B` — `K0 = K`.
//! * `len(K) < B` — `K0 = K` padded on the **right** with zeros to `B` bytes.
//! * `len(K) > B` — `K0 = H(K)` padded on the right with zeros to `B` bytes.
//!
//! The long-key branch is the one that is easy to get wrong and easy to leave
//! untested, because **no consumer in this tree exercises it**: both call sites
//! pass a 32-byte key and the block size is 64. It is implemented per spec
//! regardless, and `tests/rfc4231.rs` covers it with RFC 4231 test cases 6 and
//! 7 (131-byte keys), which is why those vectors are in the suite at all.
//!
//! # Note on what these tags are for in this tree
//!
//! Both consumers (`trust-cache`, `trust-buildcache`) say so themselves: the
//! key is derived from public, locally-available material, so a writer with
//! filesystem access can forge a tag. These are corruption and
//! producer-compatibility tags, not authentication. Implementing HMAC exactly
//! is still required — the digests are identities, and an identity that
//! disagrees with the standard disagrees with every other tool.
//!
//! # Surface
//!
//! ```
//! use trust_hmac::{Hmac, Mac};
//! use trust_sha2::Sha256;
//!
//! type HmacSha256 = Hmac<Sha256>;
//!
//! // RFC 4231 test case 2: key "Jefe", data "what do ya want for nothing?".
//! let mut mac = HmacSha256::new_from_slice(b"Jefe").expect("any key length is valid");
//! mac.update(b"what do ya want for nothing?");
//! assert_eq!(
//!     format!("{:x}", mac.finalize().into_bytes()),
//!     "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"
//! );
//! ```

use trust_sha2::Digest;

/// The largest hash block size this crate supports, in bytes.
///
/// SHA-512's 1024-bit block, the widest in `trust-sha2`. The padded key `K0`
/// is `B` bytes and `B` is only known through `D::BLOCK_SIZE`, an associated
/// const — `[u8; D::BLOCK_SIZE]` needs `generic_const_exprs`, so the buffers
/// below are fixed at this maximum and used up to `D::BLOCK_SIZE`. The bound
/// is enforced at compile time by [`Hmac::BLOCK_SIZE_FITS`], not at runtime:
/// a `Digest` with a larger block fails to build rather than silently
/// truncating its key.
const MAX_BLOCK_SIZE: usize = 128;

/// RFC 2104 §2: the inner pad byte.
const IPAD: u8 = 0x36;

/// RFC 2104 §2: the outer pad byte.
const OPAD: u8 = 0x5c;

/// A keyed message authentication code.
///
/// # Contract notes
///
/// * `update` takes `&[u8]`, **not** `impl AsRef<[u8]>`. That is the incumbent
///   `hmac 0.12` / `digest 0.10` shape, and it differs from
///   [`trust_sha2::Digest::update`] on purpose; do not "fix" the asymmetry.
/// * `finalize` and `verify_slice` both take `self` by value: a MAC state is
///   single-use, and both call sites already treat it that way.
pub trait Mac: Sized {
    /// The tag type, before the constant-time wrapper.
    type Output: AsRef<[u8]>;

    /// Create a MAC from key material of any length (RFC 2104 §3 permits any
    /// length; §3 recommends at least `L` bytes).
    ///
    /// Returns `Result` for drop-in compatibility with the incumbent, whose
    /// signature admits key-length-constrained MACs. For HMAC specifically this
    /// never fails, which is why both call sites `.expect(..)` it.
    ///
    /// # Errors
    ///
    /// Never, for HMAC. The variant exists to match the incumbent's signature.
    fn new_from_slice(key: &[u8]) -> Result<Self, InvalidLength>;

    /// Absorb more of the authenticated message.
    fn update(&mut self, data: &[u8]);

    /// Finish and return the tag inside a wrapper that discourages a
    /// variable-time comparison.
    fn finalize(self) -> CtOutput<Self>;

    /// Finish and compare against `tag` in constant time.
    ///
    /// # Errors
    ///
    /// [`MacError`] when `tag` is not the correct length, or does not match.
    fn verify_slice(self, tag: &[u8]) -> Result<(), MacError>;
}

/// HMAC over the hash `D` — RFC 2104.
///
/// # Representation
///
/// The two padded-key blocks are absorbed at construction and then discarded:
/// `inner` is a `D` that has already eaten `K0 XOR ipad`, and `outer` a `D`
/// that has already eaten `K0 XOR opad`. Nothing derived from the key is kept
/// beyond those two hash states, and `finalize` is then exactly the RFC's
/// outer step. This also means the per-message cost is one hash of the message
/// plus one compression of a two-block outer input — the standard shape.
pub struct Hmac<D: Digest> {
    /// `H(K0 XOR ipad || text)`, in progress.
    inner: D,
    /// `H(K0 XOR opad || ...)`, awaiting the inner digest.
    outer: D,
}

impl<D: Digest> Hmac<D> {
    /// Compile-time proof that `D`'s block fits the fixed-size key buffers.
    ///
    /// Evaluated because `new_from_slice` names it. A `Digest` whose
    /// `BLOCK_SIZE` exceeds [`MAX_BLOCK_SIZE`] is a build error at the point of
    /// use, never a silently truncated key.
    const BLOCK_SIZE_FITS: () = assert!(
        D::BLOCK_SIZE <= MAX_BLOCK_SIZE,
        "trust-hmac: hash block size exceeds MAX_BLOCK_SIZE; raise the constant"
    );
}

impl<D: Digest> Mac for Hmac<D> {
    type Output = D::Output;

    fn new_from_slice(key: &[u8]) -> Result<Self, InvalidLength> {
        let () = Self::BLOCK_SIZE_FITS;
        let block = D::BLOCK_SIZE;

        // FIPS 198-1 §3 steps 1-3: normalize the key to exactly `block` bytes.
        // The buffer starts zeroed, so "pad on the right with zeros" is simply
        // writing the key material into its prefix and leaving the rest.
        let mut k0 = [0u8; MAX_BLOCK_SIZE];
        if key.len() > block {
            // Step 2: keys longer than the BLOCK size are hashed first. Note it
            // is the block size, not the output size, that decides this.
            let hashed = D::digest(key);
            let hashed = hashed.as_ref();
            k0[..hashed.len()].copy_from_slice(hashed);
        } else {
            // Steps 1 and 3: shorter or equal keys are used as-is, zero-padded.
            k0[..key.len()].copy_from_slice(key);
        }

        // RFC 2104 §2: absorb `K0 XOR ipad` and `K0 XOR opad`.
        let mut ipad_key = [0u8; MAX_BLOCK_SIZE];
        let mut opad_key = [0u8; MAX_BLOCK_SIZE];
        for index in 0..block {
            ipad_key[index] = k0[index] ^ IPAD;
            opad_key[index] = k0[index] ^ OPAD;
        }

        let mut inner = D::new();
        inner.update(&ipad_key[..block]);
        let mut outer = D::new();
        outer.update(&opad_key[..block]);

        // Clear the derived key material. This is best-effort — without a
        // dependency there is no `zeroize`, and the optimizer is entitled to
        // remove a dead store. It is done anyway because it costs three
        // instructions and both consumers' keys, while not secret today, are
        // the kind of value a future caller may assume is not left on the
        // stack.
        k0.fill(0);
        ipad_key.fill(0);
        opad_key.fill(0);

        Ok(Self { inner, outer })
    }

    fn update(&mut self, data: &[u8]) {
        self.inner.update(data);
    }

    fn finalize(self) -> CtOutput<Self> {
        // RFC 2104 §2, outer step: H(K0 XOR opad || H(K0 XOR ipad || text)).
        let Self { inner, mut outer } = self;
        outer.update(inner.finalize());
        CtOutput { tag: outer.finalize() }
    }

    fn verify_slice(self, tag: &[u8]) -> Result<(), MacError> {
        let computed = self.finalize().into_bytes();
        let computed = computed.as_ref();

        // The LENGTH is not secret — it is a property of the hash, and a
        // caller-supplied tag of the wrong length is a malformed input, not a
        // near-miss. Rejecting it up front is what the incumbent's
        // `verify_slice` does too (`verify_truncated_*` are the opt-ins for
        // shorter tags, and no call site uses them).
        if computed.len() != tag.len() {
            return Err(MacError);
        }

        // Constant time in the CONTENTS: fold every byte before deciding, so
        // the loop count and the branch are both independent of where the
        // first difference is.
        let mut difference = 0u8;
        for (a, b) in computed.iter().zip(tag.iter()) {
            difference |= a ^ b;
        }
        if difference == 0 { Ok(()) } else { Err(MacError) }
    }
}

/// A finished tag, wrapped so it is not casually compared with `==`.
///
/// Mirrors the incumbent's `CtOutput`. Call [`CtOutput::into_bytes`] to get the
/// digest, which is where hex formatting lives; prefer [`Mac::verify_slice`]
/// over comparing bytes yourself.
pub struct CtOutput<M: Mac> {
    tag: M::Output,
}

impl<M: Mac> CtOutput<M> {
    /// Unwrap the tag.
    #[must_use]
    pub fn into_bytes(self) -> M::Output {
        self.tag
    }

    /// Wrap a tag. Present for symmetry; the crate itself never needs it.
    #[must_use]
    pub fn new(tag: M::Output) -> Self {
        Self { tag }
    }
}

/// The key length is not acceptable to this MAC.
///
/// HMAC never produces this — see [`Mac::new_from_slice`]. It exists because
/// the incumbent's signature has it and both call sites `.expect(..)` on the
/// `Result`, which requires `Debug`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidLength;

impl core::fmt::Display for InvalidLength {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("invalid key length")
    }
}

impl core::error::Error for InvalidLength {}

/// A MAC verification failed.
///
/// Deliberately carries nothing: a failure must not disclose whether the tag
/// was the wrong length, off by one byte, or unrelated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MacError;

impl core::fmt::Display for MacError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("MAC tag mismatch")
    }
}

impl core::error::Error for MacError {}
