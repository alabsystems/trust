// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

// `no_std` UNLESS the `std` feature is on. The feature exists for exactly one
// reason: `std::io::Write`, which `std::io::copy(&mut file, &mut hasher)` needs
// and which cannot be implemented without `std`. It adds NO dependency — the
// point of this crate is an empty dependency list, and a feature that could
// change that would defeat it.
#![cfg_attr(not(feature = "std"), no_std)]

//! **The Trust-owned SHA-2 family**, transcribed from
//! **FIPS PUB 180-4** (August 2015), *Secure Hash Standard (SHS)*.
//!
//! # Why this crate exists
//!
//! Practically every identity in this tree is a SHA-256 of something:
//! proof-certificate names, build-cache keys, MIR fingerprints, release
//! provenance records, the NDJSON report footer. Those digests are produced
//! today by the third-party `sha2` crate, which the verified lane reports as
//! `dependency-policy-excluded` — i.e. every proof that mentions a digest is
//! conditional on the correctness of a compilation unit Trust does not own.
//! Replacing it removes that condition, and it is the first of the four
//! replacements (`sha2`, `hmac`, `rand`, `ed25519-dalek`) that between them
//! retire 29 of the 95 reachable third-party packages.
//!
//! # What correctness means here, and how it is established
//!
//! A hash that silently disagrees with FIPS 180-4 on some input class does not
//! fail loudly; it renames things. Two artifacts that should share an identity
//! stop sharing it, or worse, two that should not, do. The evidence is
//! therefore layered, and each layer can fail independently of the others:
//!
//! 1. **Spec derivation, not transcription.** `tests/constant_derivation.rs`
//!    re-derives every initial hash value and every round constant from the
//!    FIPS 180-4 *definition* — fractional parts of square and cube roots of
//!    the low primes — in exact integer arithmetic, and compares against the
//!    tables in `sha256.rs`/`sha512.rs`. It shares no code with them.
//! 2. **Known-answer tests, with stated provenance.** `tests/kat.rs` carries the
//!    FIPS 180-4 Appendix vectors and the empty input. `tests/kat_published.rs`
//!    adds the **NIST CAVP** byte-oriented vectors — vendored verbatim in
//!    `tests/data/` (see `tests/data/PROVENANCE.md`), 388 `ShortMsg` records
//!    covering *every* byte length from 0 to one full block for all four
//!    widths, plus the CAVP Monte Carlo chained test (100,000 dependent hashes
//!    per algorithm) — and RFC 6234 §8.5. It separates PUBLISHED rows from
//!    DERIVED ones and enforces the distinction; do not add a row there without
//!    a source.
//!
//!    (This paragraph previously claimed `kat.rs` carried CAVP vectors. It did
//!    not — there were none in the tree until `kat_published.rs` landed.)
//! 3. **Padding boundaries.** `tests/boundary.rs` pins every input length that
//!    interacts with §5.1: 0, 55, 56, 63, 64, 119, 120, 127, 128, and their
//!    SHA-512 counterparts, plus every length from 0 to 3 blocks.
//! 4. **Chunk-boundary independence.** `tests/chunking.rs` asserts that a
//!    digest does not depend on how the byte stream was split across `update`
//!    calls — the failure mode a streaming caller actually hits.
//! 5. **Differential against the incumbent.** `tests/differential_sha2.rs`
//!    compares this implementation against the `sha2` crate over every length
//!    from 0 to 600 bytes plus randomized chunkings. This is the acceptance
//!    gate for the swap.
//!
//! # Surface
//!
//! [`Digest`] is the whole API: [`Digest::new`], [`Digest::update`],
//! [`Digest::finalize`], [`Digest::digest`]. It is shaped to be a drop-in for
//! the incumbent's surface *as this tree actually uses it* — in particular
//! `update` takes `impl AsRef<[u8]>` (call sites pass `[u8; 8]` by value,
//! `&[u8; N]` literals, `&Vec<u8>`, and `&&[u8]`), and the output type derefs
//! to `[u8]` as well as implementing `AsRef<[u8]>`, because the tree relies on
//! deref *coercion* and index autoderef, which `AsRef` does not provide.
//!
//! ```
//! use trust_sha2::{Digest, Sha256};
//!
//! let mut hasher = Sha256::new();
//! hasher.update(b"hello ");
//! hasher.update("world".as_bytes());
//! let digest = hasher.finalize();
//!
//! assert_eq!(
//!     format!("{digest:x}"),
//!     "b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9"
//! );
//! assert_eq!(&digest[..4], &[0xb9, 0x4d, 0x27, 0xb9]);
//! let bytes: [u8; 32] = digest.into();
//! assert_eq!(bytes[0], 0xb9);
//! ```

mod output;
mod sha256;
mod sha512;

pub use output::{Digest28, Digest32, Digest48, Digest64};
// The declared constant tables, for `tests/constant_derivation.rs`. Exported
// rather than tested in-crate because that test must not be able to reach the
// code that uses them: it re-derives the tables from the FIPS 180-4 definition
// and its value depends on sharing nothing with the implementation.
#[doc(hidden)]
pub use sha256::spec_tables as sha256_spec_tables;
pub use sha256::{NativeSha256, Sha224, Sha256};
#[doc(hidden)]
pub use sha512::spec_tables as sha512_spec_tables;
pub use sha512::{Sha384, Sha512};

/// A SHA-2 hash function.
///
/// # Contract notes
///
/// * `update` takes `impl AsRef<[u8]>`, deliberately. Call sites in this tree
///   pass fixed arrays **by value** (`hasher.update(len.to_le_bytes())`), and
///   a `&[u8]` parameter would reject those. This matches `digest 0.10`'s
///   `Digest::update`. Note the contrast with `trust_hmac::Mac::update`, which
///   takes `&[u8]` — that is also what the incumbent does, and the asymmetry
///   is load-bearing for a drop-in swap.
/// * `finalize` takes `self` by value. Every call site treats the hasher as
///   consumed; making it `&mut self` would silently permit reuse of a
///   finalized hasher, which is a correctness trap.
/// * The trait is intentionally not object-safe (`impl Trait` in argument
///   position, associated consts). Nothing in the tree uses `dyn Digest`.
pub trait Digest: Sized {
    /// The fixed-size digest this function produces.
    type Output: AsRef<[u8]>;

    /// The message block size in bytes (FIPS 180-4 Table 1).
    ///
    /// Not part of the incumbent's `Digest` trait, and not used by any hashing
    /// call site. It is here because HMAC (RFC 2104) is defined in terms of the
    /// hash's *block* size, not its output size, and getting that wrong is the
    /// classic HMAC implementation bug — so the value is published by the hash
    /// itself rather than being restated at the HMAC end.
    const BLOCK_SIZE: usize;

    /// The digest size in bytes.
    const OUTPUT_SIZE: usize;

    /// A hasher in the initial state H(0).
    fn new() -> Self;

    /// Absorb more of the message.
    ///
    /// The result depends only on the concatenation of everything passed, never
    /// on how it was split across calls.
    fn update(&mut self, data: impl AsRef<[u8]>);

    /// Pad per FIPS 180-4 §5.1 and emit the digest, consuming the hasher.
    fn finalize(self) -> Self::Output;

    /// One-shot convenience: `Self::new()`, one `update`, `finalize`.
    fn digest(data: impl AsRef<[u8]>) -> Self::Output {
        let mut hasher = Self::new();
        hasher.update(data);
        hasher.finalize()
    }
}

/// `std::io::Write`, so a hasher can be an `io::copy` sink.
///
/// Callers stream a file into a digest with
/// `std::io::copy(&mut reader, &mut hasher)?` rather than reading it into
/// memory first — six sites in `targo-trust` and one in `build-manifest` do
/// exactly this, and the incumbent supports it via `digest`'s `std` feature.
///
/// `write` always consumes the whole buffer, so it never reports a short write
/// and `write_all` cannot loop; `flush` is a no-op because there is no buffer
/// to a destination — the compression function has already absorbed every
/// complete block.
#[cfg(feature = "std")]
macro_rules! impl_io_write {
    ($($hasher:ty),* $(,)?) => {$(
        impl std::io::Write for $hasher {
            fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
                <$hasher as $crate::Digest>::update(self, buf);
                Ok(buf.len())
            }

            fn flush(&mut self) -> std::io::Result<()> {
                Ok(())
            }
        }
    )*};
}

#[cfg(feature = "std")]
impl_io_write!(Sha224, Sha256, Sha384, Sha512);
