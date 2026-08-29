// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Fixed-size digest outputs.
//!
//! One type per digest width. These carry no hashing logic at all — they exist
//! because the ~130 call sites in this tree consume a digest in thirteen
//! distinct ways (hex formatting, deref-to-slice, indexing, `copy_from_slice`,
//! `.into()` to `[u8; 32]`, by-value iteration), and every one of those forms
//! has to keep working when the incumbent `sha2` crate leaves the graph.
//!
//! The incumbent returns `generic_array::GenericArray<u8, U32>`. The impls here
//! are chosen to be behaviourally identical to that type on exactly the surface
//! the tree uses, so the swap is not observable. In particular
//! [`core::fmt::LowerHex`] mirrors `generic-array 0.14`'s `hex.rs`: two
//! lowercase hex digits per byte, honouring `{:.N}` precision, emitted with
//! `write_str` (so width/fill are ignored — same as the incumbent).

/// Generate a fixed-size digest output type.
///
/// `$name` is the type, `$n` its length in bytes.
macro_rules! digest_output {
    ($name:ident, $n:expr, $doc:expr) => {
        #[doc = $doc]
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $name([u8; $n]);

        impl $name {
            /// The digest length in bytes.
            pub const LEN: usize = $n;

            /// Wrap raw bytes. Used by this crate's hash finalizers.
            #[must_use]
            pub const fn from_bytes(bytes: [u8; $n]) -> Self {
                Self(bytes)
            }

            /// The digest as a fixed-size array.
            #[must_use]
            pub const fn to_bytes(self) -> [u8; $n] {
                self.0
            }

            /// The digest as a byte slice.
            #[must_use]
            pub const fn as_slice(&self) -> &[u8] {
                &self.0
            }
        }

        // Consumption form 4-8, 11, 12: `&digest` coerces to `&[u8]`,
        // `digest[0]`, `digest[..8]`, `.as_slice()`, `.iter()`, and
        // `copy_from_slice(&digest)` all come from this one impl. `AsRef`
        // cannot substitute: deref coercion and index autoderef are Deref-only.
        impl core::ops::Deref for $name {
            type Target = [u8];

            fn deref(&self) -> &[u8] {
                &self.0
            }
        }

        // Consumption form 10: `sha256_hex(hasher.finalize())` takes
        // `impl AsRef<[u8]>` BY VALUE, where no deref coercion is available.
        impl AsRef<[u8]> for $name {
            fn as_ref(&self) -> &[u8] {
                &self.0
            }
        }

        // Consumption form 9: `let x: [u8; 32] = hasher.finalize().into();`
        impl From<$name> for [u8; $n] {
            fn from(digest: $name) -> [u8; $n] {
                digest.0
            }
        }

        impl From<[u8; $n]> for $name {
            fn from(bytes: [u8; $n]) -> Self {
                Self(bytes)
            }
        }

        // Consumption form 13: `for byte in digest { .. }` yields `u8`.
        impl IntoIterator for $name {
            type Item = u8;
            type IntoIter = core::array::IntoIter<u8, $n>;

            fn into_iter(self) -> Self::IntoIter {
                self.0.into_iter()
            }
        }

        impl<'a> IntoIterator for &'a $name {
            type Item = &'a u8;
            type IntoIter = core::slice::Iter<'a, u8>;

            fn into_iter(self) -> Self::IntoIter {
                self.0.iter()
            }
        }

        // Consumption forms 1-3: `format!("{:x}", digest)`.
        impl core::fmt::LowerHex for $name {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                hex_fmt(&self.0, f, b"0123456789abcdef")
            }
        }

        impl core::fmt::UpperHex for $name {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                hex_fmt(&self.0, f, b"0123456789ABCDEF")
            }
        }

        // `{:?}` renders the hex form: a digest printed in an assertion message
        // as a 32-element decimal array is unreadable and, worse, not greppable
        // against the hex spelling every other part of the tree stores.
        impl core::fmt::Debug for $name {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.write_str(concat!(stringify!($name), "("))?;
                core::fmt::LowerHex::fmt(self, f)?;
                f.write_str(")")
            }
        }
    };
}

digest_output!(Digest28, 28, "A 224-bit (28-byte) digest. Output of [`crate::Sha224`].");
digest_output!(Digest32, 32, "A 256-bit (32-byte) digest. Output of [`crate::Sha256`].");
digest_output!(Digest48, 48, "A 384-bit (48-byte) digest. Output of [`crate::Sha384`].");
digest_output!(Digest64, 64, "A 512-bit (64-byte) digest. Output of [`crate::Sha512`].");

/// Shared hex formatter, byte-for-byte compatible with `generic-array 0.14`'s
/// `hex.rs`: two digits per byte, `{:.N}` precision truncates to `N` digits
/// (an odd `N` prints the high nibble of the last byte), and output goes
/// through `write_str`, so `{:>70x}`-style width and fill are ignored exactly
/// as they are by the incumbent.
///
/// One deliberate difference: a precision LARGER than the digest is clamped.
/// `generic-array` slices its scratch buffer with the unclamped value there and
/// panics; a formatting call must not be able to panic on a digest.
fn hex_fmt(bytes: &[u8], f: &mut core::fmt::Formatter<'_>, chars: &[u8; 16]) -> core::fmt::Result {
    // 64 bytes is the widest digest in this crate (SHA-512), so 128 hex digits.
    let mut buf = [0u8; 128];
    let max_digits = f.precision().unwrap_or(bytes.len() * 2).min(bytes.len() * 2);
    let max_hex = max_digits.div_ceil(2);

    for (i, byte) in bytes.iter().take(max_hex).enumerate() {
        buf[i * 2] = chars[usize::from(byte >> 4)];
        buf[i * 2 + 1] = chars[usize::from(byte & 0x0f)];
    }

    // Every byte written above came from `chars`, which is ASCII.
    let text = core::str::from_utf8(&buf[..max_digits]).map_err(|_| core::fmt::Error)?;
    f.write_str(text)
}
