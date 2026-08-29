// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! SHA-224 and SHA-256, per **FIPS PUB 180-4**.
//!
//! Section references in this file are to FIPS PUB 180-4 (August 2015),
//! *Secure Hash Standard (SHS)*. The two functions share one compression
//! function and differ only in the initial hash value (§5.3.2 vs §5.3.3) and
//! in how much of the final state is emitted (§6.1 vs §6.2).
//!
//! | Item | Spec location |
//! |---|---|
//! | Word size 32 bits, block size 512 bits | §1, Table 1 |
//! | `Ch`, `Maj`, `Σ0`, `Σ1`, `σ0`, `σ1` | §4.1.2, equations (4.2)-(4.7) |
//! | Round constants `K{256}` | §4.2.2 |
//! | Padding | §5.1.1 |
//! | SHA-224 initial hash value | §5.3.2 |
//! | SHA-256 initial hash value | §5.3.3 |
//! | Message schedule + compression | §6.2.2 |

use crate::Digest;
use crate::output::{Digest28, Digest32};

/// Block size in bytes. FIPS 180-4 Table 1: SHA-224/SHA-256 have a 512-bit
/// message block.
pub(crate) const BLOCK_SIZE: usize = 64;

/// Byte offset at which the 64-bit big-endian message length is written.
/// FIPS 180-4 §5.1.1: the padded message ends with a 64-bit length field, so
/// the length occupies the final 8 bytes of the final block.
const LENGTH_OFFSET: usize = BLOCK_SIZE - 8;

/// FIPS 180-4 §5.3.3 — SHA-256 initial hash value H(0).
///
/// "the first thirty-two bits of the fractional parts of the square roots of
/// the first eight prime numbers" (2, 3, 5, 7, 11, 13, 17, 19). Derived
/// independently and checked against this table by
/// `tests/constant_derivation.rs`, so a transcription slip cannot survive.
const IV_256: [u32; 8] = [
    0x6a09_e667,
    0xbb67_ae85,
    0x3c6e_f372,
    0xa54f_f53a,
    0x510e_527f,
    0x9b05_688c,
    0x1f83_d9ab,
    0x5be0_cd19,
];

/// FIPS 180-4 §5.3.2 — SHA-224 initial hash value H(0).
///
/// "the second thirty-two bits of the fractional parts of the square roots of
/// the ninth through sixteenth prime numbers" (23 .. 53).
const IV_224: [u32; 8] = [
    0xc105_9ed8,
    0x367c_d507,
    0x3070_dd17,
    0xf70e_5939,
    0xffc0_0b31,
    0x6858_1511,
    0x64f9_8fa7,
    0xbefa_4fa4,
];

/// FIPS 180-4 §4.2.2 — the sixty-four 32-bit round constants K{256}.
///
/// "the first thirty-two bits of the fractional parts of the cube roots of the
/// first sixty-four prime numbers". Derived independently and checked against
/// this table by `tests/constant_derivation.rs`.
#[rustfmt::skip]
const K256: [u32; 64] = [
    0x428a_2f98, 0x7137_4491, 0xb5c0_fbcf, 0xe9b5_dba5, 0x3956_c25b, 0x59f1_11f1, 0x923f_82a4, 0xab1c_5ed5,
    0xd807_aa98, 0x1283_5b01, 0x2431_85be, 0x550c_7dc3, 0x72be_5d74, 0x80de_b1fe, 0x9bdc_06a7, 0xc19b_f174,
    0xe49b_69c1, 0xefbe_4786, 0x0fc1_9dc6, 0x240c_a1cc, 0x2de9_2c6f, 0x4a74_84aa, 0x5cb0_a9dc, 0x76f9_88da,
    0x983e_5152, 0xa831_c66d, 0xb003_27c8, 0xbf59_7fc7, 0xc6e0_0bf3, 0xd5a7_9147, 0x06ca_6351, 0x1429_2967,
    0x27b7_0a85, 0x2e1b_2138, 0x4d2c_6dfc, 0x5338_0d13, 0x650a_7354, 0x766a_0abb, 0x81c2_c92e, 0x9272_2c85,
    0xa2bf_e8a1, 0xa81a_664b, 0xc24b_8b70, 0xc76c_51a3, 0xd192_e819, 0xd699_0624, 0xf40e_3585, 0x106a_a070,
    0x19a4_c116, 0x1e37_6c08, 0x2748_774c, 0x34b0_bcb5, 0x391c_0cb3, 0x4ed8_aa4a, 0x5b9c_ca4f, 0x682e_6ff3,
    0x748f_82ee, 0x78a5_636f, 0x84c8_7814, 0x8cc7_0208, 0x90be_fffa, 0xa450_6ceb, 0xbef9_a3f7, 0xc671_78f2,
];

// FIPS 180-4 §4.1.2, equations (4.2)-(4.7). Written as `const fn` so they are
// definitions, not fused hand-optimizations of the round body: the round body
// below reads exactly like equations (6.2)-(6.6) of §6.2.2.

/// (4.2) `Ch(x, y, z) = (x AND y) XOR ((NOT x) AND z)`.
const fn ch(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ (!x & z)
}

/// (4.3) `Maj(x, y, z) = (x AND y) XOR (x AND z) XOR (y AND z)`.
const fn maj(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ (x & z) ^ (y & z)
}

/// (4.4) `Σ{256}0(x) = ROTR2(x) XOR ROTR13(x) XOR ROTR22(x)`.
const fn big_sigma0(x: u32) -> u32 {
    x.rotate_right(2) ^ x.rotate_right(13) ^ x.rotate_right(22)
}

/// (4.5) `Σ{256}1(x) = ROTR6(x) XOR ROTR11(x) XOR ROTR25(x)`.
const fn big_sigma1(x: u32) -> u32 {
    x.rotate_right(6) ^ x.rotate_right(11) ^ x.rotate_right(25)
}

/// (4.6) `σ{256}0(x) = ROTR7(x) XOR ROTR18(x) XOR SHR3(x)`.
const fn small_sigma0(x: u32) -> u32 {
    x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3)
}

/// (4.7) `σ{256}1(x) = ROTR17(x) XOR ROTR19(x) XOR SHR10(x)`.
const fn small_sigma1(x: u32) -> u32 {
    x.rotate_right(17) ^ x.rotate_right(19) ^ (x >> 10)
}

/// The shared SHA-224/SHA-256 state machine.
///
/// Buffering is the part of a hand-written hash that actually breaks, so it is
/// stated once here and shared: `update` is called with arbitrary chunk
/// boundaries by every streaming caller in the tree (`read` loops over 8 KiB
/// and 64 KiB buffers, per-field length framing that pushes 8 bytes at a
/// time), and the digest must not depend on how the byte stream was sliced.
/// `tests/chunking.rs` asserts exactly that against every split of a
/// multi-block message.
#[derive(Clone)]
pub(crate) struct Core256 {
    /// The working hash value H, §6.2.2.
    h: [u32; 8],
    /// Bytes of the current, not-yet-compressed block.
    block: [u8; BLOCK_SIZE],
    /// How many bytes of `block` are occupied. Invariant: `< BLOCK_SIZE`.
    /// A full block is compressed immediately, never left buffered, so
    /// `finish` can always write the 0x80 pad byte without a bounds check.
    filled: usize,
    /// Total message length in bytes. FIPS 180-4 bounds a SHA-256 message at
    /// `2^64 - 1` bits, so the 64-bit BIT count cannot overflow for any
    /// message the standard defines; `wrapping_mul` states what happens past
    /// that bound rather than making it a panic in a hash function.
    total_bytes: u64,
}

impl Core256 {
    const fn new(iv: [u32; 8]) -> Self {
        Self { h: iv, block: [0; BLOCK_SIZE], filled: 0, total_bytes: 0 }
    }

    /// Absorb `data`, which may start or end anywhere relative to a block.
    fn update(&mut self, mut data: &[u8]) {
        self.total_bytes = self.total_bytes.wrapping_add(data.len() as u64);

        // 1. Top up a partially filled block first.
        if self.filled > 0 {
            let take = (BLOCK_SIZE - self.filled).min(data.len());
            self.block[self.filled..self.filled + take].copy_from_slice(&data[..take]);
            self.filled += take;
            data = &data[take..];
            if self.filled == BLOCK_SIZE {
                let block = self.block;
                self.compress(&block);
                self.filled = 0;
            }
        }

        // 2. Consume whole blocks straight out of the caller's slice.
        while data.len() >= BLOCK_SIZE {
            let (block, rest) = data.split_at(BLOCK_SIZE);
            let block: &[u8; BLOCK_SIZE] = block.try_into().expect("split_at yields BLOCK_SIZE");
            self.compress(block);
            data = rest;
        }

        // 3. Buffer the remainder. `data.len() < BLOCK_SIZE` here, and the
        //    buffer is empty (either it started empty, or step 1 emptied it,
        //    or step 1 could not fill it and `data` is now empty).
        if !data.is_empty() {
            self.block[..data.len()].copy_from_slice(data);
            self.filled = data.len();
        }
    }

    /// FIPS 180-4 §5.1.1 (padding) followed by the last one or two
    /// compressions; returns the final hash value H(N).
    ///
    /// Padding appends a single `1` bit, then `k` zero bits where `k` is the
    /// smallest non-negative solution of `l + 1 + k ≡ 448 (mod 512)`, then `l`
    /// as a 64-bit big-endian integer. Since messages here are whole bytes,
    /// the `1` bit is the byte `0x80`.
    fn finish(&mut self) -> [u32; 8] {
        let bit_len = self.total_bytes.wrapping_mul(8);

        // The `1` bit. `filled < BLOCK_SIZE` is an invariant of `update`.
        self.block[self.filled] = 0x80;
        self.filled += 1;

        // If the length field no longer fits, zero-fill and emit this block;
        // the length goes in a further, otherwise-zero block.
        if self.filled > LENGTH_OFFSET {
            self.block[self.filled..].fill(0);
            let block = self.block;
            self.compress(&block);
            self.filled = 0;
        }

        self.block[self.filled..LENGTH_OFFSET].fill(0);
        self.block[LENGTH_OFFSET..].copy_from_slice(&bit_len.to_be_bytes());
        let block = self.block;
        self.compress(&block);
        self.filled = 0;

        self.h
    }

    /// FIPS 180-4 §6.2.2 — the SHA-256 hash computation for one block.
    fn compress(&mut self, block: &[u8; BLOCK_SIZE]) {
        // Step 1: prepare the message schedule W.
        let mut w = [0u32; 64];
        for (t, word) in w.iter_mut().take(16).enumerate() {
            let bytes: [u8; 4] = block[t * 4..t * 4 + 4].try_into().expect("4-byte window");
            *word = u32::from_be_bytes(bytes);
        }
        for t in 16..64 {
            w[t] = small_sigma1(w[t - 2])
                .wrapping_add(w[t - 7])
                .wrapping_add(small_sigma0(w[t - 15]))
                .wrapping_add(w[t - 16]);
        }

        // Step 2: initialize the eight working variables with H(i-1).
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = self.h;

        // Step 3: sixty-four rounds.
        for t in 0..64 {
            let t1 = h
                .wrapping_add(big_sigma1(e))
                .wrapping_add(ch(e, f, g))
                .wrapping_add(K256[t])
                .wrapping_add(w[t]);
            let t2 = big_sigma0(a).wrapping_add(maj(a, b, c));
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }

        // Step 4: compute the i-th intermediate hash value H(i).
        for (slot, value) in self.h.iter_mut().zip([a, b, c, d, e, f, g, h]) {
            *slot = slot.wrapping_add(value);
        }
    }
}

/// Serialize the state words big-endian. FIPS 180-4 §6.2.2 step 4 / §1: the
/// digest is `H(N)0 || H(N)1 || ...`, each word most-significant byte first.
fn state_to_bytes(h: &[u32; 8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (chunk, word) in out.chunks_exact_mut(4).zip(h.iter()) {
        chunk.copy_from_slice(&word.to_be_bytes());
    }
    out
}

/// SHA-256 — FIPS PUB 180-4 §6.2.
///
/// The tree's default digest: certificate identities, cache keys, and release
/// provenance records are all SHA-256 of some canonical byte string.
///
/// ```
/// use trust_sha2::{Digest, Sha256};
///
/// // FIPS 180-4 Appendix B.1, the one-block message "abc".
/// let digest = Sha256::digest(b"abc");
/// assert_eq!(
///     format!("{digest:x}"),
///     "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
/// );
/// ```
#[derive(Clone)]
pub struct Sha256 {
    core: Core256,
}

impl Digest for Sha256 {
    type Output = Digest32;

    const BLOCK_SIZE: usize = BLOCK_SIZE;
    const OUTPUT_SIZE: usize = 32;

    fn new() -> Self {
        Self { core: Core256::new(IV_256) }
    }

    fn update(&mut self, data: impl AsRef<[u8]>) {
        self.core.update(data.as_ref());
    }

    fn finalize(mut self) -> Digest32 {
        Digest32::from_bytes(state_to_bytes(&self.core.finish()))
    }
}

impl Default for Sha256 {
    fn default() -> Self {
        <Self as Digest>::new()
    }
}

/// SHA-224 — FIPS PUB 180-4 §6.1.
///
/// SHA-256's compression run from a different initial hash value, truncated to
/// the leftmost 224 bits. No call site in this tree uses it; it is here because
/// omitting it would leave the crate a partial SHA-2 implementation whose gaps
/// are invisible until someone needs one.
#[derive(Clone)]
pub struct Sha224 {
    core: Core256,
}

impl Digest for Sha224 {
    type Output = Digest28;

    const BLOCK_SIZE: usize = BLOCK_SIZE;
    const OUTPUT_SIZE: usize = 28;

    fn new() -> Self {
        Self { core: Core256::new(IV_224) }
    }

    fn update(&mut self, data: impl AsRef<[u8]>) {
        self.core.update(data.as_ref());
    }

    fn finalize(mut self) -> Digest28 {
        // §6.1: "the final hash value ... truncated to its left-most 224 bits".
        let full = state_to_bytes(&self.core.finish());
        let mut out = [0u8; 28];
        out.copy_from_slice(&full[..28]);
        Digest28::from_bytes(out)
    }
}

impl Default for Sha224 {
    fn default() -> Self {
        <Self as Digest>::new()
    }
}

/// The constant tables, exposed to `tests/constant_derivation.rs` only.
///
/// The test re-derives every entry from the FIPS 180-4 *definition* (fractional
/// parts of square/cube roots of the low primes) using exact integer
/// arithmetic, and compares. This is what makes the tables above spec-derived
/// rather than transcribed: a single wrong nibble fails a test that shares no
/// code with the tables.
#[doc(hidden)]
pub mod spec_tables {
    /// SHA-256 round constants, for independent re-derivation in tests.
    pub const K256: [u32; 64] = super::K256;
    /// SHA-256 initial hash value, for independent re-derivation in tests.
    pub const IV_256: [u32; 8] = super::IV_256;
    /// SHA-224 initial hash value, for independent re-derivation in tests.
    pub const IV_224: [u32; 8] = super::IV_224;
}
