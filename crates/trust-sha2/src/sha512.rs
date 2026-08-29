// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! SHA-384 and SHA-512, per **FIPS PUB 180-4**.
//!
//! Structurally SHA-256 widened: 64-bit words, a 1024-bit block, eighty rounds,
//! and a 128-bit length field. The rotation amounts in §4.1.3 are *different
//! numbers*, not the §4.1.2 ones rescaled, so they are transcribed one per
//! function below with the equation number attached.
//!
//! | Item | Spec location |
//! |---|---|
//! | Word size 64 bits, block size 1024 bits | §1, Table 1 |
//! | `Ch`, `Maj`, `Σ0`, `Σ1`, `σ0`, `σ1` | §4.1.3, equations (4.8)-(4.13) |
//! | Round constants `K{512}` | §4.2.3 |
//! | Padding (128-bit length field) | §5.1.2 |
//! | SHA-384 initial hash value | §5.3.4 |
//! | SHA-512 initial hash value | §5.3.5 |
//! | Message schedule + compression | §6.4.2 |
//!
//! **Why this is here with no call site.** RFC 8032 Ed25519 is SHA-512 by
//! definition — the signature scheme's hash is not a parameter. Phase 1 of the
//! third-party replacement replaces `ed25519-dalek` next, and it cannot start
//! without this.

use crate::Digest;
use crate::output::{Digest48, Digest64};

/// Block size in bytes. FIPS 180-4 Table 1: SHA-384/SHA-512 have a 1024-bit
/// message block.
pub(crate) const BLOCK_SIZE: usize = 128;

/// Byte offset of the 128-bit big-endian message length. FIPS 180-4 §5.1.2:
/// the length field is 128 bits, i.e. the final 16 bytes of the final block.
const LENGTH_OFFSET: usize = BLOCK_SIZE - 16;

/// FIPS 180-4 §5.3.5 — SHA-512 initial hash value H(0).
///
/// "the first sixty-four bits of the fractional parts of the square roots of
/// the first eight prime numbers" (2 .. 19).
#[rustfmt::skip]
const IV_512: [u64; 8] = [
    0x6a09_e667_f3bc_c908, 0xbb67_ae85_84ca_a73b, 0x3c6e_f372_fe94_f82b, 0xa54f_f53a_5f1d_36f1,
    0x510e_527f_ade6_82d1, 0x9b05_688c_2b3e_6c1f, 0x1f83_d9ab_fb41_bd6b, 0x5be0_cd19_137e_2179,
];

/// FIPS 180-4 §5.3.4 — SHA-384 initial hash value H(0).
///
/// "the first sixty-four bits of the fractional parts of the square roots of
/// the ninth through sixteenth prime numbers" (23 .. 53). Note the SHA-224 IV
/// is the *second* thirty-two bits of these same square roots — the two tables
/// are two windows on one derivation, which the derivation test checks jointly.
#[rustfmt::skip]
const IV_384: [u64; 8] = [
    0xcbbb_9d5d_c105_9ed8, 0x629a_292a_367c_d507, 0x9159_015a_3070_dd17, 0x152f_ecd8_f70e_5939,
    0x6733_2667_ffc0_0b31, 0x8eb4_4a87_6858_1511, 0xdb0c_2e0d_64f9_8fa7, 0x47b5_481d_befa_4fa4,
];

/// FIPS 180-4 §4.2.3 — the eighty 64-bit round constants K{512}.
///
/// "the first sixty-four bits of the fractional parts of the cube roots of the
/// first eighty prime numbers". The first sixty-four entries share their high
/// thirty-two bits with `K256`, because both are windows on the same cube
/// roots; `tests/constant_derivation.rs` checks that relation as well as the
/// values themselves.
#[rustfmt::skip]
const K512: [u64; 80] = [
    0x428a_2f98_d728_ae22, 0x7137_4491_23ef_65cd, 0xb5c0_fbcf_ec4d_3b2f, 0xe9b5_dba5_8189_dbbc,
    0x3956_c25b_f348_b538, 0x59f1_11f1_b605_d019, 0x923f_82a4_af19_4f9b, 0xab1c_5ed5_da6d_8118,
    0xd807_aa98_a303_0242, 0x1283_5b01_4570_6fbe, 0x2431_85be_4ee4_b28c, 0x550c_7dc3_d5ff_b4e2,
    0x72be_5d74_f27b_896f, 0x80de_b1fe_3b16_96b1, 0x9bdc_06a7_25c7_1235, 0xc19b_f174_cf69_2694,
    0xe49b_69c1_9ef1_4ad2, 0xefbe_4786_384f_25e3, 0x0fc1_9dc6_8b8c_d5b5, 0x240c_a1cc_77ac_9c65,
    0x2de9_2c6f_592b_0275, 0x4a74_84aa_6ea6_e483, 0x5cb0_a9dc_bd41_fbd4, 0x76f9_88da_8311_53b5,
    0x983e_5152_ee66_dfab, 0xa831_c66d_2db4_3210, 0xb003_27c8_98fb_213f, 0xbf59_7fc7_beef_0ee4,
    0xc6e0_0bf3_3da8_8fc2, 0xd5a7_9147_930a_a725, 0x06ca_6351_e003_826f, 0x1429_2967_0a0e_6e70,
    0x27b7_0a85_46d2_2ffc, 0x2e1b_2138_5c26_c926, 0x4d2c_6dfc_5ac4_2aed, 0x5338_0d13_9d95_b3df,
    0x650a_7354_8baf_63de, 0x766a_0abb_3c77_b2a8, 0x81c2_c92e_47ed_aee6, 0x9272_2c85_1482_353b,
    0xa2bf_e8a1_4cf1_0364, 0xa81a_664b_bc42_3001, 0xc24b_8b70_d0f8_9791, 0xc76c_51a3_0654_be30,
    0xd192_e819_d6ef_5218, 0xd699_0624_5565_a910, 0xf40e_3585_5771_202a, 0x106a_a070_32bb_d1b8,
    0x19a4_c116_b8d2_d0c8, 0x1e37_6c08_5141_ab53, 0x2748_774c_df8e_eb99, 0x34b0_bcb5_e19b_48a8,
    0x391c_0cb3_c5c9_5a63, 0x4ed8_aa4a_e341_8acb, 0x5b9c_ca4f_7763_e373, 0x682e_6ff3_d6b2_b8a3,
    0x748f_82ee_5def_b2fc, 0x78a5_636f_4317_2f60, 0x84c8_7814_a1f0_ab72, 0x8cc7_0208_1a64_39ec,
    0x90be_fffa_2363_1e28, 0xa450_6ceb_de82_bde9, 0xbef9_a3f7_b2c6_7915, 0xc671_78f2_e372_532b,
    0xca27_3ece_ea26_619c, 0xd186_b8c7_21c0_c207, 0xeada_7dd6_cde0_eb1e, 0xf57d_4f7f_ee6e_d178,
    0x06f0_67aa_7217_6fba, 0x0a63_7dc5_a2c8_98a6, 0x113f_9804_bef9_0dae, 0x1b71_0b35_131c_471b,
    0x28db_77f5_2304_7d84, 0x32ca_ab7b_40c7_2493, 0x3c9e_be0a_15c9_bebc, 0x431d_67c4_9c10_0d4c,
    0x4cc5_d4be_cb3e_42b6, 0x597f_299c_fc65_7e2a, 0x5fcb_6fab_3ad6_faec, 0x6c44_198c_4a47_5817,
];

// FIPS 180-4 §4.1.3, equations (4.8)-(4.13).

/// (4.8) `Ch(x, y, z) = (x AND y) XOR ((NOT x) AND z)`.
const fn ch(x: u64, y: u64, z: u64) -> u64 {
    (x & y) ^ (!x & z)
}

/// (4.9) `Maj(x, y, z) = (x AND y) XOR (x AND z) XOR (y AND z)`.
const fn maj(x: u64, y: u64, z: u64) -> u64 {
    (x & y) ^ (x & z) ^ (y & z)
}

/// (4.10) `Σ{512}0(x) = ROTR28(x) XOR ROTR34(x) XOR ROTR39(x)`.
const fn big_sigma0(x: u64) -> u64 {
    x.rotate_right(28) ^ x.rotate_right(34) ^ x.rotate_right(39)
}

/// (4.11) `Σ{512}1(x) = ROTR14(x) XOR ROTR18(x) XOR ROTR41(x)`.
const fn big_sigma1(x: u64) -> u64 {
    x.rotate_right(14) ^ x.rotate_right(18) ^ x.rotate_right(41)
}

/// (4.12) `σ{512}0(x) = ROTR1(x) XOR ROTR8(x) XOR SHR7(x)`.
const fn small_sigma0(x: u64) -> u64 {
    x.rotate_right(1) ^ x.rotate_right(8) ^ (x >> 7)
}

/// (4.13) `σ{512}1(x) = ROTR19(x) XOR ROTR61(x) XOR SHR6(x)`.
const fn small_sigma1(x: u64) -> u64 {
    x.rotate_right(19) ^ x.rotate_right(61) ^ (x >> 6)
}

/// The shared SHA-384/SHA-512 state machine.
///
/// The buffering rule is the SHA-256 one with the wider block and the wider
/// length field; it is written out rather than shared with `sha256.rs` because
/// the thing most likely to be wrong in a hand-written hash is the padding
/// arithmetic, and abstracting over the two width families would put const
/// generics between the reader and §5.1.2.
#[derive(Clone)]
pub(crate) struct Core512 {
    h: [u64; 8],
    block: [u8; BLOCK_SIZE],
    /// Occupied prefix of `block`. Invariant: `< BLOCK_SIZE`.
    filled: usize,
    /// Total message length in bytes. FIPS 180-4 bounds a SHA-512 message at
    /// `2^128 - 1` bits, so a `u128` byte counter cannot overflow for any
    /// message the standard defines.
    total_bytes: u128,
}

impl Core512 {
    const fn new(iv: [u64; 8]) -> Self {
        Self { h: iv, block: [0; BLOCK_SIZE], filled: 0, total_bytes: 0 }
    }

    fn update(&mut self, mut data: &[u8]) {
        self.total_bytes = self.total_bytes.wrapping_add(data.len() as u128);

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

        while data.len() >= BLOCK_SIZE {
            let (block, rest) = data.split_at(BLOCK_SIZE);
            let block: &[u8; BLOCK_SIZE] = block.try_into().expect("split_at yields BLOCK_SIZE");
            self.compress(block);
            data = rest;
        }

        if !data.is_empty() {
            self.block[..data.len()].copy_from_slice(data);
            self.filled = data.len();
        }
    }

    /// FIPS 180-4 §5.1.2: append `1`, then `k` zero bits with `k` the smallest
    /// non-negative solution of `l + 1 + k ≡ 896 (mod 1024)`, then `l` as a
    /// 128-bit big-endian integer.
    fn finish(&mut self) -> [u64; 8] {
        let bit_len = self.total_bytes.wrapping_mul(8);

        self.block[self.filled] = 0x80;
        self.filled += 1;

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

    /// FIPS 180-4 §6.4.2 — the SHA-512 hash computation for one block.
    fn compress(&mut self, block: &[u8; BLOCK_SIZE]) {
        // Step 1: the message schedule, eighty 64-bit words.
        let mut w = [0u64; 80];
        for (t, word) in w.iter_mut().take(16).enumerate() {
            let bytes: [u8; 8] = block[t * 8..t * 8 + 8].try_into().expect("8-byte window");
            *word = u64::from_be_bytes(bytes);
        }
        for t in 16..80 {
            w[t] = small_sigma1(w[t - 2])
                .wrapping_add(w[t - 7])
                .wrapping_add(small_sigma0(w[t - 15]))
                .wrapping_add(w[t - 16]);
        }

        // Step 2.
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = self.h;

        // Step 3: eighty rounds.
        for t in 0..80 {
            let t1 = h
                .wrapping_add(big_sigma1(e))
                .wrapping_add(ch(e, f, g))
                .wrapping_add(K512[t])
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

        // Step 4.
        for (slot, value) in self.h.iter_mut().zip([a, b, c, d, e, f, g, h]) {
            *slot = slot.wrapping_add(value);
        }
    }
}

/// Serialize the state words big-endian (§6.4.2 step 4).
fn state_to_bytes(h: &[u64; 8]) -> [u8; 64] {
    let mut out = [0u8; 64];
    for (chunk, word) in out.chunks_exact_mut(8).zip(h.iter()) {
        chunk.copy_from_slice(&word.to_be_bytes());
    }
    out
}

/// SHA-512 — FIPS PUB 180-4 §6.4.
///
/// ```
/// use trust_sha2::{Digest, Sha512};
///
/// // FIPS 180-4 Appendix C.1, the one-block message "abc".
/// let digest = Sha512::digest(b"abc");
/// assert_eq!(
///     format!("{digest:x}"),
///     "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a\
///      2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
/// );
/// ```
#[derive(Clone)]
pub struct Sha512 {
    core: Core512,
}

impl Digest for Sha512 {
    type Output = Digest64;

    const BLOCK_SIZE: usize = BLOCK_SIZE;
    const OUTPUT_SIZE: usize = 64;

    fn new() -> Self {
        Self { core: Core512::new(IV_512) }
    }

    fn update(&mut self, data: impl AsRef<[u8]>) {
        self.core.update(data.as_ref());
    }

    fn finalize(mut self) -> Digest64 {
        Digest64::from_bytes(state_to_bytes(&self.core.finish()))
    }
}

impl Default for Sha512 {
    fn default() -> Self {
        <Self as Digest>::new()
    }
}

/// SHA-384 — FIPS PUB 180-4 §6.5.
///
/// SHA-512's compression from a different initial hash value, truncated to the
/// leftmost 384 bits.
#[derive(Clone)]
pub struct Sha384 {
    core: Core512,
}

impl Digest for Sha384 {
    type Output = Digest48;

    const BLOCK_SIZE: usize = BLOCK_SIZE;
    const OUTPUT_SIZE: usize = 48;

    fn new() -> Self {
        Self { core: Core512::new(IV_384) }
    }

    fn update(&mut self, data: impl AsRef<[u8]>) {
        self.core.update(data.as_ref());
    }

    fn finalize(mut self) -> Digest48 {
        let full = state_to_bytes(&self.core.finish());
        let mut out = [0u8; 48];
        out.copy_from_slice(&full[..48]);
        Digest48::from_bytes(out)
    }
}

impl Default for Sha384 {
    fn default() -> Self {
        <Self as Digest>::new()
    }
}

/// The constant tables, exposed to `tests/constant_derivation.rs` only.
#[doc(hidden)]
pub mod spec_tables {
    /// SHA-512 round constants, for independent re-derivation in tests.
    pub const K512: [u64; 80] = super::K512;
    /// SHA-512 initial hash value, for independent re-derivation in tests.
    pub const IV_512: [u64; 8] = super::IV_512;
    /// SHA-384 initial hash value, for independent re-derivation in tests.
    pub const IV_384: [u64; 8] = super::IV_384;
}
