//! Total, verified checksum / rolling-hash / parity arithmetic for `no_std`
//! Trust components.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0
//!
//! # Why this crate exists, and who calls it
//!
//! A checksum is an arithmetic claim about a byte string, and in this tree the
//! arithmetic *inside* the checksum is routinely discharged by prose or by
//! `wrapping_*`, which does not discharge it at all — it renames the overflow.
//!
//! **`crates/trust-sha2/src/sha256.rs:189`** and
//! **`crates/trust-sha2/src/sha512.rs:178`** — the message-length field:
//!
//! ```text
//! let bit_len = self.total_bytes.wrapping_mul(8);
//! ```
//!
//! The entire argument that this is the right value is the doc comment eleven
//! lines earlier at **`sha256.rs:136`** — *"FIPS 180-4 bounds a SHA-256 message
//! at `2^64 - 1` bits, so the 64-bit BIT count cannot overflow for any message
//! the standard defines"*. That is a statement about the *standard's* domain,
//! not about this function's: nothing in `update` rejects a longer message, so
//! past `2^61` bytes the length field silently wraps and the padding encodes a
//! different `l` than the one that was hashed — two distinct messages with the
//! same digest, produced by the padding rather than by a collision.
//! [`message_bit_len`] is that multiply performed where it cannot wrap, and
//! [`message_len_ok`] is the FIPS bound itself as a *checked proposition*
//! (`ensures result <= 1`) rather than as a sentence.
//!
//! **`crates/trust-binary-parse/src/unified.rs:807`** is a second, independent
//! hand-rolled SHA-256 whose length field says the same thing with no comment
//! at all:
//!
//! ```text
//! let bit_len = (bytes.len() as u64).wrapping_mul(8);
//! ```
//!
//! **`crates/trust-bmc/src/verifier_api.rs:3863-3864`** — a base-`10^9`
//! accumulator whose side condition is written in the panic message:
//!
//! ```text
//! // Exact by construction: rest % BASE < 10^9 always fits i64.
//! chunks.push(i64::try_from(rest % BASE).expect("base-10^9 chunk fits i64"));
//! ```
//!
//! [`base_1e9_chunk`] returns a `u32`, so the `try_into` and its `.expect` are
//! **deleted rather than proved**: a `u32` bounded by `10^9 - 1` converts into
//! `i64` infallibly, with no fallible conversion left to explain.
//!
//! **`crates/trust-vcgen/src/vc_simplifier.rs:864`** — a Rabin-Karp step used
//! to *name* CSE variables:
//!
//! ```text
//! h = h.wrapping_mul(31).wrapping_add(b as usize);
//! ```
//!
//! Two distinct subformulas that collide get the same CSE name. Nothing in the
//! file says what makes that safe. [`rolling_hash_step`] is the same recurrence
//! reduced into a stated modulus, so the codomain is a fact of the signature.
//!
//! **`crates/trust-witness/src/store.rs:25-26`** and
//! **`crates/trust-clean/src/mirsem/call_lift.rs:229-230`** are FNV-1a folds
//! whose collision arguments live in prose — `call_lift.rs:223` is *"negligible
//! at corpus scale (birthday ≈ 2·10⁻¹³ at 2000 keys)"*, which is a claim about
//! a corpus size nothing enforces. This crate does not replace either: a
//! collision bound on a 64-bit non-cryptographic hash is not an arithmetic
//! obligation and is out of scope here. What it does provide is the family of
//! *bounded* mixers ([`rolling_hash_step`], [`fletcher16_4`], [`adler32_4`])
//! whose codomain is small and stated, so a caller that needs a bucket rather
//! than a fingerprint stops reaching for a wrapping multiply.
//!
//! **`crates/trust-js-sem/src/lexer.rs:963`** and
//! **`crates/trust-js-interp/src/literals.rs:138`** —
//! `u16::try_from(v & 0xffff).expect("masked")`, twice, in two crates. The mask
//! makes the conversion infallible and the `.expect` says so in English.
//! [`low16`] is that same truncation with the fact in the return type.
//!
//! # Totality
//!
//! Every function here is **total**. A `requires` is fatal under the strict
//! lane, and none is needed: bytes and residues arrive by value. Where an input
//! is outside a function's meaningful domain the function returns a *stated*
//! value rather than panicking — [`message_bit_len`] returns `u64::MAX`, which
//! is not a multiple of 8 and therefore not a bit length any message has.
//!
//! # Two tiers, marked per item
//!
//! **Tier 1 — proved bound.** A grammar `ensures` clause the compiler
//! discharges: [`crc_width_bytes`], [`checksum_bytes_clamped`],
//! [`message_len_ok`], [`fletcher_state_ok`], [`adler_state_ok`] and
//! [`checksum_agrees`].
//!
//! **Tier 2 — proved totality, bound carried by the return type.** Everything
//! else. What is proved is that no product, sum, difference or shift in the
//! body can overflow, on any input.
//!
//! # What is NOT proved here, and is pinned by tests instead
//!
//! **Which byte carries which coefficient, which polynomial bit is tested, and
//! whether the modulus is the right one.** No obligation in this crate can see
//! any of that: [`fletcher_pack`]'s `(b as u16) * 256 + (a as u16)` peaks at
//! exactly `u16::MAX` whichever way round `a` and `b` go, so swapping them
//! changes no range and the strict lane still returns exit 0 while every
//! checksum is wrong. `scripts/trust_checksum_strict_gate.sh` performs that
//! swap deliberately and asserts both halves — the lane passes, and named unit
//! tests go red. Proofs cover overflow and discharged contracts; they do not
//! cover whether the answer is right.

#![no_std]

// ---------------------------------------------------------------------------
// Tier 1 — contracted.
//
// `clamp_u8` is the single composition carrier: a contracted wrapper inherits
// a bound only from a callee that itself carries one (a wrapper over an
// UNcontracted clamp measures UNKNOWN), which is why it has an `ensures` no
// caller outside this file reads.
// ---------------------------------------------------------------------------

fn clamp_u8(v: u8, hi: u8) -> u8 ensures result <= hi {
    if v > hi { hi } else { v }
}

/// The number of bytes a checksum of `width_bits` bits occupies, or `0` for a
/// width no standard checksum uses.
///
/// **Tier 1.** `ensures result <= 8` is checked.
///
/// `0` is the sentinel: no checksum occupies zero bytes, so it cannot collide
/// with an answer. The widths are CRC-8/16/24/32/64 plus Fletcher-16,
/// Adler-32 and the internet checksum, which share those sizes.
pub fn crc_width_bytes(width_bits: u8) -> u8 ensures result <= 8 {
    if width_bits == 8 { return 1; }
    if width_bits == 16 { return 2; }
    if width_bits == 24 { return 3; }
    if width_bits == 32 { return 4; }
    if width_bits == 64 { return 8; }
    0
}

/// [`crc_width_bytes`], clamped to the caller's field width `cap`.
///
/// **Tier 1.** `ensures result <= cap` is checked.
///
/// The clamp is LIVE: a caller with a four-byte trailer that is handed
/// `width_bits = 64` gets `4`, as a checked proposition, rather than an `8`
/// that overruns the field.
pub fn checksum_bytes_clamped(width_bits: u8, cap: u8) -> u8 ensures result <= cap {
    clamp_u8(crc_width_bytes(width_bits), cap)
}

/// `1` when a message of `bytes` bytes has a bit length representable in the
/// 64-bit SHA-2 length field, `0` otherwise.
///
/// **Tier 1.** `ensures result <= 1` is checked.
///
/// This is `crates/trust-sha2/src/sha256.rs:136`'s doc comment turned into an
/// obligation. `2305843009213693951` is `2^61 - 1`, the largest byte count
/// whose bit count fits a `u64`.
pub fn message_len_ok(bytes: u64) -> u8 ensures result <= 1 {
    if bytes > 2305843009213693951 { return 0; }
    1
}

/// `1` when `(a, b)` is a well-formed Fletcher-16 running state.
///
/// **Tier 1.** `ensures result <= 1` is checked.
///
/// Fletcher-16 residues live in `[0, 254]`; `255` is not a residue mod 255.
/// A state read back from storage has no such guarantee, so this is the test
/// to run before resuming.
pub fn fletcher_state_ok(a: u8, b: u8) -> u8 ensures result <= 1 {
    if a > 254 { return 0; }
    if b > 254 { return 0; }
    1
}

/// `1` when `(a, b)` is a well-formed Adler-32 running state.
///
/// **Tier 1.** `ensures result <= 1` is checked.
pub fn adler_state_ok(a: u32, b: u32) -> u8 ensures result <= 1 {
    if a > 65520 { return 0; }
    if b > 65520 { return 0; }
    1
}

/// `1` when a computed checksum equals the stored one.
///
/// **Tier 1.** `ensures result <= 1` is checked.
///
/// A comparison is not arithmetic and needs no proof; what this buys is that
/// the *result* is a `0`/`1` a caller may index or multiply with, which is
/// the shape that keeps a verification result out of a `bool`-to-integer cast.
pub fn checksum_agrees(computed: u32, stored: u32) -> u8 ensures result <= 1 {
    if computed == stored { return 1; }
    0
}

// ---------------------------------------------------------------------------
// Tier 2 — the arithmetic.
//
// Every operand here gets its range from a WIDENING CAST or from a `%` by a
// literal, never from a callee's postcondition (which does not reach the
// interval engine) and never from a constant mask (which contributes nothing).
// That is why the residues are reduced at every step rather than at the end:
// a `%`-derived local carries a range, a sum-derived local does not.
// ---------------------------------------------------------------------------

/// The bit length of a `bytes`-byte message, or `u64::MAX` when that does not
/// fit a `u64`.
///
/// **Tier 2.** Proved: the multiply cannot overflow, on any input.
///
/// This is `crates/trust-sha2/src/sha256.rs:189`'s
/// `self.total_bytes.wrapping_mul(8)` with the bound enforced instead of
/// described, and `crates/trust-binary-parse/src/unified.rs:807`'s identical
/// line, which carries no description at all. `u64::MAX` is not a multiple of
/// 8, so it is not a bit length any message has and cannot be mistaken for one.
pub fn message_bit_len(bytes: u64) -> u64 {
    if bytes > 2305843009213693951 { return 18446744073709551615; }
    bytes * 8
}

/// The low 16 bits of `v`.
///
/// **Tier 2.** Proved: the body cannot panic.
///
/// This is `crates/trust-js-sem/src/lexer.rs:963` and
/// `crates/trust-js-interp/src/literals.rs:138`'s
/// `u16::try_from(v & 0xffff).expect("masked")` with the fact in the return
/// type. The truncation is still a truncation — that is what the callers want
/// — but there is no longer a fallible conversion whose success is asserted in
/// a panic string.
pub fn low16(v: u32) -> u16 { (v & 65535) as u16 }

/// `v % 10^9`, as a `u32`.
///
/// **Tier 2.** Proved: the body cannot panic. The true range is
/// `[0, 999999999]`.
///
/// This is `crates/trust-bmc/src/verifier_api.rs:3864`'s
/// `i64::try_from(rest % BASE).expect("base-10^9 chunk fits i64")`. A `u32`
/// converts into `i64` infallibly, so the caller's `try_from` and its `.expect`
/// are deleted rather than proved — the comment at `:3863` no longer has
/// anything to justify.
pub fn base_1e9_chunk(v: u64) -> u32 { (v % 1000000000) as u32 }

/// One step of a Rabin-Karp rolling hash, reduced modulo `65521`.
///
/// **Tier 2.** Proved: neither the multiply nor the add overflows, on any
/// input. The true range is `[0, 65520]`.
///
/// This is `crates/trust-vcgen/src/vc_simplifier.rs:864`'s
/// `h.wrapping_mul(31).wrapping_add(b as usize)` with the accumulator widened
/// so nothing wraps and the codomain stated. A caller that wanted a bucket
/// gets one; a caller that wanted a fingerprint learns from the signature that
/// this is not one.
pub fn rolling_hash_step(h: u32, b: u8) -> u32 {
    let x: u64 = (h as u64) * 31 + (b as u64);
    (x % 65521) as u32
}

/// The even-parity bit of `b`: `1` when `b` has an odd number of set bits.
///
/// **Tier 2.** Proved: the shifts and the folds cannot panic. The true range
/// is `[0, 1]`.
pub fn parity8(b: u8) -> u8 {
    let x: u8 = b ^ (b >> 4);
    let y: u8 = x ^ (x >> 2);
    let z: u8 = y ^ (y >> 1);
    z & 1
}

/// The even-parity bit of `v`.
///
/// **Tier 2.** Proved: the shifts and the folds cannot panic. The true range
/// is `[0, 1]`.
pub fn parity32(v: u32) -> u8 {
    let a: u32 = v ^ (v >> 16);
    let b: u32 = a ^ (a >> 8);
    let c: u32 = b ^ (b >> 4);
    let d: u32 = c ^ (c >> 2);
    let e: u32 = d ^ (d >> 1);
    (e & 1) as u8
}

/// One bit-step of a bit-at-a-time CRC-8: shift left, and XOR the polynomial
/// back in when the bit shifted out was set.
///
/// The `u16` accumulator is what makes the doubling provable — `c * 2` at `u8`
/// overflows for `c > 127`, which is exactly the interesting half of the input
/// space. The entry guard is mathematically dead when called from [`crc8`],
/// and structurally required: without it the multiply is unbounded and its row
/// goes UNKNOWN.
fn crc8_bit(c: u16, poly: u16) -> u16 {
    if c > 255 { return 0; }
    let d: u16 = c * 2;
    if c > 127 { (d & 255) ^ poly } else { d & 255 }
}

/// The CRC-8 of the single byte `b` under polynomial `poly`, MSB-first, with a
/// zero initial register.
///
/// **Tier 2.** Proved: none of the eight doublings overflows, on any input.
///
/// Eight steps, unrolled. A `while` loop with a `decreases` clause does not
/// discharge under the strict lane (`loop-decreases measure may not decrease`),
/// and a bit-at-a-time CRC has a fixed arity per byte, so unrolling costs
/// nothing but lines.
pub fn crc8(b: u8, poly: u8) -> u8 {
    let p: u16 = poly as u16;
    let c1: u16 = crc8_bit(b as u16, p);
    let c2: u16 = crc8_bit(c1, p);
    let c3: u16 = crc8_bit(c2, p);
    let c4: u16 = crc8_bit(c3, p);
    let c5: u16 = crc8_bit(c4, p);
    let c6: u16 = crc8_bit(c5, p);
    let c7: u16 = crc8_bit(c6, p);
    let c8: u16 = crc8_bit(c7, p);
    c8 as u8
}

/// Pack a Fletcher-16 state into its checksum: `b * 256 + a`.
///
/// The peak is `255 * 256 + 255`, which is exactly `u16::MAX` — the proof has
/// no slack, and it has none *either way round*, which is why swapping `a` and
/// `b` here is invisible to every obligation in this crate. See the module
/// docs, and `scripts/trust_checksum_strict_gate.sh` mutation D.
fn fletcher_pack(a: u8, b: u8) -> u16 { (b as u16) * 256 + (a as u16) }

/// Fletcher-16 over four bytes, resuming from the running state `(a_in, b_in)`.
///
/// **Tier 2.** Proved: none of the ten reductions, eight sums or one product
/// overflows, on any input. The true range is `[0, 65278]`.
///
/// The state is reduced on entry, so a corrupt `(a_in, b_in)` read back from
/// storage cannot produce an out-of-range residue — it produces a *wrong*
/// checksum, which is what [`fletcher_state_ok`] is for.
pub fn fletcher16_4(a_in: u8, b_in: u8, d0: u8, d1: u8, d2: u8, d3: u8) -> u16 {
    let a0: u32 = (a_in as u32) % 255;
    let b0: u32 = (b_in as u32) % 255;
    let a1: u32 = (a0 + (d0 as u32)) % 255;
    let b1: u32 = (b0 + a1) % 255;
    let a2: u32 = (a1 + (d1 as u32)) % 255;
    let b2: u32 = (b1 + a2) % 255;
    let a3: u32 = (a2 + (d2 as u32)) % 255;
    let b3: u32 = (b2 + a3) % 255;
    let a4: u32 = (a3 + (d3 as u32)) % 255;
    let b4: u32 = (b3 + a4) % 255;
    fletcher_pack(a4 as u8, b4 as u8)
}

/// Pack an Adler-32 state into its checksum: `b * 65536 + a`.
///
/// The peak is `65535 * 65536 + 65535`, which is exactly `u32::MAX`.
fn adler_pack(a: u16, b: u16) -> u32 { (b as u32) * 65536 + (a as u32) }

/// Adler-32 over four bytes, resuming from the running state `(a_in, b_in)`.
///
/// **Tier 2.** Proved: none of the ten reductions, eight sums or one product
/// overflows, on any input.
pub fn adler32_4(a_in: u32, b_in: u32, d0: u8, d1: u8, d2: u8, d3: u8) -> u32 {
    let a0: u32 = a_in % 65521;
    let b0: u32 = b_in % 65521;
    let a1: u32 = (a0 + (d0 as u32)) % 65521;
    let b1: u32 = (b0 + a1) % 65521;
    let a2: u32 = (a1 + (d1 as u32)) % 65521;
    let b2: u32 = (b1 + a2) % 65521;
    let a3: u32 = (a2 + (d2 as u32)) % 65521;
    let b3: u32 = (b2 + a3) % 65521;
    let a4: u32 = (a3 + (d3 as u32)) % 65521;
    let b4: u32 = (b3 + a4) % 65521;
    adler_pack(a4 as u16, b4 as u16)
}

/// The one's-complement sum of four 16-bit words, unfolded.
///
/// **Tier 2.** Proved: no partial sum overflows. The peak is `4 * 65535`,
/// supplied entirely by the widening casts — no guard appears anywhere.
pub fn internet_sum4(w0: u16, w1: u16, w2: u16, w3: u16) -> u32 {
    (w0 as u32) + (w1 as u32) + (w2 as u32) + (w3 as u32)
}

/// The one's-complement sum of eight 16-bit words, unfolded.
///
/// **Tier 2.** Proved: no partial sum overflows. The peak is `8 * 65535`.
pub fn internet_sum8(
    w0: u16, w1: u16, w2: u16, w3: u16, w4: u16, w5: u16, w6: u16, w7: u16,
) -> u32 {
    (w0 as u32) + (w1 as u32) + (w2 as u32) + (w3 as u32)
        + (w4 as u32) + (w5 as u32) + (w6 as u32) + (w7 as u32)
}

/// RFC 1071 carry folding: add the high half back into the low half until the
/// result fits 16 bits.
///
/// **Tier 2.** Proved: none of the three folds overflows. Three folds are
/// enough for any `u32`: the first leaves at most `131070`, the second at most
/// `65536`, the third at most `65535`.
///
/// The bound is carried by the `u16` return type, which is also what makes the
/// third fold's narrowing cast safe. A `while sum > 65535 { .. }` loop — the
/// way RFC 1071 states it — does not discharge under the strict lane.
pub fn ones_complement_fold(s: u32) -> u16 {
    let f1: u32 = s / 65536 + s % 65536;
    let f2: u32 = f1 / 65536 + f1 % 65536;
    let f3: u32 = f2 / 65536 + f2 % 65536;
    f3 as u16
}

/// The internet checksum (RFC 1071) of four 16-bit words.
///
/// **Tier 2.** Proved: nothing in the sum, the folds or the complement can
/// panic.
///
/// The sum and the fold are written out rather than delegated to
/// [`internet_sum4`] and [`ones_complement_fold`]. That is not style: a callee
/// containing `/` or `%` cannot be bundled into its caller at all — the
/// delegating spelling fails with *"native typed-TrustIr lowering did not
/// complete"* — and this is the composition, not the contract, so no wrapper
/// trick avoids it. See `docs/STRICT_VERIFICATION_FRAGMENT.md` §2.4.
pub fn internet_checksum4(w0: u16, w1: u16, w2: u16, w3: u16) -> u16 {
    let s: u32 = (w0 as u32) + (w1 as u32) + (w2 as u32) + (w3 as u32);
    let f1: u32 = s / 65536 + s % 65536;
    let f2: u32 = f1 / 65536 + f1 % 65536;
    let f3: u32 = f2 / 65536 + f2 % 65536;
    !(f3 as u16)
}

/// The internet checksum (RFC 1071) of eight 16-bit words.
///
/// **Tier 2.** Proved: nothing in the sum, the folds or the complement can
/// panic.
pub fn internet_checksum8(
    w0: u16, w1: u16, w2: u16, w3: u16, w4: u16, w5: u16, w6: u16, w7: u16,
) -> u16 {
    let s: u32 = (w0 as u32) + (w1 as u32) + (w2 as u32) + (w3 as u32)
        + (w4 as u32) + (w5 as u32) + (w6 as u32) + (w7 as u32);
    let f1: u32 = s / 65536 + s % 65536;
    let f2: u32 = f1 / 65536 + f1 % 65536;
    let f3: u32 = f2 / 65536 + f2 % 65536;
    !(f3 as u16)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A deterministic 64-bit LCG (Knuth's MMIX constants), so the sweeps reach
    /// interior values no structured pattern would and stay reproducible and
    /// dependency-free.
    fn lcg(state: &mut u64) -> u64 {
        *state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        *state
    }

    // -- THE ORACLES ------------------------------------------------------
    //
    // Written by a DIFFERENT METHOD from the crate wherever one exists: loops
    // where the crate is unrolled, `<<`/`>>` where the crate multiplies, `u128`
    // where the crate reduces, and `count_ones` — a decision procedure written
    // by somebody else — for parity.

    /// Fletcher-16 the way every reference implementation spells it: a loop,
    /// with the reduction at the end of each step.
    fn oracle_fletcher(init_a: u8, init_b: u8, data: &[u8]) -> u16 {
        let mut a: u32 = (init_a as u32) % 255;
        let mut b: u32 = (init_b as u32) % 255;
        for &d in data {
            a = (a + d as u32) % 255;
            b = (b + a) % 255;
        }
        ((b << 8) | a) as u16
    }

    /// Adler-32 the way RFC 1950 spells it.
    fn oracle_adler(init_a: u32, init_b: u32, data: &[u8]) -> u32 {
        let mut a: u32 = init_a % 65521;
        let mut b: u32 = init_b % 65521;
        for &d in data {
            a = (a + d as u32) % 65521;
            b = (b + a) % 65521;
        }
        (b << 16) | a
    }

    /// RFC 1071 as written: accumulate wide, fold while it does not fit, then
    /// complement.
    fn oracle_inet(words: &[u16]) -> u16 {
        let mut sum: u64 = 0;
        for &w in words {
            sum += w as u64;
        }
        while sum > 0xffff {
            sum = (sum >> 16) + (sum & 0xffff);
        }
        !(sum as u16)
    }

    fn oracle_fold(s: u32) -> u16 {
        let mut v: u64 = s as u64;
        while v > 0xffff {
            v = (v >> 16) + (v & 0xffff);
        }
        v as u16
    }

    /// Bit-at-a-time CRC-8 with shifts and a wrapping register, MSB-first.
    fn oracle_crc8(byte: u8, poly: u8) -> u8 {
        let mut c: u8 = byte;
        for _ in 0..8 {
            if c & 0x80 != 0 {
                c = (c << 1) ^ poly;
            } else {
                c <<= 1;
            }
        }
        c
    }

    // -- PARITY -----------------------------------------------------------

    #[test]
    fn parity8_matches_count_ones_over_every_byte() {
        for b in 0u16..=255 {
            let b = b as u8;
            assert_eq!(parity8(b), (b.count_ones() % 2) as u8, "b={b}");
        }
    }

    #[test]
    fn parity32_matches_count_ones_over_a_sweep() {
        let mut s: u64 = 0x2026_08_29;
        for _ in 0..20000 {
            let v = lcg(&mut s) as u32;
            assert_eq!(parity32(v), (v.count_ones() % 2) as u8, "v={v:#010x}");
        }
        for v in [0u32, 1, 0x8000_0000, u32::MAX, 0x5555_5555, 0xAAAA_AAAA] {
            assert_eq!(parity32(v), (v.count_ones() % 2) as u8, "v={v:#010x}");
        }
    }

    // -- CRC-8 ------------------------------------------------------------

    #[test]
    fn crc8_matches_a_bitwise_oracle_over_every_byte_and_polynomial() {
        for b in 0u16..=255 {
            for p in 0u16..=255 {
                assert_eq!(crc8(b as u8, p as u8), oracle_crc8(b as u8, p as u8), "b={b} p={p}");
            }
        }
    }

    #[test]
    fn crc8_reproduces_the_published_smbus_check_value() {
        // CRC-8/SMBUS: width 8, poly 0x07, init 0x00, no reflection, no
        // xorout. Its PUBLISHED check value — the CRC of the ASCII string
        // "123456789" — is 0xF4. A multi-byte CRC is the single-byte step
        // applied to `crc ^ byte`, which is the only composition this crate's
        // one-byte function needs to support.
        let mut c: u8 = 0;
        for &b in b"123456789" {
            c = crc8(c ^ b, 0x07);
        }
        assert_eq!(c, 0xF4, "CRC-8/SMBUS check value");
    }

    // -- MESSAGE LENGTH ---------------------------------------------------

    #[test]
    fn message_bit_len_matches_checked_mul_across_the_boundary() {
        let edges: [u64; 9] = [
            0,
            1,
            2_305_843_009_213_693_950,
            2_305_843_009_213_693_951, // 2^61 - 1, the last representable
            2_305_843_009_213_693_952, // 2^61, the first that is not
            2_305_843_009_213_693_953,
            u64::MAX / 2,
            u64::MAX - 1,
            u64::MAX,
        ];
        for b in edges {
            match b.checked_mul(8) {
                Some(v) => assert_eq!(message_bit_len(b), v, "b={b}"),
                None => assert_eq!(message_bit_len(b), u64::MAX, "b={b}"),
            }
        }
        let mut s: u64 = 7;
        for _ in 0..20000 {
            let b = lcg(&mut s);
            match b.checked_mul(8) {
                Some(v) => assert_eq!(message_bit_len(b), v, "b={b}"),
                None => assert_eq!(message_bit_len(b), u64::MAX, "b={b}"),
            }
        }
    }

    #[test]
    fn message_len_ok_agrees_with_checked_mul() {
        let mut s: u64 = 11;
        for _ in 0..20000 {
            let b = lcg(&mut s);
            assert_eq!(message_len_ok(b), b.checked_mul(8).is_some() as u8, "b={b}");
        }
        assert_eq!(message_len_ok(2_305_843_009_213_693_951), 1);
        assert_eq!(message_len_ok(2_305_843_009_213_693_952), 0);
        // The sentinel is not a bit length: it is not a multiple of 8.
        assert_ne!(u64::MAX % 8, 0);
    }

    // -- FIELD AND CHUNK EXTRACTION ---------------------------------------

    #[test]
    fn base_1e9_chunk_matches_a_u128_oracle_and_always_fits_i64() {
        let mut s: u64 = 13;
        for _ in 0..20000 {
            let v = lcg(&mut s);
            let want = ((v as u128) % 1_000_000_000u128) as u32;
            assert_eq!(base_1e9_chunk(v), want, "v={v}");
            // The whole point: no fallible conversion survives.
            let _: i64 = i64::from(base_1e9_chunk(v));
        }
        assert_eq!(base_1e9_chunk(0), 0);
        assert_eq!(base_1e9_chunk(999_999_999), 999_999_999);
        assert_eq!(base_1e9_chunk(1_000_000_000), 0);
        assert_eq!(base_1e9_chunk(u64::MAX), (u64::MAX % 1_000_000_000) as u32);
    }

    #[test]
    fn low16_matches_a_truncating_cast() {
        let mut s: u64 = 17;
        for _ in 0..20000 {
            let v = lcg(&mut s) as u32;
            assert_eq!(low16(v), v as u16, "v={v:#010x}");
        }
    }

    // -- ROLLING HASH -----------------------------------------------------

    #[test]
    fn rolling_hash_step_matches_a_u128_oracle_and_stays_in_range() {
        let mut s: u64 = 19;
        for _ in 0..20000 {
            let h = lcg(&mut s) as u32;
            let b = (lcg(&mut s) & 0xff) as u8;
            let want = (((h as u128) * 31 + b as u128) % 65521) as u32;
            assert_eq!(rolling_hash_step(h, b), want, "h={h} b={b}");
            assert!(rolling_hash_step(h, b) <= 65520);
        }
        for h in [0u32, 1, 65520, 65521, u32::MAX] {
            for b in 0u16..=255 {
                let want = (((h as u128) * 31 + b as u128) % 65521) as u32;
                assert_eq!(rolling_hash_step(h, b as u8), want, "h={h} b={b}");
            }
        }
    }

    // -- FLETCHER-16 ------------------------------------------------------

    #[test]
    fn the_fletcher_oracle_reproduces_the_published_abcde_vector() {
        // The standard Fletcher-16 test vector: "abcde" -> 0xC8F0.
        // This validates the ORACLE, so the sweeps below are evidence.
        assert_eq!(oracle_fletcher(0, 0, b"abcde"), 0xC8F0);
    }

    #[test]
    fn fletcher16_4_matches_the_loop_oracle_over_a_byte_sweep() {
        let mut s: u64 = 23;
        for _ in 0..20000 {
            let r = lcg(&mut s);
            let a = (r & 0xff) as u8;
            let b = ((r >> 8) & 0xff) as u8;
            let d = [
                ((r >> 16) & 0xff) as u8,
                ((r >> 24) & 0xff) as u8,
                ((r >> 32) & 0xff) as u8,
                ((r >> 40) & 0xff) as u8,
            ];
            assert_eq!(
                fletcher16_4(a, b, d[0], d[1], d[2], d[3]),
                oracle_fletcher(a, b, &d),
                "a={a} b={b} d={d:?}"
            );
        }
    }

    #[test]
    fn fletcher16_4_agrees_per_byte_position() {
        // One byte varied at a time against a fixed background, so a
        // coefficient that moved between positions cannot hide in an average.
        for pos in 0..4usize {
            for v in 0u16..=255 {
                let mut d = [0x5Au8; 4];
                d[pos] = v as u8;
                assert_eq!(
                    fletcher16_4(3, 200, d[0], d[1], d[2], d[3]),
                    oracle_fletcher(3, 200, &d),
                    "pos={pos} v={v}"
                );
            }
        }
    }

    #[test]
    fn fletcher16_4_chains_across_two_blocks() {
        let data: [u8; 8] = [1, 2, 3, 250, 255, 0, 128, 77];
        let first = fletcher16_4(0, 0, data[0], data[1], data[2], data[3]);
        let a1 = (first & 0xff) as u8;
        let b1 = (first >> 8) as u8;
        let second = fletcher16_4(a1, b1, data[4], data[5], data[6], data[7]);
        assert_eq!(second, oracle_fletcher(0, 0, &data));
    }

    // -- ADLER-32 ---------------------------------------------------------

    #[test]
    fn adler32_4_reproduces_the_published_abcd_vector() {
        // RFC 1950 initial state is (1, 0). Adler-32("abcd") = 0x03D8018B.
        assert_eq!(adler32_4(1, 0, b'a', b'b', b'c', b'd'), 0x03D8_018B);
    }

    #[test]
    fn adler32_4_matches_the_loop_oracle_over_a_byte_sweep() {
        let mut s: u64 = 29;
        for _ in 0..20000 {
            let r = lcg(&mut s);
            let a = (r & 0xffff_ffff) as u32;
            let b = lcg(&mut s) as u32;
            let d = [
                (r & 0xff) as u8,
                ((r >> 8) & 0xff) as u8,
                ((r >> 16) & 0xff) as u8,
                ((r >> 24) & 0xff) as u8,
            ];
            assert_eq!(
                adler32_4(a, b, d[0], d[1], d[2], d[3]),
                oracle_adler(a, b, &d),
                "a={a} b={b} d={d:?}"
            );
        }
    }

    #[test]
    fn adler32_4_agrees_per_byte_position() {
        for pos in 0..4usize {
            for v in 0u16..=255 {
                let mut d = [0xA5u8; 4];
                d[pos] = v as u8;
                assert_eq!(
                    adler32_4(1, 0, d[0], d[1], d[2], d[3]),
                    oracle_adler(1, 0, &d),
                    "pos={pos} v={v}"
                );
            }
        }
    }

    // -- INTERNET CHECKSUM ------------------------------------------------

    #[test]
    fn internet_checksum_reproduces_the_rfc1071_ip_header_example() {
        // The standard 20-byte IPv4 header worked example; its checksum is
        // 0xB861. Ten words, so the last two ride a second sum.
        let s = internet_sum8(0x4500, 0x0073, 0x0000, 0x4000, 0x4011, 0x0000, 0xc0a8, 0x0001)
            + internet_sum4(0xc0a8, 0x00c7, 0, 0);
        assert_eq!(!ones_complement_fold(s), 0xB861);
    }

    #[test]
    fn internet_checksum4_and_8_match_an_rfc1071_loop_oracle() {
        let mut s: u64 = 31;
        for _ in 0..20000 {
            let r = lcg(&mut s);
            let q = lcg(&mut s);
            let w: [u16; 8] = [
                r as u16,
                (r >> 16) as u16,
                (r >> 32) as u16,
                (r >> 48) as u16,
                q as u16,
                (q >> 16) as u16,
                (q >> 32) as u16,
                (q >> 48) as u16,
            ];
            assert_eq!(internet_checksum4(w[0], w[1], w[2], w[3]), oracle_inet(&w[..4]), "{w:?}");
            assert_eq!(
                internet_checksum8(w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]),
                oracle_inet(&w),
                "{w:?}"
            );
        }
        // The extremes: all zero and all ones.
        assert_eq!(internet_checksum4(0, 0, 0, 0), oracle_inet(&[0, 0, 0, 0]));
        assert_eq!(
            internet_checksum4(0xffff, 0xffff, 0xffff, 0xffff),
            oracle_inet(&[0xffff, 0xffff, 0xffff, 0xffff])
        );
    }

    #[test]
    fn ones_complement_fold_matches_a_while_loop_oracle() {
        let mut s: u64 = 37;
        for _ in 0..20000 {
            let v = lcg(&mut s) as u32;
            assert_eq!(ones_complement_fold(v), oracle_fold(v), "v={v:#010x}");
        }
        for v in [0u32, 0xffff, 0x1_0000, 0xffff_ffff, 0xffff_0000, 0x1_ffff] {
            assert_eq!(ones_complement_fold(v), oracle_fold(v), "v={v:#010x}");
        }
    }

    #[test]
    fn internet_sum8_matches_a_u64_oracle() {
        let mut s: u64 = 41;
        for _ in 0..20000 {
            let r = lcg(&mut s);
            let q = lcg(&mut s);
            let w: [u16; 8] = [
                r as u16,
                (r >> 16) as u16,
                (r >> 32) as u16,
                (r >> 48) as u16,
                q as u16,
                (q >> 16) as u16,
                (q >> 32) as u16,
                (q >> 48) as u16,
            ];
            let want: u64 = w.iter().map(|&x| x as u64).sum();
            assert_eq!(
                internet_sum8(w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]) as u64,
                want
            );
            assert_eq!(internet_sum4(w[0], w[1], w[2], w[3]) as u64, w[..4].iter().map(|&x| x as u64).sum::<u64>());
        }
    }

    // -- THE TIER-1 CONTRACTS ---------------------------------------------

    #[test]
    fn crc_width_bytes_matches_the_standard_widths() {
        assert_eq!(crc_width_bytes(8), 1);
        assert_eq!(crc_width_bytes(16), 2);
        assert_eq!(crc_width_bytes(24), 3);
        assert_eq!(crc_width_bytes(32), 4);
        assert_eq!(crc_width_bytes(64), 8);
        // Everything else is the sentinel, and the sentinel is not a size.
        for w in 0u16..=255 {
            let w = w as u8;
            if !matches!(w, 8 | 16 | 24 | 32 | 64) {
                assert_eq!(crc_width_bytes(w), 0, "w={w}");
            }
        }
    }

    #[test]
    fn checksum_bytes_clamped_is_the_min_of_the_width_and_the_cap() {
        for w in 0u16..=255 {
            for c in 0u16..=255 {
                let got = checksum_bytes_clamped(w as u8, c as u8);
                assert_eq!(got, crc_width_bytes(w as u8).min(c as u8), "w={w} c={c}");
            }
        }
    }

    #[test]
    fn no_tier1_result_ever_exceeds_its_bound() {
        // Exhaustive over every tier-1 domain that is finite, and a sweep over
        // the two that are not. This is the assertion that must survive a
        // wrong-VALUE mutation: it pins the CONTRACTS, not the answers.
        for w in 0u16..=255 {
            assert!(crc_width_bytes(w as u8) <= 8, "w={w}");
            for c in 0u16..=255 {
                assert!(checksum_bytes_clamped(w as u8, c as u8) <= c as u8, "w={w} c={c}");
            }
        }
        for a in 0u16..=255 {
            for b in 0u16..=255 {
                assert!(fletcher_state_ok(a as u8, b as u8) <= 1);
            }
        }
        let mut s: u64 = 43;
        for _ in 0..20000 {
            let x = lcg(&mut s);
            let y = lcg(&mut s);
            assert!(message_len_ok(x) <= 1);
            assert!(adler_state_ok(x as u32, y as u32) <= 1);
            assert!(checksum_agrees(x as u32, y as u32) <= 1);
            assert!(checksum_agrees(x as u32, x as u32) <= 1);
        }
    }

    #[test]
    fn state_predicates_accept_exactly_the_residue_windows() {
        for a in 0u16..=255 {
            for b in 0u16..=255 {
                let want = (a <= 254 && b <= 254) as u8;
                assert_eq!(fletcher_state_ok(a as u8, b as u8), want, "a={a} b={b}");
            }
        }
        for a in [0u32, 1, 65519, 65520, 65521, u32::MAX] {
            for b in [0u32, 1, 65519, 65520, 65521, u32::MAX] {
                let want = (a <= 65520 && b <= 65520) as u8;
                assert_eq!(adler_state_ok(a, b), want, "a={a} b={b}");
            }
        }
    }

    #[test]
    fn checksum_agrees_is_exactly_equality() {
        let mut s: u64 = 47;
        for _ in 0..20000 {
            let x = lcg(&mut s) as u32;
            let y = lcg(&mut s) as u32;
            assert_eq!(checksum_agrees(x, y), (x == y) as u8);
            assert_eq!(checksum_agrees(x, x), 1);
        }
    }
}
