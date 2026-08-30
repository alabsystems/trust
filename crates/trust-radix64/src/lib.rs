//! Total, verified base64 / base32 / radix-64 codec arithmetic for `no_std`
//! Trust components.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0
//!
//! # Why this crate exists, and who calls it
//!
//! A radix-64 codec is arithmetic: a 3-byte quantum is repacked into four
//! 6-bit groups, a byte count is turned into a symbol count, and an alphabet
//! index is turned into an ASCII byte. In this tree every one of those three
//! is currently discharged by something that is not a proof.
//!
//! **`first-party/ty/crates/tla-base64/src/encode.rs:89-91`** — the encoded
//! length, computed and then asserted:
//!
//! ```text
//! let encoded_bytes = b64_bytes_written
//!     .checked_add(padding_bytes)
//!     .expect("usize overflow when calculating b64 length");
//! ```
//!
//! and **`encode.rs:101-128`**, the function behind it, which is `Option`-typed
//! for exactly the same reason — `complete_input_chunks.checked_mul(4)` and
//! `complete_chunk_output.checked_add(4)`, with the doc comment conceding
//! *"Returns `None` if the encoded length can't be represented in `usize`.
//! This will happen for input lengths in approximately the top quarter of the
//! range of `usize`."*
//!
//! [`b64_encoded_len`] is that computation given a signature under which the
//! overflow **cannot happen**: it takes the QUANTUM COUNT as a `u32` and
//! returns `u64`, so `q * 4 + 4` peaks at `2^34 + 4` and the fallible
//! conversion is **deleted rather than proved** — no `Option`, no `checked_*`,
//! no `.expect`. Nothing downstream has to handle a `None` that the type
//! system now makes unreachable.
//!
//! **`encode.rs:118-123`** — a remainder fact carried by a comment:
//!
//! ```text
//! let encoded_rem = match rem {
//!     1 => 2,
//!     // only other possible remainder is 2
//!     // can't use a separate _ => unreachable!() in const fns in ancient rust versions
//!     _ => 3,
//! };
//! ```
//!
//! The claim is that `bytes_len % 3 ∈ {0, 1, 2}`, and the `_` arm silently
//! answers `3` for every other value. [`b64_tail_symbols`] and
//! [`b64_padding_count`] are the same table written so that the arm which
//! cannot be reached does not have to be *believed*: both are total on all of
//! `u32`, both carry a checked `ensures`, and neither has a catch-all standing
//! in for an unproved range.
//!
//! **`first-party/ty/crates/tla-base64/src/display.rs:55`** and
//! **`alphabet.rs:133`** — the alphabet's ASCII-ness, asserted twice:
//!
//! ```text
//! .write_str(str::from_utf8(encoded).expect("base64 data was not utf8"))
//! core::str::from_utf8(&self.symbols).unwrap()
//! ```
//!
//! Both rest on "every symbol this encoder emits is ASCII", which is a fact
//! about the index-to-byte map. [`b64_symbol`] states it as a checked
//! proposition (`ensures result <= 123`) instead of as a panic site.
//!
//! **`tools/ts2rust/orca/b3_b64bytes.rs:37-44`** is the same domain reached
//! from the other side, and is the most useful precedent here: a faithful port
//! of Node's `base64ByteLength` could not verify `(bytes * 3) >>> 2` and was
//! **rewritten** into `bytes - ceil(bytes/4)` because the product *"drove the
//! verifier's SMT counterexample path"*. The identity is exact and the note is
//! careful, but the reformulation is a workaround recorded in a comment in one
//! file. [`b64_decoded_len`] does the same job with the multiply intact, at a
//! width where it is proved rather than avoided.
//!
//! **`crates/trust-vcgen/src/generate/overflow_vc.rs:610-611`** shows what the
//! verifier itself believes about this arithmetic — the routing comment names
//! *"the base64 `(full_chunks + 1) * 4` (full_chunks = len / 3, len <=
//! isize::MAX)"* as the motivating example of a **precondition-bounded**
//! product. This crate needs no such precondition: the bound is in the
//! signature.
//!
//! **`crates/trust-proof-cert/src/proof_bundle.rs:1123`** is a smaller finding
//! worth recording because it is invisible to every test: the serde module is
//! named `optional_bytes_as_base64` and its own comment says *"Encode bytes as
//! hex string for JSON compatibility without adding a base64 dependency"*. It
//! is a hex codec under a base64 name. Nothing here fixes that; it is cited so
//! that a reader searching this tree for base64 does not mistake it for one.
//!
//! # What is actually proved
//!
//! **Tier 1 — proved bound.** A grammar `ensures` clause the compiler
//! discharges: [`b64_symbol`], [`b64_value`], [`b32_symbol`], [`b32_value`],
//! [`b64_padding_count`], [`b64_tail_symbols`], [`b32_padding_count`],
//! [`b32_tail_symbols`], [`output_fits`].
//!
//! **Tier 2 — proved total.** Panic-freedom, with no contract: every packing,
//! slicing and sizing function. `/` and `%` are composition-opaque (they
//! cannot be bundled into any caller, contracted or not), so a function that
//! needs one is tier 2 by construction and its callers inline rather than
//! call it.
//!
//! **Neither tier says the answer is right.** A truncating cast is neither an
//! overflow nor a zero divisor, and no obligation in this crate can see which
//! byte got which coefficient. That is what the unit tests are for, and they
//! check against the RFC 4648 §10 published vectors and against oracles
//! written with shifts and a literal alphabet table — a different method from
//! the crate's multiplies and guard chains.
//!
//! # The shape this crate is written in, and why
//!
//! Measured 2026-08-29 (recorded in `docs/STRICT_VERIFICATION_FRAGMENT.md`
//! §8): the natural per-symbol spelling of 6-bit packing does **not** verify.
//! `(b0 % 4) * 16 + (b1 / 16)` at `u8` proves its `Mul` and leaves its `Add`
//! runtime-checked, for every one of the nine group shapes a base64/base32
//! codec needs. The repair is not a guard; it is to stop working a symbol at a
//! time. Both codecs here **accumulate the whole quantum first** — 24 bits for
//! base64, 40 for base32 — out of widening casts, which is the one arithmetic
//! shape the interval engine reads without help, and then slice it with `/`
//! and `%` by literals, which mint zero-divisor rows and no overflow at all.
//! This is also how every reference codec is written, so the fragment and the
//! idiom agree.
#![no_std]

// ---------------------------------------------------------------------------
// Contract carriers
// ---------------------------------------------------------------------------
//
// These exist so the tier-1 functions below have a contract-carrying callee to
// inherit from. A wrapper over an UNcontracted clamp measures UNKNOWN, which is
// why a private helper nobody outside this file calls still has an `ensures`.

fn clamp_u32(v: u32, hi: u32) -> u32 ensures result <= hi {
    if v > hi { hi } else { v }
}

fn clamp_u64(v: u64, hi: u64) -> u64 ensures result <= hi {
    if v > hi { hi } else { v }
}

// ---------------------------------------------------------------------------
// 1. base64 — the 3-byte / 4-symbol quantum, as a 24-bit group
// ---------------------------------------------------------------------------

/// Pack a full 3-byte quantum into its 24-bit radix-64 group.
///
/// **Tier 2.** Peak `255*65536 + 255*256 + 255 == 16777215`, so the group is
/// exactly the 24 bits the quantum holds. Every operand is a widening cast,
/// which is what makes the two `Mul`s and the two `Add`s provable without a
/// single guard.
pub fn b64_group(b0: u8, b1: u8, b2: u8) -> u32 {
    (b0 as u32) * 65536 + (b1 as u32) * 256 + (b2 as u32)
}

/// Pack a 1-byte tail quantum (the `xx==` case) into its 24-bit group.
///
/// **Tier 2.**
pub fn b64_group1(b0: u8) -> u32 { (b0 as u32) * 65536 }

/// Pack a 2-byte tail quantum (the `xxx=` case) into its 24-bit group.
///
/// **Tier 2.**
pub fn b64_group2(b0: u8, b1: u8) -> u32 { (b0 as u32) * 65536 + (b1 as u32) * 256 }

/// The first 6-bit group of a 24-bit quantum (`g >> 18`, masked to 6 bits).
///
/// **Tier 2.** Spelled `/` and `%` rather than `>>` and `&` deliberately: a
/// constant mask contributes no range to the interval engine, a literal
/// divisor does, and the two spellings compute the same value.
pub fn b64_sym0(g: u32) -> u32 { (g / 262144) % 64 }

/// The second 6-bit group of a 24-bit quantum.
///
/// **Tier 2.**
pub fn b64_sym1(g: u32) -> u32 { (g / 4096) % 64 }

/// The third 6-bit group of a 24-bit quantum.
///
/// **Tier 2.**
pub fn b64_sym2(g: u32) -> u32 { (g / 64) % 64 }

/// The fourth 6-bit group of a 24-bit quantum.
///
/// **Tier 2.**
pub fn b64_sym3(g: u32) -> u32 { g % 64 }

/// Repack four 6-bit values into the 24-bit group they encode.
///
/// **Tier 2.** Total: a value outside `0..=63` is reduced modulo 64 rather
/// than rejected, so there is no failing path to explain. The interval engine
/// reads each widened operand as `[0, 255]` — the mask the `% 64` applies is
/// invisible to it — so the peak it proves against is `255 * 266305 ==
/// 67907775`, comfortably inside `u32`. The true peak is `16777215`.
pub fn b64_regroup(v0: u8, v1: u8, v2: u8, v3: u8) -> u32 {
    ((v0 % 64) as u32) * 262144
        + ((v1 % 64) as u32) * 4096
        + ((v2 % 64) as u32) * 64
        + ((v3 % 64) as u32)
}

/// The first byte of a 24-bit quantum.
///
/// **Tier 2.**
pub fn b64_byte0(g: u32) -> u32 { (g / 65536) % 256 }

/// The second byte of a 24-bit quantum.
///
/// **Tier 2.**
pub fn b64_byte1(g: u32) -> u32 { (g / 256) % 256 }

/// The third byte of a 24-bit quantum.
///
/// **Tier 2.**
pub fn b64_byte2(g: u32) -> u32 { g % 256 }

// ---------------------------------------------------------------------------
// 2. base64 — alphabet index <-> ASCII byte (RFC 4648 §4)
// ---------------------------------------------------------------------------

/// The RFC 4648 §4 encode table, arithmetically. `255` marks "no such index".
///
/// Uncontracted: the subtraction and the additions cannot appear in a body
/// that carries an `ensures`, so the bound is stated on [`b64_symbol`].
fn raw_b64_symbol(i: u8) -> u32 {
    let x: u32 = i as u32;
    if x < 26 { return x + 65; }
    if x < 52 { return x + 71; }
    if x < 62 { return x - 4; }
    if x == 62 { return 43; }
    if x == 63 { return 47; }
    255
}

/// Alphabet index -> ASCII symbol, RFC 4648 §4 (`+/`).
///
/// **Tier 1.** `ensures result <= 123` is checked. The top of the value space
/// is `b'z' == 122`, so `123` is the sentinel one past it and an index outside
/// `0..=63` returns exactly that. The clamp is LIVE: `raw_b64_symbol` answers
/// `255` on those indices and the clamp is what brings it inside the bound.
///
/// This is `tla-base64`'s `str::from_utf8(..).expect("base64 data was not
/// utf8")` (`display.rs:55`) as a proved proposition rather than a panic site.
pub fn b64_symbol(i: u8) -> u32 ensures result <= 123 {
    clamp_u32(raw_b64_symbol(i), 123)
}

/// The RFC 4648 §4 decode table, arithmetically. `255` marks "not a symbol".
///
/// Uncontracted, for the same reason as [`raw_b64_symbol`].
fn raw_b64_value(c: u8) -> u32 {
    let x: u32 = c as u32;
    if x < 43 { return 255; }
    if x == 43 { return 62; }
    if x < 47 { return 255; }
    if x == 47 { return 63; }
    if x < 48 { return 255; }
    if x < 58 { return x + 4; }
    if x < 65 { return 255; }
    if x < 91 { return x - 65; }
    if x < 97 { return 255; }
    if x < 123 { return x - 71; }
    255
}

/// ASCII symbol -> alphabet index, RFC 4648 §4. Returns `64` for any byte that
/// is not a base64 symbol, including `b'='`.
///
/// **Tier 1.** `ensures result <= 64` is checked — `64` is the sentinel one
/// past the top of the 6-bit value space, so it is inside the bound and every
/// caller's downstream table index is bounded without a separate test. The
/// clamp is LIVE: `raw_b64_value` answers `255` for a non-symbol.
pub fn b64_value(c: u8) -> u32 ensures result <= 64 {
    clamp_u32(raw_b64_value(c), 64)
}

// ---------------------------------------------------------------------------
// 3. base32 — the 5-byte / 8-symbol quantum, as a 40-bit group
// ---------------------------------------------------------------------------

/// Pack a full 5-byte quantum into its 40-bit radix-32 group.
///
/// **Tier 2.** Peak `255 * 4311810305 == 1099511627775 == 2^40 - 1`.
pub fn b32_group(b0: u8, b1: u8, b2: u8, b3: u8, b4: u8) -> u64 {
    (b0 as u64) * 4294967296
        + (b1 as u64) * 16777216
        + (b2 as u64) * 65536
        + (b3 as u64) * 256
        + (b4 as u64)
}

/// The first 5-bit group of a 40-bit quantum.
///
/// **Tier 2.**
pub fn b32_sym0(g: u64) -> u64 { (g / 34359738368) % 32 }

/// The second 5-bit group of a 40-bit quantum.
///
/// **Tier 2.**
pub fn b32_sym1(g: u64) -> u64 { (g / 1073741824) % 32 }

/// The third 5-bit group of a 40-bit quantum.
///
/// **Tier 2.**
pub fn b32_sym2(g: u64) -> u64 { (g / 33554432) % 32 }

/// The fourth 5-bit group of a 40-bit quantum.
///
/// **Tier 2.**
pub fn b32_sym3(g: u64) -> u64 { (g / 1048576) % 32 }

/// The fifth 5-bit group of a 40-bit quantum.
///
/// **Tier 2.**
pub fn b32_sym4(g: u64) -> u64 { (g / 32768) % 32 }

/// The sixth 5-bit group of a 40-bit quantum.
///
/// **Tier 2.**
pub fn b32_sym5(g: u64) -> u64 { (g / 1024) % 32 }

/// The seventh 5-bit group of a 40-bit quantum.
///
/// **Tier 2.**
pub fn b32_sym6(g: u64) -> u64 { (g / 32) % 32 }

/// The eighth 5-bit group of a 40-bit quantum.
///
/// **Tier 2.**
pub fn b32_sym7(g: u64) -> u64 { g % 32 }

/// Repack eight 5-bit values into the 40-bit group they encode.
///
/// **Tier 2.** Total, on the same discipline as [`b64_regroup`]: the engine
/// reads each widened operand as `[0, 255]`, so the peak it proves is
/// `255 * 35468117025 == 9044369841375`, well inside `u64`. The true peak is
/// `2^40 - 1`.
pub fn b32_regroup(v0: u8, v1: u8, v2: u8, v3: u8, v4: u8, v5: u8, v6: u8, v7: u8) -> u64 {
    ((v0 % 32) as u64) * 34359738368
        + ((v1 % 32) as u64) * 1073741824
        + ((v2 % 32) as u64) * 33554432
        + ((v3 % 32) as u64) * 1048576
        + ((v4 % 32) as u64) * 32768
        + ((v5 % 32) as u64) * 1024
        + ((v6 % 32) as u64) * 32
        + ((v7 % 32) as u64)
}

/// The first byte of a 40-bit quantum.
///
/// **Tier 2.**
pub fn b32_byte0(g: u64) -> u64 { (g / 4294967296) % 256 }

/// The second byte of a 40-bit quantum.
///
/// **Tier 2.**
pub fn b32_byte1(g: u64) -> u64 { (g / 16777216) % 256 }

/// The third byte of a 40-bit quantum.
///
/// **Tier 2.**
pub fn b32_byte2(g: u64) -> u64 { (g / 65536) % 256 }

/// The fourth byte of a 40-bit quantum.
///
/// **Tier 2.**
pub fn b32_byte3(g: u64) -> u64 { (g / 256) % 256 }

/// The fifth byte of a 40-bit quantum.
///
/// **Tier 2.**
pub fn b32_byte4(g: u64) -> u64 { g % 256 }

// ---------------------------------------------------------------------------
// 4. base32 — alphabet index <-> ASCII byte (RFC 4648 §6)
// ---------------------------------------------------------------------------

/// The RFC 4648 §6 encode table, arithmetically. `255` marks "no such index".
fn raw_b32_symbol(i: u8) -> u32 {
    let x: u32 = i as u32;
    if x < 26 { return x + 65; }
    if x < 32 { return x + 24; }
    255
}

/// Alphabet index -> ASCII symbol, RFC 4648 §6 (`A-Z2-7`).
///
/// **Tier 1.** `ensures result <= 91` is checked; `b'Z' == 90` tops the value
/// space and `91` is the sentinel one past it. The clamp is LIVE.
pub fn b32_symbol(i: u8) -> u32 ensures result <= 91 {
    clamp_u32(raw_b32_symbol(i), 91)
}

/// The RFC 4648 §6 decode table, arithmetically. `255` marks "not a symbol".
fn raw_b32_value(c: u8) -> u32 {
    let x: u32 = c as u32;
    if x < 50 { return 255; }
    if x < 56 { return x - 24; }
    if x < 65 { return 255; }
    if x < 91 { return x - 65; }
    255
}

/// ASCII symbol -> alphabet index, RFC 4648 §6. Returns `32` for any byte that
/// is not a base32 symbol, including `b'='`.
///
/// **Tier 1.** `ensures result <= 32` is checked; `32` is the sentinel one
/// past the top of the 5-bit value space. The clamp is LIVE.
pub fn b32_value(c: u8) -> u32 ensures result <= 32 {
    clamp_u32(raw_b32_value(c), 32)
}

// ---------------------------------------------------------------------------
// 5. Quantum sizing and padding
// ---------------------------------------------------------------------------

/// How many complete 3-byte quanta are in `n` bytes.
///
/// **Tier 2.** Split out from [`b64_encoded_len`] because `/` cannot be
/// bundled into any caller; a caller that needs both inlines this one.
pub fn b64_full_quanta(n: u32) -> u32 { n / 3 }

/// How many bytes are left over after the complete 3-byte quanta of `n`.
///
/// **Tier 2.**
pub fn b64_tail_bytes(n: u32) -> u32 { n % 3 }

/// The padded base64 encoded length of `full_quanta` complete quanta plus
/// `tail` leftover bytes.
///
/// **Tier 2, and this is the signature that deletes an `.expect`.**
/// `tla-base64`'s `encoded_len` returns `Option<usize>` and its caller says
/// `.expect("usize overflow when calculating b64 length")` (`encode.rs:91`)
/// because `chunks * 4` can overflow a `usize`. Here the quantum count is a
/// `u32` and the result is a `u64`, so the peak is `4294967295 * 4 + 4 ==
/// 17179869184` and the overflow is impossible by signature. There is no
/// `None` to propagate and no assertion to discharge.
pub fn b64_encoded_len(full_quanta: u32, tail: u32) -> u64 {
    let base: u64 = (full_quanta as u64) * 4;
    if tail == 0 { return base; }
    base + 4
}

/// The decoded byte length of `quads` complete 4-symbol quanta carrying `pad`
/// padding characters.
///
/// **Tier 2.** The multiply is kept rather than avoided: `tools/ts2rust/orca/
/// b3_b64bytes.rs:37-44` had to rewrite `(bytes * 3) >>> 2` into
/// `bytes - ceil(bytes/4)` to get past the verifier. At `u32 -> u64` the
/// product peaks at `12884901885` and proves directly. The `t < p` guard is
/// mathematically dead for any `pad <= 2` but is what gives the subtraction
/// its range; a dead guard is fine, a dead clamp under an `ensures` is not.
pub fn b64_decoded_len(quads: u32, pad: u32) -> u64 {
    let t: u64 = (quads as u64) * 3;
    let p: u64 = pad as u64;
    if t < p { return 0; }
    t - p
}

/// How many `=` characters pad a base64 quantum with `tail` leftover bytes.
///
/// **Tier 1.** `ensures result <= 2` is checked. Total on all of `u32`: this
/// is `tla-base64`'s `match rem { 1 => 2, _ => 3 }` (`encode.rs:118-123`)
/// written so that no arm has to carry the unproved claim that `rem <= 2`.
pub fn b64_padding_count(tail: u32) -> u32 ensures result <= 2 {
    if tail == 1 { return 2; }
    if tail == 2 { return 1; }
    0
}

/// How many real symbols a base64 quantum with `tail` leftover bytes emits
/// before its padding.
///
/// **Tier 1.** `ensures result <= 3` is checked.
pub fn b64_tail_symbols(tail: u32) -> u32 ensures result <= 3 {
    if tail == 1 { return 2; }
    if tail == 2 { return 3; }
    0
}

/// How many complete 5-byte quanta are in `n` bytes.
///
/// **Tier 2.**
pub fn b32_full_quanta(n: u32) -> u32 { n / 5 }

/// How many bytes are left over after the complete 5-byte quanta of `n`.
///
/// **Tier 2.**
pub fn b32_tail_bytes(n: u32) -> u32 { n % 5 }

/// The padded base32 encoded length of `full_quanta` complete quanta plus
/// `tail` leftover bytes.
///
/// **Tier 2.** Peak `4294967295 * 8 + 8 == 34359738368`.
pub fn b32_encoded_len(full_quanta: u32, tail: u32) -> u64 {
    let base: u64 = (full_quanta as u64) * 8;
    if tail == 0 { return base; }
    base + 8
}

/// How many `=` characters pad a base32 quantum with `tail` leftover bytes.
///
/// **Tier 1.** `ensures result <= 6` is checked. Total on all of `u32`.
pub fn b32_padding_count(tail: u32) -> u32 ensures result <= 6 {
    if tail == 1 { return 6; }
    if tail == 2 { return 4; }
    if tail == 3 { return 3; }
    if tail == 4 { return 1; }
    0
}

/// How many real symbols a base32 quantum with `tail` leftover bytes emits
/// before its padding.
///
/// **Tier 1.** `ensures result <= 7` is checked.
pub fn b32_tail_symbols(tail: u32) -> u32 ensures result <= 7 {
    if tail == 1 { return 2; }
    if tail == 2 { return 4; }
    if tail == 3 { return 5; }
    if tail == 4 { return 7; }
    0
}

/// The number of output bytes a codec may actually write: `needed`, capped at
/// the caller's buffer capacity `cap`.
///
/// **Tier 1.** `ensures result <= cap` is checked, and the clamp is LIVE — it
/// is the whole point of the function. `tla-base64` spells this failure as
/// `EncodeSliceError::OutputSliceTooSmall`; stating it as a bound means a
/// caller that writes `output_fits(..)` bytes cannot overrun, as a proposition
/// rather than as a returned error somebody has to check.
pub fn output_fits(needed: u64, cap: u64) -> u64 ensures result <= cap {
    clamp_u64(needed, cap)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------
//
// The proofs cover overflow, division and the tier-1 bounds. They cover NOTHING
// about which byte got which coefficient — a truncating cast is not an
// overflow, and swapping two coefficients keeps every peak where it was. So
// every test below is checked against something written by a DIFFERENT METHOD:
// the RFC 4648 §10 published vectors, and oracles that use `<<`/`>>` and a
// literal alphabet table where the crate multiplies and computes.

#[cfg(test)]
mod tests {
    use super::*;

    /// The RFC 4648 §4 alphabet, as a literal table. This is the independent
    /// oracle for both alphabet directions: the crate computes the same map
    /// with additions and subtractions.
    const B64: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    /// The RFC 4648 §6 alphabet, as a literal table.
    const B32: &[u8; 32] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZ234567";

    /// Base64-encode with shifts and a table lookup — a different method from
    /// the crate's group multiply and arithmetic alphabet. Writes into `out`
    /// and returns the length.
    fn oracle_b64(input: &[u8], out: &mut [u8; 32]) -> usize {
        let mut n = 0usize;
        let mut i = 0usize;
        while i + 3 <= input.len() {
            let g = ((input[i] as u32) << 16) | ((input[i + 1] as u32) << 8) | (input[i + 2] as u32);
            out[n] = B64[((g >> 18) & 63) as usize];
            out[n + 1] = B64[((g >> 12) & 63) as usize];
            out[n + 2] = B64[((g >> 6) & 63) as usize];
            out[n + 3] = B64[(g & 63) as usize];
            n += 4;
            i += 3;
        }
        let rem = input.len() - i;
        if rem == 1 {
            let g = (input[i] as u32) << 16;
            out[n] = B64[((g >> 18) & 63) as usize];
            out[n + 1] = B64[((g >> 12) & 63) as usize];
            out[n + 2] = b'=';
            out[n + 3] = b'=';
            n += 4;
        } else if rem == 2 {
            let g = ((input[i] as u32) << 16) | ((input[i + 1] as u32) << 8);
            out[n] = B64[((g >> 18) & 63) as usize];
            out[n + 1] = B64[((g >> 12) & 63) as usize];
            out[n + 2] = B64[((g >> 6) & 63) as usize];
            out[n + 3] = b'=';
            n += 4;
        }
        n
    }

    /// Base64-encode using ONLY this crate's functions.
    fn crate_b64(input: &[u8], out: &mut [u8; 32]) -> usize {
        let mut n = 0usize;
        let mut i = 0usize;
        while i + 3 <= input.len() {
            let g = b64_group(input[i], input[i + 1], input[i + 2]);
            out[n] = b64_symbol(b64_sym0(g) as u8) as u8;
            out[n + 1] = b64_symbol(b64_sym1(g) as u8) as u8;
            out[n + 2] = b64_symbol(b64_sym2(g) as u8) as u8;
            out[n + 3] = b64_symbol(b64_sym3(g) as u8) as u8;
            n += 4;
            i += 3;
        }
        let tail = (input.len() - i) as u32;
        if tail != 0 {
            let g = if tail == 1 {
                b64_group1(input[i])
            } else {
                b64_group2(input[i], input[i + 1])
            };
            let syms = b64_tail_symbols(tail);
            let pad = b64_padding_count(tail);
            let s = [b64_sym0(g), b64_sym1(g), b64_sym2(g)];
            let mut k = 0u32;
            while k < syms {
                out[n] = b64_symbol(s[k as usize] as u8) as u8;
                n += 1;
                k += 1;
            }
            let mut p = 0u32;
            while p < pad {
                out[n] = b'=';
                n += 1;
                p += 1;
            }
        }
        n
    }

    /// Base32-encode using ONLY this crate's functions.
    fn crate_b32(input: &[u8], out: &mut [u8; 32]) -> usize {
        let mut n = 0usize;
        let mut i = 0usize;
        while i + 5 <= input.len() {
            let g = b32_group(input[i], input[i + 1], input[i + 2], input[i + 3], input[i + 4]);
            let s = [
                b32_sym0(g), b32_sym1(g), b32_sym2(g), b32_sym3(g),
                b32_sym4(g), b32_sym5(g), b32_sym6(g), b32_sym7(g),
            ];
            let mut k = 0usize;
            while k < 8 {
                out[n] = b32_symbol(s[k] as u8) as u8;
                n += 1;
                k += 1;
            }
            i += 5;
        }
        let tail = (input.len() - i) as u32;
        if tail != 0 {
            let mut q = [0u8; 5];
            let mut k = 0usize;
            while k < tail as usize {
                q[k] = input[i + k];
                k += 1;
            }
            let g = b32_group(q[0], q[1], q[2], q[3], q[4]);
            let s = [
                b32_sym0(g), b32_sym1(g), b32_sym2(g), b32_sym3(g),
                b32_sym4(g), b32_sym5(g), b32_sym6(g), b32_sym7(g),
            ];
            let syms = b32_tail_symbols(tail);
            let pad = b32_padding_count(tail);
            let mut j = 0u32;
            while j < syms {
                out[n] = b32_symbol(s[j as usize] as u8) as u8;
                n += 1;
                j += 1;
            }
            let mut p = 0u32;
            while p < pad {
                out[n] = b'=';
                n += 1;
                p += 1;
            }
        }
        n
    }

    // -- THE PUBLISHED CHECK VALUES --------------------------------------
    //
    // RFC 4648 §10. These are the whole point: they were written by the IETF,
    // not derived from anything in this crate.

    const RFC_B64: [(&[u8], &str); 7] = [
        (b"", ""),
        (b"f", "Zg=="),
        (b"fo", "Zm8="),
        (b"foo", "Zm9v"),
        (b"foob", "Zm9vYg=="),
        (b"fooba", "Zm9vYmE="),
        (b"foobar", "Zm9vYmFy"),
    ];

    const RFC_B32: [(&[u8], &str); 7] = [
        (b"", ""),
        (b"f", "MY======"),
        (b"fo", "MZXQ===="),
        (b"foo", "MZXW6==="),
        (b"foob", "MZXW6YQ="),
        (b"fooba", "MZXW6YTB"),
        (b"foobar", "MZXW6YTBOI======"),
    ];

    #[test]
    fn base64_reproduces_the_rfc4648_published_vectors() {
        for (input, want) in RFC_B64 {
            let mut out = [0u8; 32];
            let n = crate_b64(input, &mut out);
            assert_eq!(
                core::str::from_utf8(&out[..n]).unwrap(),
                want,
                "base64 of {:?}",
                core::str::from_utf8(input).unwrap()
            );
        }
    }

    #[test]
    fn base32_reproduces_the_rfc4648_published_vectors() {
        for (input, want) in RFC_B32 {
            let mut out = [0u8; 32];
            let n = crate_b32(input, &mut out);
            assert_eq!(
                core::str::from_utf8(&out[..n]).unwrap(),
                want,
                "base32 of {:?}",
                core::str::from_utf8(input).unwrap()
            );
        }
    }

    #[test]
    fn base64_agrees_with_the_shift_and_table_oracle_over_a_byte_sweep() {
        // Every length 0..=6 over a deterministic spread of byte values, so
        // the sweep reaches interior bytes no structured pattern would.
        let mut state: u64 = 0x2545F4914F6CDD1D;
        for _ in 0..400 {
            let mut buf = [0u8; 6];
            for b in buf.iter_mut() {
                state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                *b = (state >> 33) as u8;
            }
            for len in 0..=6usize {
                let mut a = [0u8; 32];
                let mut b = [0u8; 32];
                let na = crate_b64(&buf[..len], &mut a);
                let nb = oracle_b64(&buf[..len], &mut b);
                assert_eq!(na, nb, "length disagreement at len={len}");
                assert_eq!(&a[..na], &b[..nb], "encoding disagreement at len={len} buf={buf:?}");
            }
        }
    }

    #[test]
    fn b64_group_slices_back_to_its_three_bytes_exhaustively_per_position() {
        // Exhaustive in each byte position against the other two swept.
        for x in 0u16..=255 {
            let x = x as u8;
            for (p, q) in [(0u8, 0u8), (255, 255), (1, 254), (170, 85)] {
                for slot in 0..3 {
                    let (b0, b1, b2) = match slot {
                        0 => (x, p, q),
                        1 => (p, x, q),
                        _ => (p, q, x),
                    };
                    let g = b64_group(b0, b1, b2);
                    assert_eq!(b64_byte0(g), b0 as u32);
                    assert_eq!(b64_byte1(g), b1 as u32);
                    assert_eq!(b64_byte2(g), b2 as u32);
                }
            }
        }
    }

    #[test]
    fn b64_regroup_inverts_the_four_six_bit_slices_exhaustively_per_position() {
        for x in 0u8..64 {
            for (p, q, r) in [(0u8, 0u8, 0u8), (63, 63, 63), (1, 62, 5), (42, 21, 33)] {
                for slot in 0..4 {
                    let (v0, v1, v2, v3) = match slot {
                        0 => (x, p, q, r),
                        1 => (p, x, q, r),
                        2 => (p, q, x, r),
                        _ => (p, q, r, x),
                    };
                    let g = b64_regroup(v0, v1, v2, v3);
                    assert_eq!(b64_sym0(g), v0 as u32);
                    assert_eq!(b64_sym1(g), v1 as u32);
                    assert_eq!(b64_sym2(g), v2 as u32);
                    assert_eq!(b64_sym3(g), v3 as u32);
                }
            }
        }
    }

    #[test]
    fn b32_group_slices_back_to_its_five_bytes_exhaustively_per_position() {
        for x in 0u16..=255 {
            let x = x as u8;
            for slot in 0..5usize {
                let mut b = [7u8, 200, 0, 255, 91];
                b[slot] = x;
                let g = b32_group(b[0], b[1], b[2], b[3], b[4]);
                assert_eq!(b32_byte0(g), b[0] as u64);
                assert_eq!(b32_byte1(g), b[1] as u64);
                assert_eq!(b32_byte2(g), b[2] as u64);
                assert_eq!(b32_byte3(g), b[3] as u64);
                assert_eq!(b32_byte4(g), b[4] as u64);
            }
        }
    }

    #[test]
    fn b32_regroup_inverts_the_eight_five_bit_slices_exhaustively_per_position() {
        for x in 0u8..32 {
            for slot in 0..8usize {
                let mut v = [1u8, 31, 0, 17, 8, 30, 2, 25];
                v[slot] = x;
                let g = b32_regroup(v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7]);
                let got = [
                    b32_sym0(g), b32_sym1(g), b32_sym2(g), b32_sym3(g),
                    b32_sym4(g), b32_sym5(g), b32_sym6(g), b32_sym7(g),
                ];
                for k in 0..8 {
                    assert_eq!(got[k], v[k] as u64, "slot {slot} slice {k}");
                }
            }
        }
    }

    #[test]
    fn b64_alphabet_matches_the_rfc4648_table_exhaustively() {
        for i in 0u8..64 {
            assert_eq!(b64_symbol(i), B64[i as usize] as u32, "index {i}");
            assert_eq!(b64_value(B64[i as usize]), i as u32, "symbol {}", B64[i as usize] as char);
        }
    }

    #[test]
    fn b32_alphabet_matches_the_rfc4648_table_exhaustively() {
        for i in 0u8..32 {
            assert_eq!(b32_symbol(i), B32[i as usize] as u32, "index {i}");
            assert_eq!(b32_value(B32[i as usize]), i as u32, "symbol {}", B32[i as usize] as char);
        }
    }

    #[test]
    fn every_non_symbol_byte_decodes_to_the_sentinel_exhaustively() {
        for c in 0u16..=255 {
            let c = c as u8;
            let in64 = B64.iter().any(|&s| s == c);
            let in32 = B32.iter().any(|&s| s == c);
            assert_eq!(b64_value(c) == 64, !in64, "b64_value({c})");
            assert_eq!(b32_value(c) == 32, !in32, "b32_value({c})");
        }
        // `=` is padding, not a symbol, in both alphabets.
        assert_eq!(b64_value(b'='), 64);
        assert_eq!(b32_value(b'='), 32);
    }

    #[test]
    fn out_of_range_indices_return_the_one_past_the_top_sentinel() {
        for i in 64u16..=255 {
            assert_eq!(b64_symbol(i as u8), 123, "b64_symbol({i})");
        }
        for i in 32u16..=255 {
            assert_eq!(b32_symbol(i as u8), 91, "b32_symbol({i})");
        }
    }

    /// This test CANNOT catch a wrong alphabet, and is here so the asymmetry
    /// is recorded rather than rediscovered: it derives its expectation from
    /// the function under test. Shifting every symbol by a constant keeps the
    /// map injective, so this stays green while every encoded byte is wrong.
    /// Only `b64_alphabet_matches_the_rfc4648_table_exhaustively`, which
    /// spells the RFC table out, can refuse that.
    #[test]
    fn b64_alphabet_is_injective() {
        let mut seen = [false; 256];
        for i in 0u8..64 {
            let s = b64_symbol(i) as usize;
            assert!(!seen[s], "index {i} collides on symbol {s}");
            seen[s] = true;
        }
    }

    #[test]
    fn b64_encoded_len_matches_the_rfc_formula_over_a_sweep() {
        // Independent oracle: the closed form, in u128 so it cannot overflow.
        for n in (0u64..100_000).chain([
            4_294_967_290, 4_294_967_295, 1_000_000_000, 2_147_483_648,
        ]) {
            let n32 = (n % 4_294_967_296) as u32;
            let q = b64_full_quanta(n32);
            let t = b64_tail_bytes(n32);
            let got = b64_encoded_len(q, t);
            let want = (((n32 as u128) + 2) / 3 * 4) as u64;
            assert_eq!(got, want, "b64_encoded_len for n={n32}");
        }
    }

    #[test]
    fn b32_encoded_len_matches_the_rfc_formula_over_a_sweep() {
        for n in (0u64..100_000).chain([4_294_967_290, 4_294_967_295, 1_000_000_000]) {
            let n32 = (n % 4_294_967_296) as u32;
            let q = b32_full_quanta(n32);
            let t = b32_tail_bytes(n32);
            let got = b32_encoded_len(q, t);
            let want = (((n32 as u128) + 4) / 5 * 8) as u64;
            assert_eq!(got, want, "b32_encoded_len for n={n32}");
        }
    }

    #[test]
    fn padding_and_tail_symbol_counts_match_the_published_vectors() {
        // Read straight off the RFC 4648 §10 strings above.
        for (input, want) in RFC_B64 {
            let t = b64_tail_bytes(input.len() as u32);
            let pad = b64_padding_count(t) as usize;
            assert_eq!(pad, want.bytes().filter(|&c| c == b'=').count(), "b64 pad for {want:?}");
            if t != 0 {
                assert_eq!(b64_tail_symbols(t) as usize, 4 - pad, "b64 tail syms for {want:?}");
            }
        }
        for (input, want) in RFC_B32 {
            let t = b32_tail_bytes(input.len() as u32);
            let pad = b32_padding_count(t) as usize;
            assert_eq!(pad, want.bytes().filter(|&c| c == b'=').count(), "b32 pad for {want:?}");
            if t != 0 {
                assert_eq!(b32_tail_symbols(t) as usize, 8 - pad, "b32 tail syms for {want:?}");
            }
        }
    }

    #[test]
    fn b64_decoded_len_inverts_b64_encoded_len_on_every_tail() {
        for q in [0u32, 1, 2, 1000, 1_000_000_000, 4_294_967_294] {
            for tail in 0u32..3 {
                let enc = b64_encoded_len(q, tail);
                assert_eq!(enc % 4, 0, "encoded length is whole quanta: q={q} tail={tail}");
                let quads = (enc / 4) as u32;
                let pad = b64_padding_count(tail);
                let dec = b64_decoded_len(quads, pad);
                let want = (q as u64) * 3 + (tail as u64);
                assert_eq!(dec, want, "roundtrip q={q} tail={tail}");
            }
        }
        // The top of the quantum range, and the reason the return type is
        // `u64` rather than `u32`: at `q == u32::MAX` with a tail there is one
        // more 4-symbol quad than a `u32` can name. `tla-base64` reaches the
        // same boundary and answers `None` (`encode.rs:101`), leaving its
        // caller an `.expect` to discharge; widening the result answers it
        // instead. Written as literals so this cannot be re-derived from the
        // function under test.
        assert_eq!(b64_encoded_len(4_294_967_295, 0), 17_179_869_180);
        assert_eq!(b64_encoded_len(4_294_967_295, 1), 17_179_869_184);
        assert_eq!(b64_encoded_len(4_294_967_295, 2), 17_179_869_184);
    }

    /// Every tier-1 clause, exercised on inputs that reach the clamp. A green
    /// `ensures` row over a function whose clamp can never fire is dead code;
    /// this is the test that says each one is live.
    #[test]
    fn no_tier1_result_ever_exceeds_its_bound() {
        let mut saw_b64_symbol_clamp = false;
        let mut saw_b64_value_clamp = false;
        let mut saw_b32_symbol_clamp = false;
        let mut saw_b32_value_clamp = false;
        for c in 0u16..=255 {
            let c = c as u8;
            assert!(b64_symbol(c) <= 123);
            assert!(b64_value(c) <= 64);
            assert!(b32_symbol(c) <= 91);
            assert!(b32_value(c) <= 32);
            saw_b64_symbol_clamp |= b64_symbol(c) == 123;
            saw_b64_value_clamp |= b64_value(c) == 64;
            saw_b32_symbol_clamp |= b32_symbol(c) == 91;
            saw_b32_value_clamp |= b32_value(c) == 32;
        }
        assert!(saw_b64_symbol_clamp && saw_b64_value_clamp);
        assert!(saw_b32_symbol_clamp && saw_b32_value_clamp);

        for t in 0u32..8 {
            assert!(b64_padding_count(t) <= 2);
            assert!(b64_tail_symbols(t) <= 3);
            assert!(b32_padding_count(t) <= 6);
            assert!(b32_tail_symbols(t) <= 7);
        }
        // `output_fits` must actually clamp, not merely pass values through.
        assert_eq!(output_fits(100, 10), 10);
        assert_eq!(output_fits(10, 100), 10);
        for cap in [0u64, 1, 7, u64::MAX] {
            for needed in [0u64, 1, 8, u64::MAX] {
                assert!(output_fits(needed, cap) <= cap);
            }
        }
    }
}
