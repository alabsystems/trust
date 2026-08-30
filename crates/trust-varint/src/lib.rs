//! Total, verified LEB128 / varint / length-prefix decoding for `no_std` Trust
//! components.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0
//!
//! # Why this crate exists, and who calls it
//!
//! A varint decoder produces two things a caller immediately treats as facts:
//! **how many bytes were consumed** and **how large the value is**. In this
//! tree both are open-coded at the use site, and the second one is routinely
//! not checked at all — a decoded count becomes an allocation size or a slice
//! bound with nothing between the untrusted bytes and the arithmetic.
//!
//! **`crates/trust-binary-parse/src/dwarf/line.rs:267`** and **`:290`** — a
//! ULEB128 count sizing an allocation:
//!
//! ```text
//! let count =
//!     usize::try_from(cursor.read_uleb128()?).map_err(|_| DwarfError::InvalidLineProgram)?;
//! let mut directories = Vec::with_capacity(count);
//! ```
//!
//! `read_uleb128` returns a `u64` and can legitimately return `u64::MAX`. The
//! `try_from` discharges *representability* only, and on a 64-bit target it
//! rejects nothing a `u64` can hold — so the bound that actually matters, "the
//! count is no larger than the bytes remaining", is never stated. Eleven lines
//! earlier the same file does it correctly (`line.rs:114-119`, where
//! `read_bytes` performs the check), so the pattern is known and these two
//! sites skip it. [`uleb_clamp_u64`] returns that count already clamped to a
//! capacity the caller names, as a *checked* proposition — `ensures result <=
//! cap` — so the bound rides the signature instead of a downstream `?`.
//!
//! **`crates/trust-binary-parse/src/symbol.rs:87`** and
//! **`crates/trust-binary-parse/src/relocation.rs:41`** — multiply-then-check,
//! where the bound test inspects a value the arithmetic has already produced:
//!
//! ```text
//! let sym_end = sym_start + (nsyms as usize) * NLIST_64_SIZE;
//! if sym_end > file_data.len() { ... }
//! ```
//!
//! On a 32-bit target `nsyms * 16` with `nsyms == 0x2000_0000` wraps to `0` and
//! the check *passes*, yielding a table window that does not correspond to the
//! claimed table. `pe.rs:792` in the same crate spells the identical shape with
//! `checked_mul`, so this is an inconsistency rather than a house style.
//! [`table_end`] performs the multiply in a width where it cannot wrap and
//! returns the extent already clamped.
//!
//! **`crates/trust-binary-parse/src/dwarf/line.rs:470`** — the sharpest one,
//! because the side condition is discharged 346 lines away in a different
//! function:
//!
//! ```text
//! let adjusted = u64::from(opcode - parsed.header.opcode_base);
//! ```
//!
//! Both operands are attacker-controlled bytes (`opcode` read at `line.rs:112`,
//! `opcode_base` at `line.rs:177`). The entire proof that this `u8` subtraction
//! does not underflow is a `continue` in the caller at **`line.rs:124`**:
//!
//! ```text
//! if opcode < parsed.header.opcode_base {
//!     execute_standard_opcode(...)?;
//!     continue;
//! }
//! ```
//!
//! `execute_special_opcode` is a free `fn` with no precondition in its
//! signature and no doc comment. The sibling computation at `line.rs:431`
//! spells the same thing defensively (`u8::MAX - opcode_base`, which cannot
//! underflow); `:470` is the one that relies on a caller. In release it wraps.
//! [`special_opcode_adjusted`] is that subtraction with the guard *in the
//! function that performs it*, returning a sentinel instead of wrapping.
//!
//! The `.expect` two lines later at **`line.rs:472`** —
//! *"invariant: modulo of u8 range always fits in i64"* — is the only statement
//! of that invariant anywhere in the file: no `debug_assert`, no test named for
//! it. It survives an underflow at `:470` only by luck, because the modulo
//! result is small either way.
//!
//! **`crates/trust-vcgen/src/generate/assert_refutation.rs:1424`** — a
//! length-prefix window whose `i + len` is unchecked; [`prefix_end`] is that
//! addition performed where it cannot overflow.
//!
//! # Totality
//!
//! Every function here is **total** — defined on all inputs, with no panicking
//! path. A precondition is not available under the strict lane (both spellings
//! of `requires` are recorded `[ASSUMED] assumption:requires ... unsupported
//! MIR FullVerification::Precondition`, and an assumed row fails the gate), and
//! none is needed: bytes arrive by value, so there is no length to require.
//!
//! Sentinels buy the totality. [`uleb_len`] returns `0` for "no terminator in
//! these ten bytes" — `0` is not a valid LEB128 length, so it cannot collide
//! — and [`special_opcode_adjusted`] returns `256`, one past the top of the
//! `u8` difference space, so the sentinel is itself inside the contracted
//! bound. This is `trust-hex`'s `utf8_head_len` discipline, which returns `0`
//! on a byte that heads nothing.
//!
//! # Two tiers, marked per item
//!
//! **Tier 1 — proved bound.** A grammar `ensures` clause the compiler
//! discharges: [`uleb_len`], [`uleb_fits`], [`uleb_clamp_u32`],
//! [`uleb_clamp_u64`], [`table_end`], [`prefix_end`]. A caller may rely on the
//! clause, and a body that broke it would not compile.
//!
//! **Tier 2 — proved totality, bound carried by the return type.**
//! [`uleb_value`] and [`special_opcode_adjusted`]. What is proved is that the
//! body cannot panic: no product and no partial sum overflows, on any input.
//!
//! # THE CEILING: 56 bits, and it is a measured fragment boundary
//!
//! [`uleb_value`] decodes **eight** payload bytes — 56 bits — and not the ten a
//! full `u64` LEB128 needs. That is not a design choice; it is the exact point
//! where the strict lane stops proving, established by four probe rounds on
//! 2026-08-29 and recorded in `docs/STRICT_VERIFICATION_FRAGMENT.md` §2.7.
//!
//! The mechanism: **a constant mask contributes no range.** `(b & 127) as u64`
//! is read by the interval engine as `[0, 255]` — the range of the *widening
//! cast's source type* — not as `[0, 127]`. The mask is invisible. Summing
//! `(b_i & 127) * 2^(7i)` therefore has an engine-computed peak of
//! `255 * (2^(7n) - 1) / 127`, which crosses `u64::MAX` at **n = 9**
//! (`1.852e19` against `1.845e19`) while `n = 8` peaks at `1.447e17` and proves
//! with room to spare. Measured: the eight-term sum is `28 proved / 0 unknown`;
//! the nine-term sum is `30 proved / 1 runtime-checked / 1 unknown`, failing on
//! exactly the last multiply.
//!
//! Three repairs were measured and all three fail — see §2.7 of the map for the
//! messages. Hoisting the ninth term and guarding it adjacent to its `let` does
//! not rescue it (`30 / 1 / 1`, unchanged), because the eight-term sum then
//! intervenes between the guard and the use. Selecting the top contribution
//! between two constants rather than multiplying is opaque to the engine
//! (`0 proved / 2 unknown`). Respelling the mask as `% 128` — which supplies
//! `[0, 1]` correctly for `% 2` in a two-line body — **breaks lowering
//! outright** at this arity: *"native typed-TrustIr lowering did not complete,
//! so the panic-freedom of an unmodeled construct could not be established"*,
//! `0 proved / 75 unknown`. `u128` is not in the fragment either.
//!
//! So 56 bits is where the proof is, and this crate claims 56 bits. A caller
//! needing the last eight is told which case it is in: [`uleb_fits`] returns
//! `1` exactly when the encoding terminates within eight bytes, and
//! [`uleb_len`] scans all ten so a caller can still *skip* a value it cannot
//! *decode*. Refusing to decode a value whose bound is unproved is the
//! fail-closed direction; returning a wrapped one is not.
//!
//! # What is NOT proved here, and is pinned by tests instead
//!
//! **Which byte carries which coefficient**, and **the continuation-bit
//! semantics**. No obligation in this crate can see either: permuting the
//! coefficients or masking with `63` instead of `127` leaves every product and
//! every partial sum in range, so the strict lane still returns exit 0 while
//! the answers are wrong. `trust_varint_strict_gate.sh` mutation D does exactly
//! that and watches the lane pass while the unit tests go red. The tests are
//! therefore part of the evidence: [`uleb_value`] is checked against an
//! independent `u128`-accumulating oracle written by a different method, and
//! exhaustively over all 65536 two-byte encodings.
//!
//! # The measured fragment boundary
//!
//! See [`docs/STRICT_VERIFICATION_FRAGMENT.md`] for the full checklist. The
//! entries THIS crate established are §2.7 and §1.5, measured 2026-08-29 on the
//! authenticated `targo trust check` lane at stage1 driver `ba5e2cace25b69a8`
//! and re-confirmed unchanged on `4379d14c1706969b` after a concurrent
//! `x.py check --stage 1` rebuilt the driver mid-session. Every count in this
//! file is the same on both.
//!
//! [`docs/STRICT_VERIFICATION_FRAGMENT.md`]: ../../../docs/STRICT_VERIFICATION_FRAGMENT.md

#![no_std]

// ---------------------------------------------------------------------------
// Composition carriers.
//
// These are the only contract-carrying leaf bodies in the crate; every tier-1
// bound below is inherited from one of them. A contracted wrapper discharges
// its clause only when its callee ACTUALLY CARRIES a contract — the same
// wrapper over an uncontracted clamp measures UNKNOWN — which is why these
// exist as separate, contracted, private functions rather than as inline
// comparisons.
//
// They are re-declared here rather than imported from `trust-ratio` or
// `trust-endian`, which already have them: cross-crate composition does not
// work, because a call into a verified sibling mints a fatal absent-callee row
// in the caller. That is why all six of these crates are dependency-free.
// ---------------------------------------------------------------------------

/// `v`, clamped from above by `hi`.
fn clamp_u16(v: u16, hi: u16) -> u16 ensures result <= hi {
    if v > hi { hi } else { v }
}

/// `v`, clamped from above by `hi`.
fn clamp_u32(v: u32, hi: u32) -> u32 ensures result <= hi {
    if v > hi { hi } else { v }
}

/// `v`, clamped from above by `hi`. The 64-bit twin of [`clamp_u32`].
fn clamp_u64(v: u64, hi: u64) -> u64 ensures result <= hi {
    if v > hi { hi } else { v }
}

// ---------------------------------------------------------------------------
// Tier 1 — structure of the encoding.
//
// These are arithmetic-free: comparison and constant returns only, which is the
// one body shape that discharges an `ensures` against a constant bound.
// ---------------------------------------------------------------------------

/// The number of bytes the ULEB128 encoding starting at `b0` occupies, or `0`
/// if none of the ten bytes terminates it.
///
/// **Tier 1.** `ensures result <= 10` is checked.
///
/// Ten bytes is the maximum a `u64` LEB128 can occupy, so a `0` here means the
/// input is malformed rather than merely long. Note the deliberate asymmetry
/// with [`uleb_value`], which decodes eight: a caller can always learn how many
/// bytes to *skip*, even for a value this crate will not *decode*. Use
/// [`uleb_fits`] to tell the two cases apart.
pub fn uleb_len(
    b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8, b8: u8, b9: u8,
) -> u8 ensures result <= 10 {
    if b0 < 128 { return 1; }
    if b1 < 128 { return 2; }
    if b2 < 128 { return 3; }
    if b3 < 128 { return 4; }
    if b4 < 128 { return 5; }
    if b5 < 128 { return 6; }
    if b6 < 128 { return 7; }
    if b7 < 128 { return 8; }
    if b8 < 128 { return 9; }
    if b9 < 128 { return 10; }
    0
}

/// `1` when the ULEB128 encoding starting at `b0` terminates within these eight
/// bytes, `0` otherwise.
///
/// **Tier 1.** `ensures result <= 1` is checked.
///
/// This is the guard on [`uleb_value`]'s domain. When it returns `1`,
/// `uleb_value` is the exact encoded value; when it returns `0`, the value
/// needs more than 56 bits and this crate declines to decode it — see the
/// module docs on the ceiling.
pub fn uleb_fits(b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8) -> u8 ensures result <= 1 {
    if b0 < 128 { return 1; }
    if b1 < 128 { return 1; }
    if b2 < 128 { return 1; }
    if b3 < 128 { return 1; }
    if b4 < 128 { return 1; }
    if b5 < 128 { return 1; }
    if b6 < 128 { return 1; }
    if b7 < 128 { return 1; }
    0
}

// ---------------------------------------------------------------------------
// Tier 2 — the value.
//
// `* 128` rather than `<< 7` is not a style choice. A shift is opaque to the
// composition that carries every tier-1 bound in this crate (a contracted
// wrapper over a callee containing `>>`, `<<` or `/` fails outright with
// "member has a guarded or non-entry-prefix Assert"), and multiplication by a
// power of two composes. `<<` is what every caller site uses, and this is the
// one respelling that moves them into the fragment.
//
// The early returns are what make this the *decoder* rather than a fixed
// eight-byte sum: a ULEB128 ends at the first byte with the high bit clear, and
// every byte after that belongs to the next value.
// ---------------------------------------------------------------------------

/// The value of the ULEB128 encoding starting at `b0`, decoded from at most
/// eight payload bytes.
///
/// **Tier 2.** Proved: none of the seven products and none of the seven partial
/// sums overflows `u64`, on every input. Bound carried by the return type; the
/// true range is `[0, 2^56 - 1]`.
///
/// Exact when [`uleb_fits`] returns `1`. When it returns `0` the encoding
/// continues past byte seven and this returns the low 56 bits, which is why the
/// two are meant to be read together — `uleb_clamp_u64` does that for you.
///
/// This is `crates/trust-binary-parse/src/dwarf/line.rs:267`'s
/// `cursor.read_uleb128()` with the accumulator's width made explicit and the
/// shift amount eliminated.
pub fn uleb_value(b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8) -> u64 {
    // 128 = 2^7, 16384 = 2^14, ..., 562949953421312 = 2^49.
    let a0 = (b0 & 127) as u64;
    if b0 < 128 { return a0; }
    let a1 = a0 + ((b1 & 127) as u64) * 128;
    if b1 < 128 { return a1; }
    let a2 = a1 + ((b2 & 127) as u64) * 16384;
    if b2 < 128 { return a2; }
    let a3 = a2 + ((b3 & 127) as u64) * 2097152;
    if b3 < 128 { return a3; }
    let a4 = a3 + ((b4 & 127) as u64) * 268435456;
    if b4 < 128 { return a4; }
    let a5 = a4 + ((b5 & 127) as u64) * 34359738368;
    if b5 < 128 { return a5; }
    let a6 = a5 + ((b6 & 127) as u64) * 4398046511104;
    if b6 < 128 { return a6; }
    a6 + ((b7 & 127) as u64) * 562949953421312
}

/// `opcode - opcode_base`, or `256` when `opcode < opcode_base`.
///
/// **Tier 2.** Proved: the subtraction cannot underflow. The sentinel is one
/// past the top of the difference space (`u8 - u8` is at most `255`), so a
/// caller can test `>= 256` for "not a special opcode" without a second read of
/// `opcode_base`.
///
/// This is `crates/trust-binary-parse/src/dwarf/line.rs:470` with the guard
/// moved into the function that performs the subtraction. There, the guard is
/// a `continue` at `line.rs:124` in a different function 346 lines away, and
/// `execute_special_opcode` states no precondition; in release the subtraction
/// wraps and `adjusted` feeds `advance_address` at `line.rs:476`.
pub fn special_opcode_adjusted(opcode: u8, opcode_base: u8) -> u16 {
    if opcode < opcode_base { return 256; }
    (opcode - opcode_base) as u16
}

// ---------------------------------------------------------------------------
// Tier 1 — bounded reads.
//
// The clamp is LIVE in every one of these: a hostile eight-byte varint really
// does reach 2^56-1 and a hostile `count`/`elem` pair really does reach
// 2^48, against a capacity that is whatever the caller's buffer holds. None of
// these wrappers contains dead code, which is the property that separates a
// proved bound from a body reshaped until the encoder accepted it.
//
// Each is a contracted wrapper over exactly one contracted callee — the only
// body shape that inherits a postcondition — with all arithmetic pushed into
// an uncontracted `raw_*` helper.
// ---------------------------------------------------------------------------

fn raw_uleb_u32(b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8) -> u32 {
    let v: u64 = uleb_value(b0, b1, b2, b3, b4, b5, b6, b7);
    if v > 4294967295 { return 4294967295; }
    v as u32
}

/// A ULEB128 count, clamped to `cap`, as a `u32`.
///
/// **Tier 1.** `ensures result <= cap` is checked.
///
/// Values above `u32::MAX` saturate before the clamp, so the narrowing cannot
/// truncate a large count into a small one — the direction that turns a
/// rejected input into an accepted one. Clamp before the narrowing cast, never
/// after.
pub fn uleb_clamp_u32(
    b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8, cap: u32,
) -> u32 ensures result <= cap {
    clamp_u32(raw_uleb_u32(b0, b1, b2, b3, b4, b5, b6, b7), cap)
}

/// A ULEB128 count, clamped to `cap`.
///
/// **Tier 1.** `ensures result <= cap` is checked.
///
/// This is the discharge for `crates/trust-binary-parse/src/dwarf/line.rs:267`
/// and `:290`, where a ULEB128 count sizes a `Vec::with_capacity` with nothing
/// bounding it but `usize::try_from`, which on a 64-bit target rejects nothing.
pub fn uleb_clamp_u64(
    b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8, cap: u64,
) -> u64 ensures result <= cap {
    clamp_u64(uleb_value(b0, b1, b2, b3, b4, b5, b6, b7), cap)
}

fn raw_table_end(start: u32, count: u32, elem: u16) -> u64 {
    // Peak (2^32-1) + (2^32-1)*(2^16-1) < 2^48: the multiply cannot wrap in
    // this width, which is the entire point — at `usize` on a 32-bit target it
    // can, and the check that follows it then inspects a wrapped value.
    (start as u64) + (count as u64) * (elem as u64)
}

/// The end offset of a `count`-element table of `elem`-byte records beginning
/// at `start`, clamped to `cap`.
///
/// **Tier 1.** `ensures result <= cap` is checked.
///
/// This is `crates/trust-binary-parse/src/symbol.rs:87` and
/// `crates/trust-binary-parse/src/relocation.rs:41` with the multiply performed
/// in a width where it cannot wrap. Both sites compute
/// `start + count * elem_size` at `usize` and *then* compare against
/// `file_data.len()`; on a 32-bit target the product wraps and the comparison
/// passes. Passing `cap = file_data.len()` here makes the comparison
/// unnecessary — the returned extent is already inside the buffer.
pub fn table_end(start: u32, count: u32, elem: u16, cap: u64) -> u64 ensures result <= cap {
    clamp_u64(raw_table_end(start, count, elem), cap)
}

fn raw_prefix_end(offset: u32, len: u32) -> u64 {
    (offset as u64) + (len as u64)
}

/// The end offset of a length-prefixed window, clamped to `cap`.
///
/// **Tier 1.** `ensures result <= cap` is checked.
///
/// This is `crates/trust-vcgen/src/generate/assert_refutation.rs:1424`'s
/// `i + len`, performed where it cannot overflow. There the range bound is
/// discharged by `bytes.get(i..i + len)?` rather than by a comment, so that
/// site is the mildest of the set — but the addition itself is still unchecked,
/// and `prefix_end` is the shape that does not need a downstream `?` to be
/// safe.
pub fn prefix_end(offset: u32, len: u32, cap: u64) -> u64 ensures result <= cap {
    clamp_u64(raw_prefix_end(offset, len), cap)
}

/// [`special_opcode_adjusted`], clamped to `cap`.
///
/// **Tier 1.** `ensures result <= cap` is checked.
///
/// DWARF's special-opcode arithmetic divides the adjusted opcode by
/// `line_range`; a caller that clamps to `line_range * max_line_advance` first
/// gets that bound as a checked proposition rather than as the `.expect`
/// at `crates/trust-binary-parse/src/dwarf/line.rs:472`, whose message
/// *"invariant: modulo of u8 range always fits in i64"* is the only statement
/// of the invariant in the file.
pub fn special_opcode_clamped(opcode: u8, opcode_base: u8, cap: u16) -> u16 ensures result <= cap {
    clamp_u16(special_opcode_adjusted(opcode, opcode_base), cap)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A deterministic 64-bit LCG (Knuth's MMIX constants), used to reach
    /// interior values no structured pattern would. Not cryptographic and not
    /// meant to be — it is here so the eight-byte sweeps are reproducible and
    /// dependency-free.
    fn lcg(state: &mut u64) -> u64 {
        *state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        *state
    }

    /// Backgrounds for the per-position sweeps: both extremes, both sides of
    /// the continuation bit, and both neighbours of the top.
    const PATTERNS: [u8; 6] = [0x00, 0x01, 0x7f, 0x80, 0xfe, 0xff];

    // -- THE ORACLES ------------------------------------------------------
    //
    // Written by a DIFFERENT METHOD from the crate: `|=` with a `<< shift`
    // accumulator over `u128`, which is how every real decoder in this tree
    // spells it (`trust-binary-parse/src/leb128.rs:10-19`). The crate cannot
    // use that spelling — a shift is opaque to the composition carrying its
    // tier-1 bounds — so the two implementations share no arithmetic.

    /// The value of the ULEB128 in `b`, decoded from at most eight payload
    /// bytes. Accumulates in `u128` so the oracle itself cannot overflow.
    fn oracle_value(b: [u8; 8]) -> u64 {
        let mut acc: u128 = 0;
        let mut shift: u32 = 0;
        for &byte in b.iter() {
            acc |= u128::from(byte & 0x7f) << shift;
            if byte < 0x80 {
                return acc as u64;
            }
            shift += 7;
        }
        // Unterminated: the low 56 bits, which is what the crate returns.
        acc as u64
    }

    /// The encoded length, or 0 if unterminated within ten bytes.
    fn oracle_len(b: [u8; 10]) -> u8 {
        for (i, &byte) in b.iter().enumerate() {
            if byte < 0x80 {
                return (i + 1) as u8;
            }
        }
        0
    }

    /// Canonical ULEB128 encoder, for the round-trip test.
    fn oracle_encode(mut v: u64) -> [u8; 8] {
        let mut out = [0u8; 8];
        for slot in out.iter_mut() {
            let byte = (v & 0x7f) as u8;
            v >>= 7;
            if v == 0 {
                *slot = byte;
                return out;
            }
            *slot = byte | 0x80;
        }
        out
    }

    // -- uleb_value: EXHAUSTIVE over the first two bytes -------------------

    /// All 65536 two-byte prefixes, against six tails. When `b0 < 128` the
    /// value is `b0` and the tail is irrelevant; when it is not, `b1` decides
    /// whether the tail is read at all. This is the sub-domain where a
    /// coefficient swap between the first two positions is visible.
    #[test]
    fn uleb_value_agrees_with_shift_oracle_over_every_two_byte_prefix() {
        for pat in PATTERNS {
            for b0 in 0..=255u8 {
                for b1 in 0..=255u8 {
                    let b = [b0, b1, pat, pat, pat, pat, pat, pat];
                    assert_eq!(
                        uleb_value(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]),
                        oracle_value(b),
                        "value {b:?}"
                    );
                }
            }
        }
    }

    /// Every value in every byte position against six backgrounds. This is the
    /// sweep that sees a permuted coefficient in the interior positions, which
    /// the two-byte sweep above cannot reach.
    #[test]
    fn uleb_value_agrees_with_shift_oracle_per_position() {
        for pos in 0..8usize {
            for pat in PATTERNS {
                for v in 0..=255u8 {
                    let mut b = [pat; 8];
                    b[pos] = v;
                    assert_eq!(
                        uleb_value(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]),
                        oracle_value(b),
                        "value pos={pos} {b:?}"
                    );
                }
            }
        }
    }

    /// A pseudorandom interior sweep, plus an all-continuation sweep that
    /// forces every one of the eight terms to be summed on every iteration —
    /// the maximal-arithmetic path, where the peak is 2^56-1.
    #[test]
    fn uleb_value_agrees_with_shift_oracle_over_random_and_saturated_inputs() {
        let mut st: u64 = 0x243f_6a88_85a3_08d3;
        for _ in 0..200_000 {
            let r = lcg(&mut st);
            let b = r.to_le_bytes();
            assert_eq!(
                uleb_value(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]),
                oracle_value(b),
                "value random {b:?}"
            );
            // Force the unterminated path: every byte carries a continuation
            // bit, so all seven products and all seven sums are evaluated.
            let s = [
                b[0] | 0x80, b[1] | 0x80, b[2] | 0x80, b[3] | 0x80,
                b[4] | 0x80, b[5] | 0x80, b[6] | 0x80, b[7] | 0x80,
            ];
            assert_eq!(
                uleb_value(s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]),
                oracle_value(s),
                "value saturated {s:?}"
            );
        }
    }

    /// The proof says no partial sum overflows; it says nothing about the
    /// value being right at the top. Pin the maximum explicitly.
    #[test]
    fn uleb_value_reaches_exactly_2_pow_56_minus_1() {
        let all = 0xffu8;
        assert_eq!(
            uleb_value(all, all, all, all, all, all, all, all),
            (1u64 << 56) - 1
        );
        assert_eq!(uleb_value(0, 0, 0, 0, 0, 0, 0, 0), 0);
    }

    /// Round-trip against an independent canonical encoder, over values that
    /// exercise every encoded length from one to eight bytes.
    #[test]
    fn canonical_encodings_round_trip_through_uleb_value_and_len() {
        let mut st: u64 = 0x13198a2e_03707344;
        let mut cases: [u64; 3] = [0, 0, 0];
        for bits in 0..56u32 {
            cases[0] = 1u64 << bits;
            cases[1] = (1u64 << bits) - 1;
            cases[2] = lcg(&mut st) & ((1u64 << 56) - 1);
            for &v in cases.iter() {
                let e = oracle_encode(v);
                assert_eq!(
                    uleb_value(e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7]),
                    v,
                    "round trip {v} -> {e:?}"
                );
                assert_eq!(
                    uleb_len(e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7], 0, 0),
                    oracle_len([e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7], 0, 0]),
                    "round trip len {v}"
                );
                assert_eq!(uleb_fits(e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7]), 1);
            }
        }
    }

    // -- uleb_len / uleb_fits ---------------------------------------------

    /// All 65536 two-byte prefixes against six tails.
    #[test]
    fn uleb_len_agrees_with_scan_oracle_over_every_two_byte_prefix() {
        for pat in PATTERNS {
            for b0 in 0..=255u8 {
                for b1 in 0..=255u8 {
                    let b = [b0, b1, pat, pat, pat, pat, pat, pat, pat, pat];
                    assert_eq!(
                        uleb_len(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7], b[8], b[9]),
                        oracle_len(b),
                        "len {b:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn uleb_len_agrees_with_scan_oracle_per_position() {
        for pos in 0..10usize {
            for pat in PATTERNS {
                for v in 0..=255u8 {
                    let mut b = [pat; 10];
                    b[pos] = v;
                    assert_eq!(
                        uleb_len(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7], b[8], b[9]),
                        oracle_len(b),
                        "len pos={pos} {b:?}"
                    );
                }
            }
        }
    }

    /// `uleb_fits` must be exactly "the length is between 1 and 8", which is
    /// the domain on which `uleb_value` is exact. Checked against `uleb_len`
    /// on a tail of all-continuation bytes so the two disagree if either
    /// drifts.
    #[test]
    fn uleb_fits_is_exactly_a_length_within_eight() {
        let mut st: u64 = 0xa4093822_299f31d0;
        for _ in 0..100_000 {
            let b = lcg(&mut st).to_le_bytes();
            let len = uleb_len(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7], 0xff, 0xff);
            let fits = uleb_fits(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]);
            assert_eq!(fits == 1, len >= 1 && len <= 8, "fits/len {b:?} {fits} {len}");
            // On the fitting domain the value must equal the oracle exactly.
            if fits == 1 {
                assert_eq!(
                    uleb_value(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]),
                    oracle_value(b)
                );
            }
        }
        // The unterminated case: ten continuation bytes has no length.
        let c = 0x80u8;
        assert_eq!(uleb_len(c, c, c, c, c, c, c, c, c, c), 0);
        assert_eq!(uleb_fits(c, c, c, c, c, c, c, c), 0);
    }

    // -- special_opcode_adjusted: EXHAUSTIVE over its ENTIRE domain --------

    /// All 65536 `(opcode, opcode_base)` pairs against `checked_sub`. This is
    /// the whole input space, not a sample.
    #[test]
    fn special_opcode_adjusted_agrees_with_checked_sub_over_every_input() {
        for opcode in 0..=255u8 {
            for base in 0..=255u8 {
                let got = special_opcode_adjusted(opcode, base);
                match opcode.checked_sub(base) {
                    Some(d) => assert_eq!(got, u16::from(d), "adjusted {opcode},{base}"),
                    None => assert_eq!(got, 256, "sentinel {opcode},{base}"),
                }
            }
        }
    }

    /// The sentinel must be outside every legitimate difference, or a caller
    /// testing `>= 256` would reject a real opcode.
    #[test]
    fn special_opcode_sentinel_is_unreachable_by_a_real_difference() {
        for opcode in 0..=255u8 {
            for base in 0..=255u8 {
                if opcode >= base {
                    assert!(special_opcode_adjusted(opcode, base) <= 255);
                }
            }
        }
    }

    #[test]
    fn special_opcode_clamped_agrees_with_min_over_every_input() {
        for opcode in 0..=255u8 {
            for base in 0..=255u8 {
                for cap in [0u16, 1, 7, 255, 256, 65535] {
                    let raw = special_opcode_adjusted(opcode, base);
                    let got = special_opcode_clamped(opcode, base, cap);
                    assert_eq!(got, raw.min(cap), "clamped {opcode},{base},{cap}");
                    assert!(got <= cap, "contract {opcode},{base},{cap}");
                }
            }
        }
    }

    // -- the clamped length/count lane ------------------------------------

    #[test]
    fn uleb_clamp_u64_agrees_with_u128_oracle() {
        let mut st: u64 = 0x082efa98_ec4e6c89;
        for _ in 0..200_000 {
            let b = lcg(&mut st).to_le_bytes();
            let cap = lcg(&mut st);
            let want = u128::from(oracle_value(b)).min(u128::from(cap)) as u64;
            let got = uleb_clamp_u64(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7], cap);
            assert_eq!(got, want, "clamp64 {b:?} cap={cap}");
            assert!(got <= cap, "contract clamp64 {b:?} cap={cap}");
        }
    }

    /// The saturating narrow must not truncate a large count into a small one
    /// — the direction that turns a rejected input into an accepted one.
    #[test]
    fn uleb_clamp_u32_saturates_rather_than_truncating() {
        let mut st: u64 = 0x452821e6_38d01377;
        for _ in 0..200_000 {
            let b = lcg(&mut st).to_le_bytes();
            let cap = lcg(&mut st) as u32;
            let v = u128::from(oracle_value(b));
            let want = v.min(u128::from(u32::MAX)).min(u128::from(cap)) as u32;
            let got = uleb_clamp_u32(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7], cap);
            assert_eq!(got, want, "clamp32 {b:?} cap={cap}");
            assert!(got <= cap, "contract clamp32 {b:?} cap={cap}");
        }
        // A value above u32::MAX with a large cap must saturate to u32::MAX,
        // NOT wrap to its low 32 bits.
        let e = oracle_encode(0x1_0000_0000);
        assert_eq!(
            uleb_clamp_u32(e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7], u32::MAX),
            u32::MAX
        );
    }

    // -- table_end / prefix_end -------------------------------------------

    /// The whole point of `table_end` is that the multiply happens where it
    /// cannot wrap. Check against a `u128` oracle, including the inputs that
    /// wrap at `usize` on a 32-bit target — the `symbol.rs:87` defect.
    #[test]
    fn table_end_agrees_with_u128_oracle() {
        let mut st: u64 = 0xbe5466cf_34e90c6c;
        for _ in 0..200_000 {
            let start = lcg(&mut st) as u32;
            let count = lcg(&mut st) as u32;
            let elem = lcg(&mut st) as u16;
            let cap = lcg(&mut st);
            let want =
                (u128::from(start) + u128::from(count) * u128::from(elem)).min(u128::from(cap)) as u64;
            let got = table_end(start, count, elem, cap);
            assert_eq!(got, want, "table_end {start},{count},{elem},{cap}");
            assert!(got <= cap, "contract table_end");
        }
        // The exact `symbol.rs` shape that wraps at 32-bit usize:
        // 0x2000_0000 * 16 == 2^33, which is 0 mod 2^32.
        assert_eq!(table_end(0, 0x2000_0000, 16, u64::MAX), 8_589_934_592);
        // Peak: cannot exceed 2^48 + 2^32, far inside u64.
        assert_eq!(
            table_end(u32::MAX, u32::MAX, u16::MAX, u64::MAX),
            u64::from(u32::MAX) + u64::from(u32::MAX) * u64::from(u16::MAX)
        );
    }

    #[test]
    fn prefix_end_agrees_with_u128_oracle() {
        let mut st: u64 = 0xc0ac29b7_c97c50dd;
        for _ in 0..200_000 {
            let off = lcg(&mut st) as u32;
            let len = lcg(&mut st) as u32;
            let cap = lcg(&mut st);
            let want = (u128::from(off) + u128::from(len)).min(u128::from(cap)) as u64;
            let got = prefix_end(off, len, cap);
            assert_eq!(got, want, "prefix_end {off},{len},{cap}");
            assert!(got <= cap, "contract prefix_end");
        }
        // The pair that wraps at 32 bits and does not here.
        assert_eq!(prefix_end(u32::MAX, u32::MAX, u64::MAX), 8_589_934_590);
    }

    // -- the contracted bounds, read back ---------------------------------

    /// Every `ensures` clause in the crate, tested as a runtime property on a
    /// sweep. A proof that is green and a clause that is wrong would both be
    /// invisible without this.
    #[test]
    fn every_contracted_bound_holds_on_a_sweep() {
        let mut st: u64 = 0x9216d5d9_8979fb1b;
        for _ in 0..100_000 {
            let b = lcg(&mut st).to_le_bytes();
            let t = lcg(&mut st).to_le_bytes();
            assert!(uleb_len(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7], t[0], t[1]) <= 10);
            assert!(uleb_fits(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]) <= 1);
        }
    }
}
