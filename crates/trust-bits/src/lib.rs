//! Total, verified word-level bit manipulation for `no_std` Trust components.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0
//!
//! # Why this crate exists, and who calls it
//!
//! A shift amount and a field width are the two numbers in this tree least
//! likely to be checked and most likely to be wrong. `x << n` for `n >= 32`
//! is not an overflow that saturates — it panics with debug assertions on and
//! is **masked to `n % 32`** without them, so `1u32 << 32` evaluates to `1`
//! rather than `0` and nothing anywhere says so. `(1 << w) - 1` therefore has
//! two distinct failure modes at `w == 32` and neither produces a diagnostic
//! in a shipping build.
//!
//! This is not a hypothetical, and the incident report is already in the tree.
//! **`crates/trust-disasm/src/aarch64/decode.rs:227-235`**:
//!
//! ```text
//! /// TWO OVERFLOWS USED TO LIVE HERE, and their consequences were not
//! /// symmetric. `1u64 << (s + 1)` with `s == 63`, and `1u64 << esize` with
//! /// `esize == 64`, both overflow — i.e. EVERY 64-bit logical immediate with
//! /// a non-zero rotate. With debug assertions ON that panics (aborting the
//! /// compiler, which is not fail-closed); with them OFF — which is how the
//! /// shipped `trustc` is built — it silently produced `#0`. So
//! /// `eor x0, x0, #0x8000000000000000` decoded as the IDENTITY, and the
//! /// output gate certified it `Proven` with a kernel-re-checkable grade
//! /// against an identity spec, on machine code that is wrong for every
//! /// input. Measured: 27 such words in the 599-crate corpus.
//! ```
//!
//! A shipped miscompile, certified `Proven`, from a shift amount equal to the
//! word width. The repair at `decode.rs:259` is a local closure —
//! `let ones = |count: u32| if count >= 64 { u64::MAX } else { (1u64 << count) - 1 };`
//! — written once, in one function, for one of the many places that need it.
//! [`mask_below`] is that closure as a verified primitive.
//!
//! Six more, all re-read at the line cited:
//!
//! **`crates/trust-disasm/src/aarch64/decode.rs:20-22`** — three undischarged
//! conditions in one expression:
//!
//! ```text
//! /// Extract bits [hi:lo] (inclusive) from a 32-bit value.
//! fn bits(val: u32, hi: u32, lo: u32) -> u32 {
//!     (val >> lo) & ((1 << (hi - lo + 1)) - 1)
//! }
//! ```
//!
//! `hi - lo` underflows when `hi < lo`; `hi - lo + 1 == 32` shifts a `u32` by
//! its full width; `lo >= 32` shifts out of range. Every current caller passes
//! literals, which is the whole guarantee. The identical body is copy-pasted
//! into a second crate at
//! **`crates/trust-disasm/harness/native-invariant/src/attribute.rs:15-17`** —
//! and duplication is the argument for a primitive. [`field`] is that
//! expression with all three conditions decided.
//!
//! (`trust-interval` cites the same function for the `hi >= lo` half. The
//! split is deliberate: that crate owns `lo <= hi` as an *interval* predicate,
//! this one owns the shift-amount and mask-width obligation. Neither covers
//! the other.)
//!
//! **`crates/trust-disasm/src/aarch64/decode.rs:31-34`**:
//!
//! ```text
//! fn sign_extend(val: u32, width: u32) -> i64 {
//!     let shift = 64 - width;
//!     ((val as i64) << shift) >> shift
//! }
//! ```
//!
//! `width == 0` gives `shift == 64` — an `i64` shifted by its own width — and
//! `width > 64` underflows the subtraction into a huge shift. Both the shift
//! and the subtraction feeding it are unguarded.
//!
//! **`crates/trust-spec-elab/src/lib.rs:183-192`** — three adjacent helpers
//! over the same parameter, one guarded and two not:
//!
//! ```text
//! fn bit_mask(bits: u32) -> u128 {
//!     if bits == 128 { u128::MAX } else { (1u128 << bits) - 1 }
//! }
//! fn signed_positive_max(bits: u32) -> u128 {
//!     (1u128 << (bits - 1)) - 1
//! }
//! fn signed_negative_magnitude_max(bits: u32) -> u128 {
//!     1u128 << (bits - 1)
//! }
//! ```
//!
//! `bits == 0` underflows the second and third. The same one-sided shape is at
//! `crates/trust-vcgen/src/spec_inference.rs:16-22`, where the guard covers
//! `width == 128` and not `width == 0`, and at
//! `crates/trust-types/src/ay_bridge.rs:396-401`, which has four of them on
//! two parameters in five lines.
//!
//! **`crates/trust-vcgen/src/generate/callee_summaries.rs:1126-1131`** — the
//! precondition written in prose and nowhere else:
//!
//! ```text
//! /// Inclusive value range of an integer type (`width < 128` — guarded by
//! /// every caller; a 128-bit range does not fit `i128`).
//! pub(super) fn int_type_bounds(width: u32, signed: bool) -> (i128, i128) {
//!     if signed {
//!         (-(1i128 << (width - 1)), (1i128 << (width - 1)) - 1)
//! ```
//!
//! **`compiler/rustc_index/src/bit_set.rs:1750-1752`** — a total-looking
//! helper that is not total:
//!
//! ```text
//! fn max_bit(word: Word) -> usize {
//!     WORD_BITS - 1 - word.leading_zeros() as usize
//! }
//! ```
//!
//! `word == 0` computes `64 - 1 - 64`. Its two callers test `!= 0` first;
//! nothing in the signature says they must. [`highest_set_index`] is this with
//! the zero case decided.
//!
//! **`crates/trust-js-sem/src/bigint.rs:472-477`** — the zero case making a
//! *safety cap* vacuous rather than panicking:
//!
//! ```text
//! let per_digit = 64 - (u64::from(radix) - 1).leading_zeros();
//! if (digits.len() as u64).saturating_mul(u64::from(per_digit)) > MAX_BITS {
//! ```
//!
//! `radix == 1` gives `0u64.leading_zeros() == 64`, so `per_digit == 0`, the
//! product is `0`, and the allocation guard silently never fires.
//!
//! # The convention this crate is built on
//!
//! * **The word is `u32`, and every index is a `u32` that may be anything.**
//!   `weight(40)`, `mask_below(99)`, `field(x, 32, 8)` are all defined. There
//!   are no preconditions, because a `requires` clause is fatal under the
//!   strict lane (`docs/STRICT_VERIFICATION_FRAGMENT.md` §3) — and because a
//!   precondition is exactly the thing every site above already has and does
//!   not check.
//! * **Out-of-range answers are sentinels one past the value space**, per
//!   §1.4: [`weight`] returns `0` (no bit has weight zero),
//!   [`leading_zeros_u32`] and [`highest_set_index`] return `32` (no index is
//!   32), [`select_u8`] returns `8` and [`select_u32`] returns `32`. A
//!   caller tests a value rather than
//!   handling a panic.
//! * **There is not one shift in this crate.** `>>` and `<<` are opaque to
//!   bundling (§2.4), so a function containing either cannot be called by any
//!   verified function at all. Powers of two come from [`weight`] — an ordered
//!   guard chain over constants — and the two places that genuinely need a
//!   shift use `/` and `%` by the weight, which is the same value.
//! * **No loops, no `wrapping_*`, no `unsafe`.** A `while … decreases` does
//!   not discharge (§3), and `wrapping_add` would pass by *deleting* the
//!   obligation rather than discharging it (§7.7).
//!
//! # Tiers
//!
//! * **Tier 1 — proved bound.** A grammar `ensures` clause the compiler
//!   checks. Nine functions: four predicates ([`bit`], [`is_power_of_two`],
//!   [`is_mask_low`], [`parity`]) at `ensures result <= 1`, two live clamps
//!   ([`clamp_width`], [`clamp_index`]), and three counting chains
//!   ([`nibble_ones`], [`leading_zeros_u8`], [`trailing_zeros_u8`]). Every one
//!   of these bodies is either an arithmetic-free ordered guard chain (§1.1
//!   shape A) or a single call to a helper whose return is *pinned* to two
//!   constants (§1.1 shape B, §9.3).
//!
//! * **Tier 2 — proved total.** No contract, every arithmetic obligation
//!   discharged. The `u32`-wide counting functions are here for a reason that
//!   is a property of the report and not of the domain: a 33-arm chain mints
//!   33 postcondition rows, and past ~29 return sites in one function the
//!   report stops *sealing* — `targo trust check` exits 2 having printed no
//!   `Gate:` line, no `Summary:` and no diagnostic naming anything (§9.2).
//!   The bound is therefore stated at byte width, where the chain is nine
//!   arms, and the `u32` twin is pinned by a unit test against
//!   `u32::leading_zeros`.
//!
//!   [`ones_u32`], [`rank_u32`], [`field`], [`deposit`], [`reverse_u32`] and
//!   the rounding functions are tier 2 for the §5 quality rule instead: their
//!   bounds are structural, so a contract over them would be a green row over
//!   a clamp that can never fire.
//!
//! # What is NOT claimed
//!
//! Proofs here cover panic-freedom and the stated bounds. They do **not**
//! cover whether the answer is right: swapping two coefficients in
//! [`reverse_u8`]'s weighted sum keeps the engine's peak at exactly `255*255`,
//! so every one of its 28 rows still proves while every reversal is wrong.
//! `scripts/trust_bits_strict_gate.sh` mutation H does exactly that, on
//! purpose, and asserts that the strict lane still passes at exit 0 with a
//! byte-identical kind split while four named unit tests go red.
//!
//! The unit tests are written against `u32::count_ones`, `leading_zeros`,
//! `trailing_zeros`, `reverse_bits`, `is_power_of_two`, `checked_shl` and
//! brute-force loops over bit positions — decision procedures written by
//! someone else, by a different method — and are exhaustive over all 256
//! bytes wherever a byte is the domain.

#![no_std]

// ---------------------------------------------------------------------------
// Section 0 — the two primitives everything else is built from.
//
// `bit_set` is arithmetic-free on purpose: it tests a mask and returns one of
// two constants, so it carries no obligation, composes into any caller, and —
// per `docs/STRICT_VERIFICATION_FRAGMENT.md` §9.3 — PINS its return, which is
// what lets the tier-1 predicates below discharge their clauses.
// ---------------------------------------------------------------------------

/// `1` when the bit of weight `w` is set in `x`, otherwise `0`.
///
/// `w` is a *weight* (a power of two), not an index; [`weight`] converts.
/// A `w` that is not a power of two answers "any of these bits is set", which
/// is well-defined and is what the mask spelling means anyway.
fn bit_set(x: u32, w: u32) -> u8 {
    if x & w == 0 {
        return 0;
    }
    1
}

/// `1` when bit `k` of `x` is set, `0` otherwise — including for `k >= 32`,
/// where [`weight`] is `0` and no bit is selected.
///
/// **Tier 1.** `ensures result <= 1` is checked. The body is a single call to
/// a helper whose return is pinned to `0` or `1`, which is §1.1 shape B.
pub fn bit(x: u32, k: u32) -> u8 ensures result <= 1 {
    raw_bit(x, k)
}

fn raw_bit(x: u32, k: u32) -> u8 {
    // The two constants are spelled out rather than delegated to `bit_set`.
    // Measured 2026-08-29: `bit_set(x, weight(k))` here — the same value, one
    // fewer statement — leaves `bit`'s clause UNKNOWN x2, because §9.3's
    // discriminator is whether the bundled body PINS its return, and a body
    // that is a bare CALL does not pin it even when the callee's own body
    // does. See `docs/STRICT_VERIFICATION_FRAGMENT.md` §12.4.
    if x & weight(k) == 0 {
        return 0;
    }
    1
}

// ---------------------------------------------------------------------------
// Section 1 — the shift replacements. Generated ordered guard chains; see
// `weight`, `mask_below`, `leading_zeros_u32`, `trailing_zeros_u32`,
// `highest_set_index`, `round_down_pow2`, `round_up_pow2` below.
// ---------------------------------------------------------------------------
/// `2^k` as a word, and `0` for `k >= 32`.
///
/// This is the total replacement for `1u32 << k`, which panics with
/// debug assertions on and masks the amount to `k % 32` without them —
/// so `1u32 << 32` is `1`, not `0`, and no diagnostic says so. Here the
/// out-of-range answer is `0`, one *below* every representable weight,
/// which makes it usable as an "empty" sentinel by [`field`] and
/// [`deposit`] rather than as an error nobody checks.
///
/// **Tier 2.** Arithmetic-free, so this body carries no obligation at
/// all; the property that matters is pinned by a unit test against
/// `1u32 << k` on the range where that shift is defined.
pub fn weight(k: u32) -> u32 {
    if k == 0 {
        return 1;
    }
    if k == 1 {
        return 2;
    }
    if k == 2 {
        return 4;
    }
    if k == 3 {
        return 8;
    }
    if k == 4 {
        return 16;
    }
    if k == 5 {
        return 32;
    }
    if k == 6 {
        return 64;
    }
    if k == 7 {
        return 128;
    }
    if k == 8 {
        return 256;
    }
    if k == 9 {
        return 512;
    }
    if k == 10 {
        return 1024;
    }
    if k == 11 {
        return 2048;
    }
    if k == 12 {
        return 4096;
    }
    if k == 13 {
        return 8192;
    }
    if k == 14 {
        return 16384;
    }
    if k == 15 {
        return 32768;
    }
    if k == 16 {
        return 65536;
    }
    if k == 17 {
        return 131072;
    }
    if k == 18 {
        return 262144;
    }
    if k == 19 {
        return 524288;
    }
    if k == 20 {
        return 1048576;
    }
    if k == 21 {
        return 2097152;
    }
    if k == 22 {
        return 4194304;
    }
    if k == 23 {
        return 8388608;
    }
    if k == 24 {
        return 16777216;
    }
    if k == 25 {
        return 33554432;
    }
    if k == 26 {
        return 67108864;
    }
    if k == 27 {
        return 134217728;
    }
    if k == 28 {
        return 268435456;
    }
    if k == 29 {
        return 536870912;
    }
    if k == 30 {
        return 1073741824;
    }
    if k == 31 {
        return 2147483648;
    }
    0
}

/// The mask of the low `k` bits, `2^k - 1`, saturating at the full word.
///
/// The total replacement for `(1u32 << k) - 1`, whose two failure modes
/// are the subject of `decode.rs:21`: at `k == 32` the shift is out of
/// range, and every `k > 32` is silently folded modulo the width.
/// Saturating is the right total extension because the mask of *at
/// least* 32 low bits of a 32-bit word is the whole word.
///
/// **Tier 2.** Arithmetic-free.
pub fn mask_below(k: u32) -> u32 {
    if k <= 0 {
        return 0;
    }
    if k <= 1 {
        return 1;
    }
    if k <= 2 {
        return 3;
    }
    if k <= 3 {
        return 7;
    }
    if k <= 4 {
        return 15;
    }
    if k <= 5 {
        return 31;
    }
    if k <= 6 {
        return 63;
    }
    if k <= 7 {
        return 127;
    }
    if k <= 8 {
        return 255;
    }
    if k <= 9 {
        return 511;
    }
    if k <= 10 {
        return 1023;
    }
    if k <= 11 {
        return 2047;
    }
    if k <= 12 {
        return 4095;
    }
    if k <= 13 {
        return 8191;
    }
    if k <= 14 {
        return 16383;
    }
    if k <= 15 {
        return 32767;
    }
    if k <= 16 {
        return 65535;
    }
    if k <= 17 {
        return 131071;
    }
    if k <= 18 {
        return 262143;
    }
    if k <= 19 {
        return 524287;
    }
    if k <= 20 {
        return 1048575;
    }
    if k <= 21 {
        return 2097151;
    }
    if k <= 22 {
        return 4194303;
    }
    if k <= 23 {
        return 8388607;
    }
    if k <= 24 {
        return 16777215;
    }
    if k <= 25 {
        return 33554431;
    }
    if k <= 26 {
        return 67108863;
    }
    if k <= 27 {
        return 134217727;
    }
    if k <= 28 {
        return 268435455;
    }
    if k <= 29 {
        return 536870911;
    }
    if k <= 30 {
        return 1073741823;
    }
    if k <= 31 {
        return 2147483647;
    }
    4294967295
}

/// Leading zeros of `x`, with `32` for `x == 0`.
///
/// Agrees with `u32::leading_zeros` everywhere. It is spelled out
/// because the answer `32` is what `bit_set.rs:1751`'s
/// `WORD_BITS - 1 - word.leading_zeros()` underflows on, and a caller
/// that has this function still has to test for it — see
/// [`highest_set_index`], which decides that case instead.
///
/// **Tier 2.** A 33-arm chain cannot carry a contract: 33 return sites
/// is past the ~29 at which the report stops sealing
/// (`docs/STRICT_VERIFICATION_FRAGMENT.md` §9.2). The `<= 32` bound is
/// stated at byte width by [`leading_zeros_u8`] instead.
pub fn leading_zeros_u32(x: u32) -> u32 {
    if x < 1 {
        return 32;
    }
    if x < 2 {
        return 31;
    }
    if x < 4 {
        return 30;
    }
    if x < 8 {
        return 29;
    }
    if x < 16 {
        return 28;
    }
    if x < 32 {
        return 27;
    }
    if x < 64 {
        return 26;
    }
    if x < 128 {
        return 25;
    }
    if x < 256 {
        return 24;
    }
    if x < 512 {
        return 23;
    }
    if x < 1024 {
        return 22;
    }
    if x < 2048 {
        return 21;
    }
    if x < 4096 {
        return 20;
    }
    if x < 8192 {
        return 19;
    }
    if x < 16384 {
        return 18;
    }
    if x < 32768 {
        return 17;
    }
    if x < 65536 {
        return 16;
    }
    if x < 131072 {
        return 15;
    }
    if x < 262144 {
        return 14;
    }
    if x < 524288 {
        return 13;
    }
    if x < 1048576 {
        return 12;
    }
    if x < 2097152 {
        return 11;
    }
    if x < 4194304 {
        return 10;
    }
    if x < 8388608 {
        return 9;
    }
    if x < 16777216 {
        return 8;
    }
    if x < 33554432 {
        return 7;
    }
    if x < 67108864 {
        return 6;
    }
    if x < 134217728 {
        return 5;
    }
    if x < 268435456 {
        return 4;
    }
    if x < 536870912 {
        return 3;
    }
    if x < 1073741824 {
        return 2;
    }
    if x < 2147483648 {
        return 1;
    }
    0
}

/// Trailing zeros of `x`, with `32` for `x == 0`.
///
/// **Tier 2**, for [`leading_zeros_u32`]'s reason.
pub fn trailing_zeros_u32(x: u32) -> u32 {
    if x & 1 != 0 {
        return 0;
    }
    if x & 2 != 0 {
        return 1;
    }
    if x & 4 != 0 {
        return 2;
    }
    if x & 8 != 0 {
        return 3;
    }
    if x & 16 != 0 {
        return 4;
    }
    if x & 32 != 0 {
        return 5;
    }
    if x & 64 != 0 {
        return 6;
    }
    if x & 128 != 0 {
        return 7;
    }
    if x & 256 != 0 {
        return 8;
    }
    if x & 512 != 0 {
        return 9;
    }
    if x & 1024 != 0 {
        return 10;
    }
    if x & 2048 != 0 {
        return 11;
    }
    if x & 4096 != 0 {
        return 12;
    }
    if x & 8192 != 0 {
        return 13;
    }
    if x & 16384 != 0 {
        return 14;
    }
    if x & 32768 != 0 {
        return 15;
    }
    if x & 65536 != 0 {
        return 16;
    }
    if x & 131072 != 0 {
        return 17;
    }
    if x & 262144 != 0 {
        return 18;
    }
    if x & 524288 != 0 {
        return 19;
    }
    if x & 1048576 != 0 {
        return 20;
    }
    if x & 2097152 != 0 {
        return 21;
    }
    if x & 4194304 != 0 {
        return 22;
    }
    if x & 8388608 != 0 {
        return 23;
    }
    if x & 16777216 != 0 {
        return 24;
    }
    if x & 33554432 != 0 {
        return 25;
    }
    if x & 67108864 != 0 {
        return 26;
    }
    if x & 134217728 != 0 {
        return 27;
    }
    if x & 268435456 != 0 {
        return 28;
    }
    if x & 536870912 != 0 {
        return 29;
    }
    if x & 1073741824 != 0 {
        return 30;
    }
    if x & 2147483648 != 0 {
        return 31;
    }
    32
}

/// Index of the highest set bit of `x`, and `32` when `x == 0`.
///
/// This is `compiler/rustc_index/src/bit_set.rs:1751` with its zero case
/// decided rather than assumed. That function is
///
/// ```text
/// fn max_bit(word: Word) -> usize {
///     WORD_BITS - 1 - word.leading_zeros() as usize
/// }
/// ```
///
/// and for `word == 0` it computes `64 - 1 - 64`, a `usize` underflow.
/// Both of today's callers happen to test `!= 0` first; nothing in the
/// signature, the body or a `debug_assert!` says they must. Returning
/// `32` — one past the top index, the sentinel discipline of
/// `docs/STRICT_VERIFICATION_FRAGMENT.md` §1.4 — makes the empty case a
/// value the caller can test rather than a subtraction that wraps.
///
/// **Tier 2**, for [`leading_zeros_u32`]'s reason.
pub fn highest_set_index(x: u32) -> u32 {
    if x < 1 {
        return 32;
    }
    if x < 2 {
        return 0;
    }
    if x < 4 {
        return 1;
    }
    if x < 8 {
        return 2;
    }
    if x < 16 {
        return 3;
    }
    if x < 32 {
        return 4;
    }
    if x < 64 {
        return 5;
    }
    if x < 128 {
        return 6;
    }
    if x < 256 {
        return 7;
    }
    if x < 512 {
        return 8;
    }
    if x < 1024 {
        return 9;
    }
    if x < 2048 {
        return 10;
    }
    if x < 4096 {
        return 11;
    }
    if x < 8192 {
        return 12;
    }
    if x < 16384 {
        return 13;
    }
    if x < 32768 {
        return 14;
    }
    if x < 65536 {
        return 15;
    }
    if x < 131072 {
        return 16;
    }
    if x < 262144 {
        return 17;
    }
    if x < 524288 {
        return 18;
    }
    if x < 1048576 {
        return 19;
    }
    if x < 2097152 {
        return 20;
    }
    if x < 4194304 {
        return 21;
    }
    if x < 8388608 {
        return 22;
    }
    if x < 16777216 {
        return 23;
    }
    if x < 33554432 {
        return 24;
    }
    if x < 67108864 {
        return 25;
    }
    if x < 134217728 {
        return 26;
    }
    if x < 268435456 {
        return 27;
    }
    if x < 536870912 {
        return 28;
    }
    if x < 1073741824 {
        return 29;
    }
    if x < 2147483648 {
        return 30;
    }
    31
}

/// The greatest power of two `<= x`, and `0` for `x == 0`.
///
/// **Tier 2**, for [`leading_zeros_u32`]'s reason.
pub fn round_down_pow2(x: u32) -> u32 {
    if x < 1 {
        return 0;
    }
    if x < 2 {
        return 1;
    }
    if x < 4 {
        return 2;
    }
    if x < 8 {
        return 4;
    }
    if x < 16 {
        return 8;
    }
    if x < 32 {
        return 16;
    }
    if x < 64 {
        return 32;
    }
    if x < 128 {
        return 64;
    }
    if x < 256 {
        return 128;
    }
    if x < 512 {
        return 256;
    }
    if x < 1024 {
        return 512;
    }
    if x < 2048 {
        return 1024;
    }
    if x < 4096 {
        return 2048;
    }
    if x < 8192 {
        return 4096;
    }
    if x < 16384 {
        return 8192;
    }
    if x < 32768 {
        return 16384;
    }
    if x < 65536 {
        return 32768;
    }
    if x < 131072 {
        return 65536;
    }
    if x < 262144 {
        return 131072;
    }
    if x < 524288 {
        return 262144;
    }
    if x < 1048576 {
        return 524288;
    }
    if x < 2097152 {
        return 1048576;
    }
    if x < 4194304 {
        return 2097152;
    }
    if x < 8388608 {
        return 4194304;
    }
    if x < 16777216 {
        return 8388608;
    }
    if x < 33554432 {
        return 16777216;
    }
    if x < 67108864 {
        return 33554432;
    }
    if x < 134217728 {
        return 67108864;
    }
    if x < 268435456 {
        return 134217728;
    }
    if x < 536870912 {
        return 268435456;
    }
    if x < 1073741824 {
        return 536870912;
    }
    if x < 2147483648 {
        return 1073741824;
    }
    2147483648
}

/// The least power of two `>= x`, as a `u64`. `round_up_pow2(0)` is `1`.
///
/// `u32::next_power_of_two` has no answer for `x > 2^31`: it panics with
/// debug assertions on and returns `0` without them.
/// `crates/trust-mir-extract/src/verifier_api.rs:2730` writes
///
/// ```text
/// let width = need.max(64).next_power_of_two().min(CAP);
/// if need > width {
///     return None;
/// }
/// ```
///
/// where the `.min(CAP)` and the `if` both run *after* the panic point,
/// so they guard the result and not the operation. Returning `u64`
/// makes `2^32` representable and deletes the fallible case from every
/// caller — the same signature move as
/// `trust-radix64::b64_encoded_len` (§8.7).
///
/// **Tier 2**, for [`leading_zeros_u32`]'s reason.
pub fn round_up_pow2(x: u32) -> u64 {
    if x <= 1 {
        return 1;
    }
    if x <= 2 {
        return 2;
    }
    if x <= 4 {
        return 4;
    }
    if x <= 8 {
        return 8;
    }
    if x <= 16 {
        return 16;
    }
    if x <= 32 {
        return 32;
    }
    if x <= 64 {
        return 64;
    }
    if x <= 128 {
        return 128;
    }
    if x <= 256 {
        return 256;
    }
    if x <= 512 {
        return 512;
    }
    if x <= 1024 {
        return 1024;
    }
    if x <= 2048 {
        return 2048;
    }
    if x <= 4096 {
        return 4096;
    }
    if x <= 8192 {
        return 8192;
    }
    if x <= 16384 {
        return 16384;
    }
    if x <= 32768 {
        return 32768;
    }
    if x <= 65536 {
        return 65536;
    }
    if x <= 131072 {
        return 131072;
    }
    if x <= 262144 {
        return 262144;
    }
    if x <= 524288 {
        return 524288;
    }
    if x <= 1048576 {
        return 1048576;
    }
    if x <= 2097152 {
        return 2097152;
    }
    if x <= 4194304 {
        return 4194304;
    }
    if x <= 8388608 {
        return 8388608;
    }
    if x <= 16777216 {
        return 16777216;
    }
    if x <= 33554432 {
        return 33554432;
    }
    if x <= 67108864 {
        return 67108864;
    }
    if x <= 134217728 {
        return 134217728;
    }
    if x <= 268435456 {
        return 268435456;
    }
    if x <= 536870912 {
        return 536870912;
    }
    if x <= 1073741824 {
        return 1073741824;
    }
    if x <= 2147483648 {
        return 2147483648;
    }
    4294967296
}

// -------------------------------------------------------------------------
// Section 2 — tier-1 predicates.
// 
// Each is `docs/STRICT_VERIFICATION_FRAGMENT.md` §1.1 shape B: a contracted
// wrapper whose whole body is one call to an uncontracted helper that
// returns only `0` or `1`. §9.3's rule is that the bound is carried by the
// callee PINNING its return, not by the callee carrying a clause — measured
// here, all four discharge with one postcondition row each.
// -------------------------------------------------------------------------

/// `1` when `x` is a power of two, `0` otherwise. `is_power_of_two(0)` is `0`.
///
/// **Tier 1.** `ensures result <= 1` is checked.
pub fn is_power_of_two(x: u32) -> u32 ensures result <= 1 {
    raw_is_power_of_two(x)
}

fn raw_is_power_of_two(x: u32) -> u32 {
    if x == 0 {
        return 0;
    }
    if x & (x - 1) == 0 {
        return 1;
    }
    0
}

/// `1` when `x` is a low-bit mask — that is, `x == 2^k - 1` for some `k`.
///
/// This is the predicate `mask_below`'s callers actually want and that no site
/// in the tree states: `decode.rs:21` builds such a mask and never asks
/// whether it built one. `0` and `u32::MAX` are both masks.
///
/// **Tier 1.** `ensures result <= 1` is checked.
pub fn is_mask_low(x: u32) -> u32 ensures result <= 1 {
    raw_is_mask_low(x)
}

fn raw_is_mask_low(x: u32) -> u32 {
    // The guard must be an INEQUALITY. Measured 2026-08-29: the equality
    // spelling `if x == 4294967295` leaves BOTH rows of the `x + 1` below
    // UNKNOWN, which then makes this helper unbundlable and raises the error
    // against `is_mask_low` instead (`docs/STRICT_VERIFICATION_FRAGMENT.md`
    // §12.3). `x > 4294967294` selects the same single value and proves 2/2.
    if x > 4294967294 {
        return 1;
    }
    let y: u32 = x + 1;
    if y & x == 0 {
        return 1;
    }
    0
}

/// `1` when `x` has an odd number of set bits.
///
/// **Tier 1.** `ensures result <= 1` is checked.
pub fn parity(x: u32) -> u32 ensures result <= 1 {
    raw_parity(x)
}

fn raw_parity(x: u32) -> u32 {
    // An XOR fold over 32 bit tests. Every operand is `0` or `1` and `^`
    // cannot overflow, so this body carries no obligation at all — and the
    // comparison at the end PINS the return, which is what `parity`'s clause
    // is discharged from.
    let f: u8 = bit_set(x, 1)
        ^ bit_set(x, 2)
        ^ bit_set(x, 4)
        ^ bit_set(x, 8)
        ^ bit_set(x, 16)
        ^ bit_set(x, 32)
        ^ bit_set(x, 64)
        ^ bit_set(x, 128)
        ^ bit_set(x, 256)
        ^ bit_set(x, 512)
        ^ bit_set(x, 1024)
        ^ bit_set(x, 2048)
        ^ bit_set(x, 4096)
        ^ bit_set(x, 8192)
        ^ bit_set(x, 16384)
        ^ bit_set(x, 32768)
        ^ bit_set(x, 65536)
        ^ bit_set(x, 131072)
        ^ bit_set(x, 262144)
        ^ bit_set(x, 524288)
        ^ bit_set(x, 1048576)
        ^ bit_set(x, 2097152)
        ^ bit_set(x, 4194304)
        ^ bit_set(x, 8388608)
        ^ bit_set(x, 16777216)
        ^ bit_set(x, 33554432)
        ^ bit_set(x, 67108864)
        ^ bit_set(x, 134217728)
        ^ bit_set(x, 268435456)
        ^ bit_set(x, 536870912)
        ^ bit_set(x, 1073741824)
        ^ bit_set(x, 2147483648);
    if f == 0 {
        return 0;
    }
    1
}

// -------------------------------------------------------------------------
// Section 3 — tier-1 clamps. Both are LIVE: reachable with an argument that
// makes the returned value differ from the argument, which is the §5
// condition for a contract to be worth stating at all.
// -------------------------------------------------------------------------

/// Clamp a requested field width to the width of the word.
///
/// The `w > 32` case is the one `spec_elab.rs:190` and
/// `callee_summaries.rs:1128` leave to the caller.
///
/// **Tier 1.** `ensures result <= 32` is checked, and the clamp fires.
pub fn clamp_width(w: u32) -> u32 ensures result <= 32 {
    if w > 32 {
        return 32;
    }
    w
}

/// Clamp a bit index to the highest index the word has.
///
/// **Tier 1.** `ensures result <= 31` is checked, and the clamp fires.
pub fn clamp_index(k: u32) -> u32 ensures result <= 31 {
    if k > 31 {
        return 31;
    }
    k
}

// -------------------------------------------------------------------------
// Section 4 — population count.
// 
// The shape is forced by a boundary measured for this crate and recorded as
// §12.1: a chain of widened `u8 -> u32` additions proves for at most NINE
// terms. Ten terms leaves the tenth add RUNTIME-CHECKED with an UNKNOWN
// hardened twin; sixteen stops lowering the body at all. It is a term count,
// not a peak (the peak here is 2040) and not an arity — sixteen parameters
// summed eight at a time proves 14/14.
// 
// So a 32-bit population count cannot be one 32-term sum. It is four groups
// of eight, each narrowed back to a `u8` by `narrow8` so that §2.1's
// widening exception re-supplies the range for the four-term total. This is
// §9.1's `narrow back between steps` rule reaching a fifth domain.
// -------------------------------------------------------------------------

fn sum8(b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8) -> u32 {
    (b0 as u32)
        + (b1 as u32)
        + (b2 as u32)
        + (b3 as u32)
        + (b4 as u32)
        + (b5 as u32)
        + (b6 as u32)
        + (b7 as u32)
}

fn sum4(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    (b0 as u32) + (b1 as u32) + (b2 as u32) + (b3 as u32)
}

/// `min(s, 8)`, as a `u8`.
///
/// Exact for every `s <= 8`, which is every `s` this crate produces. It exists
/// to get a group count back into a NARROW type without a truncating cast:
/// a `s as u8` would mint no obligation at all (§2.5) and would be the §4.6
/// hole. Nine return sites, no arithmetic.
fn narrow8(s: u32) -> u8 {
    if s < 1 {
        return 0;
    }
    if s < 2 {
        return 1;
    }
    if s < 3 {
        return 2;
    }
    if s < 4 {
        return 3;
    }
    if s < 5 {
        return 4;
    }
    if s < 6 {
        return 5;
    }
    if s < 7 {
        return 6;
    }
    if s < 8 {
        return 7;
    }
    8
}

/// The number of the eight given weights that are set in `x`, as a `u8`.
fn group_ones(x: u32, w0: u32, w1: u32, w2: u32, w3: u32, w4: u32, w5: u32, w6: u32, w7: u32) -> u8 {
    narrow8(sum8(bit_set(x, w0), bit_set(x, w1), bit_set(x, w2), bit_set(x, w3), bit_set(x, w4), bit_set(x, w5), bit_set(x, w6), bit_set(x, w7)))
}

/// The number of set bits among bits 0..=7 of `v`.
fn low8_ones(v: u32) -> u32 {
    sum8(bit_set(v, 1), bit_set(v, 2), bit_set(v, 4), bit_set(v, 8), bit_set(v, 16), bit_set(v, 32), bit_set(v, 64), bit_set(v, 128))
}

/// Population count of a byte. Agrees with `u8::count_ones`.
///
/// **Tier 2.** The `<= 8` bound is structural — a byte has eight bits — so a
/// contract over it would be a green row over a clamp that can never fire,
/// which §5 rules out. [`nibble_ones`] carries the bound that IS worth
/// stating, because four is not the width of anything here.
pub fn ones_u8(b: u8) -> u32 {
    low8_ones(b as u32)
}

/// Population count of a word. Agrees with `u32::count_ones`.
///
/// **Tier 2**, for [`ones_u8`]'s reason.
pub fn ones_u32(x: u32) -> u32 {
    sum4(
        group_ones(x, 1, 2, 4, 8, 16, 32, 64, 128),
        group_ones(x, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768),
        group_ones(x, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608),
        group_ones(x, 16777216, 33554432, 67108864, 134217728, 268435456, 536870912, 1073741824, 2147483648),
    )
}

/// Population count of the low four bits of `v`.
///
/// **Tier 1.** `ensures result <= 4` is checked — seventeen return sites,
/// seventeen discharged postcondition rows, §1.1 shape A. Unlike
/// [`ones_u8`]'s, this bound is not the width of the argument type, so a
/// wrong constant in any arm refutes it rather than merely being wrong.
pub fn nibble_ones(v: u32) -> u32 ensures result <= 4 {
    if v & 15 == 0 {
        return 0;
    }
    if v & 15 == 1 {
        return 1;
    }
    if v & 15 == 2 {
        return 1;
    }
    if v & 15 == 3 {
        return 2;
    }
    if v & 15 == 4 {
        return 1;
    }
    if v & 15 == 5 {
        return 2;
    }
    if v & 15 == 6 {
        return 2;
    }
    if v & 15 == 7 {
        return 3;
    }
    if v & 15 == 8 {
        return 1;
    }
    if v & 15 == 9 {
        return 2;
    }
    if v & 15 == 10 {
        return 2;
    }
    if v & 15 == 11 {
        return 3;
    }
    if v & 15 == 12 {
        return 2;
    }
    if v & 15 == 13 {
        return 3;
    }
    if v & 15 == 14 {
        return 3;
    }
    if v & 15 == 15 {
        return 4;
    }
    0
}

// -------------------------------------------------------------------------
// Section 5 — zero runs at byte width, where the bound is statable.
// -------------------------------------------------------------------------

/// Leading zeros of a byte, with `8` for `b == 0`. Agrees with
/// `u8::leading_zeros`.
///
/// **Tier 1.** `ensures result <= 8` is checked — nine return sites, nine
/// discharged postcondition rows, §1.1 shape A.
pub fn leading_zeros_u8(b: u8) -> u32 ensures result <= 8 {
    if b < 1 {
        return 8;
    }
    if b < 2 {
        return 7;
    }
    if b < 4 {
        return 6;
    }
    if b < 8 {
        return 5;
    }
    if b < 16 {
        return 4;
    }
    if b < 32 {
        return 3;
    }
    if b < 64 {
        return 2;
    }
    if b < 128 {
        return 1;
    }
    0
}

/// Trailing zeros of a byte, with `8` for `b == 0`. Agrees with
/// `u8::trailing_zeros`.
///
/// **Tier 1.** `ensures result <= 8` is checked.
pub fn trailing_zeros_u8(b: u8) -> u32 ensures result <= 8 {
    if b & 1 != 0 {
        return 0;
    }
    if b & 2 != 0 {
        return 1;
    }
    if b & 4 != 0 {
        return 2;
    }
    if b & 8 != 0 {
        return 3;
    }
    if b & 16 != 0 {
        return 4;
    }
    if b & 32 != 0 {
        return 5;
    }
    if b & 64 != 0 {
        return 6;
    }
    if b & 128 != 0 {
        return 7;
    }
    8
}

// -------------------------------------------------------------------------
// Section 6 — rank and select.
// 
// `rank` is a dispatcher: a mask, then a call. No arithmetic of its own, so
// it reports `[NO OBLIGATIONS]` and bundles its callee's Asserts (§11.6).
// -------------------------------------------------------------------------

/// The number of set bits of `x` strictly below index `k`.
///
/// Total in `k`: `rank_u32(x, 0)` is `0` and `rank_u32(x, 99)` is
/// `ones_u32(x)`.
///
/// **Tier 2.** Structurally bounded by 32.
pub fn rank_u32(x: u32, k: u32) -> u32 {
    ones_u32(x & mask_below(k))
}

/// The number of set bits of `b` strictly below index `k`.
///
/// **Tier 2.** Structurally bounded by 8.
pub fn rank_u8(b: u8, k: u32) -> u32 {
    low8_ones((b as u32) & mask_below(k))
}

/// The index of the `n`-th set bit of `b`, counting from zero, and `8` when
/// `b` has `n` or fewer set bits.
///
/// `8` is one past the top index — the §1.4 sentinel discipline — so a
/// caller tests the returned value instead of unwrapping an `Option`.
///
/// **Tier 2.** Arithmetic-free: eight comparisons of a rank against `n`.
pub fn select_u8(b: u8, n: u32) -> u32 {
    if rank_u8(b, 1) > n {
        return 0;
    }
    if rank_u8(b, 2) > n {
        return 1;
    }
    if rank_u8(b, 3) > n {
        return 2;
    }
    if rank_u8(b, 4) > n {
        return 3;
    }
    if rank_u8(b, 5) > n {
        return 4;
    }
    if rank_u8(b, 6) > n {
        return 5;
    }
    if rank_u8(b, 7) > n {
        return 6;
    }
    if rank_u8(b, 8) > n {
        return 7;
    }
    8
}

/// The index of the `n`-th set bit of `x`, counting from zero, and `32` when
/// `x` has `n` or fewer set bits.
///
/// **Tier 2.** Arithmetic-free: thirty-two comparisons of a rank against
/// `n`. Each arm bundles a two-level population count, so this one body
/// carries the crate's deepest bundle — measured, it costs nothing: adding
/// it moved the crate from 40 bodies to 41 with the row count, the kind
/// split and the wall-clock all unchanged (§12.7).
pub fn select_u32(x: u32, n: u32) -> u32 {
    if rank_u32(x, 1) > n {
        return 0;
    }
    if rank_u32(x, 2) > n {
        return 1;
    }
    if rank_u32(x, 3) > n {
        return 2;
    }
    if rank_u32(x, 4) > n {
        return 3;
    }
    if rank_u32(x, 5) > n {
        return 4;
    }
    if rank_u32(x, 6) > n {
        return 5;
    }
    if rank_u32(x, 7) > n {
        return 6;
    }
    if rank_u32(x, 8) > n {
        return 7;
    }
    if rank_u32(x, 9) > n {
        return 8;
    }
    if rank_u32(x, 10) > n {
        return 9;
    }
    if rank_u32(x, 11) > n {
        return 10;
    }
    if rank_u32(x, 12) > n {
        return 11;
    }
    if rank_u32(x, 13) > n {
        return 12;
    }
    if rank_u32(x, 14) > n {
        return 13;
    }
    if rank_u32(x, 15) > n {
        return 14;
    }
    if rank_u32(x, 16) > n {
        return 15;
    }
    if rank_u32(x, 17) > n {
        return 16;
    }
    if rank_u32(x, 18) > n {
        return 17;
    }
    if rank_u32(x, 19) > n {
        return 18;
    }
    if rank_u32(x, 20) > n {
        return 19;
    }
    if rank_u32(x, 21) > n {
        return 20;
    }
    if rank_u32(x, 22) > n {
        return 21;
    }
    if rank_u32(x, 23) > n {
        return 22;
    }
    if rank_u32(x, 24) > n {
        return 23;
    }
    if rank_u32(x, 25) > n {
        return 24;
    }
    if rank_u32(x, 26) > n {
        return 25;
    }
    if rank_u32(x, 27) > n {
        return 26;
    }
    if rank_u32(x, 28) > n {
        return 27;
    }
    if rank_u32(x, 29) > n {
        return 28;
    }
    if rank_u32(x, 30) > n {
        return 29;
    }
    if rank_u32(x, 31) > n {
        return 30;
    }
    if rank_u32(x, 32) > n {
        return 31;
    }
    32
}

// -------------------------------------------------------------------------
// Section 7 — bit-field extraction and insertion.
// 
// These are `decode.rs:21` with all three of its conditions decided. Both
// take the field as (`lo`, `width`) and both are defined for every value of
// both, including `lo >= 32` and `width > 32`.
// 
// `field` divides, and `/` is opaque to BUNDLING (§2.4, §7.2) — so no
// verified function in this crate may call it, and the weight lookups are
// inlined into its own body rather than hoisted into a wrapper. That is why
// there is no `field_at_index` convenience: it would fail to lower.
// -------------------------------------------------------------------------

/// The `width` bits of `x` starting at index `lo`, moved down to index 0.
///
/// * `lo >= 32` — the field starts at or past the top of the word: `0`.
/// * `width >= 32` — everything from `lo` up: `x / 2^lo`.
/// * `width == 0` — the empty field: `0`.
///
/// **Tier 2.** The bound depends on `width`, and a two-clause or
/// arithmetic-derived `ensures` is out of the fragment (§1.3, §11.2).
pub fn field(x: u32, lo: u32, width: u32) -> u32 {
    let d: u32 = weight(lo);
    let m: u32 = weight(width);
    if d == 0 {
        return 0;
    }
    let q: u32 = x / d;
    if m == 0 {
        return q;
    }
    q % m
}

/// `x` with the `width` bits at index `lo` replaced by the low `width` bits of
/// `value`.
///
/// Returns `x` unchanged when the field does not lie wholly inside the word,
/// i.e. when `lo >= 32` or `lo + min(width, 32) > 32`. Both guards are LIVE.
/// Refusing is the safe total extension; the alternative is a silently
/// truncated field, which is `decode.rs:21`'s failure written the other way
/// round.
///
/// **Tier 2.** Structurally a word.
pub fn deposit(x: u32, value: u32, lo: u32, width: u32) -> u32 {
    let d: u32 = weight(lo);
    let m: u32 = mask_below(width);
    if d == 0 {
        return x;
    }
    // `u32 x u32 -> u64` peaks at `(2^32-1)^2`, four billion inside `u64::MAX`
    // (§9.3). Widening is what supplies both operands their range; a mask on
    // an already-wide value supplies none (§9.4), which is why the mask is
    // applied BEFORE the cast.
    let hole: u64 = (m as u64) * (d as u64);
    if hole > 4294967295 {
        return x;
    }
    // `value & m <= m`, so `placed <= hole <= u32::MAX` and neither narrowing
    // cast below can truncate. That is an ARGUMENT, not a proved row — a
    // truncating cast mints no obligation at all (§2.5) — so it is pinned by
    // `deposit_replaces_exactly_the_field_and_nothing_else` instead. A second
    // `if placed > 4294967295` guard would look like evidence and be
    // implied by the one above, which is worse than saying this.
    let placed: u64 = ((value & m) as u64) * (d as u64);
    (x & !(hole as u32)) | (placed as u32)
}

// -------------------------------------------------------------------------
// Section 8 — bit reversal.
// 
// One weighted eight-term sum, used four times. Sixteen weighted terms in
// one body does not lower (§12.1), so the `u32` reversal is four byte
// reversals recombined with a FOUR-term sum at `u64` — where each `u32 as
// u64` operand carries `[0, 2^32-1]` and the peak is `7.2e16`, three orders
// of magnitude inside `u64::MAX`.
// -------------------------------------------------------------------------

fn rev8(b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8) -> u32 {
    (b0 as u32) * 128
        + (b1 as u32) * 64
        + (b2 as u32) * 32
        + (b3 as u32) * 16
        + (b4 as u32) * 8
        + (b5 as u32) * 4
        + (b6 as u32) * 2
        + (b7 as u32)
}

/// Byte 0 of `x` (bits 0..=7) with its bits reversed, as a value in
/// `[0, 255]`.
fn rev_byte0(x: u32) -> u32 {
    rev8(bit_set(x, 1), bit_set(x, 2), bit_set(x, 4), bit_set(x, 8), bit_set(x, 16), bit_set(x, 32), bit_set(x, 64), bit_set(x, 128))
}

/// Byte 1 of `x` (bits 8..=15) with its bits reversed, as a value in
/// `[0, 255]`.
fn rev_byte1(x: u32) -> u32 {
    rev8(bit_set(x, 256), bit_set(x, 512), bit_set(x, 1024), bit_set(x, 2048), bit_set(x, 4096), bit_set(x, 8192), bit_set(x, 16384), bit_set(x, 32768))
}

/// Byte 2 of `x` (bits 16..=23) with its bits reversed, as a value in
/// `[0, 255]`.
fn rev_byte2(x: u32) -> u32 {
    rev8(bit_set(x, 65536), bit_set(x, 131072), bit_set(x, 262144), bit_set(x, 524288), bit_set(x, 1048576), bit_set(x, 2097152), bit_set(x, 4194304), bit_set(x, 8388608))
}

/// Byte 3 of `x` (bits 24..=31) with its bits reversed, as a value in
/// `[0, 255]`.
fn rev_byte3(x: u32) -> u32 {
    rev8(bit_set(x, 16777216), bit_set(x, 33554432), bit_set(x, 67108864), bit_set(x, 134217728), bit_set(x, 268435456), bit_set(x, 536870912), bit_set(x, 1073741824), bit_set(x, 2147483648))
}

/// Bit reversal of a byte, as a value in `[0, 255]`. Agrees with
/// `u8::reverse_bits`.
///
/// **Tier 2.** The `<= 255` bound is structural.
pub fn reverse_u8(b: u8) -> u32 {
    rev_byte0(b as u32)
}

/// Bit reversal of a word, as a `u64` in `[0, 2^32-1]`. Agrees with
/// `u32::reverse_bits`.
///
/// The return type is `u64` because the four-term recombination is what proves
/// (§12.1); computing it at `u32` and casting would buy the proof with a
/// truncating cast, which mints no obligation at all (§2.5) and is the §4.6
/// hole. Widening the RESULT instead is the same signature move as
/// `trust-radix64::b64_encoded_len` (§8.7) — the value never exceeds
/// `u32::MAX`, and a unit test against `u32::reverse_bits` pins that.
///
/// **Tier 2.** Structurally a word.
pub fn reverse_u32(x: u32) -> u64 {
    (rev_byte0(x) as u64) * 16777216
        + (rev_byte1(x) as u64) * 65536
        + (rev_byte2(x) as u64) * 256
        + (rev_byte3(x) as u64)
}

// ---------------------------------------------------------------------------
// Tests.
//
// Proofs here cover panic-freedom and the stated bounds; they do NOT cover
// whether the answer is right (`docs/STRICT_VERIFICATION_FRAGMENT.md` §4.6).
// Every oracle below is either a `core` decision procedure written by someone
// else — `count_ones`, `leading_zeros`, `trailing_zeros`, `reverse_bits`,
// `is_power_of_two`, `checked_shl` — or a brute-force loop over bit positions
// that shares no code path with the function under test. Exhaustive over all
// 256 bytes wherever a byte is the domain.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// A deterministic spread of words: every single bit, every low and high
    /// mask, a set of hand-picked patterns, and a xorshift sweep. Built from
    /// shifts and literals only.
    fn words(mut f: impl FnMut(u32)) {
        let mut i: u32 = 0;
        while i < 32 {
            f(1u32 << i);
            f(u32::MAX >> i);
            f(u32::MAX << i);
            f((1u32 << i) - 1);
            i += 1;
        }
        let picks: [u32; 14] = [
            0, 1, 2, 3, 0x8000_0000, 0xFFFF_FFFF, 0x5555_5555, 0xAAAA_AAAA, 0x0F0F_0F0F,
            0xF0F0_F0F0, 0x1234_5678, 0xDEAD_BEEF, 0x8000_0001, 0x7FFF_FFFF,
        ];
        let mut p: usize = 0;
        while p < picks.len() {
            f(picks[p]);
            p += 1;
        }
        let mut s: u32 = 0x1234_5678;
        let mut n: u32 = 0;
        while n < 4000 {
            s ^= s << 13;
            s ^= s >> 17;
            s ^= s << 5;
            f(s);
            n += 1;
        }
    }

    /// Every byte.
    fn bytes(mut f: impl FnMut(u8)) {
        let mut b: u32 = 0;
        while b < 256 {
            f(b as u8);
            b += 1;
        }
    }

    /// Independent oracle for `field`, by bit position, with no shift of a
    /// variable amount anywhere and every index range-tested first.
    fn oracle_field(x: u32, lo: u32, width: u32) -> u32 {
        let mut r: u32 = 0;
        let mut i: u32 = 0;
        while i < 32 {
            if (i as u64) < (width as u64) {
                let src: u64 = (lo as u64) + (i as u64);
                if src < 32 && (x >> (src as u32)) & 1 == 1 {
                    r |= 1u32 << i;
                }
            }
            i += 1;
        }
        r
    }

    /// The field `[lo, lo+width)` lies wholly inside the word. Stated by
    /// counting index positions, not by redoing `deposit`'s multiply.
    fn field_fits(lo: u32, width: u32) -> bool {
        let w: u64 = if (width as u64) > 32 { 32 } else { width as u64 };
        (lo as u64) < 32 && (lo as u64) + w <= 32
    }

    // -- Section 1: the shift replacements ---------------------------------

    #[test]
    fn weight_and_mask_below_are_the_shifts_they_replace() {
        let mut k: u32 = 0;
        while k <= 40 {
            let want_w: u32 = if k < 32 { 1u32 << k } else { 0 };
            assert_eq!(weight(k), want_w, "weight({k})");
            let want_m: u32 = if k < 32 { (1u32 << k) - 1 } else { u32::MAX };
            assert_eq!(mask_below(k), want_m, "mask_below({k})");
            k += 1;
        }
        // The two cases the primitives exist for. `checked_shl` is `core`'s own
        // statement that the shift has no answer here.
        assert_eq!(1u32.checked_shl(32), None, "`1u32 << 32` is not defined");
        assert_eq!(1u32.checked_shl(33), None);
        assert_eq!(weight(32), 0, "one BELOW every representable weight");
        assert_eq!(weight(4_000_000_000), 0);
        assert_eq!(mask_below(32), u32::MAX, "at least 32 low bits of a word is the word");
        assert_eq!(mask_below(4_000_000_000), u32::MAX);
        // ...and `weight` really is one below every weight, which is what makes
        // it usable as `field`/`deposit`'s empty sentinel.
        let mut i: u32 = 0;
        while i < 32 {
            assert_ne!(weight(i), 0);
            i += 1;
        }
    }

    #[test]
    fn bit_reads_the_same_bit_a_shift_would_and_is_zero_past_the_word() {
        words(|x| {
            let mut k: u32 = 0;
            while k < 32 {
                assert_eq!(bit(x, k), ((x >> k) & 1) as u8, "bit({x:#x}, {k})");
                k += 1;
            }
            assert_eq!(bit(x, 32), 0, "no word has a bit 32");
            assert_eq!(bit(x, 99), 0);
            assert_eq!(bit(x, u32::MAX), 0);
        });
    }

    // -- Section 4/5: counting ---------------------------------------------

    #[test]
    fn ones_agrees_with_count_ones() {
        bytes(|b| {
            assert_eq!(ones_u8(b), b.count_ones(), "ones_u8({b})");
            assert_eq!(ones_u32(b as u32), (b as u32).count_ones());
        });
        words(|x| {
            assert_eq!(ones_u32(x), x.count_ones(), "ones_u32({x:#x})");
        });
    }

    #[test]
    fn nibble_ones_agrees_with_count_ones_of_the_low_nibble() {
        words(|x| {
            assert_eq!(nibble_ones(x), (x & 15).count_ones(), "nibble_ones({x:#x})");
        });
        let mut v: u32 = 0;
        while v < 16 {
            assert_eq!(nibble_ones(v), v.count_ones(), "nibble_ones({v})");
            v += 1;
        }
    }

    #[test]
    fn zero_runs_agree_with_core() {
        bytes(|b| {
            assert_eq!(leading_zeros_u8(b), b.leading_zeros(), "leading_zeros_u8({b})");
            assert_eq!(trailing_zeros_u8(b), b.trailing_zeros(), "trailing_zeros_u8({b})");
        });
        words(|x| {
            assert_eq!(leading_zeros_u32(x), x.leading_zeros(), "leading_zeros_u32({x:#x})");
            assert_eq!(trailing_zeros_u32(x), x.trailing_zeros(), "trailing_zeros_u32({x:#x})");
        });
        assert_eq!(leading_zeros_u8(0), 8);
        assert_eq!(trailing_zeros_u8(0), 8);
        assert_eq!(leading_zeros_u32(0), 32);
        assert_eq!(trailing_zeros_u32(0), 32);
    }

    #[test]
    fn highest_set_index_decides_the_case_max_bit_underflows_on() {
        // `compiler/rustc_index/src/bit_set.rs:1751` computes
        // `WORD_BITS - 1 - word.leading_zeros()`, which underflows at zero.
        assert_eq!(highest_set_index(0), 32, "one past the top index, not a wrap");
        words(|x| {
            if x != 0 {
                assert_eq!(highest_set_index(x), 31 - x.leading_zeros(), "highest_set_index({x:#x})");
                // ...and it really is the highest set bit.
                assert_eq!(bit(x, highest_set_index(x)), 1);
                let h = highest_set_index(x);
                if h < 31 {
                    assert_eq!(x >> (h + 1), 0, "nothing above it");
                }
            }
        });
    }

    // -- Section 2: predicates ---------------------------------------------

    #[test]
    fn power_of_two_predicates_agree_with_core() {
        words(|x| {
            assert_eq!(
                is_power_of_two(x),
                u32::from(x.is_power_of_two()),
                "is_power_of_two({x:#x})"
            );
            // A low mask is exactly a value whose successor is a power of two,
            // decided here by counting bits instead: `x` is `2^k - 1` iff its
            // set bits are the k lowest.
            let want_mask = x.count_ones() == 32 - x.leading_zeros();
            assert_eq!(is_mask_low(x), u32::from(want_mask), "is_mask_low({x:#x})");
            assert_eq!(parity(x), x.count_ones() % 2, "parity({x:#x})");
        });
        assert_eq!(is_power_of_two(0), 0);
        assert_eq!(is_mask_low(0), 1, "the empty mask is a mask");
        assert_eq!(is_mask_low(u32::MAX), 1, "and so is the full one");
        assert_eq!(parity(0), 0);
        assert_eq!(parity(u32::MAX), 0);
        assert_eq!(parity(1), 1);
    }

    // -- Section 1: rounding -----------------------------------------------

    #[test]
    fn rounding_brackets_the_input_and_covers_what_next_power_of_two_cannot() {
        words(|x| {
            let d = round_down_pow2(x);
            let u = round_up_pow2(x);
            if x == 0 {
                assert_eq!(d, 0, "no power of two is <= 0");
                assert_eq!(u, 1, "and 1 is the least that is >= 0");
            } else {
                assert!(d <= x, "round_down_pow2({x:#x}) = {d}");
                assert!(d.is_power_of_two());
                assert_eq!(d, 1u32 << (31 - x.leading_zeros()));
                assert!(u >= x as u64, "round_up_pow2({x:#x}) = {u}");
                assert!(u.is_power_of_two());
                assert!(u / 2 < x as u64, "and it is the LEAST such");
            }
        });
        // The half of the range `u32::next_power_of_two` has no answer for: it
        // panics with debug assertions on and returns 0 without them.
        assert_eq!(round_up_pow2(0x8000_0001), 4294967296);
        assert_eq!(round_up_pow2(u32::MAX), 4294967296);
        assert_eq!(round_up_pow2(0x8000_0000), 2147483648);
        assert_eq!(0x8000_0001u32.checked_next_power_of_two(), None);
    }

    // -- Section 7: field / deposit ----------------------------------------

    #[test]
    fn field_extracts_the_same_bits_as_a_guarded_shift_and_mask() {
        let xs: [u32; 8] = [
            0, 1, u32::MAX, 0xDEAD_BEEF, 0x1234_5678, 0xAAAA_AAAA, 0x8000_0001, 0x0F0F_0F0F,
        ];
        let mut i: usize = 0;
        while i < xs.len() {
            let x = xs[i];
            let mut lo: u32 = 0;
            while lo <= 35 {
                let mut wd: u32 = 0;
                while wd <= 35 {
                    assert_eq!(field(x, lo, wd), oracle_field(x, lo, wd), "field({x:#x}, {lo}, {wd})");
                    wd += 1;
                }
                lo += 1;
            }
            i += 1;
        }
        // The three conditions `decode.rs:21` leaves undischarged.
        assert_eq!(field(u32::MAX, 0, 32), u32::MAX, "a full-width field");
        assert_eq!(field(u32::MAX, 0, 99), u32::MAX, "a width past the word");
        assert_eq!(field(u32::MAX, 32, 8), 0, "a start past the word");
        assert_eq!(field(u32::MAX, 8, 0), 0, "the empty field");
    }

    #[test]
    fn deposit_replaces_exactly_the_field_and_nothing_else() {
        let xs: [u32; 4] = [0, u32::MAX, 0xDEAD_BEEF, 0x5555_5555];
        let vs: [u32; 4] = [0, 1, u32::MAX, 0x1234_5678];
        let mut i: usize = 0;
        while i < xs.len() {
            let mut j: usize = 0;
            while j < vs.len() {
                let (x, v) = (xs[i], vs[j]);
                let mut lo: u32 = 0;
                while lo <= 34 {
                    let mut wd: u32 = 0;
                    while wd <= 34 {
                        let got = deposit(x, v, lo, wd);
                        if field_fits(lo, wd) {
                            // The field now reads back as the low `wd` bits of `v`...
                            assert_eq!(
                                field(got, lo, wd),
                                oracle_field(v, 0, wd),
                                "deposit({x:#x}, {v:#x}, {lo}, {wd}) field"
                            );
                            // ...and every bit outside it is untouched.
                            let mut k: u32 = 0;
                            while k < 32 {
                                let inside = k >= lo && (k as u64) < (lo as u64) + (wd as u64);
                                if !inside {
                                    assert_eq!(
                                        (got >> k) & 1,
                                        (x >> k) & 1,
                                        "deposit({x:#x}, {v:#x}, {lo}, {wd}) moved bit {k}"
                                    );
                                }
                                k += 1;
                            }
                        } else {
                            assert_eq!(got, x, "deposit({x:#x}, {v:#x}, {lo}, {wd}) must refuse");
                        }
                        wd += 1;
                    }
                    lo += 1;
                }
                j += 1;
            }
            i += 1;
        }
        // Both refusal guards are LIVE and they refuse different arguments.
        assert_eq!(deposit(7, 1, 32, 4), 7, "lo past the word");
        assert_eq!(deposit(7, 1, 25, 8), 7, "the field runs off the top");
        assert_eq!(deposit(7, 0, 25, 8), 7, "...even with nothing to place");
        assert_eq!(deposit(0, 0xFF, 24, 8), 0xFF00_0000, "and it fits at 24");
    }

    // -- Section 8: reversal -----------------------------------------------

    #[test]
    fn reverse_agrees_with_core_reverse_bits() {
        bytes(|b| {
            assert_eq!(reverse_u8(b), b.reverse_bits() as u32, "reverse_u8({b})");
        });
        words(|x| {
            assert_eq!(reverse_u32(x), x.reverse_bits() as u64, "reverse_u32({x:#x})");
            // The u64 return never exceeds a word, which is the argument the
            // signature makes instead of a truncating cast.
            assert!(reverse_u32(x) <= u32::MAX as u64);
        });
        assert_eq!(reverse_u32(1), 0x8000_0000);
        assert_eq!(reverse_u32(0x8000_0000), 1);
    }

    // -- Section 6: rank / select ------------------------------------------

    #[test]
    fn rank_agrees_with_a_brute_force_count() {
        words(|x| {
            let mut k: u32 = 0;
            while k <= 34 {
                let mut want: u32 = 0;
                let mut i: u32 = 0;
                while i < 32 && i < k {
                    if (x >> i) & 1 == 1 {
                        want += 1;
                    }
                    i += 1;
                }
                assert_eq!(rank_u32(x, k), want, "rank_u32({x:#x}, {k})");
                k += 1;
            }
        });
        bytes(|b| {
            let mut k: u32 = 0;
            while k <= 10 {
                let mut want: u32 = 0;
                let mut i: u32 = 0;
                while i < 8 && i < k {
                    if (b >> i) & 1 == 1 {
                        want += 1;
                    }
                    i += 1;
                }
                assert_eq!(rank_u8(b, k), want, "rank_u8({b}, {k})");
                k += 1;
            }
        });
        words(|x| assert_eq!(rank_u32(x, 32), x.count_ones()));
        words(|x| assert_eq!(rank_u32(x, 0), 0));
    }

    #[test]
    fn rank_and_select_are_inverse_on_every_byte() {
        bytes(|b| {
            let mut n: u32 = 0;
            while n <= 9 {
                let got = select_u8(b, n);
                // Independent oracle: walk the bits and count.
                let mut seen: u32 = 0;
                let mut want: u32 = 8;
                let mut i: u32 = 0;
                while i < 8 {
                    if (b >> i) & 1 == 1 {
                        if seen == n {
                            want = i;
                            i = 8;
                            continue;
                        }
                        seen += 1;
                    }
                    i += 1;
                }
                assert_eq!(got, want, "select_u8({b}, {n})");
                if got < 8 {
                    assert_eq!(bit(b as u32, got), 1, "select must land on a SET bit");
                    assert_eq!(rank_u8(b, got), n, "and rank must invert it");
                } else {
                    assert!(b.count_ones() <= n, "8 means there is no n-th set bit");
                }
                n += 1;
            }
        });
    }

    #[test]
    fn select_u32_finds_the_nth_set_bit() {
        words(|x| {
            // Independent oracle: one walk over the bit positions, recorded in
            // order, with no rank anywhere.
            let mut pos: [u32; 32] = [32; 32];
            let mut c: usize = 0;
            let mut i: u32 = 0;
            while i < 32 {
                if (x >> i) & 1 == 1 {
                    pos[c] = i;
                    c += 1;
                }
                i += 1;
            }
            let mut n: u32 = 0;
            while n <= 33 {
                let want: u32 = if (n as usize) < c { pos[n as usize] } else { 32 };
                assert_eq!(select_u32(x, n), want, "select_u32({x:#x}, {n})");
                if want < 32 {
                    assert_eq!(bit(x, want), 1, "select must land on a SET bit");
                    assert_eq!(rank_u32(x, want), n, "and rank must invert it");
                }
                n += 1;
            }
        });
    }

    // -- The tier-1 bounds, and that every clamp can FIRE -------------------

    #[test]
    fn every_tier1_bound_holds_and_every_clamp_can_fire() {
        words(|x| {
            assert!(is_power_of_two(x) <= 1);
            assert!(is_mask_low(x) <= 1);
            assert!(parity(x) <= 1);
            assert!(nibble_ones(x) <= 4);
            assert!(clamp_width(x) <= 32);
            assert!(clamp_index(x) <= 31);
            let mut k: u32 = 0;
            while k <= 34 {
                assert!(bit(x, k) <= 1);
                k += 1;
            }
        });
        bytes(|b| {
            assert!(leading_zeros_u8(b) <= 8);
            assert!(trailing_zeros_u8(b) <= 8);
        });
        // A contract over a bound that cannot be reached is a green row with no
        // content (`docs/STRICT_VERIFICATION_FRAGMENT.md` §5). Both clamps here
        // are reachable with an argument that makes them clamp, and both
        // counting chains attain their stated maximum.
        assert_eq!(clamp_width(33), 32, "the width clamp FIRES");
        assert_eq!(clamp_width(u32::MAX), 32);
        assert_eq!(clamp_width(32), 32, "and is the identity at the boundary");
        assert_eq!(clamp_index(32), 31, "the index clamp FIRES");
        assert_eq!(clamp_index(31), 31);
        assert_eq!(nibble_ones(15), 4, "the <= 4 bound is attained");
        assert_eq!(leading_zeros_u8(0), 8, "the <= 8 bounds are attained");
        assert_eq!(trailing_zeros_u8(0), 8);
        assert_eq!(is_power_of_two(1), 1, "the <= 1 bounds are attained");
        assert_eq!(is_mask_low(1), 1);
        assert_eq!(parity(1), 1);
        assert_eq!(bit(1, 0), 1);
    }

    // -- The two widths, split by WHAT THE ORACLE IS ------------------------
    //
    // Measured 2026-08-29 by the gate's mutation H, which this split exists
    // for: swapping two coefficients in `rev8` moves `reverse_u8` and
    // `reverse_u32` TOGETHER, because both call `rev8`. A cross-width check on
    // reversal therefore cannot see the mutation at all, and the same is true
    // of popcount, rank and select — every one of those pairs shares its
    // arithmetic leaf. Only the zero runs are two genuinely separate chains.
    // Keeping them in one test made a green assertion look like evidence.

    /// The zero runs at the two widths are INDEPENDENT implementations: a
    /// nine-arm chain over a `u8` and a thirty-three-arm chain over a `u32`,
    /// sharing no code. A wrong constant in either is caught here.
    #[test]
    fn the_byte_and_word_zero_runs_are_two_independent_chains() {
        bytes(|b| {
            let x = b as u32;
            assert_eq!(leading_zeros_u8(b), leading_zeros_u32(x) - 24, "leading zeros of {b}");
            assert_eq!(
                trailing_zeros_u8(b),
                if b == 0 { 8 } else { trailing_zeros_u32(x) },
                "trailing zeros of {b}"
            );
        });
    }

    /// CONSISTENCY ONLY — this test derives its expectation from the code
    /// under test and cannot refute a wrong answer.
    ///
    /// `ones_u8`/`ones_u32` share `sum8` and `bit_set`; `rank_u8`/`rank_u32`
    /// share those again; `select_u8`/`select_u32` share the ranks; and
    /// `reverse_u8`/`reverse_u32` share `rev8`. Both sides of every assertion
    /// below therefore move together under any change to a shared leaf. It is
    /// kept because it does pin the two lanes' AGREEMENT — a byte handed to
    /// the word lane must give the byte lane's answer — and it is named so
    /// that its passing is never read as evidence of correctness.
    /// `trust_bits_strict_gate.sh` mutation H asserts that it still PASSES
    /// while `reverse_agrees_with_core_reverse_bits` goes red.
    #[test]
    fn the_byte_and_word_lanes_agree_consistency_only() {
        bytes(|b| {
            let x = b as u32;
            assert_eq!(ones_u8(b), ones_u32(x), "popcount");
            assert_eq!(reverse_u8(b) * 16777216, reverse_u32(x) as u32, "reversal");
            let mut k: u32 = 0;
            while k <= 8 {
                assert_eq!(rank_u8(b, k), rank_u32(x, k), "rank at {k}");
                k += 1;
            }
            let mut n: u32 = 0;
            while n <= 8 {
                let s8 = select_u8(b, n);
                let s32 = select_u32(x, n);
                assert_eq!(if s8 == 8 { 32 } else { s8 }, s32, "select at {n}");
                n += 1;
            }
        });
    }
}
