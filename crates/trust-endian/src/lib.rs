//! Total, verified byte-order (endian) word assembly for `no_std` Trust
//! components.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0
//!
//! # Why this crate exists, and who calls it
//!
//! Every binary reader in this tree assembles a machine word out of bytes that
//! arrived from outside, and then bounds the result by hand. Both halves are
//! open-coded, and both carry a side condition nothing discharges.
//!
//! **`crates/trust-js-sem/src/typedarray.rs:185`** — the `DataView` /
//! `TypedArray` element decoder, run on every typed-array read a JS program
//! performs:
//!
//! ```text
//! fn bytes_to_u64(b: &[u8], le: bool) -> u64 {
//!     let mut v: u64 = 0;
//!     if le {
//!         for (i, &byte) in b.iter().enumerate() {
//!             v |= u64::from(byte) << (8 * i);
//! ```
//!
//! `8 * i` is a shift amount on a `u64`. At `i == 8` it is `64`, and `<< 64`
//! is an arithmetic panic, not a wrap. Nothing in `bytes_to_u64` bounds `i`:
//! the slice is short *because* its two callers pass `elem.bytes()`, and the
//! only statement of that fact in the file is the prose on `read_element` at
//! line 212 — *"Panics never (caller guarantees `bi+size <= bytes.len()`)"*.
//! [`u64_le`] and [`u64_be`] are that loop unrolled to its eight real widths,
//! so there is no shift amount to bound and no loop to invert.
//!
//! **`crates/trust-cg-bridge/src/codegen_backend.rs:1930`** — object-file
//! readers, reaching the same value through a panic:
//!
//! ```text
//! u32::from_le_bytes(bytes[offset..offset + 4].try_into().expect("u32 should fit"))
//! ```
//!
//! That `expect` is a panic site standing in for an arithmetic fact — that a
//! four-byte window really is four bytes long. Taking the bytes **by value**
//! deletes it rather than proving it, exactly as `trust-utf`'s `u16` returns
//! delete the `u16::try_from(..).expect(..)` in the two JS reassemblers.
//! (This pair is test-support code; the shipping twins at
//! `crates/trust-cg-bridge/src/verify_output.rs:1616` spell the same thing with
//! `.ok()?` and are total already — for them the value is the bound, below.)
//!
//! **`crates/trust-vcgen/src/generate/assert_refutation.rs:1424`** — a
//! length-prefixed string reader, and the reason the tier-1 half of this crate
//! exists:
//!
//! ```text
//! let len = usize::from(u16::from_le_bytes([*bytes.get(i)?, *bytes.get(i + 1)?]));
//! i += 2;
//! out.push_str(core::str::from_utf8(bytes.get(i..i + len)?).ok()?);
//! ```
//!
//! A two-byte little-endian length read out of untrusted bytes and used
//! immediately as a slice bound. [`len16_le`] returns that value already
//! clamped to a capacity the caller names, as a *checked* proposition —
//! `ensures result <= cap` — so the bound is carried by the signature instead
//! of by whichever `?` happens to be downstream.
//! `crates/trust-cg-bridge/src/verify_output_trust_ir.rs:2069` is the 64-bit
//! twin: a `__text` section size read from a Mach-O header and cast straight to
//! `usize`; [`len64_le`] is that read with the capacity applied at the source.
//!
//! Both endiannesses are here because the readers need both:
//! `crates/trust-symex/src/byte_encoding.rs:294` and `:308` dispatch `u32` and
//! `u64` loads on an `Endian`, and `crates/trust-lift/src/binary.rs:1324`
//! reads an ELF `e_machine` through whichever one `EI_DATA` selected.
//!
//! # Totality
//!
//! Every function here is **total** — defined on all inputs, with no panicking
//! path. A precondition is not available under the strict lane (both spellings
//! of `requires` are recorded `[ASSUMED] assumption:requires ... unsupported
//! MIR FullVerification::Precondition`, and an assumed row fails the gate), and
//! none is needed: taking bytes by value means there is no length to require.
//!
//! No sentinel is needed either, which is what distinguishes this crate from
//! its three siblings. Byte assembly is a **bijection** onto the target type —
//! every one of the 2^32 inputs to [`u32_le`] denotes exactly one `u32` — so
//! there is no rejecting input to report and no value space to sit one past.
//!
//! # Two tiers, marked per item
//!
//! **Tier 1 — proved bound.** A grammar `ensures` clause the compiler
//! discharges. The six `len*` functions; a caller may rely on the clause, and a
//! body that broke it would not compile.
//!
//! **Tier 2 — proved totality, bound carried by the return type.** The six
//! exact assemblers. What is proved is that the body cannot panic: no product
//! and no partial sum overflows, on any input. There is no `ensures` clause
//! because there is nothing left to say — `u32_le` is onto all of `u32`, so
//! `ensures result <= 4294967295` would be vacuous, and a vacuous clause is a
//! row that looks like evidence and is not.
//!
//! The overflow proofs are **tight, not slack**: `255 + 255*256` is exactly
//! `u16::MAX`, the four-term sum is exactly `u32::MAX`, and the eight-term sum
//! is exactly `u64::MAX`. Each is one increment away from failing, so none of
//! them is proved by a margin.
//!
//! # What is NOT proved here, and is pinned by tests instead
//!
//! **Byte order itself.** No obligation in this crate can see which byte got
//! which coefficient: swapping two of them leaves every product and every sum
//! in range, so the strict lane still returns exit 0 while the answers are
//! wrong. That is not a gap to be closed — it is what a safety obligation *is*.
//! `trust_endian_strict_gate.sh` mutation C performs exactly that swap and
//! watches the lane pass while the unit tests go red. The tests are therefore
//! part of the evidence, not a convenience: each assembler is checked against
//! `u16::from_le_bytes`, `u32::from_be_bytes`, ... — decision procedures in
//! `core`, written by someone else, by a different method — exhaustively at
//! 16 bits and over a structured plus pseudorandom sweep above it.
//!
//! # The measured fragment boundary
//!
//! See [`docs/STRICT_VERIFICATION_FRAGMENT.md`] for the full checklist. The
//! entries THIS crate established, measured 2026-08-29 on the authenticated
//! `targo trust check` lane at stage1 driver `dce70c497fba8fa5e`:
//!
//! [`docs/STRICT_VERIFICATION_FRAGMENT.md`]: ../../../docs/STRICT_VERIFICATION_FRAGMENT.md
//!
//! * **A bare widening `as` cast supplies a closed range — no guard needed.**
//!   Every assembler here is written with *no* intermediate guards at all, and
//!   all 88 of their rows prove. This does not contradict the guard-every-
//!   intermediate rule `trust-utf` established; it locates it. That rule is
//!   about *supplying a range to the interval engine*, and `b as u32` from a
//!   `u8` supplies `[0, 255]` by itself — the same mechanism as `(b & 15) as
//!   u32`, minus the mask. Where the operands are already narrow, widening is
//!   the whole technique and the guards are unnecessary.
//! * **A cast inside an `ensures` predicate is unparseable.** `ensures result
//!   >= b0 as u32` is a hard error — *"unsupported contract predicate
//!   expression"* and `SpecEnsuresUnparseable` — even though a bare parameter
//!   bound (`ensures result <= cap`) discharges and the identical cast in the
//!   *body* is fine. The predicate language is narrower than the body language.
//! * **A narrowing `as` cast in a callee is NOT composition-opaque**, unlike
//!   `>>`, `<<` and `/`. A contracted wrapper over a callee that widens to
//!   `u64`, guards, and casts back to `u32` discharges its bound.
//! * **Two `ensures` clauses discharge only with CONSTANT bounds.** The
//!   two-clause form `trust-utf` measured works on literals; the same body with
//!   *variable* bounds (`ensures result <= hi ensures result >= lo`) leaves the
//!   `trust-exact-source-clause-discharge` row and both per-branch
//!   postconditions UNKNOWN. `trust-ratio`'s one-sided `clamp_range` turns out
//!   to be at the boundary, not merely conservative.
//!
//! # A duplication that is forced, not accidental
//!
//! [`clamp_u32`](self) below is `trust-ratio`'s `clamp_upper`, re-declared.
//! That is not an oversight: **cross-crate composition does not work** — a call
//! into a verified sibling crate mints a fatal absent-callee row in the caller,
//! so a shared clamp cannot be depended on and must be re-proved in each crate
//! that composes from it. The cost is one duplicated four-line body per crate
//! and it is the reason all four of these crates are dependency-free.

#![no_std]

// ---------------------------------------------------------------------------
// Composition carriers.
//
// These are the only contract-carrying bodies in the crate; every tier-1 bound
// below is inherited from one of them. A contracted wrapper discharges its
// clause only when its callee ACTUALLY CARRIES a contract — the same wrapper
// over an uncontracted clamp measures UNKNOWN — which is why these exist as
// separate, contracted, private functions rather than as inline comparisons.
// ---------------------------------------------------------------------------

/// `v`, clamped from above by `hi`.
fn clamp_u32(v: u32, hi: u32) -> u32 ensures result <= hi {
    if v > hi { hi } else { v }
}

/// `v`, clamped from above by `hi`. The 64-bit twin of [`clamp_u32`].
fn clamp_u64(v: u64, hi: u64) -> u64 ensures result <= hi {
    if v > hi { hi } else { v }
}

// ---------------------------------------------------------------------------
// Tier 2 — exact assembly.
//
// `* 256` rather than `<< 8` is not a style choice. A shift is opaque to the
// composition that carries every tier-1 bound in this crate (a contracted
// wrapper over a callee containing `>>`, `<<` or `/` fails outright with
// "member has a guarded or non-entry-prefix Assert"), and multiplication by a
// power of two composes. `<<` is what all six caller sites use, and this is the
// one respelling that moves them into the fragment.
// ---------------------------------------------------------------------------

/// The `u16` whose little-endian byte serialisation is `[b0, b1]`.
///
/// **Tier 2.** Proved: neither the product nor the sum overflows `u16`, on
/// every input. The peak is `255 + 255 * 256 == 65535 == u16::MAX` exactly.
///
/// Equivalent to `u16::from_le_bytes([b0, b1])`, which
/// `u16_le_agrees_with_core` pins exhaustively over all 65536 inputs.
pub fn u16_le(b0: u8, b1: u8) -> u16 {
    b0 as u16 + (b1 as u16) * 256
}

/// The `u16` whose big-endian byte serialisation is `[b0, b1]`.
///
/// **Tier 2.** Peak `255 * 256 + 255 == 65535 == u16::MAX` exactly.
pub fn u16_be(b0: u8, b1: u8) -> u16 {
    (b0 as u16) * 256 + b1 as u16
}

/// The `u32` whose little-endian byte serialisation is `[b0, b1, b2, b3]`.
///
/// **Tier 2.** Proved: none of the three products and none of the three partial
/// sums overflows `u32`. The peak is exactly `u32::MAX`.
///
/// This is `crates/trust-cg-bridge/src/codegen_backend.rs:1930` without the
/// `try_into().expect("u32 should fit")` — the bytes arrive by value, so the
/// window length is a fact about the signature rather than a panic.
pub fn u32_le(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    // 256 = 2^8, 65536 = 2^16, 16777216 = 2^24.
    b0 as u32 + (b1 as u32) * 256 + (b2 as u32) * 65536 + (b3 as u32) * 16777216
}

/// The `u32` whose big-endian byte serialisation is `[b0, b1, b2, b3]`.
///
/// **Tier 2.** Peak exactly `u32::MAX`.
pub fn u32_be(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    (b0 as u32) * 16777216 + (b1 as u32) * 65536 + (b2 as u32) * 256 + b3 as u32
}

/// The `u64` whose little-endian byte serialisation is `[b0, ..., b7]`.
///
/// **Tier 2.** Proved: none of the seven products and none of the seven partial
/// sums overflows `u64`. The peak is exactly `u64::MAX`.
///
/// This is `crates/trust-js-sem/src/typedarray.rs:185`'s accumulation loop
/// unrolled. The loop's `<< (8 * i)` has an unbounded shift amount — `<< 64` is
/// a panic, and only a comment on the caller says `i < 8`. Unrolled, there is
/// no shift amount and no loop invariant to state.
pub fn u64_le(b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8) -> u64 {
    // 2^8, 2^16, 2^24, 2^32, 2^40, 2^48, 2^56.
    b0 as u64
        + (b1 as u64) * 256
        + (b2 as u64) * 65536
        + (b3 as u64) * 16777216
        + (b4 as u64) * 4294967296
        + (b5 as u64) * 1099511627776
        + (b6 as u64) * 281474976710656
        + (b7 as u64) * 72057594037927936
}

/// The `u64` whose big-endian byte serialisation is `[b0, ..., b7]`.
///
/// **Tier 2.** Peak exactly `u64::MAX`. This is the `else` arm of the same
/// loop, whose `v = (v << 8) | ..` form hides the identical hazard.
pub fn u64_be(b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8) -> u64 {
    (b0 as u64) * 72057594037927936
        + (b1 as u64) * 281474976710656
        + (b2 as u64) * 1099511627776
        + (b3 as u64) * 4294967296
        + (b4 as u64) * 16777216
        + (b5 as u64) * 65536
        + (b6 as u64) * 256
        + b7 as u64
}

// ---------------------------------------------------------------------------
// `u32`-valued 16-bit assembly.
//
// These exist because a cast in a CONTRACTED body is outside the fragment, so
// `clamp_u32(u16_le(b0, b1) as u32, cap)` cannot be written. The widened
// assembly has to be its own body. `wide16_le_agrees_with_u16_le` pins the two
// against each other over all 65536 inputs so the pair cannot drift.
// ---------------------------------------------------------------------------

fn wide16_le(b0: u8, b1: u8) -> u32 {
    b0 as u32 + (b1 as u32) * 256
}

fn wide16_be(b0: u8, b1: u8) -> u32 {
    (b0 as u32) * 256 + b1 as u32
}

// ---------------------------------------------------------------------------
// Tier 1 — bounded length-prefix reads.
//
// The clamp is LIVE in every one of these: a hostile two-byte prefix really is
// 65535 and a hostile eight-byte one really is u64::MAX, against a capacity
// that is whatever the caller's buffer holds. None of these wrappers contains
// dead code, which is the property that separates a proved bound from a body
// reshaped until the encoder accepted it.
// ---------------------------------------------------------------------------

/// A little-endian two-byte length prefix, clamped to `cap`.
///
/// **Tier 1.** `ensures result <= cap` is checked.
///
/// `crates/trust-vcgen/src/generate/assert_refutation.rs:1424` reads exactly
/// this value out of untrusted bytes and uses it as a slice bound on the next
/// line; here the bound is a checked proposition attached to the value.
pub fn len16_le(b0: u8, b1: u8, cap: u32) -> u32 ensures result <= cap {
    clamp_u32(wide16_le(b0, b1), cap)
}

/// A big-endian two-byte length prefix, clamped to `cap`.
///
/// **Tier 1.** `ensures result <= cap` is checked.
pub fn len16_be(b0: u8, b1: u8, cap: u32) -> u32 ensures result <= cap {
    clamp_u32(wide16_be(b0, b1), cap)
}

/// A little-endian four-byte length prefix, clamped to `cap`.
///
/// **Tier 1.** `ensures result <= cap` is checked.
pub fn len32_le(b0: u8, b1: u8, b2: u8, b3: u8, cap: u32) -> u32 ensures result <= cap {
    clamp_u32(u32_le(b0, b1, b2, b3), cap)
}

/// A big-endian four-byte length prefix, clamped to `cap`.
///
/// **Tier 1.** `ensures result <= cap` is checked.
pub fn len32_be(b0: u8, b1: u8, b2: u8, b3: u8, cap: u32) -> u32 ensures result <= cap {
    clamp_u32(u32_be(b0, b1, b2, b3), cap)
}

/// A little-endian eight-byte length or size field, clamped to `cap`.
///
/// **Tier 1.** `ensures result <= cap` is checked.
///
/// `crates/trust-cg-bridge/src/verify_output_trust_ir.rs:2069` reads a
/// `__text` section size out of a Mach-O header this way and casts it straight
/// to `usize`.
#[allow(clippy::too_many_arguments)]
pub fn len64_le(
    b0: u8,
    b1: u8,
    b2: u8,
    b3: u8,
    b4: u8,
    b5: u8,
    b6: u8,
    b7: u8,
    cap: u64,
) -> u64 ensures result <= cap {
    clamp_u64(u64_le(b0, b1, b2, b3, b4, b5, b6, b7), cap)
}

/// A big-endian eight-byte length or size field, clamped to `cap`.
///
/// **Tier 1.** `ensures result <= cap` is checked.
#[allow(clippy::too_many_arguments)]
pub fn len64_be(
    b0: u8,
    b1: u8,
    b2: u8,
    b3: u8,
    b4: u8,
    b5: u8,
    b6: u8,
    b7: u8,
    cap: u64,
) -> u64 ensures result <= cap {
    clamp_u64(u64_be(b0, b1, b2, b3, b4, b5, b6, b7), cap)
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::cmp::min;

    /// A deterministic 64-bit LCG (Knuth's MMIX constants), used to reach
    /// interior values no structured pattern would. Not cryptographic and not
    /// meant to be — it is here so the sweeps above 16 bits are reproducible
    /// and dependency-free.
    fn lcg(state: &mut u64) -> u64 {
        *state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        *state
    }

    /// Backgrounds for the per-position sweeps: both extremes, both sides of
    /// the sign bit, and both neighbours of the top.
    const PATTERNS: [u8; 6] = [0x00, 0x01, 0x7f, 0x80, 0xfe, 0xff];

    // -- 16-bit: EXHAUSTIVE over the entire domain, against `core`.

    #[test]
    fn u16_assembly_agrees_with_core_over_every_input() {
        for b0 in 0..=255u8 {
            for b1 in 0..=255u8 {
                assert_eq!(u16_le(b0, b1), u16::from_le_bytes([b0, b1]), "le {b0},{b1}");
                assert_eq!(u16_be(b0, b1), u16::from_be_bytes([b0, b1]), "be {b0},{b1}");
            }
        }
    }

    /// The `u32`-valued 16-bit assemblers exist only because a cast in a
    /// contracted body is outside the fragment. They are a second copy of the
    /// same arithmetic, so they can drift from the exact ones while every proof
    /// stays green. Pin them over the whole domain.
    #[test]
    fn wide16_agrees_with_the_exact_assemblers_over_every_input() {
        for b0 in 0..=255u8 {
            for b1 in 0..=255u8 {
                assert_eq!(wide16_le(b0, b1), u32::from(u16_le(b0, b1)), "le {b0},{b1}");
                assert_eq!(wide16_be(b0, b1), u32::from(u16_be(b0, b1)), "be {b0},{b1}");
            }
        }
    }

    // -- 32- and 64-bit: every value in every byte position against six
    //    backgrounds, plus a pseudorandom interior sweep. Oracle is `core`.

    #[test]
    fn u32_assembly_agrees_with_core() {
        for pos in 0..4usize {
            for pat in PATTERNS {
                for v in 0..=255u8 {
                    let mut b = [pat; 4];
                    b[pos] = v;
                    assert_eq!(u32_le(b[0], b[1], b[2], b[3]), u32::from_le_bytes(b), "le {b:?}");
                    assert_eq!(u32_be(b[0], b[1], b[2], b[3]), u32::from_be_bytes(b), "be {b:?}");
                }
            }
        }
        let mut s = 0x1234_5678_9abc_def0u64;
        for _ in 0..200_000 {
            let r = lcg(&mut s);
            let b = [r as u8, (r >> 8) as u8, (r >> 16) as u8, (r >> 24) as u8];
            assert_eq!(u32_le(b[0], b[1], b[2], b[3]), u32::from_le_bytes(b), "le {b:?}");
            assert_eq!(u32_be(b[0], b[1], b[2], b[3]), u32::from_be_bytes(b), "be {b:?}");
        }
    }

    #[test]
    fn u64_assembly_agrees_with_core() {
        for pos in 0..8usize {
            for pat in PATTERNS {
                for v in 0..=255u8 {
                    let mut b = [pat; 8];
                    b[pos] = v;
                    let le = u64_le(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]);
                    let be = u64_be(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]);
                    assert_eq!(le, u64::from_le_bytes(b), "le {b:?}");
                    assert_eq!(be, u64::from_be_bytes(b), "be {b:?}");
                }
            }
        }
        let mut s = 0x0f1e_2d3c_4b5a_6978u64;
        for _ in 0..200_000 {
            let r = lcg(&mut s);
            let b = r.to_ne_bytes();
            let le = u64_le(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]);
            let be = u64_be(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]);
            assert_eq!(le, u64::from_le_bytes(b), "le {b:?}");
            assert_eq!(be, u64::from_be_bytes(b), "be {b:?}");
        }
    }

    /// A second, independent characterisation of the same twelve bodies: big
    /// endian is little endian read backwards. `core` is not consulted here, so
    /// a coefficient that is wrong in BOTH directions the same way — which the
    /// oracle tests above would catch only if `core` agreed — is caught twice.
    #[test]
    fn big_endian_is_little_endian_reversed() {
        for b0 in 0..=255u8 {
            for b1 in 0..=255u8 {
                assert_eq!(u16_le(b0, b1), u16_be(b1, b0), "{b0},{b1}");
            }
        }
        let mut s = 0xdead_beef_cafe_f00du64;
        for _ in 0..100_000 {
            let r = lcg(&mut s);
            let b = r.to_ne_bytes();
            assert_eq!(
                u32_le(b[0], b[1], b[2], b[3]),
                u32_be(b[3], b[2], b[1], b[0]),
                "u32 {b:?}"
            );
            assert_eq!(
                u64_le(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]),
                u64_be(b[7], b[6], b[5], b[4], b[3], b[2], b[1], b[0]),
                "u64 {b:?}"
            );
        }
    }

    /// The overflow proofs are claimed TIGHT — the peak of each sum is exactly
    /// the top of its type, not a bound with slack. That claim is only true if
    /// the extreme is actually reached, so reach it.
    #[test]
    fn assembly_reaches_both_extremes_of_its_type() {
        assert_eq!(u16_le(0, 0), 0);
        assert_eq!(u16_be(0, 0), 0);
        assert_eq!(u16_le(255, 255), u16::MAX);
        assert_eq!(u16_be(255, 255), u16::MAX);
        assert_eq!(u32_le(0, 0, 0, 0), 0);
        assert_eq!(u32_le(255, 255, 255, 255), u32::MAX);
        assert_eq!(u32_be(255, 255, 255, 255), u32::MAX);
        assert_eq!(u64_le(0, 0, 0, 0, 0, 0, 0, 0), 0);
        assert_eq!(u64_le(255, 255, 255, 255, 255, 255, 255, 255), u64::MAX);
        assert_eq!(u64_be(255, 255, 255, 255, 255, 255, 255, 255), u64::MAX);
    }

    // -- Tier 1: the bounded reads, against `core::cmp::min` as the oracle.

    #[test]
    fn len16_agrees_with_core_min_over_every_input() {
        for cap in [0u32, 1, 4, 100, 255, 256, 65534, 65535, u32::MAX] {
            for b0 in 0..=255u8 {
                for b1 in 0..=255u8 {
                    let le = u32::from(u16::from_le_bytes([b0, b1]));
                    let be = u32::from(u16::from_be_bytes([b0, b1]));
                    assert_eq!(len16_le(b0, b1, cap), min(le, cap), "le {b0},{b1},{cap}");
                    assert_eq!(len16_be(b0, b1, cap), min(be, cap), "be {b0},{b1},{cap}");
                }
            }
        }
    }

    #[test]
    fn len32_agrees_with_core_min() {
        let mut s = 0x5151_2626_9797_3838u64;
        for cap in [0u32, 1, 1024, 65536, 0x7fff_ffff, 0x8000_0000, u32::MAX] {
            for pos in 0..4usize {
                for pat in PATTERNS {
                    for v in 0..=255u8 {
                        let mut b = [pat; 4];
                        b[pos] = v;
                        let le = u32::from_le_bytes(b);
                        let be = u32::from_be_bytes(b);
                        assert_eq!(len32_le(b[0], b[1], b[2], b[3], cap), min(le, cap), "le {b:?}");
                        assert_eq!(len32_be(b[0], b[1], b[2], b[3], cap), min(be, cap), "be {b:?}");
                    }
                }
            }
            for _ in 0..20_000 {
                let r = lcg(&mut s);
                let b = [r as u8, (r >> 8) as u8, (r >> 16) as u8, (r >> 24) as u8];
                let le = u32::from_le_bytes(b);
                let be = u32::from_be_bytes(b);
                assert_eq!(len32_le(b[0], b[1], b[2], b[3], cap), min(le, cap), "le {b:?}");
                assert_eq!(len32_be(b[0], b[1], b[2], b[3], cap), min(be, cap), "be {b:?}");
            }
        }
    }

    #[test]
    fn len64_agrees_with_core_min() {
        let mut s = 0x0a0b_0c0d_0e0f_1011u64;
        for cap in [0u64, 1, 4096, u64::from(u32::MAX), 1 << 63, u64::MAX] {
            for _ in 0..40_000 {
                let r = lcg(&mut s);
                let b = r.to_ne_bytes();
                let le = u64::from_le_bytes(b);
                let be = u64::from_be_bytes(b);
                let gle = len64_le(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7], cap);
                let gbe = len64_be(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7], cap);
                assert_eq!(gle, min(le, cap), "le {b:?} cap {cap}");
                assert_eq!(gbe, min(be, cap), "be {b:?} cap {cap}");
            }
        }
    }

    /// The `ensures result <= cap` clauses are checked by the compiler, but the
    /// clause is only worth having if the clamp can actually FIRE. A wrapper
    /// whose clamp is unreachable would carry the same green row while being
    /// dead code — the shape this crate deliberately avoids, and the reason no
    /// constant-bounded `u24_le` is offered. Pin both sides.
    #[test]
    fn the_clamp_is_live_in_both_directions() {
        // Clamped: the assembled value exceeds the capacity.
        assert_eq!(len16_le(255, 255, 100), 100);
        assert_eq!(len16_be(255, 255, 100), 100);
        assert_eq!(len32_le(255, 255, 255, 255, 1024), 1024);
        assert_eq!(len32_be(255, 255, 255, 255, 1024), 1024);
        assert_eq!(len64_le(255, 255, 255, 255, 255, 255, 255, 255, 4096), 4096);
        assert_eq!(len64_be(255, 255, 255, 255, 255, 255, 255, 255, 4096), 4096);
        // Passed through: the assembled value is within the capacity.
        assert_eq!(len16_le(4, 0, 100), 4);
        assert_eq!(len16_be(0, 4, 100), 4);
        assert_eq!(len32_le(7, 0, 0, 0, 1024), 7);
        assert_eq!(len32_be(0, 0, 0, 7, 1024), 7);
        assert_eq!(len64_le(9, 0, 0, 0, 0, 0, 0, 0, 4096), 9);
        assert_eq!(len64_be(0, 0, 0, 0, 0, 0, 0, 9, 4096), 9);
    }

    /// The tier-1 contract, restated as a runtime property over a sweep. The
    /// compiler checks it statically; this checks that the shipped behaviour
    /// and the checked proposition are about the same function.
    #[test]
    fn no_bounded_read_ever_exceeds_its_cap() {
        let mut s = 0x3141_5926_5358_9793u64;
        for _ in 0..100_000 {
            let r = lcg(&mut s);
            let b = r.to_ne_bytes();
            let cap32 = (lcg(&mut s) >> 32) as u32;
            let cap64 = lcg(&mut s);
            assert!(len16_le(b[0], b[1], cap32) <= cap32);
            assert!(len16_be(b[0], b[1], cap32) <= cap32);
            assert!(len32_le(b[0], b[1], b[2], b[3], cap32) <= cap32);
            assert!(len32_be(b[0], b[1], b[2], b[3], cap32) <= cap32);
            assert!(len64_le(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7], cap64) <= cap64);
            assert!(len64_be(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7], cap64) <= cap64);
        }
    }
}
