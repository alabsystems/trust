//! Total, verified ASCII hex codec primitives for `no_std` Trust components.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0
//!
//! # Why this crate exists, and who calls it
//!
//! Every hex string this repo produces or consumes is built from two pieces of
//! open-coded arithmetic, and both carry a side condition nobody discharges.
//!
//! **Encode.** `crates/trust-types/src/digest.rs::lowercase_hex` — the function
//! under `stable_sha256_hex`, and so under most seal and manifest digests — is:
//!
//! ```text
//! const HEX: &[u8; 16] = b"0123456789abcdef";
//! encoded.push(HEX[usize::from(byte >> 4)] as char);
//! encoded.push(HEX[usize::from(byte & 0x0f)] as char);
//! ```
//!
//! That indexes a 16-entry table twice. Both indices are in range, and the
//! argument for it lives in the reader's head: `byte >> 4` and `byte & 0x0f` are
//! `u8` values below 16. [`low_nibble`] turns the second half of that argument
//! into a **checked proposition** — `ensures result <= 15`, discharged by the
//! compiler — so a caller indexing a 16-entry table has the bound rather than
//! the reasoning.
//!
//! **Decode.** `crates/trust-json/src/de.rs::decode_hex_escape`, which runs on
//! every `\uXXXX` in every JSON document Trust reads, is:
//!
//! ```text
//! b'0'..=b'9' => u16::from(b - b'0'),
//! b'a'..=b'f' => u16::from(b - b'a') + 10,
//! b'A'..=b'F' => u16::from(b - b'A') + 10,
//! ```
//!
//! Three `u8` subtractions, each safe only because a match arm above it
//! constrains the operand. Delete or widen an arm and the subtraction underflows
//! — a debug-build panic in a parser, reached from untrusted input.
//! [`hex_digit_value`] is that function with the non-underflow proved, and
//! [`hex_quad_value`] is the whole four-digit escape in one total call.
//!
//! **The `format!` sites cannot ever be verified.** `crates/trust-cache/src/`
//! `fingerprint.rs`, `crates/trust-proof-cert/src/proof_bundle.rs`,
//! `crates/trust-certify/src/lib.rs` and `crates/trust-js-trace/src/lib.rs` all
//! spell the same encoder as `format!("{b:02x}")`. That routes through
//! `core::fmt::Formatter`, whose `buf` is a `&mut dyn Write` — a vtable slot with
//! no body to encode, and therefore a measured, structural wall for this
//! verifier. Nibble arithmetic that goes through `fmt` can never be proved
//! panic-free; nibble arithmetic that goes through this crate already is.
//!
//! # Totality, and the sentinels that buy it
//!
//! Every function here is **total** — defined on all inputs, with no panicking
//! path — because a precondition is not available: both spellings of `requires`
//! are recorded as `[ASSUMED] assumption:requires ... unsupported MIR
//! FullVerification::Precondition`, and an assumed row fails the strict gate.
//!
//! Totality has a price on the decode side, and it is paid with a sentinel
//! rather than hidden: [`hex_digit_value`] returns `16` for a byte that is not a
//! hex digit, [`hex_pair_value`] returns `256`, [`hex_quad_value`] returns
//! `65536`. Each is one past the largest real result, which is why each function
//! can also carry `ensures result <= <that sentinel>`. Use [`is_hex_digit`], or
//! compare against the sentinel, before treating a result as a value.
//!
//! `Option<u8>` is the idiomatic alternative and it is **not** blocked here — it
//! was measured on this lane and verifies (2 obligations, both proved). It is
//! not used because an `Option` return cannot carry the range clause, and the
//! checked bound is the thing this crate exists to supply.
//!
//! On the encode side no sentinel is needed: [`lower_hex_digit`] and
//! [`upper_hex_digit`] take a whole byte and render its **low nibble**, so every
//! `u8` is a meaningful input and `lower_hex_digit(0xAB) == b'b'`.
//!
//! # Two tiers, marked per item
//!
//! **Tier 1 — proved bound.** A grammar `ensures` clause the compiler
//! discharges. A caller may rely on it; a body that broke it would not compile.
//!
//! **Tier 2 — proved totality, range by construction.** No contract. What is
//! proved is that the body cannot panic. [`high_nibble`] is the only one, and
//! the reason is recorded on it.
//!
//! # The measured fragment boundary
//!
//! Recorded because it is why the code is shaped this way, and because the
//! shapes below look interchangeable and are not. All measured 2026-08-29 on the
//! authenticated `targo trust check` lane, and reproduced across two separate
//! stage1 driver builds (`7b7fdb7dc` and `da0b15ad8`) with identical verdicts.
//!
//! * A grammar `ensures` is discharged and published in exactly two shapes:
//!   **(A)** an arithmetic-free body against a **constant** bound — `byte & 15`
//!   and `if v > 102 { 102 } else { v }` both qualify, `&` is not counted as
//!   arithmetic; and **(B)** a body that is a **single call** to a
//!   contract-carrying callee, with no arithmetic of its own. Every tier-1
//!   function here is one or the other.
//! * Shape (B) requires the callee to **carry a contract**. The same wrapper
//!   over an uncontracted callee measures UNKNOWN on both rows — which is why
//!   the `clamp*` helpers below have `ensures` clauses even though they are
//!   private and never appear in a signature a caller reads.
//! * With any of `+ - * / >> <<` or an index in the body, an extra
//!   `trust-exact-source-clause-discharge` row appears and returns UNKNOWN even
//!   when every per-branch postcondition VC is PROVED. That is what puts the
//!   arithmetic in the `raw_*` helpers rather than in the contracted wrappers.
//! * **`>>` cannot be hidden behind a helper, and neither can an index.** A
//!   contracted wrapper whose callee contains a shift fails outright with
//!   *"native typed-TrustIr lowering did not complete, so the panic-freedom of an
//!   unmodeled construct could not be established"* — the same refusal
//!   `trust-ratio` records for division. `+ - *`, casts and `&` compose fine.
//!   This is the sole reason [`high_nibble`] is tier 2, and the two ways of
//!   spelling it fail *differently*: `low_nibble(high_nibble(byte))` and
//!   `clamp15(high_nibble(byte))` hit the lowering refusal above, while moving
//!   the shift inline as `clamp15(byte >> 4)` lowers fine and instead leaves the
//!   `trust-exact-source-clause-discharge` row UNKNOWN. Neither publishes.
//! * **CORRECTED 2026-08-29 — "a parameter bound is not discharged" was two
//!   different facts wearing one sentence, and the bigger half was a
//!   REGRESSION, since fixed.** The original note read two controlled pairs as
//!   one rule. Re-measured after the `trust-certify` duplicate-conjunct fix,
//!   they disagree:
//!   * `if v > hi { hi } else { v }` against `result <= hi` **now discharges
//!     and publishes** — 2 of its 3 rows kernel-certified, exactly like its
//!     `if v > 15 { 15 } else { v }` / `result <= 15` twin. It stopped for one
//!     day because a duplicated hypothesis made ay revoke an UNSAT proof it had
//!     already computed; a constant bound closes in the closed-constant lane
//!     before ay is reached, which is the whole reason this crate never
//!     noticed. That is what had `trust-ratio` failing the lane it was written
//!     for, and it is closed.
//!   * `v & hi` against `result <= hi` **still does not**, and this half is a
//!     real capability gap rather than a publication one: the compiler reports
//!     `0 proved, 2 unknown` — it never proves the row at all — where `b & 15`
//!     against `result <= 15` proves both. A bitwise-AND upper bound by a
//!     VARIABLE mask is simply not in the fragment yet.
//!
//!   Every bound in this crate is a constant, so nothing here depends on
//!   either half; the distinction is recorded because reading them as one rule
//!   is what let a regression look like a design limit for a day.
//! * A `while ... decreases n` loop does **not** discharge: the measure row comes
//!   back *"non-termination: loop-decreases measure `n` may not decrease"*. There
//!   are no loops here.
//! * A **shared**-slice read behind a length guard proves its bounds obligation;
//!   a **mutable**-slice write behind the same guard does not. So there is no
//!   `encode_into(&mut [u8])` in this crate — the write would be the one
//!   unproved row in it.
//!
//! # One shape that was measured, verified, and deliberately NOT shipped
//!
//! [`high_nibble`] can be given a checked `ensures result <= 15` by writing it as
//! a sixteen-way comparison chain (`if byte >= 240 { 15 }` and so on down). That
//! is shape (A), it was measured, and it verifies — 16 obligations, all proved.
//!
//! It is not shipped. It replaces one instruction with sixteen comparisons in
//! the crate meant to sit under hot encoding loops, and it adds sixteen proved
//! rows that describe a body chosen to satisfy the encoder rather than to serve
//! the caller. This repo has already paid for that trade once: a `percent`
//! function reshaped to please the verifier passed every obligation it had and
//! returned `4` for `percent(42_949_673, 1)`. A proved row about a body nobody
//! would otherwise write is not evidence about the function anyone wants.

#![no_std]

// ---------------------------------------------------------------------------
// Constant-bound clamps. Private, and each carries a contract ON PURPOSE: the
// tier-1 wrappers below inherit their bounds from these postconditions, and the
// same wrappers over uncontracted clamps measure UNKNOWN. See the module note.
//
// Each clamp is a provable no-op on the value its caller passes — the `raw_*`
// helpers already return in range. It is the postcondition that is load-bearing,
// not the comparison; the `*_is_a_no_op` tests pin that the comparison never
// fires on a real input, so a clamp can never quietly mask a wrong `raw_*`.
// ---------------------------------------------------------------------------

fn clamp16(v: u8) -> u8 ensures result <= 16 {
    if v > 16 { 16 } else { v }
}

fn clamp70(v: u8) -> u8 ensures result <= 70 {
    if v > 70 { 70 } else { v }
}

fn clamp102(v: u8) -> u8 ensures result <= 102 {
    if v > 102 { 102 } else { v }
}

fn clamp256(v: u16) -> u16 ensures result <= 256 {
    if v > 256 { 256 } else { v }
}

fn clamp65536(v: u32) -> u32 ensures result <= 65536 {
    if v > 65536 { 65536 } else { v }
}

// ---------------------------------------------------------------------------
// Nibbles.
// ---------------------------------------------------------------------------

/// The low four bits of `byte`.
///
/// **Tier 1.** `ensures result <= 15` is checked — exactly the fact that makes
/// `HEX[usize::from(byte & 0x0f)]` an in-bounds index into a 16-entry table.
pub fn low_nibble(byte: u8) -> u8 ensures result <= 15 {
    byte & 15
}

/// The high four bits of `byte`.
///
/// **Tier 2.** Proved: the shift cannot overflow and cannot panic. Not proved,
/// and true by construction only: the result is in `0..=15`.
///
/// The bound is not a checked proposition here because `>>` is opaque to the
/// composition that carries every other bound in this crate — see the module
/// note, where the two measured alternatives and the reason for rejecting the
/// third are recorded. A caller that needs the bound as a *checked* fact can
/// write `low_nibble(high_nibble(byte))`, which is a free mask at runtime and
/// returns a value under [`low_nibble`]'s postcondition.
pub fn high_nibble(byte: u8) -> u8 {
    byte >> 4
}

// ---------------------------------------------------------------------------
// Encode: byte -> ASCII hex digit. Total on every `u8`; the low nibble is what
// is rendered, so there is no invalid input and no sentinel.
// ---------------------------------------------------------------------------

/// The low nibble of `byte` as a **lowercase** ASCII hex digit.
///
/// **Tier 1.** `ensures result <= 102` is checked — `102` is `b'f'`, the largest
/// byte this can return, and the clause is what makes "the output is ASCII" a
/// machine-checked fact rather than a comment.
///
/// `lower_hex_digit(0xAB) == b'b'`. To render a whole byte, call it twice:
/// `lower_hex_digit(high_nibble(b))` then `lower_hex_digit(b)`.
pub fn lower_hex_digit(byte: u8) -> u8 ensures result <= 102 {
    clamp102(raw_lower_hex_digit(byte))
}

/// The low nibble of `byte` as an **uppercase** ASCII hex digit.
///
/// **Tier 1.** `ensures result <= 70` is checked — `70` is `b'F'`.
pub fn upper_hex_digit(byte: u8) -> u8 ensures result <= 70 {
    clamp70(raw_upper_hex_digit(byte))
}

// ---------------------------------------------------------------------------
// Decode: ASCII -> value, with an explicit one-past-the-top sentinel.
// ---------------------------------------------------------------------------

/// The value of the hex digit `ascii`, or `16` if it is not one.
///
/// **Tier 1.** `ensures result <= 16` is checked, and each of the three
/// subtractions is proved not to underflow — the obligation
/// `decode_hex_escape`'s match arms discharge only by inspection.
///
/// Accepts `0-9`, `a-f` and `A-F`. Test with [`is_hex_digit`] or against `16`
/// before using the result as a value.
pub fn hex_digit_value(ascii: u8) -> u8 ensures result <= 16 {
    clamp16(raw_hex_digit_value(ascii))
}

/// Whether `ascii` is a hex digit in either case.
pub fn is_hex_digit(ascii: u8) -> bool {
    hex_digit_value(ascii) < 16
}

/// The byte spelled by the two hex digits `hi` then `lo`, or `256` if either is
/// not a hex digit.
///
/// **Tier 1.** `ensures result <= 256` is checked, and the `hi * 16 + lo` is
/// proved not to overflow.
pub fn hex_pair_value(hi: u8, lo: u8) -> u16 ensures result <= 256 {
    clamp256(raw_hex_pair_value(hi, lo))
}

/// The 16-bit code unit spelled by four hex digits, or `65536` if any of them is
/// not a hex digit.
///
/// **Tier 1.** `ensures result <= 65536` is checked, and the arithmetic is
/// proved not to overflow.
///
/// This is `decode_hex_escape`'s whole job — the `\uXXXX` body — as one total
/// call, with the four subtractions underneath it proved rather than argued.
pub fn hex_quad_value(a: u8, b: u8, c: u8, d: u8) -> u32 ensures result <= 65536 {
    clamp65536(raw_hex_quad_value(a, b, c, d))
}

// ---------------------------------------------------------------------------
// Uncontracted arithmetic helpers. These exist so the tier-1 wrappers above can
// stay arithmetic-free; their own safety obligations are proved.
// ---------------------------------------------------------------------------

fn raw_lower_hex_digit(byte: u8) -> u8 {
    let n: u8 = byte & 15;
    if n > 9 {
        // n is in 10..=15, so this lands in 97..=102 (`a`..=`f`).
        return n + 87;
    }
    n + 48
}

fn raw_upper_hex_digit(byte: u8) -> u8 {
    let n: u8 = byte & 15;
    if n > 9 {
        // n is in 10..=15, so this lands in 65..=70 (`A`..=`F`).
        return n + 55;
    }
    n + 48
}

fn raw_hex_digit_value(ascii: u8) -> u8 {
    // Written as ordered half-open guards rather than a `match` with range
    // patterns: a match body measures UNKNOWN on this lane (4 rows), and the
    // guards make every subtraction's precondition syntactically local.
    if ascii < 48 {
        return 16;
    }
    if ascii < 58 {
        return ascii - 48;
    }
    if ascii < 65 {
        return 16;
    }
    if ascii < 71 {
        return ascii - 55;
    }
    if ascii < 97 {
        return 16;
    }
    if ascii < 103 {
        return ascii - 87;
    }
    16
}

fn raw_hex_pair_value(hi: u8, lo: u8) -> u16 {
    let h: u8 = hex_digit_value(hi);
    if h > 15 {
        return 256;
    }
    let l: u8 = hex_digit_value(lo);
    if l > 15 {
        return 256;
    }
    // Widened before the multiply, so the peak `15 * 16 + 15 == 255` is nowhere
    // near `u16::MAX` and the overflow row proves for every input. The other
    // order — multiply in `u8`, widen after — reads the same and would be a
    // truncating cast the verifier has nothing to say about.
    (h as u16) * 16 + (l as u16)
}

fn raw_hex_quad_value(a: u8, b: u8, c: u8, d: u8) -> u32 {
    let hi: u16 = hex_pair_value(a, b);
    if hi > 255 {
        return 65536;
    }
    let lo: u16 = hex_pair_value(c, d);
    if lo > 255 {
        return 65536;
    }
    (hi as u32) * 256 + (lo as u32)
}

#[cfg(test)]
mod tests {
    use super::*;

    const LOWER: &[u8; 16] = b"0123456789abcdef";
    const UPPER: &[u8; 16] = b"0123456789ABCDEF";

    // -- Value correctness. A proved safety obligation is not a proved
    // -- specification, so every function is checked against an independent
    // -- reference over its ENTIRE u8 domain, not on spot values.

    #[test]
    fn nibbles_match_the_bit_operations_they_replace() {
        for b in 0..=u8::MAX {
            assert_eq!(low_nibble(b), b & 0x0f, "low_nibble({b})");
            assert_eq!(high_nibble(b), b >> 4, "high_nibble({b})");
            // The composition the docs prescribe for a checked high-nibble bound
            // must not change the value.
            assert_eq!(low_nibble(high_nibble(b)), b >> 4, "checked high({b})");
        }
    }

    #[test]
    fn encode_matches_the_table_lookup_it_replaces() {
        for b in 0..=u8::MAX {
            let want_lower = LOWER[usize::from(b & 0x0f)];
            let want_upper = UPPER[usize::from(b & 0x0f)];
            assert_eq!(lower_hex_digit(b), want_lower, "lower_hex_digit({b})");
            assert_eq!(upper_hex_digit(b), want_upper, "upper_hex_digit({b})");
        }
    }

    #[test]
    fn encoding_a_whole_byte_reproduces_format_02x() {
        // The exact pair of pushes `digest.rs::lowercase_hex` performs.
        for b in 0..=u8::MAX {
            let hi = lower_hex_digit(high_nibble(b));
            let lo = lower_hex_digit(b);
            assert_eq!(hi, LOWER[usize::from(b >> 4)], "hi of {b}");
            assert_eq!(lo, LOWER[usize::from(b & 0x0f)], "lo of {b}");
        }
        assert_eq!(lower_hex_digit(high_nibble(0x00)), b'0');
        assert_eq!(lower_hex_digit(0x00), b'0');
        assert_eq!(lower_hex_digit(high_nibble(0xff)), b'f');
        assert_eq!(lower_hex_digit(0xff), b'f');
        assert_eq!(lower_hex_digit(high_nibble(0xa5)), b'a');
        assert_eq!(lower_hex_digit(0xa5), b'5');
    }

    #[test]
    fn decode_agrees_with_core_over_the_whole_domain() {
        for b in 0..=u8::MAX {
            let v = hex_digit_value(b);
            // `is_ascii_hexdigit` is an independent oracle from `core`.
            assert_eq!(is_hex_digit(b), b.is_ascii_hexdigit(), "is_hex_digit({b})");
            if b.is_ascii_hexdigit() {
                let want = u8::try_from(char::from(b).to_digit(16).expect("hex")).expect("<16");
                assert_eq!(v, want, "hex_digit_value({b})");
            } else {
                assert_eq!(v, 16, "hex_digit_value({b}) must be the sentinel");
            }
        }
    }

    #[test]
    fn decode_inverts_encode_on_both_cases() {
        for n in 0..=u8::MAX {
            assert_eq!(hex_digit_value(lower_hex_digit(n)), n & 0x0f, "lower {n}");
            assert_eq!(hex_digit_value(upper_hex_digit(n)), n & 0x0f, "upper {n}");
        }
    }

    #[test]
    fn hex_pair_covers_every_pair_of_bytes() {
        for hi in 0..=u8::MAX {
            for lo in 0..=u8::MAX {
                let got = hex_pair_value(hi, lo);
                if hi.is_ascii_hexdigit() && lo.is_ascii_hexdigit() {
                    let h = u16::from(hex_digit_value(hi));
                    let l = u16::from(hex_digit_value(lo));
                    assert_eq!(got, h * 16 + l, "hex_pair_value({hi},{lo})");
                    assert!(got <= 255, "a valid pair must fit in a byte");
                } else {
                    assert_eq!(got, 256, "hex_pair_value({hi},{lo}) must be the sentinel");
                }
            }
        }
        assert_eq!(hex_pair_value(b'f', b'f'), 255);
        assert_eq!(hex_pair_value(b'F', b'F'), 255);
        assert_eq!(hex_pair_value(b'0', b'0'), 0);
        assert_eq!(hex_pair_value(b'a', b'5'), 0xa5);
    }

    #[test]
    fn hex_quad_reproduces_the_json_unicode_escape() {
        // The cases `trust-json`'s `decode_hex_escape` is exercised on.
        assert_eq!(hex_quad_value(b'0', b'0', b'0', b'0'), 0x0000);
        assert_eq!(hex_quad_value(b'0', b'0', b'4', b'1'), 0x0041); // 'A'
        assert_eq!(hex_quad_value(b'2', b'0', b'a', b'c'), 0x20ac); // '€'
        assert_eq!(hex_quad_value(b'D', b'8', b'3', b'D'), 0xd83d); // lead surrogate
        assert_eq!(hex_quad_value(b'f', b'f', b'f', b'f'), 0xffff);
        assert_eq!(hex_quad_value(b'F', b'F', b'F', b'F'), 0xffff);
        // Mixed case is accepted, exactly as the parser's three arms do.
        assert_eq!(hex_quad_value(b'a', b'B', b'c', b'D'), 0xabcd);
        // One bad digit in any position poisons the whole escape.
        assert_eq!(hex_quad_value(b'g', b'0', b'0', b'0'), 65536);
        assert_eq!(hex_quad_value(b'0', b'g', b'0', b'0'), 65536);
        assert_eq!(hex_quad_value(b'0', b'0', b'g', b'0'), 65536);
        assert_eq!(hex_quad_value(b'0', b'0', b'0', b'g'), 65536);
        assert_eq!(hex_quad_value(b' ', b' ', b' ', b' '), 65536);
    }

    /// The three bytes that bracket each accepted run. An off-by-one in
    /// `raw_hex_digit_value`'s guards is invisible to every proof here — the
    /// subtraction would still not underflow — and shows up only as a wrong
    /// value, so it is pinned by hand.
    #[test]
    fn decode_boundaries_are_exact() {
        assert_eq!(hex_digit_value(b'/'), 16); // just below '0'
        assert_eq!(hex_digit_value(b'0'), 0);
        assert_eq!(hex_digit_value(b'9'), 9);
        assert_eq!(hex_digit_value(b':'), 16); // just above '9'
        assert_eq!(hex_digit_value(b'@'), 16); // just below 'A'
        assert_eq!(hex_digit_value(b'A'), 10);
        assert_eq!(hex_digit_value(b'F'), 15);
        assert_eq!(hex_digit_value(b'G'), 16); // just above 'F'
        assert_eq!(hex_digit_value(b'`'), 16); // just below 'a'
        assert_eq!(hex_digit_value(b'a'), 10);
        assert_eq!(hex_digit_value(b'f'), 15);
        assert_eq!(hex_digit_value(b'g'), 16); // just above 'f'
    }

    /// Every `clamp*` must be a NO-OP on every value its caller can hand it.
    ///
    /// This is the test that stops a clamp from laundering a wrong `raw_*`: the
    /// clamps exist to carry a postcondition, and if one ever actually fired it
    /// would be silently correcting a defect into a green proof.
    #[test]
    fn clamps_never_fire_on_a_real_input() {
        for b in 0..=u8::MAX {
            assert!(raw_lower_hex_digit(b) <= 102, "clamp102 would fire on {b}");
            assert!(raw_upper_hex_digit(b) <= 70, "clamp70 would fire on {b}");
            assert!(raw_hex_digit_value(b) <= 16, "clamp16 would fire on {b}");
        }
        for hi in 0..=u8::MAX {
            for lo in 0..=u8::MAX {
                assert!(raw_hex_pair_value(hi, lo) <= 256, "clamp256 on ({hi},{lo})");
            }
        }
        assert!(raw_hex_quad_value(b'f', b'f', b'f', b'f') <= 65536);
        assert!(raw_hex_quad_value(b'g', b'g', b'g', b'g') <= 65536);
    }

    /// The checked bounds, asserted at runtime as well.
    ///
    /// They are already discharged by the compiler, so this is not where they
    /// are established — it is a tripwire for the day someone edits a body and
    /// the contract silently stops being checked (a `requires`/`ensures` row
    /// that goes UNKNOWN does not change the value, so nothing else would say).
    #[test]
    fn the_contracted_bounds_hold_at_runtime_too() {
        for b in 0..=u8::MAX {
            assert!(low_nibble(b) <= 15);
            assert!(lower_hex_digit(b) <= 102);
            assert!(upper_hex_digit(b) <= 70);
            assert!(hex_digit_value(b) <= 16);
            // Tier 2: stated range, not a checked proposition.
            assert!(high_nibble(b) <= 15);
        }
        assert!(hex_pair_value(0, 0) <= 256);
        assert!(hex_quad_value(0, 0, 0, 0) <= 65536);
    }
}
