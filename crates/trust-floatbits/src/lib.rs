#![no_std]
//! IEEE-754 binary32/binary64 **field arithmetic over the raw bit pattern** —
//! the exponent and fraction field widths, the magnitude mask, the all-ones
//! (non-finite) exponent, and the bit pattern of an exact power of two.
//!
//! There is no `f32`/`f64` anywhere in this crate. Every function takes and
//! returns an integer, and the `to_bits`/`from_bits` reinterpretation stays in
//! the consumer. That is not a stylistic choice: it is what puts this domain
//! inside `docs/STRICT_VERIFICATION_FRAGMENT.md`'s measured boundary at all.
//!
//! # Why this crate exists: the bound is a HYPOTHESIS the solver is handed
//!
//! [`exp2_binary64_bits`] is `trust-vcgen`'s int→f64 cast magnitude bound. The
//! consumer reads:
//!
//! ```text
//! Some(Ty::Int { width, .. }) => {
//!     let bound = exp2i(*width)?;
//!     finite_outward(-bound, bound)
//! }
//! ```
//!
//! and that interval is then **conjoined onto float-overflow obligations as a
//! fact**. A bound that is too WIDE is sound and merely imprecise. A bound that
//! is too NARROW discharges a real overflow — it is a false hypothesis, and the
//! verdict goes green with nothing in the counts saying so. The original spelled
//! the whole derivation as one expression with three magic numbers in it:
//!
//! ```text
//! (w <= 1023).then(|| f64::from_bits((u64::from(w) + 1023) << 52))
//! ```
//!
//! `1023` is the binary64 exponent bias, `52` is its fraction field width, and
//! `1023` again is the largest exponent an exact power of two can carry. Each is
//! spelled once, unchecked, in the one direction where being wrong is a false
//! PROVE.
//!
//! The rest of the crate is the same three numbers and their binary32 twins
//! (`8`, `23`, `255`; `11`, `52`, `2047`), which `trust-vcgen`'s float-overflow
//! witness builder wrote out **three separate times** as ad-hoc tuple literals —
//! `(8, 23, …, 0xff)` / `(11, 52, …, 0x7ff)` in the Add/Sub arm, the Div arm,
//! and a fourth `(1u64 << mag_width) - 1` open-coded in the contract-hypothesis
//! builder. Four independent spellings of one table is four chances to disagree.
//!
//! # THE SENTINEL DIRECTION REVERSES INSIDE THIS CRATE
//!
//! `docs/STRICT_VERIFICATION_FRAGMENT.md` §16.1 and §17.4 record that the
//! saturation direction is decided by the CONSUMER's use, not by taste. This
//! crate carries both directions at once, and they are not interchangeable:
//!
//! | function | the answer is used as | so an out-of-domain input returns |
//! |---|---|---|
//! | [`exp2_binary64_bits`] | a magnitude BOUND conjoined onto a VC | [`BINARY64_POS_INF_BITS`] — the WIDE end. `f64::from_bits` of it is `+inf`, which the consumer's own `is_finite()` gate turns into a decline. Zero would be catastrophic: it is a bound of `0.0`, under which *every* cast is claimed non-overflowing. |
//! | every field width, mask and exponent accessor | a DECISION about a format | `0` — the narrow end. Nothing fits a zero-width field, so an unrecognised format builds no witness rather than a wrong one. |
//!
//! Because every accessor saturates, a caller cannot distinguish "unsupported"
//! from a legitimate answer by the value alone. [`format_supported`] and
//! [`exp2_binary64_supported`] exist for exactly that, and the consumer calls
//! them FIRST — the same mitigation `trust-intbound`'s `width_is_supported`
//! carries, for the same reason.
//!
//! # What is PROVED here, and what is only TESTED
//!
//! The clauses are constant bounds, and each was chosen for the wrong
//! implementation it EXCLUDES rather than for looking tight. Every doc comment
//! below names, explicitly, a wrong implementation its clause still admits —
//! because a clause you cannot state the counterexample to is a clause you have
//! not read. Those residual wrong answers are what the exhaustive oracle tests
//! are for, and `scripts/trust_floatbits_strict_gate.sh` watches a wrong-VALUE
//! mutation pass the strict lane at exit 0 while the named tests go red.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0


// Bootstrap rustc cannot parse Trust's native signature clauses, while the
// verified lane must retain those exact clause tokens. Each invocation below
// owns its function body once. Trust injects `cfg(trust_verify)` only while
// verification is active, selecting the native-clause expansion; an ordinary
// compiler emits the same function and body without the clauses. This is tied
// to the authenticated verification session, not to a forgeable compiler name.
#[cfg(trust_verify)]
macro_rules! trust_contract_fn {
    (
        $(#[$meta:meta])*
        $vis:vis fn $name:ident($($arg:ident : $arg_ty:ty),* $(,)?) -> $ret:ident
        clauses [$($clauses:tt)+]
        { $($body:tt)* }
    ) => {
        $(#[$meta])*
        $vis fn $name($($arg: $arg_ty),*) -> $ret
            $($clauses)+
        { $($body)* }
    };
}

#[cfg(not(trust_verify))]
macro_rules! trust_contract_fn {
    (
        $(#[$meta:meta])*
        $vis:vis fn $name:ident($($arg:ident : $arg_ty:ty),* $(,)?) -> $ret:ident
        clauses [$($clauses:tt)+]
        { $($body:tt)* }
    ) => {
        $(#[$meta])*
        $vis fn $name($($arg: $arg_ty),*) -> $ret { $($body)* }
    };
}

/// `0x7FF0_0000_0000_0000` — the binary64 bit pattern of `+inf`: sign clear,
/// exponent all ones, fraction zero. Also this crate's out-of-domain answer for
/// [`exp2_binary64_bits`], because it is the largest magnitude that exists and
/// every consumer of a magnitude bound already rejects a non-finite one.
pub const BINARY64_POS_INF_BITS: u64 = 9218868437227405312;

/// `0x3FF0_0000_0000_0000` — the binary64 bit pattern of `1.0`, i.e. `2^0`, the
/// SMALLEST value [`exp2_binary64_bits`] may ever return. The clause
/// `result >= BINARY64_ONE_BITS` is what rules out the whole zero/subnormal
/// half of the encoding, which is the false-hypothesis half.
pub const BINARY64_ONE_BITS: u64 = 4607182418800017408;

/// `0x7FFF_FFFF_FFFF_FFFF` — every binary64 bit except the sign.
pub const BINARY64_MAGNITUDE_MASK: u64 = 9223372036854775807;

/// `0x7FFF_FFFF` — every binary32 bit except the sign.
pub const BINARY32_MAGNITUDE_MASK: u32 = 2147483647;

/// The binary64 exponent bias, and equally the largest `w` for which `2^w` is a
/// finite binary64.
pub const BINARY64_EXPONENT_BIAS: u32 = 1023;

trust_contract_fn! {
/// `1` when `width` is a format this crate describes (32 or 64), `0` otherwise.
///
/// **Call this before any accessor below.** Each of them saturates to `0` on an
/// unrecognised width, and `0` is also a legitimate answer for none of them —
/// but a caller that skips this check reads "this format has a zero-bit
/// exponent field" as if it were a fact rather than a refusal.
///
/// **Clause `result <= 1`.** Rules out every non-boolean answer. It admits the
/// constant `0` (refuse everything — fail-closed, and visible immediately) and
/// the constant `1` (accept `f16`/`f128`, whose fabricated constants are exactly
/// the under-approximating witness `trust-vcgen`'s own doc says must never be
/// built). `format_supported_accepts_exactly_binary32_and_binary64` is
/// exhaustive over `0..=256` and rules out both.
#[must_use]
pub fn format_supported(width: u32) -> u32
clauses [ensures result <= 1]
{
    if width == 32 {
        return 1;
    }
    if width == 64 {
        return 1;
    }
    0
}
}

trust_contract_fn! {
/// The exponent field width of `width`-bit IEEE-754 binary interchange format:
/// 8 for binary32, 11 for binary64. `0` for anything else.
///
/// **Clause `result <= 11`.** The exponent field of a format this crate
/// describes is never wider than binary64's, and 11 is three bits inside the
/// smallest thing that would matter, so it is not the vacuous `u32` bound. It
/// rules out the transposed table (23/52 in this slot), every fabricated wider
/// format, and the `width - 1` spelling. It admits the constant `0`, and it
/// admits swapping 8 and 11 between the two formats;
/// `field_widths_match_core_float_constants` derives both from
/// `f32::MANTISSA_DIGITS`/`f64::MANTISSA_DIGITS` and the type sizes, which is an
/// oracle this crate does not participate in.
#[must_use]
pub fn exponent_field_width(width: u32) -> u32
clauses [ensures result <= 11]
{
    if width == 32 {
        return 8;
    }
    if width == 64 {
        return 11;
    }
    0
}
}

trust_contract_fn! {
/// The fraction (trailing significand) field width of `width`-bit IEEE-754
/// binary interchange format: 23 for binary32, 52 for binary64. `0` otherwise.
///
/// **Clause `result <= 52`.** Rules out the transposed table, every wider
/// fabricated format, and the whole-width spelling. It admits the constant `0`
/// and admits the two formats' values being swapped;
/// `field_widths_match_core_float_constants` is the oracle for both.
#[must_use]
pub fn fraction_field_width(width: u32) -> u32
clauses [ensures result <= 52]
{
    if width == 32 {
        return 23;
    }
    if width == 64 {
        return 52;
    }
    0
}
}

trust_contract_fn! {
/// The magnitude field width — everything but the sign bit: 31 for binary32,
/// 63 for binary64. `0` otherwise.
///
/// **Clause `result <= 63`.** This is the one clause here that is a real
/// soundness property rather than a table check: the consumer uses this number
/// as the WIDTH of a `Formula::BitVec` compared against a magnitude extraction,
/// and a value of 64 would put the SIGN BIT inside the magnitude — under which
/// every negative float compares as enormous and the overflow witness stops
/// firing. That is the under-approximating direction. It admits the constant
/// `0`, which is the fail-closed direction (a zero-width bitvector builds no
/// comparison at all), and `magnitude_field_width_is_the_format_minus_the_sign`
/// pins both values.
#[must_use]
pub fn magnitude_field_width(width: u32) -> u32
clauses [ensures result <= 63]
{
    if width == 32 {
        return 31;
    }
    if width == 64 {
        return 63;
    }
    0
}
}

trust_contract_fn! {
/// The magnitude mask of `width`-bit format, widened to `u64`: `2^31 - 1` for
/// binary32, `2^63 - 1` for binary64. `0` otherwise.
///
/// **Clause `result <= 9223372036854775807`.** `2^63 - 1` is precisely "the sign
/// bit is clear", and that is the property: a mask that keeps the sign bit lets
/// a negative operand's pattern through as its magnitude, which is the
/// under-approximating direction described on [`magnitude_field_width`]. It
/// admits the constant `0` (fail-closed: masks everything to zero, so no
/// witness), and it admits handing binary32 the binary64 mask —
/// `magnitude_masks_are_the_core_sign_bit_complement` derives both from
/// `f32::INFINITY ^ f32::NEG_INFINITY` rather than from any constant here.
#[must_use]
pub fn magnitude_mask(width: u32) -> u64
clauses [ensures result <= 9223372036854775807]
{
    if width == 32 {
        return 2147483647;
    }
    if width == 64 {
        return 9223372036854775807;
    }
    0
}
}

trust_contract_fn! {
/// The all-ones (non-finite) biased exponent of `width`-bit format: 255 for
/// binary32, 2047 for binary64. `0` otherwise.
///
/// This is the value a witness compares an operand's exponent field against to
/// say "this operand is finite".
///
/// **Clause `result <= 2047`.** Rules out every value that cannot be an
/// exponent field of a format this crate describes, and in particular the
/// off-by-one `2048`/`256` (one past all-ones), under which the finiteness
/// conjunct is unsatisfiable and the whole witness silently stops firing. It
/// admits the constant `0` and admits the two formats swapped;
/// `nonfinite_exponents_match_core_infinity_patterns` reads both off
/// `f32::INFINITY.to_bits()` / `f64::INFINITY.to_bits()`.
#[must_use]
pub fn nonfinite_exponent(width: u32) -> u32
clauses [ensures result <= 2047]
{
    if width == 32 {
        return 255;
    }
    if width == 64 {
        return 2047;
    }
    0
}
}

trust_contract_fn! {
/// `bits` with the sign bit cleared — the binary64 magnitude pattern.
///
/// **Clause `result <= 9223372036854775807`.** The sign bit is clear in the
/// result, for every input, which is the whole content of the operation. It
/// admits the constant `0` and admits masking with any narrower constant;
/// `binary64_magnitude_bits_matches_an_abs_oracle` compares against
/// `f64::from_bits(bits).abs().to_bits()` over every exponent and both signs.
#[must_use]
pub fn binary64_magnitude_bits(bits: u64) -> u64
clauses [ensures result <= 9223372036854775807]
{
    bits & 9223372036854775807
}
}

trust_contract_fn! {
/// The biased exponent field of a binary64 bit pattern: bits 52..=62.
///
/// **Clause `result <= 2047`.** The field is 11 bits wide, so this is exact
/// rather than a stand-in — a larger answer would mean bits outside the field
/// leaked in, which is the only way this function can be wrong in a direction
/// that matters (a leaked bit from the fraction or the sign makes a finite
/// value read as non-finite, or the reverse). It admits the constant `0` and
/// admits the wrong shift distance combined with a mask that happens to keep
/// the result in range; `binary64_biased_exponent_matches_a_powers_oracle`
/// walks every exponent value with a libm-computed operand.
#[must_use]
pub fn binary64_biased_exponent(bits: u64) -> u32
clauses [ensures result <= 2047]
{
    let raw = raw_biased_exponent(bits);
    if raw > 2047 {
        return 2047;
    }
    raw
}
}

/// The shift-and-mask alone. Exists to put the `>>` one call below the clause
/// on [`binary64_biased_exponent`] — a shift-derived local supplies no range to
/// its own body's clause (fragment map §17.2 for `/`, §13.3 for `*`), so the
/// operator moves down and the guarded clamp above discharges.
///
/// The clamp arm is UNREACHABLE (`(x >> 52) & 2047 <= 2047` for every `x`) and
/// returns `2047`, which is the fail-closed value here rather than the bound it
/// clamps to — `2047` is the NON-FINITE exponent, so a hypothetical leak reads
/// as "this operand may be inf/NaN" and the finiteness conjunct refuses it,
/// instead of reading as a small finite exponent and admitting a false bound.
/// See fragment map §17.3.
fn raw_biased_exponent(bits: u64) -> u32 {
    ((bits >> 52) & 2047) as u32
}

trust_contract_fn! {
/// `1` when `2^w` is an exact finite binary64 (`w <= 1023`), `0` otherwise.
///
/// **Call this before [`exp2_binary64_bits`].** That function saturates to
/// `+inf`'s pattern, which is a *legitimate* pattern; only this predicate
/// separates "the bound is `+inf`" from "there is no bound".
///
/// **Clause `result <= 1`.** Rules out every non-boolean answer. It admits the
/// constant `1` — which would claim `2^1024` is representable — and the constant
/// `0`, which refuses every cast bound and is the fail-closed direction.
/// `exp2_supported_is_exactly_the_finite_powers_of_two` is exhaustive over
/// `0..=2048` against a libm oracle.
#[must_use]
pub fn exp2_binary64_supported(w: u32) -> u32
clauses [ensures result <= 1]
{
    if w > 1023 {
        return 0;
    }
    1
}
}

trust_contract_fn! {
/// The binary64 bit pattern of `2^w` — the int→f64 cast magnitude bound.
/// [`BINARY64_POS_INF_BITS`] when `w > 1023`.
///
/// **This is the false-hypothesis site this crate was extracted for.** The
/// consumer conjoins `[-2^w, 2^w]` onto float-overflow obligations as a FACT, so
/// a value below the true `2^w` discharges a real overflow. The saturating
/// answer therefore points UP, at `+inf`, which the consumer's `is_finite()`
/// gate rejects — see the sentinel table in the module docs.
///
/// **Clauses `result <= 9218868437227405312` and
/// `result >= 4607182418800017408`.** Together they say: the sign bit is clear,
/// the pattern is never a NaN, and — the load-bearing half — the pattern is
/// never below `1.0`. That second clause excludes the entire zero-and-subnormal
/// region, which is where the catastrophic wrong answers live: a `0` return is
/// the magnitude bound `0.0`, under which *every* int→f64 cast is claimed
/// non-overflowing, and it is exactly what a dropped guard, a wrong shift
/// distance, or a missing bias produces.
///
/// **The wrong implementation both clauses still admit** is `BINARY64_ONE_BITS`
/// returned unconditionally — a bound of `1.0` for every width, which is
/// unsound for every `w >= 1`. No constant-bounded clause can exclude it,
/// because the honest property relates the result to `w` and the predicate
/// language takes a comparison against a constant or a bare parameter, not
/// against `2^w`. That residue is what
/// `exp2_binary64_bits_matches_a_libm_powers_oracle` is for — it is exhaustive
/// over `0..=2048` against `2.0f64.powi(..)`, a value this crate never computes
/// — and what the gate's wrong-value mutation demonstrates the lane cannot see.
#[must_use]
pub fn exp2_binary64_bits(w: u32) -> u64
clauses [ensures result <= 9218868437227405312 ensures result >= 4607182418800017408]
{
    if w > 1023 {
        return 9218868437227405312;
    }
    // The assembly is one call down, and both clamp arms return the FAIL-CLOSED
    // value (`+inf`'s pattern) rather than the bound they clamp to: too-small is
    // the unsound direction here, so a hypothetical arithmetic fault must not be
    // rounded UP into a plausible small bound. Fragment map §17.2 and §17.3.
    let raw = raw_exp2_bits(w);
    if raw > 9218868437227405312 {
        return 9218868437227405312;
    }
    if raw < 4607182418800017408 {
        return 9218868437227405312;
    }
    raw
}
}

/// The exponent-field assembly alone: bias `w` and shift it into place. Exists
/// to put the `+` and the `<<` one call below the clauses on
/// [`exp2_binary64_bits`].
///
/// **The widening must be spelled `w as u64`, NOT `u64::from(w)`, and the
/// difference is a refutation.** Measured while building this crate: the
/// `From` spelling makes the addend the return value of an unmodelled call, so
/// the range the widening was supposed to supply is lost entirely —
/// `unsupported MIR 'UnmodeledCalleeReturn': the obligation's verdict is the
/// return value of an unmodelled call (`_3`), which nothing in this body
/// constrains` — and the `+` overflow row is **refuted**, not merely left
/// unknown (`0 proved / 1 failed / 1 unknown of 5`). The `as` spelling is a MIR
/// `Cast` the encoder reads directly and proves all five. Note that
/// `clippy::cast_lossless` pushes authors toward the spelling that breaks the
/// proof. See fragment map §2.1 and §18.
fn raw_exp2_bits(w: u32) -> u64 {
    ((w as u64) + 1023) << 52
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `2^w` computed by REPEATED DOUBLING in floating point — no bit assembly,
    /// no exponent bias, no shift. This is the oracle for
    /// [`exp2_binary64_bits`], and it shares nothing with it but the IEEE
    /// semantics both are supposed to implement.
    fn oracle_exp2(w: u32) -> Option<f64> {
        let mut v = 1.0f64;
        for _ in 0..w {
            v *= 2.0;
            if !v.is_finite() {
                return None;
            }
        }
        Some(v)
    }

    /// The ORIGINAL body of `trust_vcgen::generate::float_range::exp2i`,
    /// transcribed verbatim from the pre-extraction source. The replacement must
    /// agree with it at every input.
    fn original_exp2i(w: u32) -> Option<f64> {
        (w <= 1023).then(|| f64::from_bits((u64::from(w) + 1023) << 52))
    }

    /// The composed replacement, exactly as the consumer now spells it.
    fn replacement_exp2i(w: u32) -> Option<f64> {
        (exp2_binary64_supported(w) == 1).then(|| f64::from_bits(exp2_binary64_bits(w)))
    }

    // -----------------------------------------------------------------------
    // exp2_binary64_bits — the false-hypothesis site
    // -----------------------------------------------------------------------

    #[test]
    fn exp2_binary64_bits_matches_a_libm_powers_oracle() {
        for w in 0..=2048u32 {
            let want = oracle_exp2(w);
            let got = replacement_exp2i(w);
            assert_eq!(
                got, want,
                "2^{w}: repeated-doubling oracle says {want:?}, this crate says {got:?}"
            );
        }
    }

    #[test]
    fn replaced_consumer_body_is_reproduced_exactly() {
        for w in 0..=2048u32 {
            assert_eq!(
                replacement_exp2i(w),
                original_exp2i(w),
                "2^{w}: the extraction changed what the consumer computes"
            );
        }
    }

    /// THE SENTINEL DIRECTION (§16.1, §17.4). Out of domain, the bound must
    /// saturate UP to a non-finite pattern, never down. A `0` here is the
    /// magnitude bound `0.0`, under which every int->f64 cast is claimed
    /// non-overflowing — the false-hypothesis direction this crate exists for.
    #[test]
    fn exp2_sentinel_is_the_wide_end_and_is_not_finite() {
        for w in [1024u32, 1025, 2047, 2048, 65535, u32::MAX] {
            let bits = exp2_binary64_bits(w);
            assert_eq!(bits, BINARY64_POS_INF_BITS, "w={w}: sentinel is not +inf's pattern");
            assert!(!f64::from_bits(bits).is_finite(), "w={w}: the sentinel is FINITE, so a consumer's is_finite() gate cannot fail-close on it");
            assert!(f64::from_bits(bits) > 0.0, "w={w}: the sentinel is not positive");
        }
    }

    /// The residue both clauses admit, ruled out by value. A constant `1.0`
    /// satisfies `result <= +inf` and `result >= 1.0` at every `w` and is
    /// unsound at every `w >= 1`.
    #[test]
    fn exp2_binary64_bits_is_not_the_constant_one() {
        assert_ne!(exp2_binary64_bits(1), BINARY64_ONE_BITS);
        assert_ne!(exp2_binary64_bits(64), BINARY64_ONE_BITS);
        assert_eq!(exp2_binary64_bits(0), BINARY64_ONE_BITS, "2^0 IS 1.0");
    }

    #[test]
    fn exp2_supported_is_exactly_the_finite_powers_of_two() {
        for w in 0..=2048u32 {
            let want = u32::from(oracle_exp2(w).is_some());
            assert_eq!(exp2_binary64_supported(w), want, "w={w}");
        }
        assert_eq!(exp2_binary64_supported(u32::MAX), 0);
    }

    // -----------------------------------------------------------------------
    // The format field table — oracles read off core's own float constants
    // -----------------------------------------------------------------------

    #[test]
    fn format_supported_accepts_exactly_binary32_and_binary64() {
        for width in 0..=256u32 {
            let want = u32::from(width == 32 || width == 64);
            assert_eq!(format_supported(width), want, "width={width}");
        }
        assert_eq!(format_supported(16), 0, "binary16 is deliberately not described");
        assert_eq!(format_supported(128), 0, "binary128 is deliberately not described");
    }

    #[test]
    fn field_widths_match_core_float_constants() {
        // MANTISSA_DIGITS counts the implicit leading bit; the STORED fraction
        // field is one narrower. The exponent field is whatever is left after
        // the sign and the fraction. Neither number is spelled in this crate.
        let f32_frac = f32::MANTISSA_DIGITS - 1;
        let f64_frac = f64::MANTISSA_DIGITS - 1;
        assert_eq!(fraction_field_width(32), f32_frac);
        assert_eq!(fraction_field_width(64), f64_frac);
        assert_eq!(exponent_field_width(32), 32 - 1 - f32_frac);
        assert_eq!(exponent_field_width(64), 64 - 1 - f64_frac);
        for width in 0..=256u32 {
            if width != 32 && width != 64 {
                assert_eq!(fraction_field_width(width), 0, "width={width}");
                assert_eq!(exponent_field_width(width), 0, "width={width}");
            }
        }
    }

    #[test]
    fn magnitude_field_width_is_the_format_minus_the_sign() {
        assert_eq!(magnitude_field_width(32), 31);
        assert_eq!(magnitude_field_width(64), 63);
        for width in 0..=256u32 {
            if width != 32 && width != 64 {
                assert_eq!(magnitude_field_width(width), 0, "width={width}");
            }
        }
    }

    #[test]
    fn magnitude_masks_are_the_core_sign_bit_complement() {
        // The sign bit is the ONLY bit differing between +inf and -inf, so its
        // complement is the magnitude mask. Derived from core, not from this
        // crate's constants.
        let sign32 = f32::INFINITY.to_bits() ^ f32::NEG_INFINITY.to_bits();
        let sign64 = f64::INFINITY.to_bits() ^ f64::NEG_INFINITY.to_bits();
        assert_eq!(magnitude_mask(32), u64::from(!sign32));
        assert_eq!(magnitude_mask(64), !sign64);
        assert_eq!(magnitude_mask(32), u64::from(BINARY32_MAGNITUDE_MASK));
        assert_eq!(magnitude_mask(64), BINARY64_MAGNITUDE_MASK);
        for width in 0..=256u32 {
            if width != 32 && width != 64 {
                assert_eq!(magnitude_mask(width), 0, "width={width}");
            }
        }
    }

    #[test]
    fn nonfinite_exponents_match_core_infinity_patterns() {
        // +inf is the all-ones exponent with a zero fraction, so shifting its
        // pattern down by the fraction width recovers the all-ones field.
        assert_eq!(nonfinite_exponent(32), f32::INFINITY.to_bits() >> (f32::MANTISSA_DIGITS - 1));
        assert_eq!(
            nonfinite_exponent(64),
            (f64::INFINITY.to_bits() >> (f64::MANTISSA_DIGITS - 1)) as u32
        );
        for width in 0..=256u32 {
            if width != 32 && width != 64 {
                assert_eq!(nonfinite_exponent(width), 0, "width={width}");
            }
        }
    }

    // -----------------------------------------------------------------------
    // Bit-pattern readers
    // -----------------------------------------------------------------------

    /// Bit patterns worth walking: every exponent value at both signs, plus the
    /// special patterns.
    fn interesting_binary64_bits() -> impl Iterator<Item = u64> {
        (0..2048u64)
            .flat_map(|e| [e << 52, (e << 52) | (1u64 << 63), (e << 52) | 0xF_FFFF_FFFF_FFFF])
            .chain([0, u64::MAX, 1, 1u64 << 63, f64::MAX.to_bits(), f64::MIN.to_bits()])
    }

    #[test]
    fn binary64_magnitude_bits_matches_an_abs_oracle() {
        for bits in interesting_binary64_bits() {
            let v = f64::from_bits(bits);
            // NaN's abs() is a NaN whose payload is unspecified, so compare the
            // patterns only where the value is a number.
            if v.is_nan() {
                assert_eq!(binary64_magnitude_bits(bits), bits & !(1u64 << 63));
                continue;
            }
            assert_eq!(
                binary64_magnitude_bits(bits),
                v.abs().to_bits(),
                "bits={bits:#x}: not the abs() pattern"
            );
        }
    }

    #[test]
    fn binary64_biased_exponent_matches_a_powers_oracle() {
        // For every exponent that a power of two occupies, the field read back
        // must be the biased exponent the doubling oracle implies.
        for w in 0..=1023u32 {
            let v = oracle_exp2(w).expect("2^w is finite for w <= 1023");
            assert_eq!(binary64_biased_exponent(v.to_bits()), w + 1023, "2^{w}");
        }
        assert_eq!(binary64_biased_exponent(f64::INFINITY.to_bits()), 2047);
        assert_eq!(binary64_biased_exponent(f64::NAN.to_bits()), 2047);
        assert_eq!(binary64_biased_exponent(0.0f64.to_bits()), 0);
        assert_eq!(binary64_biased_exponent((-0.0f64).to_bits()), 0, "the sign bit must not leak in");
        assert_eq!(binary64_biased_exponent(u64::MAX), 2047, "no bit outside the field may leak in");
        for bits in interesting_binary64_bits() {
            assert!(binary64_biased_exponent(bits) <= 2047, "bits={bits:#x}");
        }
    }

    /// The crate's own constants agree with core. A constant that drifts from
    /// what the clause literals say is the one skew a proof cannot see, because
    /// the clause and the body would both move together.
    #[test]
    fn crate_constants_agree_with_core() {
        assert_eq!(BINARY64_POS_INF_BITS, f64::INFINITY.to_bits());
        assert_eq!(BINARY64_ONE_BITS, 1.0f64.to_bits());
        assert_eq!(BINARY64_MAGNITUDE_MASK, !(f64::INFINITY.to_bits() ^ f64::NEG_INFINITY.to_bits()));
        assert_eq!(BINARY32_MAGNITUDE_MASK, !(f32::INFINITY.to_bits() ^ f32::NEG_INFINITY.to_bits()));
        assert_eq!(BINARY64_EXPONENT_BIAS, 1023);
    }
}
