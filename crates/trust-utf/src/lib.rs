//! Total, verified UTF-8 and UTF-16 scalar arithmetic for `no_std` Trust
//! components.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0
//!
//! # Why this crate exists, and who calls it
//!
//! Three places in this tree reassemble a Unicode scalar out of smaller pieces,
//! on input that arrives from outside. All three are open-coded, and all three
//! carry a side condition that is discharged only by a range check somewhere
//! above them in the same function.
//!
//! **`crates/trust-json/src/de.rs:440`** — the `\uXXXX` reader, run on every
//! escape in every JSON document Trust parses:
//!
//! ```text
//! n1 @ 0xD800..=0xDBFF => {
//!     ...
//!     let n = ((u32::from(n1 - 0xD800) << 10) | u32::from(n2 - 0xDC00)) + 0x1_0000;
//! ```
//!
//! Two `u16` subtractions. `n1 - 0xD800` cannot underflow *because a range
//! pattern twenty lines up says so*, and `n2 - 0xDC00` because of an
//! `if !(0xDC00..=0xDFFF).contains(&n2)` guard. Widen either range and the
//! subtraction underflows — a debug-build panic in a parser, reachable from a
//! string literal. [`combine_surrogates`] is that expression with the
//! non-underflow proved and the result's range checked.
//!
//! **`crates/trust-js-interp/src/builtins_uri.rs:124`** — `decodeURIComponent`,
//! accumulating a scalar out of UTF-8 continuation bytes and then splitting it
//! back into a surrogate pair:
//!
//! ```text
//! cp = (cp << 6) | u32::from(b & 0x3f);
//! ...
//! out.push(u16::try_from(0xd800 + (v >> 10)).expect("high"));
//! out.push(u16::try_from(0xdc00 + (v & 0x3ff)).expect("low"));
//! ```
//!
//! **`crates/trust-js-sem/src/builtins.rs:2177`** — `String.fromCodePoint`,
//! with the same two `expect`s on the same two expressions.
//!
//! Those `expect`s are the interesting part. Each one is a *panic site written
//! to assert an arithmetic fact the author could not otherwise state*: that
//! `0xd800 + (v >> 10)` fits in a `u16`. [`high_surrogate`] and
//! [`low_surrogate`] return `u16` directly, so the fact is carried by the type
//! and the `expect` has nothing left to do — the panic site is deleted rather
//! than proved.
//!
//! [`utf8_decode2`], [`utf8_decode3`] and [`utf8_decode4`] are the accumulation
//! loop's body, unrolled per length, with the shortest-form and surrogate
//! exclusions that `builtins_uri.rs` performs afterwards folded in — so an
//! out-of-fragment answer is a sentinel rather than a value the caller must
//! remember to re-check.
//!
//! # Totality, and the sentinels that buy it
//!
//! Every function here is **total** — defined on all inputs, with no panicking
//! path — because a precondition is not available: both spellings of `requires`
//! are recorded as `[ASSUMED] assumption:requires ... unsupported MIR
//! FullVerification::Precondition`, and an assumed row fails the strict gate.
//!
//! Two sentinel conventions, both one step outside the value space:
//!
//! * **Scalar-producing functions return [`NOT_A_SCALAR`] (`0x11_0000`)**, one
//!   past `char::MAX`, for input that does not denote a scalar value. That is
//!   what makes `ensures result <= 1114112` sayable *and* what makes
//!   [`combine_surrogates`]'s second clause, `result >= 65536`, true on every
//!   input including the rejecting ones.
//! * **Surrogate-producing functions return `0`** for a code point that needs
//!   no surrogate pair. `0` is not a surrogate, so it is unambiguous; test with
//!   [`is_supplementary`] first, exactly as the two JS sites already do.
//!
//! # Two tiers, marked per item
//!
//! **Tier 1 — proved bound.** A grammar `ensures` clause the compiler
//! discharges. A caller may rely on it; a body that broke it would not compile.
//!
//! **Tier 2 — proved totality, range by construction.** No contract. What is
//! proved is that the body cannot panic. [`high_surrogate`] is the only one,
//! and the reason is recorded on it.
//!
//! # The measured fragment boundary
//!
//! See [`docs/STRICT_VERIFICATION_FRAGMENT.md`] for the full checklist — that
//! file is the one to read before writing a new crate, and it carries the
//! `trust-ratio` and `trust-hex` entries as well. The entries THIS crate
//! established, measured 2026-08-29 on the authenticated `targo trust check`
//! lane (the shape probes at stage1 driver `d55c7f90a5b8a4fc`, the final
//! verdicts and the three-way comparison below at `f56f8520d8ff5671` — a
//! concurrent compiler rebuild moved the driver between the two, and every
//! result quoted here was re-run after it moved):
//!
//! [`docs/STRICT_VERIFICATION_FRAGMENT.md`]: ../../../docs/STRICT_VERIFICATION_FRAGMENT.md
//!
//! * **`* 1024` is in the fragment where `<< 10` is not.** Multiplication by a
//!   power of two composes through a contracted wrapper; the shift does not.
//!   Every scalar assembly here is therefore written with `*`, and it is not a
//!   style choice — `<<` is what the three caller sites use and it is the one
//!   respelling that moves them into the fragment.
//! * **A bound must be *syntactically local to the operator*, on EVERY operand,
//!   including intermediates.** This is the rule the crate cost the most to
//!   find, and three plausible ways of supplying the bound were measured
//!   against each other on one expression, `(hi - 55296) * 1024 + (lo - 56320)
//!   + 65536`, with the parameters already guarded into range:
//!   * **parameter guards only** — multiply and both adds `RUNTIME CHECKED`,
//!     hardened twins UNKNOWN, and the contracted *wrapper* then fails outright
//!     with *"native TrustIr bundle for `X` refused Assert-bearing member `Y`:
//!     member has a guarded or non-entry-prefix Assert"*;
//!   * **a mask instead of the subtraction** (`hi & 1023`, equal on the guarded
//!     range) — still 2 runtime-checked, 2 unknown. **A mask on a `u32` does
//!     not supply a range**, even though `((b0 & 15) as u32)` from a `u8`
//!     does — which is why [`utf8_decode3`] proves and this did not;
//!   * **a contracted clamp** (`clamp1023(hi - 55296)`, `ensures result <=
//!     1023`) — still 2 runtime-checked, 2 unknown. **A callee postcondition
//!     does NOT feed the interval engine's overflow reasoning.** It carries
//!     contract composition, which is a different lane. This one is worth
//!     knowing: the whole tier-1 design rests on postcondition composition, so
//!     it is natural to assume it also supplies arithmetic ranges. It does not.
//!
//!   What works is binding every intermediate to a local and guarding *that*
//!   local against a constant on the line before it is used — subtraction,
//!   product and partial sum alike. All 10 rows then prove and the bundle is
//!   accepted. Same operators, same values, four different verdicts.
//! * **Two `ensures` clauses on one function both discharge** — measured, 6
//!   obligations, all proved — where a single conjunctive `ensures a && b` does
//!   not. So a two-sided bound IS available; it is spelled as two clauses.
//!   [`combine_surrogates`] uses it.
//! * **A narrowing `as` cast inside a contracted body is out of the fragment**,
//!   even when the body is otherwise arithmetic-free and the bound is a
//!   constant: `if v > 57343 { 57343 } else { v as u16 }` against
//!   `ensures result <= 57343` returns *"unsupported MIR `SpecUnverifiable`:
//!   ... return assignment is outside the encoder fragment and no conjunct pins
//!   the return slot"*. Widening casts are fine. Every narrowing cast in this
//!   crate is therefore inside an **uncontracted** `raw_*` helper, with a
//!   contracted clamp of the already-narrowed type above it.
//! * **A `const` reference inside a verified body IS in the fragment** —
//!   measured, verified. This crate still spells literals in verified bodies,
//!   because the `ensures` clause must spell one either way and a body that
//!   says `NOT_A_SCALAR` where the clause says `1114112` hides the agreement a
//!   reader needs to check. The constants are public for callers, and
//!   `constants_match_the_literals_in_the_bodies` pins them equal.
//! * **`/` is composition-opaque in `u32`, exactly as `>>` is in `u8`** — the
//!   same *"member has a guarded or non-entry-prefix Assert"* refusal. That is
//!   the sole reason [`high_surrogate`] is tier 2 while its twin
//!   [`low_surrogate`], which needs only `&`, is tier 1. The two are otherwise
//!   the same function, which makes them a controlled pair for that rule.
//! * **A per-function `[VERIFIED]` in the transport does not mean the compiler
//!   verified it.** Measured four times while building this crate: a probe
//!   published `[VERIFIED] (1 obligations: 1 proved ...)` in the same run in
//!   which the compiler emitted `error: Trust full verification failed for` the
//!   same function. The exit code, the `Gate:` line and the crate Summary were
//!   all correct; only the per-function line was not. Read `error:` lines — and
//!   note this is the *opposite* direction from the `Summary`-reads-green trap
//!   `trust_strict_pass_frontier.sh` guards, so neither check subsumes the
//!   other.

#![no_std]

// ---------------------------------------------------------------------------
// The value space, for callers. These are NOT used in the verified bodies
// below — see the fragment note in the module docs — and
// `constants_match_the_literals_in_the_bodies` pins each one to the literal it
// stands for.
// ---------------------------------------------------------------------------

/// One past `char::MAX`: the sentinel every scalar-producing function in this
/// crate returns for input that does not denote a Unicode scalar value.
pub const NOT_A_SCALAR: u32 = 1_114_112;

/// `char::MAX`.
pub const MAX_SCALAR: u32 = 1_114_111;

/// First code unit of the high (leading) surrogate range, `0xD800`.
pub const HIGH_SURROGATE_FIRST: u32 = 55_296;

/// Last code unit of the high (leading) surrogate range, `0xDBFF`.
pub const HIGH_SURROGATE_LAST: u32 = 56_319;

/// First code unit of the low (trailing) surrogate range, `0xDC00`.
pub const LOW_SURROGATE_FIRST: u32 = 56_320;

/// Last code unit of the low (trailing) surrogate range, `0xDFFF`.
pub const LOW_SURROGATE_LAST: u32 = 57_343;

/// First supplementary-plane scalar, `0x1_0000` — the smallest code point that
/// needs a surrogate pair in UTF-16 and four bytes in UTF-8.
pub const SUPPLEMENTARY_FIRST: u32 = 65_536;

// ---------------------------------------------------------------------------
// Constant-bound clamps. Private, and each carries a contract ON PURPOSE: the
// tier-1 wrappers below inherit their bounds from these postconditions, and a
// wrapper over an uncontracted clamp measures UNKNOWN.
//
// Every clamp is a provable no-op on the values its caller can hand it — the
// `raw_*` helpers already return in range. It is the postcondition that is
// load-bearing, not the comparison; `clamps_never_fire_on_a_real_input` pins
// that no clamp ever actually corrects a value, so a clamp cannot quietly
// launder a wrong `raw_*` into a green proof.
// ---------------------------------------------------------------------------

fn clamp_scalar(v: u32) -> u32 ensures result <= 1114112 {
    if v > 1114112 { 1114112 } else { v }
}

/// Two clauses rather than one conjunctive clause: `ensures a && b` is not
/// discharged, two separate `ensures` are. See the module note.
fn clamp_supplementary(v: u32) -> u32 ensures result <= 1114112 ensures result >= 65536 {
    if v > 1114112 {
        return 1114112;
    }
    if v < 65536 {
        return 65536;
    }
    v
}

fn clamp_low_surrogate(v: u16) -> u16 ensures result <= 57343 {
    if v > 57343 { 57343 } else { v }
}

// ---------------------------------------------------------------------------
// Classification. Comparison only, so these carry no obligations at all — they
// exist so a caller never has to spell a surrogate boundary by hand, which is
// the mistake that makes the arithmetic below unsafe in the first place.
// ---------------------------------------------------------------------------

/// Whether `unit` is a high (leading) surrogate code unit, `0xD800..=0xDBFF`.
pub fn is_high_surrogate(unit: u32) -> bool {
    if unit < 55296 {
        return false;
    }
    unit < 56320
}

/// Whether `unit` is a low (trailing) surrogate code unit, `0xDC00..=0xDFFF`.
pub fn is_low_surrogate(unit: u32) -> bool {
    if unit < 56320 {
        return false;
    }
    unit < 57344
}

/// Whether `unit` is either half of a surrogate pair, `0xD800..=0xDFFF`.
pub fn is_surrogate(unit: u32) -> bool {
    if unit < 55296 {
        return false;
    }
    unit < 57344
}

/// Whether `cp` is a Unicode scalar value: at most `char::MAX` and not a
/// surrogate. This is exactly `char::from_u32(cp).is_some()`.
pub fn is_scalar_value(cp: u32) -> bool {
    if cp > 1114111 {
        return false;
    }
    if cp < 55296 {
        return true;
    }
    cp > 57343
}

/// Whether `cp` is a supplementary-plane scalar — the branch condition both JS
/// sites already spell as `cp <= 0xffff`, inverted and named.
pub fn is_supplementary(cp: u32) -> bool {
    if cp < 65536 {
        return false;
    }
    cp < 1114112
}

/// Whether `b` is a UTF-8 continuation byte, `0b10xx_xxxx`.
pub fn is_continuation_byte(b: u8) -> bool {
    (b & 192) == 128
}

// ---------------------------------------------------------------------------
// UTF-16: surrogate pair <-> scalar.
// ---------------------------------------------------------------------------

/// The scalar spelled by the surrogate pair `hi`, `lo`, or [`NOT_A_SCALAR`] if
/// those two code units are not a well-formed pair.
///
/// **Tier 1**, with a two-sided bound: `ensures result <= 1114112` and
/// `ensures result >= 65536` are both checked. The lower bound is the useful
/// half — it says a value returned from here can never be mistaken for a BMP
/// code unit, on any input, including the rejecting ones.
///
/// This is `trust-json`'s `de.rs:440` with both subtractions proved not to
/// underflow rather than argued from a range pattern, and with the `<< 10`
/// respelled as `* 1024` so the expression is in the verifiable fragment.
pub fn combine_surrogates(hi: u32, lo: u32) -> u32 ensures result <= 1114112 ensures result >= 65536 {
    clamp_supplementary(raw_combine_surrogates(hi, lo))
}

/// The high (leading) surrogate for `cp`, or `0` if `cp` is not a
/// supplementary-plane scalar.
///
/// **Tier 2.** Proved: the subtraction cannot underflow, the division cannot
/// divide by zero, and the addition cannot overflow — on every input. Not
/// proved, and true by construction only: the result is in
/// `0xD800..=0xDBFF`, or `0`.
///
/// The bound is not a checked proposition here because the body needs a
/// division, and `/` is opaque to the composition that carries every other
/// bound in this crate — the same wall [`low_nibble`]'s sibling `high_nibble`
/// hits in `trust-hex` for `>>`. [`low_surrogate`] is the controlled twin:
/// identical shape, needs only `&`, and is tier 1.
///
/// Returning `u16` is the point. `builtins_uri.rs` and `builtins.rs` both spell
/// this as `u16::try_from(0xd800 + (v >> 10)).expect("high")`; the `expect` is a
/// panic site standing in for an arithmetic fact, and here the type carries it.
///
/// [`low_nibble`]: https://docs.rs/trust-hex
pub fn high_surrogate(cp: u32) -> u16 {
    if cp < 65536 {
        return 0;
    }
    if cp > 1114111 {
        return 0;
    }
    // `v` is bound and then guarded, rather than relying on the guards above:
    // a bound the verifier can use must be syntactically local to the operator.
    let v: u32 = cp - 65536;
    if v > 1048575 {
        return 0;
    }
    let unit: u32 = v / 1024 + 55296;
    // `unit` is at most 1023 + 55296 = 56319, so this cast is value-preserving.
    // `high_surrogate_never_truncates` pins that over the whole domain — a
    // truncating cast is neither an overflow nor a zero divisor, so no
    // obligation above would ever see it.
    unit as u16
}

/// The low (trailing) surrogate for `cp`, or `0` if `cp` is not a
/// supplementary-plane scalar.
///
/// **Tier 1.** `ensures result <= 57343` is checked — `57343` is `0xDFFF`.
///
/// The `- 0x10000` the two JS sites perform first is absent on purpose and is
/// not an optimisation: `0x10000` has no bits below bit 10, so
/// `(cp - 0x10000) & 0x3FF` and `cp & 0x3FF` are equal on every input, and the
/// second spelling has no subtraction to discharge.
pub fn low_surrogate(cp: u32) -> u16 ensures result <= 57343 {
    clamp_low_surrogate(raw_low_surrogate(cp))
}

// ---------------------------------------------------------------------------
// UTF-8.
// ---------------------------------------------------------------------------

/// How many bytes the UTF-8 sequence starting with `b0` occupies, or `0` if
/// `b0` cannot start one.
///
/// **Tier 1.** `ensures result <= 4` is checked.
///
/// `0xC0` and `0xC1` are rejected (they can only begin an overlong two-byte
/// form) and so is everything above `0xF4`, which matches
/// `builtins_uri.rs`'s `0xc2..=0xdf | 0xe0..=0xef | 0xf0..=0xf4` table. Written
/// as ordered half-open guards rather than a `match` with range patterns: a
/// match body measures UNKNOWN on this lane.
pub fn utf8_head_len(b0: u8) -> u8 ensures result <= 4 {
    if b0 < 128 {
        return 1;
    }
    if b0 < 194 {
        return 0;
    }
    if b0 < 224 {
        return 2;
    }
    if b0 < 240 {
        return 3;
    }
    if b0 < 245 {
        return 4;
    }
    0
}

/// How many UTF-8 bytes the scalar `cp` encodes to, or `0` if `cp` is not a
/// scalar value.
///
/// **Tier 1.** `ensures result <= 4` is checked. This is
/// `char::len_utf8` extended to be total: `char::len_utf8` cannot be called
/// without first building a `char`, which is the step that panics.
pub fn utf8_len(cp: u32) -> u8 ensures result <= 4 {
    if cp < 128 {
        return 1;
    }
    if cp < 2048 {
        return 2;
    }
    if cp < 55296 {
        return 3;
    }
    if cp < 57344 {
        return 0;
    }
    if cp < 65536 {
        return 3;
    }
    if cp < 1114112 {
        return 4;
    }
    0
}

/// The scalar spelled by the two-byte UTF-8 sequence `b0 b1`, or
/// [`NOT_A_SCALAR`] if those two bytes are not one.
///
/// **Tier 1.** `ensures result <= 1114112` is checked, and the multiplication
/// and addition are proved not to overflow.
///
/// Rejects overlong forms: `0xC0` and `0xC1` never pass the head guard, so the
/// result is always at least `0x80`.
pub fn utf8_decode2(b0: u8, b1: u8) -> u32 ensures result <= 1114112 {
    clamp_scalar(raw_utf8_decode2(b0, b1))
}

/// The scalar spelled by the three-byte UTF-8 sequence `b0 b1 b2`, or
/// [`NOT_A_SCALAR`] if those three bytes are not one.
///
/// **Tier 1.** `ensures result <= 1114112` is checked.
///
/// Rejects overlong forms (`cp < 0x800`) and surrogates (`0xD800..=0xDFFF`) —
/// the two checks `builtins_uri.rs` performs after its accumulation loop, done
/// here before the value is handed back, so there is no window in which a
/// caller holds an unvalidated code point.
pub fn utf8_decode3(b0: u8, b1: u8, b2: u8) -> u32 ensures result <= 1114112 {
    clamp_scalar(raw_utf8_decode3(b0, b1, b2))
}

/// The scalar spelled by the four-byte UTF-8 sequence `b0 b1 b2 b3`, or
/// [`NOT_A_SCALAR`] if those four bytes are not one.
///
/// **Tier 1.** `ensures result <= 1114112` is checked.
///
/// Rejects overlong forms (`cp < 0x1_0000`) and anything above `char::MAX`,
/// which is reachable from a `0xF4` head byte.
pub fn utf8_decode4(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 ensures result <= 1114112 {
    clamp_scalar(raw_utf8_decode4(b0, b1, b2, b3))
}

// ---------------------------------------------------------------------------
// Uncontracted arithmetic helpers. These exist so the tier-1 wrappers above can
// stay arithmetic-free; their own safety obligations are proved.
//
// Every bound below is bound to a local and guarded IMMEDIATELY BEFORE the
// operator that needs it. Relying on the parameter guards at the top of the
// function instead leaves the multiply and the adds RUNTIME CHECKED and makes
// the contracted wrapper fail outright. See the module note.
// ---------------------------------------------------------------------------

// Every operand of every operator below is a local that was guarded against a
// constant on the line before. That is not defensive style — it is the measured
// requirement. Dropping the `p`/`s` guards and writing the peak-annotated
// one-liner `h * 1024 + l + 65536` leaves BOTH adds `RUNTIME CHECKED` and their
// hardened twins UNKNOWN, even though the multiply proves and both
// subtractions prove. `combine_surrogates_intermediate_guards_never_fire` pins
// every one of these guards as unreachable, so none of them can mask a defect.
fn raw_combine_surrogates(hi: u32, lo: u32) -> u32 {
    if hi < 55296 {
        return 1114112;
    }
    let h: u32 = hi - 55296;
    if h > 1023 {
        return 1114112;
    }
    if lo < 56320 {
        return 1114112;
    }
    let l: u32 = lo - 56320;
    if l > 1023 {
        return 1114112;
    }
    let p: u32 = h * 1024;
    if p > 1047552 {
        return 1114112;
    }
    let s: u32 = p + l;
    if s > 1048575 {
        return 1114112;
    }
    // Peak: 1023 * 1024 + 1023 + 65536 == 1114111 == char::MAX.
    s + 65536
}

fn raw_low_surrogate(cp: u32) -> u16 {
    if cp < 65536 {
        return 0;
    }
    if cp > 1114111 {
        return 0;
    }
    // The mask bounds this to 1023, so the sum is at most 57343 and the cast
    // below is value-preserving. `low_surrogate_never_truncates` pins it.
    let v: u32 = (cp & 1023) + 56320;
    v as u16
}

fn raw_utf8_decode2(b0: u8, b1: u8) -> u32 {
    if b0 < 194 {
        return 1114112;
    }
    if b0 > 223 {
        return 1114112;
    }
    if !is_continuation_byte(b1) {
        return 1114112;
    }
    // Peak: 31 * 64 + 63 == 2047.
    ((b0 & 31) as u32) * 64 + ((b1 & 63) as u32)
}

fn raw_utf8_decode3(b0: u8, b1: u8, b2: u8) -> u32 {
    if b0 < 224 {
        return 1114112;
    }
    if b0 > 239 {
        return 1114112;
    }
    if !is_continuation_byte(b1) {
        return 1114112;
    }
    if !is_continuation_byte(b2) {
        return 1114112;
    }
    // Peak: 15 * 4096 + 63 * 64 + 63 == 65535.
    let cp: u32 = ((b0 & 15) as u32) * 4096 + ((b1 & 63) as u32) * 64 + ((b2 & 63) as u32);
    if cp < 2048 {
        return 1114112;
    }
    if cp < 55296 {
        return cp;
    }
    if cp < 57344 {
        return 1114112;
    }
    cp
}

fn raw_utf8_decode4(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    if b0 < 240 {
        return 1114112;
    }
    if b0 > 244 {
        return 1114112;
    }
    if !is_continuation_byte(b1) {
        return 1114112;
    }
    if !is_continuation_byte(b2) {
        return 1114112;
    }
    if !is_continuation_byte(b3) {
        return 1114112;
    }
    // Peak: 7 * 262144 + 63 * 4096 + 63 * 64 + 63 == 2097151.
    let cp: u32 = ((b0 & 7) as u32) * 262144
        + ((b1 & 63) as u32) * 4096
        + ((b2 & 63) as u32) * 64
        + ((b3 & 63) as u32);
    if cp < 65536 {
        return 1114112;
    }
    if cp > 1114111 {
        return 1114112;
    }
    cp
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The verified bodies spell literals; the public constants spell names.
    /// If those two ever disagree the crate's documentation becomes a lie while
    /// every proof stays green, so the agreement is pinned here.
    #[test]
    fn constants_match_the_literals_in_the_bodies() {
        assert_eq!(NOT_A_SCALAR, 1_114_112);
        assert_eq!(MAX_SCALAR, 1_114_111);
        assert_eq!(HIGH_SURROGATE_FIRST, 55_296);
        assert_eq!(HIGH_SURROGATE_LAST, 56_319);
        assert_eq!(LOW_SURROGATE_FIRST, 56_320);
        assert_eq!(LOW_SURROGATE_LAST, 57_343);
        assert_eq!(SUPPLEMENTARY_FIRST, 65_536);
        assert_eq!(NOT_A_SCALAR, MAX_SCALAR + 1);
        assert_eq!(MAX_SCALAR, u32::from(char::MAX));
    }

    // -- Classification, against `core` as an independent oracle.

    #[test]
    fn classification_agrees_with_core_over_every_code_point() {
        for cp in 0..=1_114_115u32 {
            assert_eq!(
                is_scalar_value(cp),
                char::from_u32(cp).is_some(),
                "is_scalar_value({cp})"
            );
            assert_eq!(is_high_surrogate(cp), (0xD800..=0xDBFF).contains(&cp), "hi({cp})");
            assert_eq!(is_low_surrogate(cp), (0xDC00..=0xDFFF).contains(&cp), "lo({cp})");
            assert_eq!(is_surrogate(cp), (0xD800..=0xDFFF).contains(&cp), "sur({cp})");
            assert_eq!(
                is_supplementary(cp),
                (0x1_0000..=0x10_FFFF).contains(&cp),
                "supp({cp})"
            );
        }
    }

    #[test]
    fn continuation_byte_is_exact_over_the_whole_u8_domain() {
        for b in 0..=u8::MAX {
            assert_eq!(is_continuation_byte(b), (0x80..=0xBF).contains(&b), "cont({b})");
        }
    }

    #[test]
    fn head_len_matches_the_table_it_replaces() {
        for b in 0..=u8::MAX {
            let want = match b {
                0x00..=0x7F => 1,
                0xC2..=0xDF => 2,
                0xE0..=0xEF => 3,
                0xF0..=0xF4 => 4,
                _ => 0,
            };
            assert_eq!(utf8_head_len(b), want, "utf8_head_len({b:#04x})");
        }
        // The two overlong heads, called out because rejecting them is the
        // whole reason the guard is `< 194` and not `< 192`.
        assert_eq!(utf8_head_len(0xC0), 0);
        assert_eq!(utf8_head_len(0xC1), 0);
        assert_eq!(utf8_head_len(0xC2), 2);
        assert_eq!(utf8_head_len(0xF4), 4);
        assert_eq!(utf8_head_len(0xF5), 0);
    }

    #[test]
    fn utf8_len_agrees_with_char_len_utf8() {
        for cp in 0..=1_114_115u32 {
            match char::from_u32(cp) {
                Some(c) => assert_eq!(
                    usize::from(utf8_len(cp)),
                    c.len_utf8(),
                    "utf8_len({cp})"
                ),
                None => assert_eq!(utf8_len(cp), 0, "utf8_len({cp}) must be the sentinel"),
            }
            // The contracted bound, and the head byte's view of the same length.
            assert!(utf8_len(cp) <= 4);
        }
    }

    // -- UTF-16.

    #[test]
    fn combine_surrogates_reproduces_the_json_escape_reader() {
        // Exhaustive over the entire accepting domain: 1024 x 1024 pairs.
        for hi in 0xD800u32..=0xDBFF {
            for lo in 0xDC00u32..=0xDFFF {
                let got = combine_surrogates(hi, lo);
                // The incumbent expression at trust-json/src/de.rs:440.
                let want = ((hi - 0xD800) << 10 | (lo - 0xDC00)) + 0x1_0000;
                assert_eq!(got, want, "combine_surrogates({hi:#06x},{lo:#06x})");
                assert!(char::from_u32(got).is_some(), "must be a scalar: {got}");
            }
        }
        assert_eq!(combine_surrogates(0xD800, 0xDC00), 0x1_0000);
        assert_eq!(combine_surrogates(0xDBFF, 0xDFFF), 0x10_FFFF);
        // The pair from `tests/acceptance_gate.rs`: "𝄞" is U+1D11E.
        assert_eq!(combine_surrogates(0xD834, 0xDD1E), 0x1_D11E);
    }

    #[test]
    fn combine_surrogates_rejects_everything_that_is_not_a_pair() {
        // Both boundaries of both ranges, plus the swapped-order case that the
        // `0xDC00..=0xDFFF` arm of `parse_escape` exists to reject.
        for &hi in &[0u32, 1, 0xD7FF, 0xD800, 0xDBFF, 0xDC00, 0xDFFF, 0xE000, 0x10_FFFF, 0x11_0000, u32::MAX] {
            for &lo in &[0u32, 1, 0xD7FF, 0xD800, 0xDBFF, 0xDC00, 0xDFFF, 0xE000, 0x10_FFFF, 0x11_0000, u32::MAX] {
                let ok = (0xD800..=0xDBFF).contains(&hi) && (0xDC00..=0xDFFF).contains(&lo);
                let got = combine_surrogates(hi, lo);
                if ok {
                    assert!(got >= 0x1_0000 && got <= 0x10_FFFF, "({hi:#x},{lo:#x}) -> {got}");
                } else {
                    assert_eq!(got, NOT_A_SCALAR, "({hi:#x},{lo:#x}) must be the sentinel");
                }
            }
        }
        // A lone leading surrogate paired with itself: the `de.rs` "two leading
        // surrogates" case from tests/adversarial.rs.
        assert_eq!(combine_surrogates(0xD800, 0xD800), NOT_A_SCALAR);
        // Ordinary BMP text must never look like a pair.
        assert_eq!(combine_surrogates(u32::from('a'), u32::from('b')), NOT_A_SCALAR);
    }

    #[test]
    fn surrogate_split_agrees_with_core_encode_utf16() {
        let mut buf = [0u16; 2];
        for cp in 0x1_0000u32..=0x10_FFFF {
            let c = char::from_u32(cp).expect("supplementary scalars are all valid");
            let units = c.encode_utf16(&mut buf);
            assert_eq!(units.len(), 2, "supplementary must be a pair");
            assert_eq!(high_surrogate(cp), units[0], "high_surrogate({cp:#x})");
            assert_eq!(low_surrogate(cp), units[1], "low_surrogate({cp:#x})");
            // Round trip through the combiner: the inverse must be exact.
            assert_eq!(
                combine_surrogates(u32::from(units[0]), u32::from(units[1])),
                cp,
                "round trip {cp:#x}"
            );
        }
    }

    #[test]
    fn surrogate_split_returns_zero_off_the_supplementary_plane() {
        for &cp in &[0u32, 1, 0x7F, 0x80, 0xD7FF, 0xD800, 0xDFFF, 0xE000, 0xFFFF, 0x10_FFFF, 0x11_0000, u32::MAX] {
            if (0x1_0000..=0x10_FFFF).contains(&cp) {
                continue;
            }
            assert_eq!(high_surrogate(cp), 0, "high_surrogate({cp:#x})");
            assert_eq!(low_surrogate(cp), 0, "low_surrogate({cp:#x})");
        }
        assert_eq!(high_surrogate(0x0_FFFF), 0);
        assert_eq!(high_surrogate(0x1_0000), 0xD800);
        assert_eq!(low_surrogate(0x1_0000), 0xDC00);
        assert_eq!(high_surrogate(0x10_FFFF), 0xDBFF);
        assert_eq!(low_surrogate(0x10_FFFF), 0xDFFF);
        assert_eq!(high_surrogate(0x11_0000), 0);
    }

    /// A truncating `as` cast is neither an overflow nor a zero divisor, so no
    /// obligation in this crate would ever see one — the exact hole that let a
    /// fully-proved `percent` return `4` for `percent(42_949_673, 1)`. Both
    /// `u32 -> u16` casts are therefore pinned value-preserving over the whole
    /// input domain, independently of the surrogate comparison above.
    #[test]
    fn surrogate_casts_never_truncate() {
        for cp in 0..=1_114_115u32 {
            assert!(raw_low_surrogate(cp) <= 57343, "raw_low_surrogate({cp})");
            assert!(u32::from(high_surrogate(cp)) <= 56319, "high_surrogate({cp})");
            // The pre-cast value, recomputed here in u32, must equal the
            // post-cast one. If the cast ever truncated these would differ.
            if (0x1_0000..=0x10_FFFF).contains(&cp) {
                assert_eq!(u32::from(high_surrogate(cp)), (cp - 65536) / 1024 + 55296);
                assert_eq!(u32::from(low_surrogate(cp)), (cp & 1023) + 56320);
            }
        }
    }

    // -- UTF-8 decode, against `core::str::from_utf8` as an independent oracle.
    //    `from_utf8` decides well-formedness by an entirely different route
    //    (a DFA over byte classes), so agreeing with it is real evidence.

    fn oracle(bytes: &[u8]) -> u32 {
        match core::str::from_utf8(bytes) {
            Ok(s) => {
                let mut it = s.chars();
                match (it.next(), it.next()) {
                    (Some(c), None) => u32::from(c),
                    _ => NOT_A_SCALAR,
                }
            }
            Err(_) => NOT_A_SCALAR,
        }
    }

    #[test]
    fn decode2_agrees_with_core_over_every_byte_pair() {
        // Exhaustive: all 65_536 two-byte sequences.
        for b0 in 0..=u8::MAX {
            for b1 in 0..=u8::MAX {
                assert_eq!(
                    utf8_decode2(b0, b1),
                    oracle(&[b0, b1]),
                    "utf8_decode2({b0:#04x},{b1:#04x})"
                );
            }
        }
        assert_eq!(utf8_decode2(0xC2, 0x80), 0x80);
        assert_eq!(utf8_decode2(0xDF, 0xBF), 0x7FF);
        // Overlong: `0xC0 0x80` is the classic NUL smuggle.
        assert_eq!(utf8_decode2(0xC0, 0x80), NOT_A_SCALAR);
        assert_eq!(utf8_decode2(0xC1, 0xBF), NOT_A_SCALAR);
    }

    #[test]
    fn decode3_agrees_with_core_over_every_sequence_it_can_accept() {
        // Exhaustive over every head byte that can begin a three-byte form,
        // times both continuation slots: 16 * 65_536 sequences.
        for b0 in 0xE0..=0xEFu8 {
            for b1 in 0..=u8::MAX {
                for b2 in 0..=u8::MAX {
                    assert_eq!(
                        utf8_decode3(b0, b1, b2),
                        oracle(&[b0, b1, b2]),
                        "utf8_decode3({b0:#04x},{b1:#04x},{b2:#04x})"
                    );
                }
            }
        }
        // Every other head byte must be refused outright.
        for b0 in 0..=u8::MAX {
            if (0xE0..=0xEF).contains(&b0) {
                continue;
            }
            assert_eq!(utf8_decode3(b0, 0x80, 0x80), NOT_A_SCALAR, "head {b0:#04x}");
        }
        assert_eq!(utf8_decode3(0xE0, 0xA0, 0x80), 0x800);
        assert_eq!(utf8_decode3(0xEF, 0xBF, 0xBF), 0xFFFF);
        assert_eq!(utf8_decode3(0xE2, 0x82, 0xAC), 0x20AC); // EURO SIGN
        // Overlong three-byte form of U+0000, and a UTF-8-encoded lone
        // surrogate — the input `trust-json/tests/adversarial.rs:241` feeds in.
        assert_eq!(utf8_decode3(0xE0, 0x80, 0x80), NOT_A_SCALAR);
        assert_eq!(utf8_decode3(0xED, 0xA0, 0x80), NOT_A_SCALAR);
        assert_eq!(utf8_decode3(0xED, 0x9F, 0xBF), 0xD7FF);
        assert_eq!(utf8_decode3(0xEE, 0x80, 0x80), 0xE000);
    }

    #[test]
    fn decode4_round_trips_every_supplementary_scalar() {
        let mut buf = [0u8; 4];
        for cp in 0x1_0000u32..=0x10_FFFF {
            let c = char::from_u32(cp).expect("supplementary scalars are all valid");
            let s = c.encode_utf8(&mut buf);
            let b = s.as_bytes();
            assert_eq!(b.len(), 4, "supplementary must encode to 4 bytes");
            assert_eq!(utf8_decode4(b[0], b[1], b[2], b[3]), cp, "decode4 of {cp:#x}");
            assert_eq!(u32::from(utf8_len(cp)), 4);
            assert_eq!(utf8_head_len(b[0]), 4);
        }
    }

    #[test]
    fn decode4_agrees_with_core_on_the_boundary_structure() {
        // The full 4-byte space is 2^32; sweep every head byte and every first
        // continuation, against the boundary values of the last two slots —
        // which is where every accept/reject transition lives.
        const EDGE: [u8; 8] = [0x00, 0x7F, 0x80, 0x81, 0xBE, 0xBF, 0xC0, 0xFF];
        for b0 in 0..=u8::MAX {
            for b1 in 0..=u8::MAX {
                for b2 in EDGE {
                    for b3 in EDGE {
                        assert_eq!(
                            utf8_decode4(b0, b1, b2, b3),
                            oracle(&[b0, b1, b2, b3]),
                            "utf8_decode4({b0:#04x},{b1:#04x},{b2:#04x},{b3:#04x})"
                        );
                    }
                }
            }
        }
        assert_eq!(utf8_decode4(0xF0, 0x90, 0x80, 0x80), 0x1_0000);
        assert_eq!(utf8_decode4(0xF4, 0x8F, 0xBF, 0xBF), 0x10_FFFF);
        // Overlong, and one past char::MAX.
        assert_eq!(utf8_decode4(0xF0, 0x80, 0x80, 0x80), NOT_A_SCALAR);
        assert_eq!(utf8_decode4(0xF4, 0x90, 0x80, 0x80), NOT_A_SCALAR);
        assert_eq!(utf8_decode4(0xF5, 0x80, 0x80, 0x80), NOT_A_SCALAR);
    }

    /// Every `clamp*` must be a NO-OP on every value its caller can hand it.
    ///
    /// This is the test that stops a clamp from laundering a wrong `raw_*`: the
    /// clamps exist to carry a postcondition, and if one ever actually fired it
    /// would be silently correcting a defect into a green proof.
    #[test]
    fn clamps_never_fire_on_a_real_input() {
        for hi in 0xD7FFu32..=0xDC00 {
            for lo in 0xDBFFu32..=0xE000 {
                let raw = raw_combine_surrogates(hi, lo);
                assert!(raw <= 1114112 && raw >= 65536, "clamp_supplementary on ({hi:#x},{lo:#x})");
            }
        }
        for &hi in &[0u32, 0xD800, 0xDBFF, u32::MAX] {
            for &lo in &[0u32, 0xDC00, 0xDFFF, u32::MAX] {
                let raw = raw_combine_surrogates(hi, lo);
                assert!(raw <= 1114112 && raw >= 65536, "clamp_supplementary on ({hi:#x},{lo:#x})");
            }
        }
        for cp in 0..=1_114_115u32 {
            assert!(raw_low_surrogate(cp) <= 57343, "clamp_low_surrogate would fire on {cp}");
        }
        for b0 in 0..=u8::MAX {
            for b1 in 0..=u8::MAX {
                assert!(raw_utf8_decode2(b0, b1) <= 1114112, "clamp_scalar on 2({b0},{b1})");
                assert!(raw_utf8_decode3(b0, b1, 0x80) <= 1114112, "clamp_scalar on 3({b0},{b1})");
                assert!(raw_utf8_decode4(b0, b1, 0x80, 0x80) <= 1114112, "clamp_scalar on 4");
            }
        }
        for b0 in 0xE0..=0xEFu8 {
            for b1 in 0..=u8::MAX {
                for b2 in 0..=u8::MAX {
                    assert!(raw_utf8_decode3(b0, b1, b2) <= 1114112, "clamp_scalar on 3");
                }
            }
        }
    }

    /// Every intermediate guard inside `raw_combine_surrogates` must be
    /// UNREACHABLE on every input.
    ///
    /// Those guards exist only because the verifier needs a bound syntactically
    /// local to each operator; they are not part of the specification. If one
    /// ever fired it would be silently returning the sentinel for a pair that
    /// should have produced a scalar, and every proof would stay green — the
    /// same failure mode `clamps_never_fire_on_a_real_input` guards for the
    /// clamps. Checked here by recomputing each intermediate independently.
    #[test]
    fn combine_surrogates_intermediate_guards_never_fire() {
        for hi in 0xD800u32..=0xDBFF {
            let h = hi - 55296;
            assert!(h <= 1023, "the `h > 1023` guard would fire at {hi:#x}");
            let p = h * 1024;
            assert!(p <= 1047552, "the `p > 1047552` guard would fire at {hi:#x}");
            for lo in 0xDC00u32..=0xDFFF {
                let l = lo - 56320;
                assert!(l <= 1023, "the `l > 1023` guard would fire at {lo:#x}");
                let s = p + l;
                assert!(s <= 1048575, "the `s > 1048575` guard would fire at ({hi:#x},{lo:#x})");
                assert_eq!(s + 65536, combine_surrogates(hi, lo));
            }
        }
    }

    /// The checked bounds, asserted at runtime as well.
    ///
    /// They are already discharged by the compiler, so this is not where they
    /// are established — it is a tripwire for the day someone edits a body and
    /// the contract silently stops being checked. An `ensures` row that goes
    /// UNKNOWN does not change any value, so nothing else here would notice.
    #[test]
    fn the_contracted_bounds_hold_at_runtime_too() {
        for cp in 0..=1_114_115u32 {
            assert!(utf8_len(cp) <= 4);
            assert!(low_surrogate(cp) <= 57343);
        }
        for b0 in 0..=u8::MAX {
            assert!(utf8_head_len(b0) <= 4);
            for b1 in 0..=u8::MAX {
                assert!(utf8_decode2(b0, b1) <= 1114112);
            }
        }
        for &hi in &[0u32, 0xD800, 0xDBFF, 0xDFFF, u32::MAX] {
            for &lo in &[0u32, 0xDC00, 0xDFFF, u32::MAX] {
                let c = combine_surrogates(hi, lo);
                assert!(c <= 1114112, "upper clause");
                assert!(c >= 65536, "lower clause");
            }
        }
        assert!(utf8_decode3(0xE2, 0x82, 0xAC) <= 1114112);
        assert!(utf8_decode4(0xF0, 0x90, 0x80, 0x80) <= 1114112);
    }
}
