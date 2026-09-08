#![no_std]
//! Two's-complement bounds for machine integer widths, 1..=64 bits.
//!
//! # Why this crate exists
//!
//! `(1i128 << (width - 1)) - 1` and `(1i128 << width) - 1` are written **by
//! hand, from scratch, at least nine times** in this tree, in nine files that
//! do not share a line of code:
//!
//! | site | shape |
//! |---|---|
//! | `trust-router/src/interval_backend.rs:260-292` | `bv_unsigned_max` / `signed_threshold` / `signed_min_of` / `signed_max_of` |
//! | `trust-ir-bridge/src/lower.rs:8412` | `native_int_min_max` — **the consumer this crate replaced** |
//! | `trust-ir-bridge/src/lower.rs:31170` | `cast_integer_bounds` |
//! | `trust-ir-bridge/src/lower.rs:5442` | `safety_type_min_formula` / `safety_type_max_formula` |
//! | `trust-certify/src/lib.rs:7436` | `signed_width_range` |
//! | `trust-types/src/facet_inference.rs:98` | `unsigned_fits_width` / `signed_fits_width` |
//! | `trust-types/src/admissible_body.rs:691` | `uint_fits_width` |
//! | `trust-mir-extract/src/verifier_api.rs:2210` | `bv_fits_unsigned` |
//! | `trust-spec-elab/src/lib.rs:183` | `bit_mask` / `signed_positive_max` / `signed_negative_magnitude_max` |
//!
//! Three of those nine disagree about the DOMAIN of the same question —
//! `1..=128`, `== 128` and `>= 127` are each used as "the width is too wide"
//! by a different file. Six of the nine are **partial**: at `width == 0` they
//! evaluate `1 << (0u32 - 1)`, which is a `u32` subtract-overflow panic in
//! debug and a shift by `4294967295` in release. Every one is currently
//! unreachable behind a caller's guard, which is a property of the callers,
//! not of the functions.
//!
//! This is not a style complaint. These functions decide the range facts the
//! verifier CONJOINS ONTO ITS OWN VCs. A bound that is too NARROW is a false
//! hypothesis handed to the solver, and it discharges a real overflow with no
//! kernel backstop — see `native_widening_cast_facts`, which pushes
//! `from_min <= dest <= from_max` onto every VC in the function.
//!
//! # The domain is 1..=64, and that is what makes it verifiable
//!
//! The nine sites above all traffic in `i128`/`u128` because `Formula::Int`
//! carries an `i128`. `u128` arithmetic is outside the strict verification
//! fragment (`docs/STRICT_VERIFICATION_FRAGMENT.md` §2.3, §3), so a faithful
//! `i128` restatement is not writable. It does not have to be: the whole
//! `1..=64` domain fits `u64` exactly, with `unsigned_max(64) == u64::MAX`,
//! `signed_max(64) == 2^63 - 1` and `signed_min_magnitude(64) == 2^63`. The
//! replaced consumer, `native_int_min_max`, declines above 64 already.
//!
//! # Signs are returned as MAGNITUDES, deliberately
//!
//! There is no `signed_min` here returning a negative `i64`. §10.1 of the
//! fragment map measured that a NEGATIVE LITERAL in an `ensures` predicate is
//! three silent UNKNOWN rows with no diagnostic — `result >= 0` proves on an
//! `i32` body and `result >= -1` does not. A signed-returning twin could
//! therefore carry no clause at all. [`signed_min_magnitude`] returns
//! `2^(w-1)` as a `u64` and the caller applies the sign, which keeps every
//! clause in this crate on the unsigned side where the fragment is strong.
//!
//! # THE SENTINEL, AND WHY IT POINTS THE WAY IT DOES
//!
//! Every function here is TOTAL: there are no preconditions, because a
//! `requires` is fatal under the strict lane (fragment map §3). Out-of-domain
//! widths (`0`, or above `64`) return a SENTINEL.
//!
//! §15.5 of the fragment map records that a total callee's sentinel does not
//! compose: `trust_bits::mask_below` saturates, which is right for a mask and
//! wrong one level up for a field width, and a 33-bit field certified as
//! fitting in 32 bits with **every obligation proving**. The lesson taken here
//! is that the sentinel must be chosen in the direction that fails SAFE for
//! the consumer's use, and for a RANGE BOUND that direction is measurable:
//!
//! * a bound that is too **WIDE** over-approximates — sound, less precise;
//! * a bound that is too **NARROW** is a false hypothesis — **unsound**.
//!
//! So every sentinel here is the WIDEST value in the crate's domain
//! (`unsigned_max` -> `u64::MAX`, `signed_max` -> `2^63 - 1`,
//! `signed_min_magnitude` -> `2^63`). A consumer that forgets the guard gets
//! an imprecise answer, never an unsound one. Returning `0` would have been
//! the natural "nothing fits" reading and is exactly backwards.
//!
//! **The residual trap, stated because it is real:** the sentinel COLLIDES
//! with a legitimate answer — `unsigned_max(0)`, `unsigned_max(65)` and
//! `unsigned_max(64)` are all `u64::MAX`. This function alone therefore cannot
//! tell a caller whether the width was supported. Call [`width_is_supported`]
//! first; the replaced consumer does, and `sentinel_is_the_wide_end_not_zero`
//! plus `unsigned_max_sentinel_collides_with_width_64` pin both halves.
//!
//! # What is proved, and what is only tested
//!
//! The clauses below are the strongest the clause language admits: it accepts
//! `result` against a bare literal or a bare parameter, and nothing built from
//! an operator (fragment map §13.9, §14.8). `signed_max(w) == 2^(w-1) - 1` is
//! therefore not statable. Each clause's doc names the wrong implementation it
//! still admits, and every VALUE in this crate is pinned by an exhaustive test
//! against an INDEPENDENT `u128` oracle over the whole `0..=200` width domain.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

// Bootstrap cannot parse Trust's native signature clauses, while the verified
// lane must keep those exact clause tokens. Each invocation below owns its
// function body exactly once. Trust injects `cfg(trust_verify)` exactly when
// verification is active, selecting the native-clause expansion; an ordinary
// compiler expands the same invocation to the same function without clauses.
mod trust_contract_surface {
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

    pub(crate) use trust_contract_fn;
}

use trust_contract_surface::trust_contract_fn;

trust_contract_fn! {
/// `1` iff `w` names a width this crate has an exact bound for, i.e. `1 <= w <= 64`.
///
/// **Call this before reading any bound.** The three bound functions are total
/// and saturate, so they answer for every `u32`; this is the only function that
/// distinguishes "the answer is the bound" from "the answer is the sentinel".
///
/// **Clause `result <= 1`.** Admits a function that always returns `0` (nothing
/// is ever supported — safe but useless) and one that always returns `1` (the
/// dangerous direction). Neither is ruled out by the clause; both are ruled out
/// by `width_is_supported_is_exactly_1_through_64`, which checks all of
/// `0..=200` against the literal predicate.
pub fn width_is_supported(w: u32) -> u8
clauses [ensures result <= 1]
{
    raw_width_is_supported(w)
}
}

fn raw_width_is_supported(w: u32) -> u8 {
    if w == 0 {
        return 0;
    }
    if w > 64 {
        return 0;
    }
    1
}

/// `2^w - 1` for `1 <= w <= 64` — the largest value of an unsigned `w`-bit
/// integer. Out of domain: `u64::MAX`, the WIDEST answer (see the module doc).
///
/// Uncontracted on purpose. The only bound statable against a bare literal is
/// `result <= 18446744073709551615`, which is the `u64` type maximum and
/// therefore vacuous — it is satisfied by every `u64`-returning function that
/// exists. Rather than ship a clause that proves nothing and reads as a
/// guarantee, the value is pinned by `unsigned_max_matches_a_u128_oracle`.
fn unsigned_max_raw(w: u32) -> u64 {
    if w == 1 {
        return 1;
    }
    if w == 2 {
        return 3;
    }
    if w == 3 {
        return 7;
    }
    if w == 4 {
        return 15;
    }
    if w == 5 {
        return 31;
    }
    if w == 6 {
        return 63;
    }
    if w == 7 {
        return 127;
    }
    if w == 8 {
        return 255;
    }
    if w == 9 {
        return 511;
    }
    if w == 10 {
        return 1023;
    }
    if w == 11 {
        return 2047;
    }
    if w == 12 {
        return 4095;
    }
    if w == 13 {
        return 8191;
    }
    if w == 14 {
        return 16383;
    }
    if w == 15 {
        return 32767;
    }
    if w == 16 {
        return 65535;
    }
    if w == 17 {
        return 131071;
    }
    if w == 18 {
        return 262143;
    }
    if w == 19 {
        return 524287;
    }
    if w == 20 {
        return 1048575;
    }
    if w == 21 {
        return 2097151;
    }
    if w == 22 {
        return 4194303;
    }
    if w == 23 {
        return 8388607;
    }
    if w == 24 {
        return 16777215;
    }
    if w == 25 {
        return 33554431;
    }
    if w == 26 {
        return 67108863;
    }
    if w == 27 {
        return 134217727;
    }
    if w == 28 {
        return 268435455;
    }
    if w == 29 {
        return 536870911;
    }
    if w == 30 {
        return 1073741823;
    }
    if w == 31 {
        return 2147483647;
    }
    if w == 32 {
        return 4294967295;
    }
    if w == 33 {
        return 8589934591;
    }
    if w == 34 {
        return 17179869183;
    }
    if w == 35 {
        return 34359738367;
    }
    if w == 36 {
        return 68719476735;
    }
    if w == 37 {
        return 137438953471;
    }
    if w == 38 {
        return 274877906943;
    }
    if w == 39 {
        return 549755813887;
    }
    if w == 40 {
        return 1099511627775;
    }
    if w == 41 {
        return 2199023255551;
    }
    if w == 42 {
        return 4398046511103;
    }
    if w == 43 {
        return 8796093022207;
    }
    if w == 44 {
        return 17592186044415;
    }
    if w == 45 {
        return 35184372088831;
    }
    if w == 46 {
        return 70368744177663;
    }
    if w == 47 {
        return 140737488355327;
    }
    if w == 48 {
        return 281474976710655;
    }
    if w == 49 {
        return 562949953421311;
    }
    if w == 50 {
        return 1125899906842623;
    }
    if w == 51 {
        return 2251799813685247;
    }
    if w == 52 {
        return 4503599627370495;
    }
    if w == 53 {
        return 9007199254740991;
    }
    if w == 54 {
        return 18014398509481983;
    }
    if w == 55 {
        return 36028797018963967;
    }
    if w == 56 {
        return 72057594037927935;
    }
    if w == 57 {
        return 144115188075855871;
    }
    if w == 58 {
        return 288230376151711743;
    }
    if w == 59 {
        return 576460752303423487;
    }
    if w == 60 {
        return 1152921504606846975;
    }
    if w == 61 {
        return 2305843009213693951;
    }
    if w == 62 {
        return 4611686018427387903;
    }
    if w == 63 {
        return 9223372036854775807;
    }
    if w == 64 {
        return 18446744073709551615;
    }
    18446744073709551615
}

/// `2^w - 1` for `1 <= w <= 64`; `u64::MAX` out of domain.
///
/// See [`width_is_supported`] — the sentinel is indistinguishable from the
/// genuine answer at `w == 64`.
pub fn unsigned_max(w: u32) -> u64 {
    unsigned_max_raw(w)
}

/// `2^(w-1) - 1`, saturating to `i64::MAX` out of domain.
fn raw_signed_max(w: u32) -> u64 {
    if w == 1 {
        return 0;
    }
    if w == 2 {
        return 1;
    }
    if w == 3 {
        return 3;
    }
    if w == 4 {
        return 7;
    }
    if w == 5 {
        return 15;
    }
    if w == 6 {
        return 31;
    }
    if w == 7 {
        return 63;
    }
    if w == 8 {
        return 127;
    }
    if w == 9 {
        return 255;
    }
    if w == 10 {
        return 511;
    }
    if w == 11 {
        return 1023;
    }
    if w == 12 {
        return 2047;
    }
    if w == 13 {
        return 4095;
    }
    if w == 14 {
        return 8191;
    }
    if w == 15 {
        return 16383;
    }
    if w == 16 {
        return 32767;
    }
    if w == 17 {
        return 65535;
    }
    if w == 18 {
        return 131071;
    }
    if w == 19 {
        return 262143;
    }
    if w == 20 {
        return 524287;
    }
    if w == 21 {
        return 1048575;
    }
    if w == 22 {
        return 2097151;
    }
    if w == 23 {
        return 4194303;
    }
    if w == 24 {
        return 8388607;
    }
    if w == 25 {
        return 16777215;
    }
    if w == 26 {
        return 33554431;
    }
    if w == 27 {
        return 67108863;
    }
    if w == 28 {
        return 134217727;
    }
    if w == 29 {
        return 268435455;
    }
    if w == 30 {
        return 536870911;
    }
    if w == 31 {
        return 1073741823;
    }
    if w == 32 {
        return 2147483647;
    }
    if w == 33 {
        return 4294967295;
    }
    if w == 34 {
        return 8589934591;
    }
    if w == 35 {
        return 17179869183;
    }
    if w == 36 {
        return 34359738367;
    }
    if w == 37 {
        return 68719476735;
    }
    if w == 38 {
        return 137438953471;
    }
    if w == 39 {
        return 274877906943;
    }
    if w == 40 {
        return 549755813887;
    }
    if w == 41 {
        return 1099511627775;
    }
    if w == 42 {
        return 2199023255551;
    }
    if w == 43 {
        return 4398046511103;
    }
    if w == 44 {
        return 8796093022207;
    }
    if w == 45 {
        return 17592186044415;
    }
    if w == 46 {
        return 35184372088831;
    }
    if w == 47 {
        return 70368744177663;
    }
    if w == 48 {
        return 140737488355327;
    }
    if w == 49 {
        return 281474976710655;
    }
    if w == 50 {
        return 562949953421311;
    }
    if w == 51 {
        return 1125899906842623;
    }
    if w == 52 {
        return 2251799813685247;
    }
    if w == 53 {
        return 4503599627370495;
    }
    if w == 54 {
        return 9007199254740991;
    }
    if w == 55 {
        return 18014398509481983;
    }
    if w == 56 {
        return 36028797018963967;
    }
    if w == 57 {
        return 72057594037927935;
    }
    if w == 58 {
        return 144115188075855871;
    }
    if w == 59 {
        return 288230376151711743;
    }
    if w == 60 {
        return 576460752303423487;
    }
    if w == 61 {
        return 1152921504606846975;
    }
    if w == 62 {
        return 2305843009213693951;
    }
    if w == 63 {
        return 4611686018427387903;
    }
    if w == 64 {
        return 9223372036854775807;
    }
    9223372036854775807
}

trust_contract_fn! {
/// `2^(w-1) - 1` for `1 <= w <= 64` — the largest value of a SIGNED `w`-bit
/// two's-complement integer. Out of domain: `2^63 - 1`, the widest answer.
///
/// **Clause `result <= 9223372036854775807`.** This is `i64::MAX`, not the
/// `u64` type maximum, so it is NOT vacuous: it rules out the single most
/// likely wrong implementation of this function, which is returning the
/// UNSIGNED maximum `2^w - 1` by confusing the two (at `w == 64` that is
/// `u64::MAX`, which violates the clause). It still admits a function that
/// always returns `0`, and one that returns `2^(w-1) - 1` for the wrong `w`;
/// `signed_max_matches_a_u128_oracle` rules both out.
pub fn signed_max(w: u32) -> u64
clauses [ensures result <= 9223372036854775807]
{
    raw_signed_max(w)
}
}

/// `2^(w-1)`, saturating to `2^63` out of domain.
fn raw_signed_min_magnitude(w: u32) -> u64 {
    if w == 1 {
        return 1;
    }
    if w == 2 {
        return 2;
    }
    if w == 3 {
        return 4;
    }
    if w == 4 {
        return 8;
    }
    if w == 5 {
        return 16;
    }
    if w == 6 {
        return 32;
    }
    if w == 7 {
        return 64;
    }
    if w == 8 {
        return 128;
    }
    if w == 9 {
        return 256;
    }
    if w == 10 {
        return 512;
    }
    if w == 11 {
        return 1024;
    }
    if w == 12 {
        return 2048;
    }
    if w == 13 {
        return 4096;
    }
    if w == 14 {
        return 8192;
    }
    if w == 15 {
        return 16384;
    }
    if w == 16 {
        return 32768;
    }
    if w == 17 {
        return 65536;
    }
    if w == 18 {
        return 131072;
    }
    if w == 19 {
        return 262144;
    }
    if w == 20 {
        return 524288;
    }
    if w == 21 {
        return 1048576;
    }
    if w == 22 {
        return 2097152;
    }
    if w == 23 {
        return 4194304;
    }
    if w == 24 {
        return 8388608;
    }
    if w == 25 {
        return 16777216;
    }
    if w == 26 {
        return 33554432;
    }
    if w == 27 {
        return 67108864;
    }
    if w == 28 {
        return 134217728;
    }
    if w == 29 {
        return 268435456;
    }
    if w == 30 {
        return 536870912;
    }
    if w == 31 {
        return 1073741824;
    }
    if w == 32 {
        return 2147483648;
    }
    if w == 33 {
        return 4294967296;
    }
    if w == 34 {
        return 8589934592;
    }
    if w == 35 {
        return 17179869184;
    }
    if w == 36 {
        return 34359738368;
    }
    if w == 37 {
        return 68719476736;
    }
    if w == 38 {
        return 137438953472;
    }
    if w == 39 {
        return 274877906944;
    }
    if w == 40 {
        return 549755813888;
    }
    if w == 41 {
        return 1099511627776;
    }
    if w == 42 {
        return 2199023255552;
    }
    if w == 43 {
        return 4398046511104;
    }
    if w == 44 {
        return 8796093022208;
    }
    if w == 45 {
        return 17592186044416;
    }
    if w == 46 {
        return 35184372088832;
    }
    if w == 47 {
        return 70368744177664;
    }
    if w == 48 {
        return 140737488355328;
    }
    if w == 49 {
        return 281474976710656;
    }
    if w == 50 {
        return 562949953421312;
    }
    if w == 51 {
        return 1125899906842624;
    }
    if w == 52 {
        return 2251799813685248;
    }
    if w == 53 {
        return 4503599627370496;
    }
    if w == 54 {
        return 9007199254740992;
    }
    if w == 55 {
        return 18014398509481984;
    }
    if w == 56 {
        return 36028797018963968;
    }
    if w == 57 {
        return 72057594037927936;
    }
    if w == 58 {
        return 144115188075855872;
    }
    if w == 59 {
        return 288230376151711744;
    }
    if w == 60 {
        return 576460752303423488;
    }
    if w == 61 {
        return 1152921504606846976;
    }
    if w == 62 {
        return 2305843009213693952;
    }
    if w == 63 {
        return 4611686018427387904;
    }
    if w == 64 {
        return 9223372036854775808;
    }
    9223372036854775808
}

trust_contract_fn! {
/// `2^(w-1)` for `1 <= w <= 64` — the MAGNITUDE of the most negative value of a
/// signed `w`-bit two's-complement integer. The true minimum is
/// `-(signed_min_magnitude(w) as i128)`; see the module doc for why the sign is
/// the caller's job. Out of domain: `2^63`, the widest answer.
///
/// **Clause `result <= 9223372036854775808`.** `2^63` — one above
/// [`signed_max`]'s bound, which is exactly the asymmetry of two's complement
/// and the thing most often got wrong by one. It rules out returning the
/// unsigned maximum. It admits `0`; `signed_min_magnitude_matches_a_u128_oracle`
/// and `min_magnitude_is_exactly_one_above_max` do not.
pub fn signed_min_magnitude(w: u32) -> u64
clauses [ensures result <= 9223372036854775808]
{
    raw_signed_min_magnitude(w)
}
}

trust_contract_fn! {
/// `w` clamped into `0..=64`.
///
/// The fragment-legal, TOTAL replacement for the six sites listed in the module
/// doc that panic (debug) or shift by `4294967295` (release) at `w == 0` or
/// `w > 128`. Those sites are safe today only because each caller guards.
///
/// **Clauses `result <= 64` and `result <= w`.** Two upper bounds, one against
/// a literal and one against a PARAMETER, which is the strongest pair the
/// clause language admits here: together they say the result never exceeds the
/// ceiling AND never exceeds the input, so no widening is possible in either
/// direction. They admit a function that always returns `0`, which
/// `clamp_width_is_identity_below_65_and_saturates_above` rules out.
pub fn clamp_width(w: u32) -> u32
clauses [ensures result <= 64 ensures result <= w]
{
    if w > 64 {
        return 64;
    }
    w
}
}

trust_contract_fn! {
/// `value` saturated down to `max`.
///
/// **Clauses `result <= value` and `result <= max`.** The pair is genuinely
/// two-sided in effect: the result cannot exceed either input, so this cannot
/// widen a value into a range it does not belong to. It admits a function that
/// always returns `0` — the reason `clamp_to_max_is_the_minimum` checks it
/// against an independent `core::cmp::min` over a 4096-pair grid.
///
/// **The second parameter is `limit`, and it may NOT be renamed to `max`.**
/// Measured here 2026-08-30: a parameter named `max` or `min` is silently
/// unreadable from an `ensures` clause. `ensures result <= max` over a
/// parameter `max` yields 4 UNKNOWN rows with NO diagnostic naming the
/// identifier, while the byte-identical body with the parameter called
/// `limit`, `mask` or `m` proves 4/4 in the same compilation. See §16.2 of
/// `docs/STRICT_VERIFICATION_FRAGMENT.md`; `trust_intbound_strict_gate.sh`
/// mutation F pins it.
pub fn clamp_to_max(value: u64, limit: u64) -> u64
clauses [ensures result <= value ensures result <= limit]
{
    if value > limit {
        return limit;
    }
    value
}
}

// a param named `max` used ONLY IN THE BODY, never in a clause
// `max` in the clause, but the clause is the ONLY mention
trust_contract_fn! {
/// `value` saturated to the largest value an unsigned `w`-bit integer holds.
///
/// **Tier 2.** A dispatcher over [`clamp_to_max`], which states the bound.
/// Out-of-domain widths saturate to `u64::MAX`, i.e. they do not clamp at all —
/// the WIDE direction, per the module doc.
///
/// **Clause `result <= value`.** This is a saturating clamp, so the bound it
/// can state is the one `clamp_to_max` already proves on the value side; the
/// WIDTH side is out of the fragment here because out-of-domain widths
/// deliberately do not clamp at all. One real obligation is the point: without
/// a contract this body has ZERO, and a zero-obligation body whose calls the
/// registry cannot discharge publishes `native-verification-gap` rather than a
/// vacuous green.
pub fn clamp_unsigned_to_width(value: u64, w: u32) -> u64
clauses [ensures result <= value]
{
    clamp_to_max(value, unsigned_max(w))
}
}

trust_contract_fn! {
/// `1` iff `value` is representable in an unsigned `w`-bit integer.
///
/// The fragment-legal restatement of `unsigned_fits_width`, `uint_fits_width`
/// and `bv_fits_unsigned` — three functions that answer this question with
/// three different domain conventions (module doc). Out-of-domain widths answer
/// `0`: nothing fits a width this crate cannot bound, which is the fail-closed
/// direction for an ADMISSION test (as opposed to a RANGE bound, where wide is
/// the safe direction — the two point opposite ways and that is not an
/// inconsistency, it is what each one is for).
///
/// **Clause `result <= 1`.** Admits constant `0` and constant `1`;
/// `unsigned_fits_matches_a_u128_oracle` admits neither.
pub fn unsigned_fits(value: u64, w: u32) -> u8
clauses [ensures result <= 1]
{
    raw_unsigned_fits(value, w)
}
}

fn raw_unsigned_fits(value: u64, w: u32) -> u8 {
    if raw_width_is_supported(w) == 0 {
        return 0;
    }
    let m = unsigned_max_raw(w);
    if value <= m {
        return 1;
    }
    0
}

trust_contract_fn! {
/// `1` iff the NON-NEGATIVE `value` is representable in a signed `w`-bit
/// two's-complement integer, i.e. `value <= 2^(w-1) - 1`.
///
/// **Clause `result <= 1`.** Admits constant `0` and constant `1`;
/// `signed_fits_matches_a_u128_oracle` admits neither, and
/// `signed_fits_is_strictly_tighter_than_unsigned_fits` pins that this is not
/// accidentally the same function as [`unsigned_fits`].
pub fn signed_fits_nonneg(value: u64, w: u32) -> u8
clauses [ensures result <= 1]
{
    raw_signed_fits_nonneg(value, w)
}
}

fn raw_signed_fits_nonneg(value: u64, w: u32) -> u8 {
    if raw_width_is_supported(w) == 0 {
        return 0;
    }
    let m = raw_signed_max(w);
    if value <= m {
        return 1;
    }
    0
}

trust_contract_fn! {
/// `1` iff a NEGATIVE value of magnitude `mag` is representable in a signed
/// `w`-bit two's-complement integer, i.e. `mag <= 2^(w-1)`.
///
/// Split from [`signed_fits_nonneg`] because two's complement is ASYMMETRIC:
/// `-128` fits an `i8` and `128` does not. A single predicate over a signed
/// value cannot be written here (§10.1 — a negative literal in a clause is
/// silently UNKNOWN), and collapsing the two into one bound is precisely the
/// off-by-one this crate exists to stop.
///
/// **Clause `result <= 1`.** Admits constant `0` and constant `1`;
/// `signed_fits_magnitude_admits_exactly_one_more_than_nonneg` rules out both,
/// and rules out the collapse.
pub fn signed_fits_magnitude(mag: u64, w: u32) -> u8
clauses [ensures result <= 1]
{
    raw_signed_fits_magnitude(mag, w)
}
}

fn raw_signed_fits_magnitude(mag: u64, w: u32) -> u8 {
    if raw_width_is_supported(w) == 0 {
        return 0;
    }
    let m = raw_signed_min_magnitude(w);
    if mag <= m {
        return 1;
    }
    0
}


#[cfg(test)]
mod tests {
    use super::*;

    /// INDEPENDENT ORACLE. `2^n - 1` by repeated doubling — no shift, no table,
    /// no call into the crate under test. It shares no line and no operator
    /// with the 64-arm literal chains it checks, which is the point: an oracle
    /// derived from the function under test cannot fail under a mutation of it.
    fn ones_oracle(n: u32) -> u128 {
        let mut acc: u128 = 0;
        let mut i = 0;
        while i < n {
            acc = acc * 2 + 1;
            i += 1;
        }
        acc
    }

    /// INDEPENDENT ORACLE. `2^n` by repeated doubling.
    fn pow2_oracle(n: u32) -> u128 {
        let mut acc: u128 = 1;
        let mut i = 0;
        while i < n {
            acc *= 2;
            i += 1;
        }
        acc
    }

    /// The whole out-of-domain range plus every supported width.
    const WIDTHS: core::ops::RangeInclusive<u32> = 0..=200;

    #[test]
    fn ones_oracle_is_itself_right() {
        // The oracle is checked against the language before anything is checked
        // against the oracle.
        assert_eq!(ones_oracle(0), 0);
        assert_eq!(ones_oracle(1), 1);
        assert_eq!(ones_oracle(8), 255);
        assert_eq!(ones_oracle(64), u64::MAX as u128);
        assert_eq!(pow2_oracle(0), 1);
        assert_eq!(pow2_oracle(63), 1u128 << 63);
        assert_eq!(pow2_oracle(64), 1u128 << 64);
    }

    #[test]
    fn width_is_supported_is_exactly_1_through_64() {
        for w in WIDTHS {
            let want = u8::from(w >= 1 && w <= 64);
            assert_eq!(width_is_supported(w), want, "width_is_supported({w})");
        }
    }

    #[test]
    fn unsigned_max_matches_a_u128_oracle() {
        for w in WIDTHS {
            let want =
                if w >= 1 && w <= 64 { ones_oracle(w) as u64 } else { u64::MAX };
            assert_eq!(unsigned_max(w), want, "unsigned_max({w})");
        }
    }

    #[test]
    fn signed_max_matches_a_u128_oracle() {
        for w in WIDTHS {
            let want =
                if w >= 1 && w <= 64 { ones_oracle(w - 1) as u64 } else { (1u128 << 63) as u64 - 1 };
            assert_eq!(signed_max(w), want, "signed_max({w})");
        }
    }

    #[test]
    fn signed_min_magnitude_matches_a_u128_oracle() {
        for w in WIDTHS {
            let want =
                if w >= 1 && w <= 64 { pow2_oracle(w - 1) as u64 } else { (1u128 << 63) as u64 };
            assert_eq!(signed_min_magnitude(w), want, "signed_min_magnitude({w})");
        }
    }

    /// The two's-complement ASYMMETRY, as a law rather than a table: the
    /// negative side reaches exactly one further than the positive side. This
    /// is the single relation most often got wrong by one, and it is checked
    /// across the whole supported domain rather than at a few widths.
    #[test]
    fn min_magnitude_is_exactly_one_above_max() {
        for w in 1..=64u32 {
            assert_eq!(
                signed_min_magnitude(w),
                signed_max(w) + 1,
                "two's-complement asymmetry at width {w}"
            );
        }
    }

    /// The unsigned range is exactly twice the signed one, plus one.
    #[test]
    fn unsigned_max_is_twice_signed_max_plus_one() {
        for w in 1..=63u32 {
            assert_eq!(unsigned_max(w), 2 * signed_max(w) + 1, "at width {w}");
        }
        // w = 64 checked in u128 to avoid the u64 wrap the relation would need.
        assert_eq!(unsigned_max(64) as u128, 2 * signed_max(64) as u128 + 1);
    }

    /// §15.5. THE SENTINEL POINTS AT THE WIDE END, AND THAT IS LOAD-BEARING.
    /// A too-narrow bound is a false hypothesis handed to the solver; a
    /// too-wide one merely loses precision. If a future edit makes any of
    /// these `0`, every consumer that forgets `width_is_supported` silently
    /// starts claiming that nothing fits — the unsound direction.
    #[test]
    fn sentinel_is_the_wide_end_not_zero() {
        for w in [0u32, 65, 66, 100, 128, 200, u32::MAX] {
            assert_eq!(unsigned_max(w), u64::MAX, "unsigned_max sentinel at {w}");
            assert_eq!(signed_max(w), (1u128 << 63) as u64 - 1, "signed_max sentinel at {w}");
            assert_eq!(
                signed_min_magnitude(w),
                (1u128 << 63) as u64,
                "signed_min_magnitude sentinel at {w}"
            );
            assert_ne!(unsigned_max(w), 0);
        }
    }

    /// §15.5's residual trap, pinned so it cannot be forgotten: the sentinel is
    /// INDISTINGUISHABLE from the genuine answer at the top of the domain. A
    /// consumer reading a bound without first reading `width_is_supported`
    /// cannot tell `w = 64` from `w = 0` or `w = 999`.
    #[test]
    fn unsigned_max_sentinel_collides_with_width_64() {
        assert_eq!(unsigned_max(64), unsigned_max(0));
        assert_eq!(unsigned_max(64), unsigned_max(999));
        assert_eq!(width_is_supported(64), 1);
        assert_eq!(width_is_supported(0), 0);
        assert_eq!(width_is_supported(999), 0);
    }

    #[test]
    fn clamp_width_is_identity_below_65_and_saturates_above() {
        for w in WIDTHS {
            let want = if w > 64 { 64 } else { w };
            assert_eq!(clamp_width(w), want, "clamp_width({w})");
        }
    }

    #[test]
    fn clamp_to_max_is_the_minimum() {
        let grid = [0u64, 1, 2, 7, 127, 128, 255, 256, 65535, 1 << 32, u64::MAX - 1, u64::MAX];
        for &a in &grid {
            for &b in &grid {
                assert_eq!(clamp_to_max(a, b), core::cmp::min(a, b), "clamp_to_max({a},{b})");
            }
        }
    }

    #[test]
    fn clamp_unsigned_to_width_saturates_into_the_width() {
        for w in 1..=64u32 {
            let m = ones_oracle(w) as u64;
            assert_eq!(clamp_unsigned_to_width(u64::MAX, w), m, "saturate at width {w}");
            assert_eq!(clamp_unsigned_to_width(0, w), 0);
        }
        // Out of domain the sentinel does not clamp at all — the WIDE direction.
        assert_eq!(clamp_unsigned_to_width(u64::MAX, 0), u64::MAX);
        assert_eq!(clamp_unsigned_to_width(u64::MAX, 65), u64::MAX);
    }

    #[test]
    fn unsigned_fits_matches_a_u128_oracle() {
        let values = [0u64, 1, 2, 127, 128, 255, 256, 65535, 65536, u64::MAX - 1, u64::MAX];
        for w in WIDTHS {
            for &v in &values {
                let want = u8::from(w >= 1 && w <= 64 && (v as u128) <= ones_oracle(w));
                assert_eq!(unsigned_fits(v, w), want, "unsigned_fits({v},{w})");
            }
        }
    }

    #[test]
    fn signed_fits_matches_a_u128_oracle() {
        let values = [0u64, 1, 2, 126, 127, 128, 255, 32767, 32768, u64::MAX];
        for w in WIDTHS {
            for &v in &values {
                let nonneg = u8::from(w >= 1 && w <= 64 && (v as u128) <= ones_oracle(w - 1));
                assert_eq!(signed_fits_nonneg(v, w), nonneg, "signed_fits_nonneg({v},{w})");
                let mag = u8::from(w >= 1 && w <= 64 && (v as u128) <= pow2_oracle(w - 1));
                assert_eq!(signed_fits_magnitude(v, w), mag, "signed_fits_magnitude({v},{w})");
            }
        }
    }

    /// The three predicates are three DIFFERENT functions. Without this a
    /// mutation collapsing any pair of them passes every test above that only
    /// checks one at a time.
    #[test]
    fn signed_fits_is_strictly_tighter_than_unsigned_fits() {
        // 127 fits i8, 128 does not; both fit u8.
        assert_eq!(signed_fits_nonneg(127, 8), 1);
        assert_eq!(signed_fits_nonneg(128, 8), 0);
        assert_eq!(unsigned_fits(128, 8), 1);
        assert_eq!(unsigned_fits(255, 8), 1);
        assert_eq!(unsigned_fits(256, 8), 0);
    }

    /// Two's complement admits `-128i8` but not `128i8`. A single predicate for
    /// both signs is the off-by-one this crate exists to stop.
    #[test]
    fn signed_fits_magnitude_admits_exactly_one_more_than_nonneg() {
        assert_eq!(signed_fits_magnitude(128, 8), 1); // -128 fits i8
        assert_eq!(signed_fits_nonneg(128, 8), 0); //  128 does not
        assert_eq!(signed_fits_magnitude(129, 8), 0);
        for w in 1..=64u32 {
            let boundary = signed_min_magnitude(w);
            assert_eq!(signed_fits_magnitude(boundary, w), 1, "at width {w}");
            assert_eq!(signed_fits_nonneg(boundary, w), 0, "at width {w}");
        }
    }

    /// THE CONSUMER DIFFERENTIAL. `trust-ir-bridge`'s `native_int_min_max` was
    /// deleted and rebuilt on this crate; this is the exact `i128` shift body
    /// it used to have, checked against the composition that replaced it over
    /// the whole width domain and both signednesses. If these ever disagree the
    /// extraction changed behaviour, which is the one thing it must not do.
    #[test]
    fn replaced_consumer_body_is_reproduced_exactly() {
        fn original(width: u32, signed: bool) -> Option<(i128, i128)> {
            if width == 0 || width > 64 {
                return None;
            }
            if signed {
                Some((-(1i128 << (width - 1)), (1i128 << (width - 1)) - 1))
            } else {
                Some((0, (1i128 << width) - 1))
            }
        }
        fn replacement(width: u32, signed: bool) -> Option<(i128, i128)> {
            if width_is_supported(width) == 0 {
                return None;
            }
            if signed {
                Some((
                    -i128::from(signed_min_magnitude(width)),
                    i128::from(signed_max(width)),
                ))
            } else {
                Some((0, i128::from(unsigned_max(width))))
            }
        }
        for w in WIDTHS {
            for signed in [false, true] {
                assert_eq!(original(w, signed), replacement(w, signed), "at ({w}, {signed})");
            }
        }
    }
}
