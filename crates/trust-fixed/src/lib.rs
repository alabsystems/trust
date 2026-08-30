//! Total, verified fixed-point / scaled-integer arithmetic for `no_std` Trust
//! components: Q-format conversion, scaled multiply-divide, the four integer
//! rounding modes, and percentage-with-precision.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0
//!
//! # Why this crate exists, and who calls it
//!
//! This tree already has [`trust-ratio`](../trust_ratio/index.html) for scaled
//! ratios. Every one of its three ratio functions **truncates**, and none of
//! them says which rounding mode a caller is getting because there is only one:
//!
//! **`crates/trust-ratio/src/lib.rs:197-246`**
//!
//! ```text
//! pub fn percent(num: u32, den: u32) -> u32 { … (num as u64) * 100 / (den as u64) … }
//! pub fn permille(num: u32, den: u32) -> u32 { … * 1000 / … }
//! pub fn scaled_ratio(num: u32, den: u32, scale: u32) -> u32 { … * (scale as u64) / … }
//! ```
//!
//! Truncation toward zero is a *rounding mode nobody chose*. It is the default
//! only because `/` is, and its bias is one-sided: `percent(99, 100)` and
//! `percent(999, 1000)` are both `99`, and no obligation in this tree can see
//! the difference between "99%" and "99.9% reported as 99%". `trust-ratio`'s own
//! module note records the sharper version of the same hazard —
//! `percent(42_949_673, 1)` returned `4` while every obligation it had was
//! proved — because a truncating `as` cast is neither an overflow nor a zero
//! divisor (`docs/STRICT_VERIFICATION_FRAGMENT.md` §2.5, §4.6).
//!
//! This crate is the other half: the **rounded**, **ceilinged** and
//! **half-to-even** twins of the same arithmetic, plus the Q-format scale
//! lattice they are computed against, each with its overflow and zero-divisor
//! obligations discharged on every input.
//!
//! ## The four sites this was written for
//!
//! **1. A coverage percentage printed to two decimals, computed by flooring.**
//!
//! `crates/trust-clean-origin/src/table.rs:2343-2347`
//!
//! ```text
//! pub fn coverage_basis_points() -> usize {
//!     if DEMANDS.is_empty() { return 0; }
//!     covered_demands() * 10_000 / DEMANDS.len()
//! }
//! ```
//!
//! and `crates/trust-clean-origin/tests/table_controls.rs:947-951` prints it as
//!
//! ```text
//! COVERAGE : {}.{:02}%  ({basis_points} basis points)
//! …
//! basis_points / 100,
//! basis_points % 100,
//! ```
//!
//! Two separate facts are unstated there. The multiply `covered * 10_000` is
//! unbounded — nothing in that function or its callers bounds `covered_demands()`
//! — and the division floors, so a coverage of 99.995% prints as `99.99%`. The
//! rounding direction of a *published coverage number* is exactly the kind of
//! thing that should be a decision rather than a side effect of the operator.
//! [`percent_hundredths`] is that computation with the multiply proved and the
//! rounding chosen; [`percent_whole`] and [`percent_fraction`] are the split.
//!
//! **2. A memory budget as a scaled fraction of physical RAM.**
//!
//! `crates/trust-router/src/memory_jobserver.rs:483-487`
//!
//! ```text
//! let observed = ((u128::from(total) * u128::from(DEFAULT_BUDGET_NUMERATOR))
//!     / u128::from(DEFAULT_BUDGET_DENOMINATOR)) as u64;
//! ```
//!
//! The `u128` widening is there to make the multiply safe, and it does — but a
//! `u128` multiply is measured **outside** the verifiable fragment
//! (`docs/STRICT_VERIFICATION_FRAGMENT.md` §2.3), so that spelling can never be
//! proved. [`mul_div_trunc`] is the same computation one width down, where the
//! multiply's own overflow row proves for every input.
//!
//! **3. A scaled multiply-divide with a hand-tuned rounding bias, spelled twice
//! in two crates.**
//!
//! `crates/trust-js-differential/src/util.rs:40-41`
//!
//! ```text
//! let mp = (5 * doy + 2) / 153;
//! let d = (doy - (153 * mp + 2) / 5 + 1) as u32;
//! ```
//!
//! and `targo-trust/src/release_cli/product_proof.rs:3438`
//!
//! ```text
//! let day_of_year = (153 * month_prime + 2) / 5 + day as i32 - 1;
//! ```
//!
//! The `+ 2` is a rounding constant chosen by hand for one divisor. That is
//! [`mul_div_round`]'s job, where the constant is `d / 2` and is derived from
//! the divisor rather than transcribed.
//!
//! **4. A power-of-ten scale table.**
//!
//! `crates/trust-bignum/src/decimal.rs:115,129` index `POW10` for a decimal
//! scale factor. [`decimal_scale`] is the same lookup as a *checked
//! proposition*: `ensures result <= 1_000_000_000` is discharged on every
//! input, including the ones past the end of the table, where an index would
//! panic and this saturates.
//!
//! # How to read a function here
//!
//! **Tier 1** functions carry an `ensures` clause that the compiler discharges;
//! they state a bound on their result and that bound is a proved proposition.
//! **Tier 2** functions carry no clause: what is proved for them is *totality* —
//! no overflow, no division by zero, no panic, on every input — and nothing
//! else. Both tiers are proved fail-closed; the difference is what is claimed.
//!
//! Every function is total. There are no `requires` clauses, because a
//! precondition is fatal under the strict lane; a rejected input gets a
//! saturating or sentinel answer, never a panic.
//!
//! # Two shapes this crate is built around, and why
//!
//! **The scale is a parameter, never a format code.** `to_int_round(value,
//! scale)` takes `65536`, not `16`. That is not an API preference: an
//! arithmetic `Assert` sitting after a CALL cannot be bundled into any caller
//! (`docs/STRICT_VERIFICATION_FRAGMENT.md` §9.1), so folding the
//! [`binary_scale`] lookup into an arithmetic body makes every caller of that
//! body fail to lower. Look the scale up once, pass the value in.
//!
//! **The divider is spelled out at every entry point.** `/` and `%` are opaque
//! to bundling in both directions — an *uncontracted* caller of a
//! division-bearing callee fails exactly as a contracted one does (§7.2) — so
//! [`rescale_trunc`] cannot call [`mul_div_trunc`] even though it computes
//! exactly `mul_div_trunc(value, to_scale, from_scale)`. The duplication is
//! forced by the fragment, and the equivalence it risks is pinned by
//! `rescale_trunc_is_mul_div_trunc_with_its_arguments_reordered` rather than by
//! a comment.
//!
//! # What is NOT here, and why
//!
//! **Signed fixed-point.** Measured 2026-08-29 against stage1 driver
//! `803f47350d324d26`, `i32`/`i64` are outside the fragment in three separate
//! places, and the first of them is fatal for this domain:
//!
//! * a widening signed multiply by a **variable** — `(a as i64) * (b as i64)`,
//!   and equally `(a as i32) * (b as i32)` from two `i16` — is RUNTIME CHECKED
//!   with an UNKNOWN hardened twin, where the unsigned shape one signedness
//!   over proves. A signed multiply by a **constant** proves. A scaled
//!   multiply-divide is a variable multiply by definition, so there is no
//!   signed lane for the core of this crate;
//! * `a / b` at `i32` is **refuted**, with the counterexample
//!   `a = -2147483648, b = -1` — correctly, and it stays UNKNOWN even with both
//!   side conditions guarded;
//! * an `ensures` bound against a **negative literal** (`result >= -1`) measures
//!   UNKNOWN, while `result >= 0` on the same `i32` proves.
//!
//! A signed twin would therefore be tier 2 at best and could not state a single
//! bound. It is not written rather than written weaker.
//!
//! **A `usize` lane.** The saturating multiply that a `usize` scale needs is a
//! `u128` multiply, which §2.3 measures as runtime-checked with an unknown
//! twin. This crate is `u32`-in / `u64`-internal for that reason.
//!
//! **Fractional bits above 16.** [`binary_scale`] stops at `2^16`, which is
//! Q16.16 — the canonical format, and the largest whose scale, mask and
//! saturating product all stay meaningful in a `u32` word. Extending it is
//! bounded by the transport rather than by the domain: each additional arm is
//! another discharged postcondition row, and past roughly 70 postconditions in
//! one crate `targo trust check` exits 2 having printed only `could not seal the
//! final compiler rows …` — no `Gate:`, no `Summary:`, no diagnostic naming
//! anything (`docs/STRICT_VERIFICATION_FRAGMENT.md` §9.2). The 52 rows here are
//! deliberately inside that bracket.
//!
//! **A rounding-mode parameter.** `to_int(value, scale, mode)` would be one
//! function instead of four, and it cannot be written: a two-armed select
//! between constants supplies the interval engine no range at all (§2.7), so
//! the rounding increment has to be a literal in each body.

#![no_std]

// ---------------------------------------------------------------------------
// TIER 1 — the scale lattice.
//
// These are the lookups a caller hoists (§9.1) before doing any arithmetic.
// Each is an ordered guard chain returning constants, which is the one body
// shape that discharges a postcondition with no arithmetic in it at all.
// ---------------------------------------------------------------------------

/// `10^decimals`, saturating at `10^9`.
///
/// **Tier 1.** Proved: `result <= 1_000_000_000` on every input, including the
/// ones past the top of the supported set. Total where a `POW10[decimals]`
/// table index panics.
///
/// Ask [`decimal_scale_is_exact`] whether the answer is the true power or the
/// saturated ceiling.
pub fn decimal_scale(decimals: u32) -> u32 ensures result <= 1000000000 {
    if decimals == 0 {
        return 1;
    }
    if decimals == 1 {
        return 10;
    }
    if decimals == 2 {
        return 100;
    }
    if decimals == 3 {
        return 1000;
    }
    if decimals == 4 {
        return 10000;
    }
    if decimals == 5 {
        return 100000;
    }
    if decimals == 6 {
        return 1000000;
    }
    if decimals == 7 {
        return 10000000;
    }
    if decimals == 8 {
        return 100000000;
    }
    1000000000
}

/// `1` when [`decimal_scale`] returns the true `10^decimals`, `0` when it
/// saturated.
///
/// **Tier 1.** Proved: `result <= 1`.
pub fn decimal_scale_is_exact(decimals: u32) -> u8 ensures result <= 1 {
    if decimals > 9 {
        return 0;
    }
    1
}

/// `2^frac_bits`, saturating at `2^16`.
///
/// **Tier 1.** Proved: `result <= 65536` on every input. This is the Q-format
/// scale: pass `binary_scale(16)` for Q16.16.
///
/// Ask [`binary_scale_is_exact`] whether the answer is the true power.
pub fn binary_scale(frac_bits: u32) -> u32 ensures result <= 65536 {
    if frac_bits == 0 {
        return 1;
    }
    if frac_bits == 1 {
        return 2;
    }
    if frac_bits == 2 {
        return 4;
    }
    if frac_bits == 3 {
        return 8;
    }
    if frac_bits == 4 {
        return 16;
    }
    if frac_bits == 5 {
        return 32;
    }
    if frac_bits == 6 {
        return 64;
    }
    if frac_bits == 7 {
        return 128;
    }
    if frac_bits == 8 {
        return 256;
    }
    if frac_bits == 9 {
        return 512;
    }
    if frac_bits == 10 {
        return 1024;
    }
    if frac_bits == 11 {
        return 2048;
    }
    if frac_bits == 12 {
        return 4096;
    }
    if frac_bits == 13 {
        return 8192;
    }
    if frac_bits == 14 {
        return 16384;
    }
    if frac_bits == 15 {
        return 32768;
    }
    65536
}

/// `1` when [`binary_scale`] returns the true `2^frac_bits`, `0` when it
/// saturated.
///
/// **Tier 1.** Proved: `result <= 1`.
pub fn binary_scale_is_exact(frac_bits: u32) -> u8 ensures result <= 1 {
    if frac_bits > 16 {
        return 0;
    }
    1
}

/// `2^frac_bits - 1`: the low-bit mask that selects the fractional part of a
/// binary fixed-point word, saturating at `2^16 - 1`.
///
/// **Tier 1.** Proved: `result <= 65535`.
///
/// This exists as its own lattice rather than as `binary_scale(b) - 1` because
/// the subtraction would have to happen *inside* an arithmetic body, and a
/// subtraction destroys the range a widening cast supplies
/// (`docs/STRICT_VERIFICATION_FRAGMENT.md` §9.1). Feeding
/// [`binary_frac_part`] from here keeps that whole class of repair unnecessary.
pub fn binary_frac_mask(frac_bits: u32) -> u32 ensures result <= 65535 {
    if frac_bits == 0 {
        return 0;
    }
    if frac_bits == 1 {
        return 1;
    }
    if frac_bits == 2 {
        return 3;
    }
    if frac_bits == 3 {
        return 7;
    }
    if frac_bits == 4 {
        return 15;
    }
    if frac_bits == 5 {
        return 31;
    }
    if frac_bits == 6 {
        return 63;
    }
    if frac_bits == 7 {
        return 127;
    }
    if frac_bits == 8 {
        return 255;
    }
    if frac_bits == 9 {
        return 511;
    }
    if frac_bits == 10 {
        return 1023;
    }
    if frac_bits == 11 {
        return 2047;
    }
    if frac_bits == 12 {
        return 4095;
    }
    if frac_bits == 13 {
        return 8191;
    }
    if frac_bits == 14 {
        return 16383;
    }
    if frac_bits == 15 {
        return 32767;
    }
    65535
}

// ---------------------------------------------------------------------------
// Uncontracted arithmetic helpers. These exist so the tier-1 wrappers below can
// stay arithmetic-free (§1.1); their own safety obligations are all proved, and
// none of them contains `/`, `%`, `>>` or `<<`, which is what lets them be
// bundled into a caller at all (§7.2).
// ---------------------------------------------------------------------------

fn clamp_u32(v: u32, hi: u32) -> u32 ensures result <= hi {
    if v > hi { hi } else { v }
}

fn raw_sat_add(a: u32, b: u32) -> u32 {
    let s: u64 = (a as u64) + (b as u64);
    if s > 4294967295 {
        return 4294967295;
    }
    s as u32
}

fn raw_sat_sub(a: u32, b: u32) -> u32 {
    if a < b {
        return 0;
    }
    a - b
}

fn raw_sat_mul(a: u32, b: u32) -> u32 {
    let p: u64 = (a as u64) * (b as u64);
    if p > 4294967295 {
        return 4294967295;
    }
    p as u32
}

fn raw_from_parts(int_part: u32, frac: u32, scale: u32) -> u32 {
    let p: u64 = (int_part as u64) * (scale as u64);
    let s: u64 = p + (frac as u64);
    if s > 4294967295 {
        return 4294967295;
    }
    s as u32
}

// ---------------------------------------------------------------------------
// TIER 2 — saturating scaled arithmetic. No division, so every one of these
// bundles into a caller and can sit under a tier-1 wrapper.
// ---------------------------------------------------------------------------

/// Sum of two fixed-point values at the same scale, saturating at `u32::MAX`.
///
/// **Tier 2.** Proved: the addition cannot overflow. Agrees with
/// `u32::saturating_add` on every input.
pub fn scaled_add(a: u32, b: u32) -> u32 {
    raw_sat_add(a, b)
}

/// Difference of two fixed-point values at the same scale, saturating at `0`.
///
/// **Tier 2.** Proved: the subtraction cannot underflow. Agrees with
/// `u32::saturating_sub` on every input.
pub fn scaled_sub(a: u32, b: u32) -> u32 {
    raw_sat_sub(a, b)
}

/// `units` whole units as a fixed-point value at `scale`, saturating at
/// `u32::MAX`.
///
/// **Tier 2.** Proved: the multiplication cannot overflow. This is the
/// conversion `POW10`-style table code performs with an unchecked `*`.
pub fn to_fixed(units: u32, scale: u32) -> u32 {
    raw_sat_mul(units, scale)
}

/// A fixed-point value assembled from an integer part and a fractional
/// numerator, saturating at `u32::MAX`.
///
/// **Tier 2.** Proved: neither the multiplication nor the addition can
/// overflow. `frac` is *not* required to be below `scale`; a caller that passes
/// a larger numerator gets a correctly carried result rather than a rejection.
pub fn from_parts(int_part: u32, frac: u32, scale: u32) -> u32 {
    raw_from_parts(int_part, frac, scale)
}

/// The fractional part of a **binary** fixed-point value, selected by the mask
/// from [`binary_frac_mask`].
///
/// **Tier 2**, and it carries no obligations at all: a bitwise `&` cannot
/// overflow, so there is nothing to prove and its absence is not missing
/// coverage (`docs/STRICT_VERIFICATION_FRAGMENT.md` §7.10).
///
/// This is the one fractional-part spelling that **bundles**. [`frac_part`]
/// computes the same value for a power-of-two scale with `%`, and a `%` makes
/// its function unbundlable into any caller (§7.2). Prefer this one wherever
/// the scale is a power of two.
pub fn binary_frac_part(value: u32, mask: u32) -> u32 {
    value & mask
}

// ---------------------------------------------------------------------------
// TIER 1 — contracted wrappers. Each is a single call to a contract-carrying
// callee and nothing else (§1.1 shape B), and each clamp is LIVE: there is an
// argument that reaches it.
// ---------------------------------------------------------------------------

/// [`scaled_add`], never above `cap`.
///
/// **Tier 1.** Proved: `result <= cap` on every input.
pub fn scaled_add_within(a: u32, b: u32, cap: u32) -> u32 ensures result <= cap {
    clamp_u32(raw_sat_add(a, b), cap)
}

/// [`to_fixed`], never above `cap`.
///
/// **Tier 1.** Proved: `result <= cap` on every input. The bound a caller
/// actually wants from a scale conversion — "this stays inside my word" — as a
/// checked proposition rather than a comment.
pub fn to_fixed_within(units: u32, scale: u32, cap: u32) -> u32 ensures result <= cap {
    clamp_u32(raw_sat_mul(units, scale), cap)
}

/// [`from_parts`], never above `cap`.
///
/// **Tier 1.** Proved: `result <= cap` on every input.
pub fn from_parts_within(int_part: u32, frac: u32, scale: u32, cap: u32) -> u32
    ensures result <= cap
{
    clamp_u32(raw_from_parts(int_part, frac, scale), cap)
}

/// [`binary_frac_part`], never above `cap`.
///
/// **Tier 1.** Proved: `result <= cap` on every input.
pub fn binary_frac_within(value: u32, mask: u32, cap: u32) -> u32 ensures result <= cap {
    clamp_u32(value & mask, cap)
}

// ---------------------------------------------------------------------------
// TIER 2 — the four rounding modes.
//
// Each spells its own division out. `/` and `%` cannot be bundled in either
// direction (§7.2), so there is no shared divider to factor out and no wrapper
// that would help; the alternative to duplication is not sharing, it is not
// verifying.
// ---------------------------------------------------------------------------

/// `value / scale`, truncated toward zero. Returns `0` when `scale == 0`.
///
/// **Tier 2.** Proved: no division-by-zero panic on any input. The rounding
/// mode `trust-ratio` gives you without asking.
pub fn to_int_trunc(value: u32, scale: u32) -> u32 {
    if scale == 0 {
        return 0;
    }
    value / scale
}

/// `value / scale`, rounded half **away from zero**. Returns `0` when
/// `scale == 0`.
///
/// **Tier 2.** Proved: neither the rounding addition nor the division can
/// panic, on any input. The addition is performed one width up, where
/// `(2^32 - 1) + (2^31 - 1)` cannot wrap; the `+ scale/2` is derived from the
/// divisor rather than being a transcribed constant like
/// `crates/trust-js-differential/src/util.rs:40`'s `+ 2`.
pub fn to_int_round(value: u32, scale: u32) -> u32 {
    if scale == 0 {
        return 0;
    }
    let v: u64 = value as u64;
    let s: u64 = scale as u64;
    let h: u64 = s / 2;
    let n: u64 = v + h;
    let q: u64 = n / s;
    q as u32
}

/// `value / scale`, rounded up. Returns `0` when `scale == 0`.
///
/// **Tier 2.** Proved: no overflow and no division-by-zero, on any input.
///
/// Note the spelling. The textbook `(value + scale - 1) / scale` is **outside**
/// the fragment: the `scale - 1` destroys the range the widening cast supplies,
/// and the addition then measures RUNTIME CHECKED with an UNKNOWN hardened twin
/// (`docs/STRICT_VERIFICATION_FRAGMENT.md` §10.2). Taking the quotient and the
/// remainder and incrementing has no subtraction in it and proves 6/6.
pub fn to_int_ceil(value: u32, scale: u32) -> u32 {
    if scale == 0 {
        return 0;
    }
    let v: u64 = value as u64;
    let s: u64 = scale as u64;
    let q: u64 = v / s;
    let r: u64 = v % s;
    if r == 0 {
        return q as u32;
    }
    if q > 4294967294 {
        return 4294967295;
    }
    let up: u64 = q + 1;
    up as u32
}

/// `value / scale`, rounded half to **even** (banker's rounding). Returns `0`
/// when `scale == 0`.
///
/// **Tier 2.** Proved: no overflow and no division-by-zero, on any input.
///
/// An exact half only exists when `scale` is even, so the odd case is decided
/// by `scale % 2` rather than by the tie rule: for an odd `scale`,
/// `value % scale == scale / 2` is strictly *below* one half and rounds down.
/// Getting that wrong is the classic off-by-one in a half-even implementation
/// and it is invisible to every obligation this function has.
pub fn to_int_round_even(value: u32, scale: u32) -> u32 {
    if scale == 0 {
        return 0;
    }
    let v: u64 = value as u64;
    let s: u64 = scale as u64;
    let i: u64 = v / s;
    let f: u64 = v % s;
    let h: u64 = s / 2;
    let par: u64 = s % 2;
    if f < h {
        return i as u32;
    }
    if f == h {
        if par == 1 {
            return i as u32;
        }
        let e: u64 = i % 2;
        if e == 0 {
            return i as u32;
        }
    }
    if i > 4294967294 {
        return 4294967295;
    }
    let up: u64 = i + 1;
    up as u32
}

/// `value % scale`: the fractional numerator of a fixed-point value. Returns
/// `0` when `scale == 0`.
///
/// **Tier 2.** Proved: no remainder-by-zero panic on any input. For a
/// power-of-two scale prefer [`binary_frac_part`], which computes the same
/// value and, unlike this, can be bundled into a caller.
pub fn frac_part(value: u32, scale: u32) -> u32 {
    if scale == 0 {
        return 0;
    }
    value % scale
}

// ---------------------------------------------------------------------------
// TIER 2 — scaled multiply-divide. `a * b / d` at `u32`, performed at `u64`
// where `(2^32 - 1)^2` cannot wrap, in each of three rounding modes.
// ---------------------------------------------------------------------------

/// `a * b / d`, truncated toward zero and saturating at `u32::MAX`. Returns `0`
/// when `d == 0`.
///
/// **Tier 2.** Proved: the multiplication cannot overflow and the division
/// cannot panic, on every input. This is
/// `crates/trust-router/src/memory_jobserver.rs:485-486`'s budget computation
/// one width down, where the multiply is provable.
pub fn mul_div_trunc(a: u32, b: u32, d: u32) -> u32 {
    if d == 0 {
        return 0;
    }
    let p: u64 = (a as u64) * (b as u64);
    let dd: u64 = d as u64;
    let q: u64 = p / dd;
    if q > 4294967295 {
        return 4294967295;
    }
    q as u32
}

/// `a * b / d`, rounded half away from zero and saturating at `u32::MAX`.
/// Returns `0` when `d == 0`.
///
/// **Tier 2.** Proved: no overflow and no division-by-zero, on every input.
///
/// The proof has almost no slack and that is the point: `p` peaks at
/// `(2^32 - 1)^2 == 18446744065119617025` and `d / 2` at `2147483647`, so the
/// sum peaks at `18446744067267100672` against a `u64::MAX` of
/// `18446744073709551615`. Rounding *at all* is only possible because the
/// increment is `d / 2` and not `d`.
pub fn mul_div_round(a: u32, b: u32, d: u32) -> u32 {
    if d == 0 {
        return 0;
    }
    let p: u64 = (a as u64) * (b as u64);
    let dd: u64 = d as u64;
    let h: u64 = dd / 2;
    let n: u64 = p + h;
    let q: u64 = n / dd;
    if q > 4294967295 {
        return 4294967295;
    }
    q as u32
}

/// `a * b / d`, rounded up and saturating at `u32::MAX`. Returns `0` when
/// `d == 0`.
///
/// **Tier 2.** Proved: no overflow and no division-by-zero, on every input.
/// Spelled with a remainder test rather than `+ (d - 1)`, for the reason
/// [`to_int_ceil`] gives.
pub fn mul_div_ceil(a: u32, b: u32, d: u32) -> u32 {
    if d == 0 {
        return 0;
    }
    let p: u64 = (a as u64) * (b as u64);
    let dd: u64 = d as u64;
    let q: u64 = p / dd;
    let r: u64 = p % dd;
    if r == 0 {
        if q > 4294967295 {
            return 4294967295;
        }
        return q as u32;
    }
    if q > 4294967294 {
        return 4294967295;
    }
    let up: u64 = q + 1;
    up as u32
}

/// The same value re-expressed at a different scale, truncated toward zero.
/// Returns `0` when `from_scale == 0`.
///
/// **Tier 2.** Proved: no overflow and no division-by-zero, on every input.
///
/// This computes exactly `mul_div_trunc(value, to_scale, from_scale)` and
/// cannot call it: a callee containing `/` cannot be bundled into any caller,
/// contracted or not (`docs/STRICT_VERIFICATION_FRAGMENT.md` §7.2). The
/// duplication is forced, and
/// `rescale_trunc_is_mul_div_trunc_with_its_arguments_reordered` is what keeps
/// the two copies honest.
pub fn rescale_trunc(value: u32, from_scale: u32, to_scale: u32) -> u32 {
    if from_scale == 0 {
        return 0;
    }
    let p: u64 = (value as u64) * (to_scale as u64);
    let f: u64 = from_scale as u64;
    let q: u64 = p / f;
    if q > 4294967295 {
        return 4294967295;
    }
    q as u32
}

/// The same value re-expressed at a different scale, rounded half away from
/// zero. Returns `0` when `from_scale == 0`.
///
/// **Tier 2.** Proved: no overflow and no division-by-zero, on every input.
/// The rounded twin of [`rescale_trunc`], and the one to reach for when a value
/// is rescaled more than once: truncation compounds, rounding does not.
pub fn rescale_round(value: u32, from_scale: u32, to_scale: u32) -> u32 {
    if from_scale == 0 {
        return 0;
    }
    let p: u64 = (value as u64) * (to_scale as u64);
    let f: u64 = from_scale as u64;
    let h: u64 = f / 2;
    let n: u64 = p + h;
    let q: u64 = n / f;
    if q > 4294967295 {
        return 4294967295;
    }
    q as u32
}

// ---------------------------------------------------------------------------
// TIER 2 — percentage with precision.
// ---------------------------------------------------------------------------

/// `part` as a percentage of `whole`, in **hundredths of a percent**, rounded
/// half away from zero and clamped to `10000` (= 100.00%). Returns `0` when
/// `whole == 0`.
///
/// **Tier 2.** Proved: the `* 10000` cannot overflow and the division cannot
/// panic, on every input.
///
/// This is `crates/trust-clean-origin/src/table.rs:2347`'s
/// `covered * 10_000 / DEMANDS.len()` with both of its unstated facts
/// discharged: the multiply is performed at `u64`, where `(2^32 - 1) * 10000`
/// cannot wrap, and the rounding direction is a decision rather than whatever
/// `/` does. Split it for display with [`percent_whole`] and
/// [`percent_fraction`].
pub fn percent_hundredths(part: u32, whole: u32) -> u32 {
    if whole == 0 {
        return 0;
    }
    let n: u64 = (part as u64) * 10000;
    let w: u64 = whole as u64;
    let h: u64 = w / 2;
    let t: u64 = n + h;
    let q: u64 = t / w;
    if q > 10000 {
        return 10000;
    }
    q as u32
}

/// The whole-percent part of a [`percent_hundredths`] value.
///
/// **Tier 2.** Proved: no division-by-zero (the divisor is the literal `100`).
pub fn percent_whole(hundredths: u32) -> u32 {
    hundredths / 100
}

/// The two-decimal part of a [`percent_hundredths`] value: the digits after the
/// point, in `0..=99`.
///
/// **Tier 2.** Proved: no remainder-by-zero. Together with [`percent_whole`]
/// this is the `{}.{:02}%` split
/// `crates/trust-clean-origin/tests/table_controls.rs:949-950` performs by
/// hand.
pub fn percent_fraction(hundredths: u32) -> u32 {
    hundredths % 100
}

// ---------------------------------------------------------------------------
// TESTS
//
// The proofs above cover overflow, division-by-zero and the discharged tier-1
// bounds. They do NOT cover whether the answer is right: a truncating `as` cast
// is neither an overflow nor a zero divisor, and a rounding threshold is
// invisible to every obligation in this crate
// (`docs/STRICT_VERIFICATION_FRAGMENT.md` §4.6). Everything below is checked
// against a decision procedure written by a different method — `core`'s own
// `div_ceil` / `saturating_*`, an exact `u128` rational oracle, or a counting
// loop — and exhaustively wherever the domain allows.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::*;

    /// Values chosen to include zero, one, the powers of two and ten this
    /// crate's scales are built from, and both ends of `u32`.
    const VALUES: [u32; 20] = [
        0, 1, 2, 3, 7, 99, 100, 101, 255, 256, 999, 1000, 1001, 65535, 65536, 65537, 1_000_000,
        2_147_483_647, 4_294_967_294, 4_294_967_295,
    ];
    /// Scales including `0` (the sentinel path), odd and even, and both ends.
    const SCALES: [u32; 16] = [
        0, 1, 2, 3, 5, 7, 10, 100, 1000, 4096, 10000, 65536, 999, 1_000_000, 2_147_483_647,
        4_294_967_295,
    ];

    const U32MAX: u128 = 4_294_967_295;

    fn sat(x: u128) -> u32 {
        if x > U32MAX { 4_294_967_295 } else { x as u32 }
    }

    // --- the scale lattice, against `core`'s own exponentiation -------------

    #[test]
    fn decimal_scale_matches_ten_to_the_power_and_saturates_past_it() {
        for d in 0..=9u32 {
            assert_eq!(u64::from(decimal_scale(d)), 10u64.pow(d), "decimal_scale({d})");
            assert_eq!(decimal_scale_is_exact(d), 1, "decimal_scale_is_exact({d})");
        }
        for d in 10..=64u32 {
            assert_eq!(decimal_scale(d), 1_000_000_000, "decimal_scale({d}) must saturate");
            assert_eq!(decimal_scale_is_exact(d), 0, "decimal_scale_is_exact({d})");
        }
    }

    #[test]
    fn binary_scale_matches_two_to_the_power_and_saturates_past_it() {
        for b in 0..=16u32 {
            assert_eq!(u64::from(binary_scale(b)), 1u64 << b, "binary_scale({b})");
            assert_eq!(binary_scale_is_exact(b), 1, "binary_scale_is_exact({b})");
        }
        for b in 17..=64u32 {
            assert_eq!(binary_scale(b), 65536, "binary_scale({b}) must saturate");
            assert_eq!(binary_scale_is_exact(b), 0, "binary_scale_is_exact({b})");
        }
    }

    #[test]
    fn binary_frac_mask_matches_the_low_bit_mask_and_saturates_past_it() {
        for b in 0..=16u32 {
            assert_eq!(u64::from(binary_frac_mask(b)), (1u64 << b) - 1, "binary_frac_mask({b})");
        }
        for b in 17..=64u32 {
            assert_eq!(binary_frac_mask(b), 65535, "binary_frac_mask({b}) must saturate");
        }
    }

    // --- the four rounding modes, against exact oracles ---------------------

    /// Truncation, by counting rather than by dividing. Slow, so it is used
    /// only on the exhaustive small sweep; the extremes go through `u128`.
    fn trunc_by_counting(v: u32, s: u32) -> u32 {
        if s == 0 {
            return 0;
        }
        let mut k: u64 = 0;
        while (k + 1) * u64::from(s) <= u64::from(v) {
            k += 1;
        }
        k as u32
    }

    /// `round(v/s)` half away from zero, exactly: `floor((2v + s) / 2s)`.
    fn round_exact(v: u32, s: u32) -> u32 {
        if s == 0 {
            return 0;
        }
        let (v, s) = (u128::from(v), u128::from(s));
        sat((2 * v + s) / (2 * s))
    }

    /// `round(v/s)` half to even, exactly, comparing `2f` against `s` so that
    /// an odd `s` has no tie at all.
    fn round_even_exact(v: u32, s: u32) -> u32 {
        if s == 0 {
            return 0;
        }
        let (v, s) = (u128::from(v), u128::from(s));
        let i = v / s;
        let f = v % s;
        if f * 2 > s {
            return sat(i + 1);
        }
        if f * 2 < s {
            return sat(i);
        }
        if i % 2 == 0 { sat(i) } else { sat(i + 1) }
    }

    #[test]
    fn every_rounding_mode_matches_its_oracle_exhaustively_on_small_inputs() {
        for v in 0..=400u32 {
            for s in 0..=40u32 {
                assert_eq!(to_int_trunc(v, s), trunc_by_counting(v, s), "to_int_trunc({v},{s})");
                assert_eq!(to_int_round(v, s), round_exact(v, s), "to_int_round({v},{s})");
                let ceil = if s == 0 { 0 } else { v.div_ceil(s) };
                assert_eq!(to_int_ceil(v, s), ceil, "to_int_ceil({v},{s})");
                assert_eq!(
                    to_int_round_even(v, s),
                    round_even_exact(v, s),
                    "to_int_round_even({v},{s})"
                );
                let frac = if s == 0 { 0 } else { v % s };
                assert_eq!(frac_part(v, s), frac, "frac_part({v},{s})");
            }
        }
    }

    #[test]
    fn every_rounding_mode_matches_its_oracle_at_the_extremes() {
        for &v in VALUES.iter() {
            for &s in SCALES.iter() {
                let t = if s == 0 { 0 } else { (u128::from(v) / u128::from(s)) as u32 };
                assert_eq!(to_int_trunc(v, s), t, "to_int_trunc({v},{s})");
                assert_eq!(to_int_round(v, s), round_exact(v, s), "to_int_round({v},{s})");
                // `core::u32::div_ceil` — a decision procedure written by
                // someone else, by a different method.
                let c = if s == 0 { 0 } else { v.div_ceil(s) };
                assert_eq!(to_int_ceil(v, s), c, "to_int_ceil({v},{s})");
                assert_eq!(
                    to_int_round_even(v, s),
                    round_even_exact(v, s),
                    "to_int_round_even({v},{s})"
                );
            }
        }
    }

    /// The classic half-even off-by-one: for an ODD scale there is no exact
    /// half, so `v % s == s / 2` must round DOWN, not to the nearest even.
    /// Spelled out separately because it is the one case a symmetric-looking
    /// implementation gets wrong, and no obligation in this crate can see it.
    #[test]
    fn half_even_has_no_tie_at_an_odd_scale() {
        // 7/3 == 2.333: `f == h == 1`, and the answer is 2, not 3.
        assert_eq!(to_int_round_even(7, 3), 2);
        assert_eq!(to_int_round_even(8, 3), 3);
        // 5/2 == 2.5 is a real tie and rounds to the EVEN 2, where half-up
        // gives 3. This pair is what separates the two modes.
        assert_eq!(to_int_round_even(5, 2), 2);
        assert_eq!(to_int_round(5, 2), 3);
        assert_eq!(to_int_round_even(7, 2), 4);
        assert_eq!(to_int_round(7, 2), 4);
    }

    #[test]
    fn the_rounding_modes_are_ordered_on_every_input() {
        for &v in VALUES.iter() {
            for &s in SCALES.iter() {
                let t = to_int_trunc(v, s);
                let r = to_int_round(v, s);
                let c = to_int_ceil(v, s);
                let e = to_int_round_even(v, s);
                assert!(t <= r, "trunc {t} > round {r} at ({v},{s})");
                assert!(r <= c, "round {r} > ceil {c} at ({v},{s})");
                assert!(t <= e && e <= c, "round_even {e} outside [{t},{c}] at ({v},{s})");
            }
        }
    }

    // --- scaled multiply-divide, against a u128 oracle ----------------------

    #[test]
    fn mul_div_matches_the_u128_oracle_in_all_three_modes() {
        for &a in VALUES.iter() {
            for &b in VALUES.iter() {
                for &d in SCALES.iter() {
                    if d == 0 {
                        assert_eq!(mul_div_trunc(a, b, d), 0);
                        assert_eq!(mul_div_round(a, b, d), 0);
                        assert_eq!(mul_div_ceil(a, b, d), 0);
                        continue;
                    }
                    let (p, dd) = (u128::from(a) * u128::from(b), u128::from(d));
                    assert_eq!(mul_div_trunc(a, b, d), sat(p / dd), "trunc({a},{b},{d})");
                    assert_eq!(
                        mul_div_round(a, b, d),
                        sat((2 * p + dd) / (2 * dd)),
                        "round({a},{b},{d})"
                    );
                    assert_eq!(mul_div_ceil(a, b, d), sat(p.div_ceil(dd)), "ceil({a},{b},{d})");
                }
            }
        }
    }

    /// The rounding increment is HALF the divisor. A different fraction leaves
    /// every obligation in this crate proved and the answers wrong, so the
    /// threshold is pinned by name: these are the inputs that sit exactly on
    /// it.
    #[test]
    fn mul_div_round_turns_over_at_exactly_half_the_divisor() {
        // 1*4/8: exactly 0.5, rounds away from zero to 1.
        assert_eq!(mul_div_round(1, 4, 8), 1);
        // one below the half rounds down, one above rounds up.
        assert_eq!(mul_div_round(3, 1, 8), 0);
        assert_eq!(mul_div_round(5, 1, 8), 1);
        // and at a large odd divisor, where `d / 2` is not `d * 0.5`.
        assert_eq!(mul_div_round(1, 499, 999), 0);
        assert_eq!(mul_div_round(1, 500, 999), 1);
    }

    /// The two rescale entry points duplicate `mul_div_*`'s body because a
    /// `/`-bearing callee cannot be bundled into any caller. That duplication
    /// is only safe while the copies agree; this is the assertion that they do.
    #[test]
    fn rescale_is_mul_div_with_its_arguments_reordered() {
        for &v in VALUES.iter() {
            for &f in SCALES.iter() {
                for &t in SCALES.iter() {
                    assert_eq!(
                        rescale_trunc(v, f, t),
                        mul_div_trunc(v, t, f),
                        "rescale_trunc({v},{f},{t})"
                    );
                    assert_eq!(
                        rescale_round(v, f, t),
                        mul_div_round(v, t, f),
                        "rescale_round({v},{f},{t})"
                    );
                }
            }
        }
    }

    #[test]
    fn rescale_preserves_a_value_that_is_exactly_representable() {
        // 1.5 at Q16.16 is 98304; at a decimal scale of 1000 it is 1500.
        assert_eq!(rescale_trunc(98304, 65536, 1000), 1500);
        assert_eq!(rescale_round(98304, 65536, 1000), 1500);
        assert_eq!(rescale_trunc(1500, 1000, 65536), 98304);
        // ... and a value that is not: 1/3 at scale 3 is 1, and at scale 100
        // it is 33.33 — truncation gives 33, rounding gives 33 too, but at
        // scale 1000 the two part company on 333.33 vs 333.
        assert_eq!(rescale_trunc(1, 3, 1000), 333);
        assert_eq!(rescale_round(1, 3, 1000), 333);
        assert_eq!(rescale_trunc(2, 3, 1000), 666);
        assert_eq!(rescale_round(2, 3, 1000), 667);
    }

    // --- percentage with precision -----------------------------------------

    #[test]
    fn percent_hundredths_matches_the_exact_rational_oracle() {
        for &p in VALUES.iter() {
            for &w in VALUES.iter() {
                if w == 0 {
                    assert_eq!(percent_hundredths(p, w), 0);
                    continue;
                }
                let (n, ww) = (u128::from(p) * 10000, u128::from(w));
                let exact = (2 * n + ww) / (2 * ww);
                let want = if exact > 10000 { 10000 } else { exact as u32 };
                assert_eq!(percent_hundredths(p, w), want, "percent_hundredths({p},{w})");
                assert!(percent_hundredths(p, w) <= 10000);
            }
        }
    }

    /// The site this crate was written for. `covered * 10_000 / total` at
    /// `trust-clean-origin/src/table.rs:2347` floors, and
    /// `tests/table_controls.rs:949-950` prints the result as `{}.{:02}%`. At
    /// 19999/20000 the true figure is 99.995%; the floored basis points print
    /// `99.99%` and the rounded ones print `100.00%`.
    #[test]
    fn percent_hundredths_rounds_where_a_floored_basis_point_truncates() {
        let floored = |c: u64, t: u64| (c * 10_000 / t) as u32;

        assert_eq!(floored(19_999, 20_000), 9_999);
        assert_eq!(percent_hundredths(19_999, 20_000), 10_000);
        assert_eq!(percent_whole(10_000), 100);
        assert_eq!(percent_fraction(10_000), 0);

        assert_eq!(floored(2, 3), 6_666);
        assert_eq!(percent_hundredths(2, 3), 6_667);
        assert_eq!(percent_whole(6_667), 66);
        assert_eq!(percent_fraction(6_667), 67);

        // ... and where they agree, they agree.
        assert_eq!(floored(1, 3), 3_333);
        assert_eq!(percent_hundredths(1, 3), 3_333);
        assert_eq!(percent_whole(3_333), 33);
        assert_eq!(percent_fraction(3_333), 33);
    }

    #[test]
    fn percent_whole_and_percent_fraction_split_every_hundredth() {
        for h in 0..=10_000u32 {
            assert_eq!(percent_whole(h), h / 100);
            assert_eq!(percent_fraction(h), h % 100);
            assert_eq!(percent_whole(h) * 100 + percent_fraction(h), h);
            assert!(percent_fraction(h) <= 99);
        }
    }

    // --- saturating scaled arithmetic, against `core` ----------------------

    #[test]
    fn the_saturating_helpers_match_cores_own_saturating_operators() {
        for &a in VALUES.iter() {
            for &b in VALUES.iter() {
                assert_eq!(scaled_add(a, b), a.saturating_add(b), "scaled_add({a},{b})");
                assert_eq!(scaled_sub(a, b), a.saturating_sub(b), "scaled_sub({a},{b})");
                assert_eq!(to_fixed(a, b), a.saturating_mul(b), "to_fixed({a},{b})");
            }
        }
    }

    #[test]
    fn to_fixed_saturates_where_the_unguarded_multiply_wraps() {
        // 65536 * 65536 == 2^32, one past the word. An unguarded `u32` multiply
        // gives 0 here; nothing about that is an overflow the proofs can see
        // once the saturation is deleted, which is why this test exists.
        assert_eq!(to_fixed(65536, 65536), 4_294_967_295);
        assert_eq!(to_fixed(65535, 65536), 4_294_901_760);
        assert_eq!(to_fixed(4_294_967_295, 2), 4_294_967_295);
        assert_eq!(to_fixed(4_294_967_295, 1), 4_294_967_295);
        assert_eq!(to_fixed(0, 4_294_967_295), 0);
    }

    #[test]
    fn from_parts_carries_and_saturates() {
        // 3 units and 1/4 at Q16.16.
        assert_eq!(from_parts(3, 16384, 65536), 3 * 65536 + 16384);
        // a fractional numerator ABOVE the scale carries rather than rejecting.
        assert_eq!(from_parts(3, 70000, 65536), 3 * 65536 + 70000);
        // and the whole thing saturates rather than wrapping.
        assert_eq!(from_parts(65536, 0, 65536), 4_294_967_295);
        assert_eq!(from_parts(4_294_967_295, 4_294_967_295, 4_294_967_295), 4_294_967_295);
    }

    #[test]
    fn from_parts_round_trips_through_to_int_trunc_and_frac_part() {
        for &scale in [1u32, 2, 10, 100, 1000, 4096, 65536].iter() {
            for &i in [0u32, 1, 2, 7, 99, 1000].iter() {
                for f in 0..scale.min(37) {
                    let q = from_parts(i, f, scale);
                    assert_eq!(to_int_trunc(q, scale), i, "int part of ({i},{f},{scale})");
                    assert_eq!(frac_part(q, scale), f, "frac part of ({i},{f},{scale})");
                }
            }
        }
    }

    #[test]
    fn binary_frac_part_matches_modulo_at_every_supported_binary_scale() {
        for b in 0..=16u32 {
            let scale = binary_scale(b);
            let mask = binary_frac_mask(b);
            for &v in VALUES.iter() {
                assert_eq!(binary_frac_part(v, mask), frac_part(v, scale), "b={b} v={v}");
            }
            for v in 0..1000u32 {
                assert_eq!(binary_frac_part(v, mask), v % scale, "b={b} v={v}");
            }
        }
    }

    // --- the tier-1 bounds ------------------------------------------------

    /// Every discharged `ensures` in this crate, asserted from the outside,
    /// plus the fact that each clamp can actually FIRE. A tier-1 bound over a
    /// clamp that no input reaches is a green row about nothing
    /// (`docs/STRICT_VERIFICATION_FRAGMENT.md` §5).
    #[test]
    fn every_tier1_clamp_is_live_and_no_result_ever_exceeds_its_bound() {
        for d in 0..=64u32 {
            assert!(decimal_scale(d) <= 1_000_000_000);
            assert!(decimal_scale_is_exact(d) <= 1);
        }
        for b in 0..=64u32 {
            assert!(binary_scale(b) <= 65536);
            assert!(binary_scale_is_exact(b) <= 1);
            assert!(binary_frac_mask(b) <= 65535);
        }

        let mut add_fired = false;
        let mut fix_fired = false;
        let mut parts_fired = false;
        let mut frac_fired = false;
        for &a in VALUES.iter() {
            for &b in VALUES.iter() {
                for &cap in [0u32, 1, 100, 65536, 4_294_967_295].iter() {
                    let r = scaled_add_within(a, b, cap);
                    assert!(r <= cap, "scaled_add_within({a},{b},{cap}) = {r}");
                    add_fired |= r == cap && scaled_add(a, b) > cap;

                    let r = to_fixed_within(a, b, cap);
                    assert!(r <= cap, "to_fixed_within({a},{b},{cap}) = {r}");
                    fix_fired |= r == cap && to_fixed(a, b) > cap;

                    let r = from_parts_within(a, b, 65536, cap);
                    assert!(r <= cap, "from_parts_within({a},{b},65536,{cap}) = {r}");
                    parts_fired |= r == cap && from_parts(a, b, 65536) > cap;

                    let r = binary_frac_within(a, 65535, cap);
                    assert!(r <= cap, "binary_frac_within({a},65535,{cap}) = {r}");
                    frac_fired |= r == cap && binary_frac_part(a, 65535) > cap;
                }
            }
        }
        assert!(add_fired, "scaled_add_within's clamp is never reached — the bound is vacuous");
        assert!(fix_fired, "to_fixed_within's clamp is never reached — the bound is vacuous");
        assert!(parts_fired, "from_parts_within's clamp is never reached — the bound is vacuous");
        assert!(frac_fired, "binary_frac_within's clamp is never reached — the bound is vacuous");
    }

    /// A CONSISTENCY test, kept deliberately: it computes its expectation from
    /// [`binary_scale`], so it moves with any change to that function and can
    /// never catch one. `scripts/trust_fixed_strict_gate.sh` mutation D asserts
    /// that this one still PASSES while the spelled-out tests go red — a test
    /// that derives its oracle from the code under test is not a test, and this
    /// is the in-tree demonstration.
    #[test]
    fn a_whole_unit_converts_back_to_one_at_every_binary_scale() {
        for b in 0..=16u32 {
            let one = binary_scale(b);
            assert_eq!(to_int_trunc(one, binary_scale(b)), 1);
            assert_eq!(to_int_round(one, binary_scale(b)), 1);
            assert_eq!(to_int_ceil(one, binary_scale(b)), 1);
            assert_eq!(frac_part(one, binary_scale(b)), 0);
        }
    }

    /// Q16.16, spelled out with the numbers rather than with the lattice, so
    /// that a wrong scale is visible.
    #[test]
    fn q16_16_arithmetic_reproduces_hand_computed_values() {
        assert_eq!(binary_scale(16), 65536);
        assert_eq!(binary_frac_mask(16), 65535);
        // 1.5 * 2.5 == 3.75
        let a = from_parts(1, 32768, 65536); // 1.5
        let b = from_parts(2, 32768, 65536); // 2.5
        assert_eq!(mul_div_trunc(a, b, 65536), from_parts(3, 49152, 65536));
        // 10 / 4 == 2.5
        assert_eq!(mul_div_trunc(to_fixed(10, 65536), 65536, to_fixed(4, 65536)), b);
        // and the integer part / rounding of 3.75
        let c = from_parts(3, 49152, 65536);
        assert_eq!(to_int_trunc(c, 65536), 3);
        assert_eq!(to_int_round(c, 65536), 4);
        assert_eq!(to_int_ceil(c, 65536), 4);
        assert_eq!(to_int_round_even(c, 65536), 4);
    }

    #[test]
    fn a_zero_scale_is_a_sentinel_everywhere_rather_than_a_panic() {
        for &v in VALUES.iter() {
            assert_eq!(to_int_trunc(v, 0), 0);
            assert_eq!(to_int_round(v, 0), 0);
            assert_eq!(to_int_ceil(v, 0), 0);
            assert_eq!(to_int_round_even(v, 0), 0);
            assert_eq!(frac_part(v, 0), 0);
            assert_eq!(mul_div_trunc(v, v, 0), 0);
            assert_eq!(mul_div_round(v, v, 0), 0);
            assert_eq!(mul_div_ceil(v, v, 0), 0);
            assert_eq!(rescale_trunc(v, 0, 100), 0);
            assert_eq!(rescale_round(v, 0, 100), 0);
            assert_eq!(percent_hundredths(v, 0), 0);
        }
    }
}
