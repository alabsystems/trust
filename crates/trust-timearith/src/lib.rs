//! Total, verified calendar-free time and duration arithmetic for `no_std`
//! Trust components.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0
//!
//! # Why this crate exists, and who should call it
//!
//! Time arithmetic in this tree is done by hand, with the side conditions
//! written down instead of discharged, and — the part that makes it worth a
//! crate — **the same computation is guarded in one file and unguarded in
//! another**. Five spellings of that, all re-read at the line cited:
//!
//! **`crates/trust-proof-cert/src/timestamp.rs:33-37`** — parsed text
//! multiplied by unit factors with nothing bounding it:
//!
//! ```text
//! let days_since_epoch = (year.saturating_sub(1970)) * 365
//!     + (year.saturating_sub(1969)) / 4
//!     + cumulative_month_days(month)
//!     + day.saturating_sub(1);
//! Some(days_since_epoch * 86400 + hour * 3600 + min * 60 + sec)
//! ```
//!
//! `year`, `hour`, `min` and `sec` are `parse::<u64>()` of arbitrary text from
//! a certificate file. `saturating_sub` guards the *subtractions* and nothing
//! guards the four multiplications. The wrapped value is then a *staleness
//! verdict*: `registry.rs:433` computes `now_epoch.saturating_sub(epoch) >
//! max_age_secs`, so an epoch that wrapped above `now_epoch` saturates to `0`
//! and the certificate is never expired. That is a wrong answer in released
//! code, in the direction that retains stale proof evidence.
//!
//! **`crates/trust-clean-origin/src/emit.rs:1759`** and
//! **`gate.rs:685`** — `Instant::now() + TIMEOUT`, whose `impl Add` panics with
//! *"overflow when adding duration to instant"*:
//!
//! ```text
//! let deadline = Instant::now() + INDUCTIVE_PROJECTION_TOTAL_TIMEOUT;
//! ```
//!
//! 167 lines below the second one, the same file writes the checked form
//! (`gate.rs:852`, `deadline.checked_duration_since(...)`), and two other Trust
//! crates use `checked_add` for the identical computation
//! (`trust-router/src/coordinator.rs:3046`,
//! `trust-router/src/memory_jobserver.rs:295`). Half the deadline computations
//! in the tree are guarded and half are not.
//!
//! **`crates/trust-bmc/src/subprocess.rs:159,169`** — a truncating cast turned
//! into a verdict:
//!
//! ```text
//! let elapsed = start.elapsed().as_millis() as u64;
//! ...
//! if run.timed_out || elapsed >= self.timeout_ms {
//! ```
//!
//! `as_millis()` is `u128` and `as u64` is truncating, not checked. A truncated
//! `elapsed` compares *below* `timeout_ms`, so the run is reported as a
//! completed solve rather than a timeout. `trust-wp/src/native.rs:962-963`
//! writes the guarded twin — `u64::try_from(...).unwrap_or(u64::MAX)` — three
//! lines long, in a sibling crate.
//!
//! **`crates/trust-clean/src/replay.rs:678-680`** — `impl Sum for Duration` is
//! `checked_add(..).expect("overflow when summing durations")`, so the first
//! line panics outright on a long replay, and the second discards a remainder
//! that the third then doubles into an exact `>` threshold:
//!
//! ```text
//! let total: Duration = times.iter().sum();
//! let avg_nanos = total.as_nanos() / times.len() as u128;
//! let threshold = avg_nanos * 2;
//! ```
//!
//! **`first-party/ay/crates/ay-sys/src/lib.rs:626-628`** — the `Duration::new`
//! hazard in its purest form:
//!
//! ```text
//! let secs = u64::try_from(ts.tv_sec).ok()?;
//! let nanos = u32::try_from(ts.tv_nsec).ok()?;
//! Some(std::time::Duration::new(secs, nanos))
//! ```
//!
//! `u32::try_from` proves `tv_nsec < 2^32`. The bound `Duration::new` actually
//! needs is `tv_nsec < 1000000000` — it carries the excess into `secs` and
//! panics *"overflow when adding durations"* if that carry overflows. The
//! checked bound is not the needed bound, and nothing says so.
//! [`is_canonical_nanos`] is that bound as a proposition; [`nanos_field_sum`]
//! and [`nanos_field_carry`] are the carry it does by hand.
//!
//! # What this crate is, and what it deliberately is not
//!
//! A duration here is a pair of integers — `(secs: u32, nanos: u32)` with
//! `nanos <= 999999999` — and every operation on that pair is *total*: defined
//! on all inputs, with no panicking path, no `Option`, and no `debug_assert!`
//! standing in for a proof. There is **no calendar** in this crate: no dates,
//! no time zones, no leap seconds, no month lengths, no formatting. Those are
//! all questions about a *civil* calendar, and none of them is arithmetic.
//!
//! Every function is verified by `targo trust check` under the default
//! `unix_hardened` policy and under `-Ztrust-policy=certify`, and the source is
//! written to the measured boundary in
//! [`docs/STRICT_VERIFICATION_FRAGMENT.md`](../../../docs/STRICT_VERIFICATION_FRAGMENT.md)
//! §13, which this crate wrote.
//!
//! # Why the seconds field is `u32` and the totals are `u64`
//!
//! `u32` seconds is about 136 years, which is longer than any *elapsed* time a
//! process measures, and it is what makes the crate verifiable: the total
//! nanosecond count of any representable duration is
//!
//! ```text
//! 4294967295 * 1000000000 + 4294967295  ==  4294967299294967295
//! ```
//!
//! against a `u64::MAX` of `18446744073709551615` — a factor of 4.29 inside the
//! type, so the multiply and the add that build it need no guard at all, and
//! the *sum* of two such totals (8589934598589934590) still fits. That is the
//! whole reason the arithmetic here has almost no dead guards in it. Widening
//! the result rather than narrowing the operands is §8.7's "a signature can
//! DELETE an overflow instead of proving it", applied to time.
//!
//! # Tiers
//!
//! **Tier 1** functions carry an `ensures` clause the compiler discharges.
//! **Tier 2** functions carry none; their panic-freedom is still proved. A
//! function is tier 2 here for one of exactly three measured reasons:
//!
//! 1. it contains `/` or `%`, which are opaque to bundling (§2.4, §7.2), so a
//!    contracted wrapper over it cannot lower at all;
//! 2. its honest bound is structural rather than enforced, and §5 forbids
//!    manufacturing a green row by wrapping it in a clamp that can never fire;
//! 3. the proposition worth stating is not in the `ensures` predicate language
//!    — see "What this crate cannot state" below.
//!
//! # THE POSTCONDITION TRAP, WRITTEN DOWN BECAUSE THIS DOMAIN IS FULL OF IT
//!
//! `ensures result <= 999999999` is true of a nanosecond normalizer that
//! silently throws the whole seconds away. It is a *range declaration*, not a
//! conservation law. Every tier-1 clause in this crate is annotated below with
//! the wrong implementation that still satisfies it, and the gap is closed by a
//! unit test against an independent oracle — never by a stronger-sounding
//! clause that is not actually stronger.
//!
//! The conservation law this crate most wants to state is
//!
//! ```text
//! nanos_field_carry(a, b) * 1000000000 + nanos_field_sum(a, b)  ==  a + b
//! ```
//!
//! and it **cannot** be an `ensures` clause: the predicate language admits a
//! comparison of `result` against a bare parameter or a bare decimal literal,
//! and nothing built from `*` or `+` (§1.2, §3, §13.1). It is pinned instead by
//! `carry_and_field_conserve_the_whole_sum`, which is exhaustive over the
//! carry boundary and checked against `u128`.
//!
//! # What this crate cannot state, and why
//!
//! * **Conservation of elapsed time**, above. Not a bound the fragment refuses
//!   — a proposition the clause language has no room for.
//! * **A saturating add or multiply at `u64`.** `if a > 18446744073709551615 - b`
//!   measures 0 proved / 1 runtime-checked / 3 unknown, and the multiply guarded
//!   by `18446744073709551615 / f` measures 2 proved / 2 unknown (§13.4). Both
//!   would need the `u128` multiply §2.3 lacks. The repair is architectural and
//!   it is the reason this crate's addition takes *four* `u32` components rather
//!   than two `u64` totals: at `u32` components the sum cannot overflow, so the
//!   saturation is not discharged, it is unrepresentable.
//! * **That a nanosecond field is canonical, as a precondition.** `requires` is
//!   fatal under strict (§3). Every function here is therefore total on
//!   non-canonical input too, and says in its docs what it does with it.
//! * **A verified caller of any `/`-bearing function.** §7.2: the callee cannot
//!   be bundled into anything, contracted or not. The up-conversion ladder
//!   (multiplication only) is separated from the down-conversion ladder
//!   (division) for exactly this reason, and a verified caller that needs a
//!   division must inline it.

#![no_std]

// ===========================================================================
// SECTION 1 — canonicalizers (TIER 1)
//
// These are the crate's live clamps. Each takes an arbitrary `u32` — the whole
// point is that the caller's value may be out of range — and returns one inside
// the field's range. §5's rule that a tier-1 `ensures` is honest only where the
// clamp can FIRE is satisfied by construction here: `clamp_nanos(2000000000)`
// reaches the clamp.
//
// WRONG IMPLEMENTATION THAT STILL SATISFIES `ensures result <= 999999999`:
// `fn clamp_nanos(_v: u32) -> u32 { 0 }`. Pinned by
// `canonicalizers_are_the_identity_inside_their_range`.
// ===========================================================================

/// Canonicalize a nanosecond field: any value at or above one second becomes
/// `999999999`.
///
/// This is a *saturation*, not a normalization — it does not produce a carry.
/// Use [`nanos_field_sum`] and [`nanos_field_carry`] together when the whole
/// seconds matter.
pub fn clamp_nanos(v: u32) -> u32 ensures result <= 999999999 {
    if v > 999999999 {
        return 999999999;
    }
    v
}

/// Canonicalize a microsecond field.
pub fn clamp_micros(v: u32) -> u32 ensures result <= 999999 {
    if v > 999999 {
        return 999999;
    }
    v
}

/// Canonicalize a millisecond field.
pub fn clamp_millis(v: u32) -> u32 ensures result <= 999 {
    if v > 999 {
        return 999;
    }
    v
}

/// A division period that is guaranteed nonzero *and* bounded, in nanoseconds.
///
/// This is the crate's only two-sided constant contract (§1.3), and both bounds
/// are live: `nonzero_period(0)` is raised to `1` and `nonzero_period(2000000000)`
/// is lowered to `1000000000`. `result >= 1` is the interesting half — it is
/// exactly the side condition a division needs, stated as a checked proposition
/// rather than as a `debug_assert!`.
///
/// WRONG IMPLEMENTATION THAT STILL SATISFIES BOTH CLAUSES: `{ 1 }`. Pinned by
/// `nonzero_period_is_the_identity_on_its_own_range`.
pub fn nonzero_period(period_nanos: u32) -> u32
ensures result <= 1000000000
ensures result >= 1
{
    if period_nanos == 0 {
        return 1;
    }
    if period_nanos > 1000000000 {
        return 1000000000;
    }
    period_nanos
}

// ===========================================================================
// SECTION 2 — nanosecond carry and borrow (TIER 1 over TIER 2 raws)
//
// The shape is §1.1's (B): a contracted clamp applied to an UNCONTRACTED
// arithmetic helper. The helper's own arithmetic Assert sits at its entry
// prefix, which is what lets the wrapper bundle it (§9.1).
//
// Each `raw_*` helper is deliberately allowed to return a value ABOVE the
// field range when its inputs are non-canonical, so the clamp above it is live
// rather than decorative.
// ===========================================================================

fn raw_nanos_field_sum(a: u32, b: u32) -> u32 {
    let s: u64 = (a as u64) + (b as u64);
    if s < 1000000000 {
        return s as u32;
    }
    let d: u64 = s - 1000000000;
    if d > 4294967295 {
        return 4294967295;
    }
    d as u32
}

fn raw_nanos_field_carry(a: u32, b: u32) -> u32 {
    let s: u64 = (a as u64) + (b as u64);
    if s < 1000000000 {
        return 0;
    }
    1
}

// The `a < b` arm borrows a second. TWO spellings of that were measured and
// only this one verifies (§13.5, §13.6):
//
//   1000000000 - (b - a)     0 proved / 1 runtime-checked / 1 unknown.
//                            A subtraction whose MINUEND is a literal does not
//                            prove at any width, and no guard repairs it — not
//                            even on a bare parameter.
//   (a + 1000000000) - b     6/6 proved, below. `var - var` with the guard
//                            adjacent, which is the shape that is in the
//                            fragment.
//
// The `s < t` guard is NOT dead: at `a == 0, b == 4294967295` the borrowed
// second really is smaller than `b`, so the textbook spelling of this arm is a
// genuine underflow rather than merely an unproven one.
//
// `d as u32` is a truncating cast and mints no obligation (§2.5). It is safe by
// argument, not by a proved row: in this arm `b > a`, so
// `d == a + 1000000000 - b < 1000000000`. Pinned by
// `borrow_and_diff_conserve_the_whole_difference`, which is exhaustive over the
// carry boundary — the same discipline `trust-interval`'s `midpoint` uses.
fn raw_nanos_field_diff(a: u32, b: u32) -> u32 {
    if a >= b {
        return a - b;
    }
    let s: u64 = (a as u64) + 1000000000;
    let t: u64 = b as u64;
    if s < t {
        return 0;
    }
    let d: u64 = s - t;
    d as u32
}

fn raw_nanos_field_borrow(a: u32, b: u32) -> u32 {
    if a >= b {
        return 0;
    }
    1
}

/// The sub-second part of `a + b`, where `a` and `b` are nanosecond fields.
///
/// Pair with [`nanos_field_carry`], which reports the whole second this drops.
/// On canonical input (`a`, `b` both `<= 999999999`) the pair is exact; on
/// non-canonical input the clamp fires and the answer is saturated.
///
/// WRONG IMPLEMENTATION THAT STILL SATISFIES THE CLAUSE: one that returns
/// `a + b` truncated to the field, discarding the carry — which is precisely
/// the trap this crate's header names. Pinned by
/// `carry_and_field_conserve_the_whole_sum`.
pub fn nanos_field_sum(a: u32, b: u32) -> u32 ensures result <= 999999999 {
    clamp_nanos(raw_nanos_field_sum(a, b))
}

/// The whole second carried out of `a + b`: `0` or `1`.
///
/// `ensures result <= 1` is the tightest statement available about a carry, and
/// it is what makes the return value safe to add to a seconds field. It is
/// discharged by §9.3's pinned-return rule — `raw_nanos_field_carry` returns
/// one of two constants — not by a clamp.
///
/// WRONG IMPLEMENTATION THAT STILL SATISFIES THE CLAUSE: `{ 0 }`.
pub fn nanos_field_carry(a: u32, b: u32) -> u32 ensures result <= 1 {
    raw_nanos_field_carry(a, b)
}

/// The sub-second part of `a - b`, borrowing a second when `a < b`.
///
/// Pair with [`nanos_field_borrow`].
pub fn nanos_field_diff(a: u32, b: u32) -> u32 ensures result <= 999999999 {
    clamp_nanos(raw_nanos_field_diff(a, b))
}

/// The whole second borrowed by `a - b`: `0` or `1`.
pub fn nanos_field_borrow(a: u32, b: u32) -> u32 ensures result <= 1 {
    raw_nanos_field_borrow(a, b)
}

// ===========================================================================
// SECTION 3 — total nanosecond arithmetic (TIER 2)
//
// Structurally bounded, so §5 keeps them out of tier 1: a
// `ensures result <= 4294967299294967295` over a value that cannot approach it
// would be a green row with no content, and `trust-endian`'s header says the
// same thing about `ensures result <= 4294967295`.
// ===========================================================================

/// The total nanosecond count of `(secs, nanos)`.
///
/// Exact for every representable duration: the peak is `4294967299294967295`,
/// which is 4.29x inside `u64`. The multiply and the add therefore need no
/// guard — the widening casts supply their ranges (§2.1's exception).
pub fn total_nanos(secs: u32, nanos: u32) -> u64 {
    (secs as u64) * 1000000000 + (nanos as u64)
}

/// The total microsecond count of `(secs, micros)`.
pub fn total_micros(secs: u32, micros: u32) -> u64 {
    (secs as u64) * 1000000 + (micros as u64)
}

/// The total millisecond count of `(secs, millis)`.
pub fn total_millis(secs: u32, millis: u32) -> u64 {
    (secs as u64) * 1000 + (millis as u64)
}

/// The total nanosecond count of `a + b`, exactly.
///
/// Takes four `u32` components rather than two `u64` totals on purpose: at
/// `u32` components the sum peaks at `8589934598589934590`, which fits `u64`,
/// so there is nothing to saturate. A `u64 + u64` saturating add is not in the
/// fragment (§13.4), so this signature is what makes the operation exact
/// instead of merely bounded.
pub fn sum_total_nanos(a_secs: u32, a_nanos: u32, b_secs: u32, b_nanos: u32) -> u64 {
    let ta: u64 = (a_secs as u64) * 1000000000 + (a_nanos as u64);
    let tb: u64 = (b_secs as u64) * 1000000000 + (b_nanos as u64);
    ta + tb
}

/// Saturating difference of two nanosecond totals: `0` when `b > a`.
///
/// Exists as its own function, and not inlined into [`diff_total_nanos`],
/// because of the boundary in §13.3: the *same* guarded subtraction over
/// multiply-derived LOCALS leaves its `arithmetic_overflow_sub` row UNKNOWN,
/// and crossing the call boundary is what re-supplies the range. Inlining this
/// body into its caller is `trust_timearith_strict_gate.sh` mutation E.
pub fn sat_sub_u64(a: u64, b: u64) -> u64 {
    if a < b {
        return 0;
    }
    a - b
}

/// The total nanosecond count of `a - b`, saturating at zero.
pub fn diff_total_nanos(a_secs: u32, a_nanos: u32, b_secs: u32, b_nanos: u32) -> u64 {
    let ta: u64 = (a_secs as u64) * 1000000000 + (a_nanos as u64);
    let tb: u64 = (b_secs as u64) * 1000000000 + (b_nanos as u64);
    sat_sub_u64(ta, tb)
}

/// The whole seconds of `a + b`, including the second carried out of the
/// nanosecond fields.
pub fn sum_secs(a_secs: u32, a_nanos: u32, b_secs: u32, b_nanos: u32) -> u64 {
    let n: u64 = (a_nanos as u64) + (b_nanos as u64);
    let s: u64 = (a_secs as u64) + (b_secs as u64);
    if n < 1000000000 {
        return s;
    }
    s + 1
}

// ===========================================================================
// SECTION 4 — the up-conversion ladder (TIER 2, multiplication only)
//
// Every one of these is exact: the `u32` input times a constant factor cannot
// leave `u64`. There is no `Option`, no `checked_mul` and no `.expect` — the
// overflow is not discharged, it is unrepresentable (§8.7).
//
// These contain no `/` and no `%`, so a verified caller CAN bundle them.
// ===========================================================================

/// Hours to seconds. Peak `15461882262000`.
pub fn hours_to_secs(hours: u32) -> u64 {
    (hours as u64) * 3600
}

/// Minutes to seconds. Peak `257698037700`.
pub fn minutes_to_secs(minutes: u32) -> u64 {
    (minutes as u64) * 60
}

/// Seconds to milliseconds. Peak `4294967295000`.
pub fn secs_to_millis(secs: u32) -> u64 {
    (secs as u64) * 1000
}

/// Seconds to microseconds. Peak `4294967295000000`.
pub fn secs_to_micros(secs: u32) -> u64 {
    (secs as u64) * 1000000
}

/// Seconds to nanoseconds. Peak `4294967295000000000`.
pub fn secs_to_nanos(secs: u32) -> u64 {
    (secs as u64) * 1000000000
}

/// Milliseconds to nanoseconds. Peak `4294967295000000`.
pub fn millis_to_nanos(millis: u32) -> u64 {
    (millis as u64) * 1000000
}

/// Microseconds to nanoseconds. Peak `4294967295000`.
pub fn micros_to_nanos(micros: u32) -> u64 {
    (micros as u64) * 1000
}

// ===========================================================================
// SECTION 5 — scaling by an integer factor (TIER 2, multiplication only)
//
// A whole duration scaled by a `u32` factor does NOT fit `u64`, so the crate
// does not offer one function that pretends it does. It offers the two exact
// halves and a normalizer, and the caller composes them. The peak of each half
// is `(2^32-1)^2 == 18446744065119617025`, inside `u64::MAX` by 8589934590.
// ===========================================================================

/// `secs * factor`, exactly, in seconds.
pub fn scale_secs(secs: u32, factor: u32) -> u64 {
    (secs as u64) * (factor as u64)
}

/// `nanos * factor`, exactly, in nanoseconds. May exceed one second; feed it to
/// [`scaled_carry_secs`] and [`scaled_subsec_nanos`].
pub fn scale_nanos(nanos: u32, factor: u32) -> u64 {
    (nanos as u64) * (factor as u64)
}

/// The whole seconds carried out of `nanos * factor`.
pub fn scaled_carry_secs(nanos: u32, factor: u32) -> u64 {
    let n: u64 = (nanos as u64) * (factor as u64);
    n / 1000000000
}

/// The sub-second remainder of `nanos * factor`.
pub fn scaled_subsec_nanos(nanos: u32, factor: u32) -> u32 {
    let n: u64 = (nanos as u64) * (factor as u64);
    (n % 1000000000) as u32
}

// ===========================================================================
// SECTION 6 — the down-conversion ladder and period division (TIER 2)
//
// EVERY function below contains `/` or `%`. §7.2: a body that CALLS one of them
// cannot be lowered, contracted or not. They are terminal for verification, and
// nothing else in this crate calls them.
// ===========================================================================

/// Whole microseconds in a nanosecond count.
pub fn nanos_to_micros(nanos: u64) -> u64 {
    nanos / 1000
}

/// Whole milliseconds in a nanosecond count.
pub fn nanos_to_millis(nanos: u64) -> u64 {
    nanos / 1000000
}

/// Whole seconds in a nanosecond count.
pub fn nanos_to_secs(nanos: u64) -> u64 {
    nanos / 1000000000
}

/// Whole minutes in a second count.
pub fn secs_to_minutes(secs: u64) -> u64 {
    secs / 60
}

/// Whole hours in a second count.
pub fn secs_to_hours(secs: u64) -> u64 {
    secs / 3600
}

/// The sub-second nanosecond field of a nanosecond total.
pub fn subsec_nanos(total_nanos: u64) -> u32 {
    (total_nanos % 1000000000) as u32
}

/// The sub-second millisecond field of a nanosecond total.
pub fn subsec_millis(total_nanos: u64) -> u32 {
    ((total_nanos % 1000000000) / 1000000) as u32
}

/// The seconds-within-the-minute of a second count.
pub fn secs_of_minute(secs: u64) -> u32 {
    (secs % 60) as u32
}

/// The minutes-within-the-hour of a second count.
pub fn minutes_of_hour(secs: u64) -> u32 {
    ((secs % 3600) / 60) as u32
}

/// The seconds field of a nanosecond total, saturating at `u32::MAX`.
///
/// The guard is live: `nanos_to_secs(u64::MAX)` is `18446744073`, which is four
/// times what a `u32` holds.
pub fn secs_from_total_nanos(total_nanos: u64) -> u32 {
    let s: u64 = total_nanos / 1000000000;
    if s > 4294967295 {
        return 4294967295;
    }
    s as u32
}

/// How many whole `period_nanos` periods fit in `total_nanos`.
///
/// A zero period yields `0` rather than a division by zero. Pass
/// [`nonzero_period`]'s output to make that impossible at the call site as a
/// *checked* proposition rather than a convention.
pub fn whole_periods(total_nanos: u64, period_nanos: u64) -> u64 {
    if period_nanos == 0 {
        return 0;
    }
    total_nanos / period_nanos
}

/// What is left over after [`whole_periods`]. A zero period yields the whole
/// input, so `whole_periods * period + period_remainder == total` holds in that
/// degenerate case too.
pub fn period_remainder(total_nanos: u64, period_nanos: u64) -> u64 {
    if period_nanos == 0 {
        return total_nanos;
    }
    total_nanos % period_nanos
}

// ===========================================================================
// SECTION 7 — deadlines, budgets and backoff (TIER 1, live clamps)
//
// These are the tier-1 functions whose bound is a caller-supplied PARAMETER.
// Each clamp genuinely fires, and each clause says something a wrong
// implementation can violate.
// ===========================================================================

fn raw_sat_add_secs(a: u32, b: u32) -> u32 {
    let s: u64 = (a as u64) + (b as u64);
    if s > 4294967295 {
        return 4294967295;
    }
    s as u32
}

fn clamp_upper_secs(v: u32, cap: u32) -> u32 ensures result <= cap {
    if v > cap {
        return cap;
    }
    v
}

/// Extend a duration by `b` seconds but never past `cap`.
///
/// `ensures result <= cap` is the deadline law: a budgeted extension cannot
/// exceed the budget. The clamp is live — `capped_add_secs(10, 10, 5) == 5` —
/// and the inner add is saturating, so no input overflows.
///
/// WRONG IMPLEMENTATION THAT STILL SATISFIES THE CLAUSE: `{ cap }`, and also
/// one that SUBTRACTS instead of adding. Pinned by
/// `capped_add_is_a_saturating_sum_then_a_cap`.
pub fn capped_add_secs(a: u32, b: u32, cap: u32) -> u32 ensures result <= cap {
    clamp_upper_secs(raw_sat_add_secs(a, b), cap)
}

/// Raise a duration to a floor: a retry interval is never shorter than
/// `floor_secs`.
///
/// `ensures result >= floor_secs` is a genuine lower bound against a variable
/// (§11.6), and it is the direction that matters for a backoff — the hazard is
/// a retry storm, not a long wait.
pub fn at_least_secs(v: u32, floor_secs: u32) -> u32 ensures result >= floor_secs {
    if v < floor_secs {
        return floor_secs;
    }
    v
}

/// Truncate a duration to a budget: the result never exceeds the duration
/// itself.
///
/// The clause is `result <= secs`, not `result <= budget_secs`, on purpose. Both
/// are true and only one is interesting: "clamping to a budget never *lengthens*
/// a duration" is the property a timeout computation actually depends on, and
/// it is the one a swapped-argument bug violates.
pub fn clamp_secs_to_budget(secs: u32, budget_secs: u32) -> u32 ensures result <= secs {
    if budget_secs < secs {
        return budget_secs;
    }
    secs
}

// ===========================================================================
// SECTION 8 — ordering and predicates (TIER 1, arithmetic-free)
//
// §11.6: an ordered guard chain over four parameters is the cheapest tier-1
// function in the fragment — one postcondition row per return site and no
// arithmetic at all. The clause on a discriminant is a RANGE DECLARATION, which
// is what makes the value safe to `match` on; it is not a clamp, and no clamp
// was added to obtain it.
// ===========================================================================

/// Compare two durations: `0` if `a < b`, `1` if equal, `2` if `a > b`.
///
/// A `u32` discriminant rather than `core::cmp::Ordering` because `derive` and
/// enum returns are outside the fragment (§3).
pub fn duration_cmp(a_secs: u32, a_nanos: u32, b_secs: u32, b_nanos: u32) -> u32
ensures result <= 2
{
    if a_secs < b_secs {
        return 0;
    }
    if a_secs > b_secs {
        return 2;
    }
    if a_nanos < b_nanos {
        return 0;
    }
    if a_nanos > b_nanos {
        return 2;
    }
    1
}

/// `1` when the nanosecond field is canonical (`< 1000000000`), else `0`.
pub fn is_canonical_nanos(nanos: u32) -> u32 ensures result <= 1 {
    if nanos > 999999999 {
        return 0;
    }
    1
}

/// `1` when a second count fits the `u32` seconds field, else `0`.
pub fn fits_secs_field(secs: u64) -> u32 ensures result <= 1 {
    if secs > 4294967295 {
        return 0;
    }
    1
}

/// `1` when `(secs, nanos)` is the zero duration, else `0`.
pub fn is_zero(secs: u32, nanos: u32) -> u32 ensures result <= 1 {
    if secs > 0 {
        return 0;
    }
    if nanos > 0 {
        return 0;
    }
    1
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::time::Duration;

    const NPS: u128 = 1000000000;

    /// The carry boundary, plus the places a hand-written normalizer goes
    /// wrong: zero, one below a second, exactly a second, one above, exactly
    /// two seconds, and the top of the type.
    const EDGE: [u32; 12] = [
        0,
        1,
        2,
        499999999,
        500000000,
        999999998,
        999999999,
        1000000000,
        1000000001,
        1999999999,
        2000000000,
        4294967295,
    ];

    const SECS_EDGE: [u32; 8] = [0, 1, 2, 59, 60, 3599, 3600, 4294967295];

    // -- Section 1: canonicalizers ------------------------------------------

    #[test]
    fn canonicalizers_are_the_identity_inside_their_range() {
        // The clause `result <= 999999999` is satisfied by `{ 0 }`. This is the
        // test that says the function is not that.
        for &v in EDGE.iter() {
            let want: u32 = if v > 999999999 { 999999999 } else { v };
            assert_eq!(clamp_nanos(v), want, "clamp_nanos({v})");
            let wm: u32 = if v > 999999 { 999999 } else { v };
            assert_eq!(clamp_micros(v), wm, "clamp_micros({v})");
            let wl: u32 = if v > 999 { 999 } else { v };
            assert_eq!(clamp_millis(v), wl, "clamp_millis({v})");
        }
        // Every clamp can FIRE, which is what makes its clause non-vacuous.
        assert_eq!(clamp_nanos(1000000000), 999999999);
        assert_eq!(clamp_micros(1000000), 999999);
        assert_eq!(clamp_millis(1000), 999);
    }

    #[test]
    fn nonzero_period_is_the_identity_on_its_own_range() {
        // `{ 1 }` satisfies both clauses; this rules it out.
        for &v in EDGE.iter() {
            let want: u32 = if v == 0 {
                1
            } else if v > 1000000000 {
                1000000000
            } else {
                v
            };
            assert_eq!(nonzero_period(v), want, "nonzero_period({v})");
            assert!(nonzero_period(v) >= 1);
            assert!(nonzero_period(v) <= 1000000000);
        }
        // Both bounds are live.
        assert_eq!(nonzero_period(0), 1);
        assert_eq!(nonzero_period(4294967295), 1000000000);
    }

    // -- Section 2: carry / borrow, against an exact u128 oracle -------------

    /// THE CONSERVATION LAW. It cannot be an `ensures` clause (see the header),
    /// so it is a test, and it is the reason `nanos_field_sum`'s
    /// `ensures result <= 999999999` is not the whole story.
    #[test]
    fn carry_and_field_conserve_the_whole_sum() {
        let mut checked = 0u32;
        for &a in EDGE.iter() {
            for &b in EDGE.iter() {
                if a > 999999999 || b > 999999999 {
                    continue; // conservation is claimed for canonical input
                }
                let got: u128 =
                    (nanos_field_carry(a, b) as u128) * NPS + (nanos_field_sum(a, b) as u128);
                assert_eq!(got, (a as u128) + (b as u128), "carry+field for {a}+{b}");
                checked += 1;
            }
        }
        assert!(checked >= 49, "the sweep degenerated: only {checked} pairs");
    }

    #[test]
    fn borrow_and_diff_conserve_the_whole_difference() {
        for &a in EDGE.iter() {
            for &b in EDGE.iter() {
                if a > 999999999 || b > 999999999 {
                    continue;
                }
                // a - b + borrow*1e9 == field, i.e. field - borrow*1e9 == a - b
                let got: i128 =
                    (nanos_field_diff(a, b) as i128) - (nanos_field_borrow(a, b) as i128) * 1000000000;
                assert_eq!(got, (a as i128) - (b as i128), "borrow+diff for {a}-{b}");
            }
        }
    }

    #[test]
    fn the_carry_is_exactly_the_one_second_boundary() {
        assert_eq!(nanos_field_carry(999999999, 0), 0);
        assert_eq!(nanos_field_carry(999999999, 1), 1);
        assert_eq!(nanos_field_sum(999999999, 1), 0);
        assert_eq!(nanos_field_sum(999999999, 2), 1);
        assert_eq!(nanos_field_sum(500000000, 500000000), 0);
        assert_eq!(nanos_field_carry(500000000, 500000000), 1);
        assert_eq!(nanos_field_sum(499999999, 500000000), 999999999);
        assert_eq!(nanos_field_carry(499999999, 500000000), 0);
        // Borrow side.
        assert_eq!(nanos_field_borrow(0, 1), 1);
        assert_eq!(nanos_field_diff(0, 1), 999999999);
        assert_eq!(nanos_field_borrow(1, 1), 0);
        assert_eq!(nanos_field_diff(1, 1), 0);
    }

    // -- Section 3: totals, against u128 and core::time::Duration ------------

    #[test]
    fn totals_match_an_exact_u128_oracle_and_core_duration() {
        for &s in SECS_EDGE.iter() {
            for &n in EDGE.iter() {
                assert_eq!(
                    total_nanos(s, n) as u128,
                    (s as u128) * NPS + (n as u128),
                    "total_nanos({s},{n})"
                );
                if n <= 999999999 {
                    // core::time::Duration agrees on canonical input.
                    assert_eq!(total_nanos(s, n) as u128, Duration::new(s as u64, n).as_nanos());
                }
                assert_eq!(total_micros(s, n) as u128, (s as u128) * 1000000 + (n as u128));
                assert_eq!(total_millis(s, n) as u128, (s as u128) * 1000 + (n as u128));
            }
        }
        // The stated peak, exactly.
        assert_eq!(total_nanos(4294967295, 4294967295), 4294967299294967295);
    }

    #[test]
    fn sum_and_diff_totals_match_u128_and_saturate_correctly() {
        for &s in SECS_EDGE.iter() {
            for &n in EDGE.iter() {
                let ta: u128 = (s as u128) * NPS + (n as u128);
                let tb: u128 = (n as u128) * NPS + (s as u128);
                assert_eq!(sum_total_nanos(s, n, n, s) as u128, ta + tb);
                let want: u128 = if ta >= tb { ta - tb } else { 0 };
                assert_eq!(diff_total_nanos(s, n, n, s) as u128, want);
            }
        }
        // The stated peak of the sum, exactly.
        assert_eq!(
            sum_total_nanos(4294967295, 4294967295, 4294967295, 4294967295),
            8589934598589934590
        );
        assert_eq!(diff_total_nanos(0, 0, 5, 0), 0, "must saturate, not wrap");
    }

    #[test]
    fn sat_sub_agrees_with_the_core_saturating_sub() {
        // An independent oracle written by someone else, by a different method.
        let xs: [u64; 8] = [
            0,
            1,
            999999999,
            1000000000,
            4294967295,
            4294967299294967295,
            18446744073709551614,
            18446744073709551615,
        ];
        for &a in xs.iter() {
            for &b in xs.iter() {
                assert_eq!(sat_sub_u64(a, b), a.saturating_sub(b), "sat_sub_u64({a},{b})");
            }
        }
    }

    #[test]
    fn sum_secs_carries_the_second_out_of_the_nanosecond_fields() {
        for &an in EDGE.iter() {
            for &bn in EDGE.iter() {
                if an > 999999999 || bn > 999999999 {
                    continue;
                }
                let carry: u64 = if (an as u64) + (bn as u64) >= 1000000000 { 1 } else { 0 };
                assert_eq!(sum_secs(7, an, 11, bn), 18 + carry, "sum_secs 7.{an} + 11.{bn}");
            }
        }
        // ...and it agrees with reassembling the total.
        for &an in EDGE.iter() {
            if an > 999999999 {
                continue;
            }
            let t: u64 = sum_total_nanos(7, an, 11, 500000000);
            assert_eq!(sum_secs(7, an, 11, 500000000), t / 1000000000);
        }
    }

    // -- Section 4 & 5: ladders and scaling ---------------------------------

    #[test]
    fn the_up_conversion_ladder_is_exact_at_the_top_of_u32() {
        assert_eq!(hours_to_secs(1), 3600);
        assert_eq!(minutes_to_secs(1), 60);
        assert_eq!(secs_to_millis(1), 1000);
        assert_eq!(secs_to_micros(1), 1000000);
        assert_eq!(secs_to_nanos(1), 1000000000);
        assert_eq!(millis_to_nanos(1), 1000000);
        assert_eq!(micros_to_nanos(1), 1000);
        // Exactness at the top of the input type is the property the widened
        // return buys; a `u32`-in / `u32`-out ladder wraps here.
        assert_eq!(hours_to_secs(4294967295), 15461882262000);
        assert_eq!(minutes_to_secs(4294967295), 257698037700);
        assert_eq!(secs_to_millis(4294967295), 4294967295000);
        assert_eq!(secs_to_micros(4294967295), 4294967295000000);
        assert_eq!(secs_to_nanos(4294967295), 4294967295000000000);
        assert_eq!(millis_to_nanos(4294967295), 4294967295000000);
        assert_eq!(micros_to_nanos(4294967295), 4294967295000);
        // And against core::time::Duration, which uses a different method.
        for &s in SECS_EDGE.iter() {
            assert_eq!(secs_to_nanos(s) as u128, Duration::from_secs(s as u64).as_nanos());
            assert_eq!(secs_to_millis(s) as u128, Duration::from_secs(s as u64).as_millis());
            assert_eq!(hours_to_secs(s), Duration::from_secs(s as u64 * 3600).as_secs());
        }
    }

    #[test]
    fn the_two_scaling_halves_recombine_to_the_exact_product() {
        let factors: [u32; 7] = [0, 1, 2, 1000, 65536, 1000000, 4294967295];
        for &s in SECS_EDGE.iter() {
            for &n in EDGE.iter() {
                if n > 999999999 {
                    continue;
                }
                for &f in factors.iter() {
                    let exact: u128 = ((s as u128) * NPS + (n as u128)) * (f as u128);
                    let got: u128 = (scale_secs(s, f) as u128) * NPS + (scale_nanos(n, f) as u128);
                    assert_eq!(got, exact, "scale ({s},{n}) x {f}");
                    // And the normalized form of the nanosecond half.
                    let nn: u128 = (n as u128) * (f as u128);
                    assert_eq!(scaled_carry_secs(n, f) as u128, nn / NPS);
                    assert_eq!(scaled_subsec_nanos(n, f) as u128, nn % NPS);
                }
            }
        }
        assert_eq!(scale_secs(4294967295, 4294967295), 18446744065119617025);
    }

    // -- Section 6: down-conversion and period division ---------------------

    #[test]
    fn the_down_conversion_ladder_truncates_toward_zero_like_the_oracle() {
        let ns: [u64; 10] = [
            0,
            1,
            999,
            1000,
            999999,
            1000000,
            999999999,
            1000000000,
            1000000001,
            18446744073709551615,
        ];
        for &v in ns.iter() {
            assert_eq!(nanos_to_micros(v) as u128, (v as u128) / 1000);
            assert_eq!(nanos_to_millis(v) as u128, (v as u128) / 1000000);
            assert_eq!(nanos_to_secs(v) as u128, (v as u128) / NPS);
            assert_eq!(subsec_nanos(v) as u128, (v as u128) % NPS);
            assert_eq!(subsec_millis(v) as u128, ((v as u128) % NPS) / 1000000);
            assert_eq!(secs_to_minutes(v) as u128, (v as u128) / 60);
            assert_eq!(secs_to_hours(v) as u128, (v as u128) / 3600);
            assert_eq!(secs_of_minute(v) as u128, (v as u128) % 60);
            assert_eq!(minutes_of_hour(v) as u128, ((v as u128) % 3600) / 60);
        }
        // Against core::time::Duration on canonical input.
        for &s in SECS_EDGE.iter() {
            for &n in EDGE.iter() {
                if n > 999999999 {
                    continue;
                }
                let d = Duration::new(s as u64, n);
                let t = total_nanos(s, n);
                assert_eq!(subsec_nanos(t), d.subsec_nanos());
                assert_eq!(subsec_millis(t), d.subsec_millis());
                assert_eq!(nanos_to_secs(t), d.as_secs());
            }
        }
    }

    #[test]
    fn the_seconds_field_saturates_rather_than_truncating() {
        assert_eq!(secs_from_total_nanos(0), 0);
        assert_eq!(secs_from_total_nanos(999999999), 0);
        assert_eq!(secs_from_total_nanos(1000000000), 1);
        assert_eq!(secs_from_total_nanos(4294967295000000000), 4294967295);
        // One nanosecond past the top of the field: the guard is LIVE, and a
        // truncating `as u32` would return 0 here instead of saturating.
        assert_eq!(secs_from_total_nanos(4294967296000000000), 4294967295);
        assert_eq!(secs_from_total_nanos(18446744073709551615), 4294967295);
    }

    #[test]
    fn the_total_nanosecond_split_round_trips() {
        for &s in SECS_EDGE.iter() {
            for &n in EDGE.iter() {
                if n > 999999999 {
                    continue;
                }
                let t = total_nanos(s, n);
                assert_eq!(secs_from_total_nanos(t), s, "secs of {s}.{n}");
                assert_eq!(subsec_nanos(t), n, "nanos of {s}.{n}");
                assert_eq!(total_nanos(secs_from_total_nanos(t), subsec_nanos(t)), t);
            }
        }
    }

    #[test]
    fn periods_and_remainder_partition_the_total_exactly() {
        let totals: [u64; 8] = [
            0,
            1,
            999999999,
            1000000000,
            1000000001,
            4294967299294967295,
            18446744073709551614,
            18446744073709551615,
        ];
        let periods: [u64; 8] = [0, 1, 2, 7, 1000000, 1000000000, 3600000000000, 18446744073709551615];
        for &t in totals.iter() {
            for &p in periods.iter() {
                let q = whole_periods(t, p);
                let r = period_remainder(t, p);
                if p == 0 {
                    assert_eq!(q, 0);
                    assert_eq!(r, t, "a zero period must yield the whole input");
                    continue;
                }
                assert_eq!(
                    (q as u128) * (p as u128) + (r as u128),
                    t as u128,
                    "q*p+r != t for {t} / {p}"
                );
                assert!(r < p, "remainder {r} not below period {p}");
            }
        }
        // nonzero_period makes the degenerate case unreachable at the call site.
        for &t in totals.iter() {
            let p = nonzero_period(0) as u64;
            assert_eq!(p, 1);
            assert_eq!(whole_periods(t, p), t);
            assert_eq!(period_remainder(t, p), 0);
        }
    }

    // -- Section 7: deadlines, budgets, backoff -----------------------------

    #[test]
    fn capped_add_is_a_saturating_sum_then_a_cap() {
        // `{ cap }` satisfies `ensures result <= cap`, and so does a SUBTRACTION
        // clamped to `cap`. Both are ruled out here.
        let vs: [u32; 7] = [0, 1, 5, 10, 1000, 2147483648, 4294967295];
        for &a in vs.iter() {
            for &b in vs.iter() {
                for &cap in vs.iter() {
                    let sum: u64 = (a as u64) + (b as u64);
                    let sat: u64 = if sum > 4294967295 { 4294967295 } else { sum };
                    let want: u64 = if sat > cap as u64 { cap as u64 } else { sat };
                    assert_eq!(capped_add_secs(a, b, cap) as u64, want, "({a}+{b}) cap {cap}");
                }
            }
        }
        assert_eq!(capped_add_secs(2, 3, 100), 5, "must ADD, not subtract");
        assert_eq!(capped_add_secs(10, 10, 5), 5, "the cap must FIRE");
        assert_eq!(capped_add_secs(4294967295, 1, 4294967295), 4294967295, "must saturate");
    }

    #[test]
    fn floor_and_budget_agree_with_core_cmp() {
        let vs: [u32; 7] = [0, 1, 5, 10, 1000, 2147483648, 4294967295];
        for &v in vs.iter() {
            for &w in vs.iter() {
                // Independent oracles: core::cmp::max / min.
                assert_eq!(at_least_secs(v, w), core::cmp::max(v, w), "at_least({v},{w})");
                assert_eq!(clamp_secs_to_budget(v, w), core::cmp::min(v, w), "budget({v},{w})");
                assert!(at_least_secs(v, w) >= w);
                assert!(clamp_secs_to_budget(v, w) <= v);
            }
        }
        assert_eq!(at_least_secs(1, 9), 9, "the floor must FIRE");
        assert_eq!(clamp_secs_to_budget(9, 1), 1, "the budget must FIRE");
    }

    // -- Section 8: ordering and predicates ---------------------------------

    #[test]
    fn duration_cmp_agrees_with_core_duration_ordering() {
        for &as_ in SECS_EDGE.iter() {
            for &an in EDGE.iter() {
                for &bs in SECS_EDGE.iter() {
                    for &bn in EDGE.iter() {
                        if an > 999999999 || bn > 999999999 {
                            continue;
                        }
                        let a = Duration::new(as_ as u64, an);
                        let b = Duration::new(bs as u64, bn);
                        let want: u32 = if a < b {
                            0
                        } else if a == b {
                            1
                        } else {
                            2
                        };
                        assert_eq!(duration_cmp(as_, an, bs, bn), want, "{as_}.{an} vs {bs}.{bn}");
                    }
                }
            }
        }
    }

    #[test]
    fn the_predicates_agree_with_brute_force() {
        for &n in EDGE.iter() {
            assert_eq!(is_canonical_nanos(n), u32::from(n < 1000000000), "canonical({n})");
        }
        for &s in SECS_EDGE.iter() {
            for &n in EDGE.iter() {
                assert_eq!(is_zero(s, n), u32::from(s == 0 && n == 0), "is_zero({s},{n})");
            }
        }
        let big: [u64; 5] = [0, 4294967294, 4294967295, 4294967296, 18446744073709551615];
        for &v in big.iter() {
            assert_eq!(fits_secs_field(v), u32::from(v <= 4294967295), "fits({v})");
        }
    }

    /// Every tier-1 clause, checked as a runtime property over the sweep, and
    /// every clamp shown to FIRE. A discharged clause over a clamp that cannot
    /// fire is a green row with no content (§5).
    #[test]
    fn every_tier1_bound_holds_and_every_clamp_can_fire() {
        let vs: [u32; 7] = [0, 1, 999999999, 1000000000, 1000000001, 2000000000, 4294967295];
        let mut fired = 0u32;
        for &v in vs.iter() {
            assert!(clamp_nanos(v) <= 999999999);
            assert!(clamp_micros(v) <= 999999);
            assert!(clamp_millis(v) <= 999);
            assert!(nonzero_period(v) <= 1000000000 && nonzero_period(v) >= 1);
            assert!(is_canonical_nanos(v) <= 1);
            if v > 999999999 {
                assert_eq!(clamp_nanos(v), 999999999);
                fired += 1;
            }
            for &w in vs.iter() {
                assert!(nanos_field_sum(v, w) <= 999999999);
                assert!(nanos_field_carry(v, w) <= 1);
                assert!(nanos_field_diff(v, w) <= 999999999);
                assert!(nanos_field_borrow(v, w) <= 1);
                assert!(at_least_secs(v, w) >= w);
                assert!(clamp_secs_to_budget(v, w) <= v);
                assert!(duration_cmp(v, 0, w, 0) <= 2);
                assert!(is_zero(v, w) <= 1);
                for &c in vs.iter() {
                    assert!(capped_add_secs(v, w, c) <= c);
                }
            }
        }
        assert!(fired >= 4, "the clamps never fired: the bounds are vacuous here");
    }
}
