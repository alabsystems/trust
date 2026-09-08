//! Total, verified modular integer arithmetic over a **runtime** modulus.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0
//!
//! # Why this crate exists, and who calls it
//!
//! Every `%` and `/` by a value that is not a literal carries a zero-divisor
//! obligation, and every "wrap it back into range" respelling carries an
//! overflow one. Both are normally discharged by a *separate* `is_empty()` or
//! `!= 0` test somewhere above, and the connection between the test and the
//! operator is prose. Seven sites in this tree, all re-read at the line cited:
//!
//! **`crates/trust-loop/src/scheduling.rs:205-209`**,
//! **`crates/trust-symex/src/search.rs:213-216`** and
//! **`crates/trust-symex/src/concolic_fuzzing.rs:743-746`** are the same three
//! lines written three times in three crates:
//!
//! ```text
//! if self.candidates.is_empty() { return None; }
//! let idx = self.round_robin_index % self.candidates.len();
//! ```
//!
//! The guard is correct in all three. It is also *re-derived* in all three,
//! and nothing checks that a fourth copy keeps it. [`reduce`] is that
//! expression with the condition decided rather than restated.
//!
//! **`crates/trust-vcgen/src/generate/callee_summaries.rs:546-551`** records
//! the same shape as the canonical *discharge* pattern —
//! `let n = v.max(C) as u64; h % n` — and
//! **`crates/trust-ir-bridge/src/lower.rs:8421`** relies on it
//! (*"`num_partitions.max(1) as u64`, so `h % n` cannot divide by zero"*).
//! That `.max(1)` is [`modulus_floor`], and here it is not a comment: the
//! compiler discharges `result >= 1` as a checked proposition.
//!
//! **`crates/trust-vcgen/src/generate/intrinsic_semantics_tests.rs:98-100`**
//! is the classic sign-correcting remainder —
//! `let m = 1i128.checked_shl(*w)…; let r = ((x % m) + m) % m;` — in which
//! `(x % m) + m` is an undischarged addition sitting between two undischarged
//! divisions. [`reduce`] and [`neg_mod`] are its two halves with every one of
//! those conditions proved.
//!
//! **`crates/trust-js-value/src/binary.rs:23-28`** (`to_uint_bits`) computes a
//! modular negation as `modu - u` behind `if t < 0.0 && u != 0`. The guard is
//! exactly [`neg_reduced`]'s, and the subtraction is exactly the one this
//! crate proves cannot underflow.
//!
//! # The sentinel, and why `0` was not used
//!
//! `requires` is fatal under the strict lane, so every function here is
//! **total**: `m == 0` has to return *something*. It returns
//! [`NOT_A_RESIDUE`] == `4294967295` rather than `0`, and that choice is not
//! cosmetic. A residue modulo a `u32` modulus `m >= 1` is at most `m - 1`, and
//! `m <= 4294967295`, so **`4294967295` is never a legitimate residue for any
//! modulus**. `0` is a legitimate residue for every one of them. Returning `0`
//! would make "the modulus was zero" indistinguishable from "the answer is
//! zero" at every call site in the crate. This is §1.4's *one past the top*
//! sentinel discipline applied to a value space that has no top of its own.
//!
//! # Three tiers, and the reason they exist
//!
//! The measured fragment boundary that shapes this entire crate is
//! `docs/STRICT_VERIFICATION_FRAGMENT.md` §2.4 / §7.2: **a function whose body
//! contains `%` or `/` cannot be bundled into any caller.** Not "cannot carry a
//! contract" — cannot be *called* by a verified function at all. So:
//!
//! | Tier | What it is | Example |
//! |---|---|---|
//! | 1 | contracted, `%`-free, arithmetic-free — a discharged `ensures` | [`modulus_floor`], [`residue_clamp`] |
//! | 2a | `%`-free arithmetic — no contract, but **callable** by verified code | [`add_reduced`], [`sub_reduced`] |
//! | 2b | `%`- or `/`-bearing — proved total, and **terminal**: no verified function may call one | [`add_mod`], [`mul_mod`] |
//!
//! Tier 2a is the part worth knowing about. `add_reduced`, `sub_reduced`,
//! `neg_reduced` and `reduce_once` compute modular sums and differences by
//! conditional subtraction instead of `%`, so a *verified caller* can compose
//! them — [`double_reduced`] does exactly that, and its own row count is zero
//! because the whole obligation lives in the bundled callee. They are correct
//! only for operands already in `[0, m)`; [`is_reduced_pair`] is how a caller
//! establishes that, because `requires` cannot.
//!
//! # What each `ensures` clause admits — read this before trusting one
//!
//! A discharged postcondition is a proved *bound*, never a proved *function*.
//! Every clause below is listed with the wrong implementation that still
//! satisfies it, because that is the only honest way to read one:
//!
//! | Function | Clauses | A WRONG implementation that still satisfies them |
//! |---|---|---|
//! | [`modulus_floor`] | `result >= 1`, `result >= m` | `4294967295` for every input — both clauses stay true |
//! | [`residue_clamp`] | `result <= last`, `result <= v` | `0` for every input |
//! | [`is_zero_modulus`] | `result <= 1` | `0` for every input |
//! | [`is_residue`] | `result <= 1` | `0` for every input |
//! | [`is_reduced_pair`] | `result <= 1` | `0` for every input |
//!
//! Note what the two-clause forms buy and what they do not. `residue_clamp`'s
//! pair pins the result to `<= min(v, last)`, which is exactly the value it
//! returns — so the *only* wrong implementations that survive are ones that
//! return something too small. That is a materially stronger statement than
//! either clause alone, and it is still not a specification. `residue_clamp`
//! returning `0` when `v > last` passes the strict lane at exit 0; the gate's
//! mutation D demonstrates it, and only the unit tests refuse it.
//!
//! **Nothing in tier 2 carries a contract at all.** The proposition a modular
//! library most wants — `add_mod(a, b, m) == (a + b) mod m` — needs `+` and
//! `%` inside the predicate, and the clause language admits `result` against a
//! bare parameter or a bare decimal literal and nothing built from an operator
//! (fragment map §1.2, §3, §13.9). Every tier-2 value in this crate is pinned
//! by exhaustive unit tests against a `u128` oracle instead, which is a test
//! and not a proof. What *is* proved of tier 2 is total panic-freedom: no
//! overflow, no underflow, no division or remainder by zero, on every input.
//!
//! # Exponentiation
//!
//! [`pow_mod_step`] is one square-and-multiply step and is the general
//! primitive: a caller chains it MSB-first for an exponent of any width, the
//! way `trust-checksum`'s `crc8` is chained per byte. [`pow_mod`] unrolls
//! **four** steps and therefore covers `exp <= 15`, returning [`NOT_A_RESIDUE`]
//! above that.
//!
//! Two measured boundaries put it there, and neither is a taste (§14.2, §14.3):
//!
//! * The per-step multiplier **cannot be selected inline.**
//!   `let f = if bit == 0 { 1 } else { base };` leaves the following multiply's
//!   hardened twin UNKNOWN even though `f as u64` is a widening cast — a select
//!   between a constant and an *unguarded* variable supplies no range, and the
//!   cast does not restore it. [`pow_factor`] is that select moved one call
//!   down, which repairs it: 8/8 for one step, 32/32 for four.
//! * **Four steps is the ceiling.** Five times out (`20 unknown, 20 timeouts`
//!   of 40); six and seven fail with `native typed-TrustIr lowering did not
//!   complete`.
//!
//! # Modular inverse
//!
//! The extended Euclidean algorithm needs a loop, and `while … decreases` does
//! not discharge (fragment map §3). [`quotient`], [`gcd_step`] and
//! [`bezout_step`] are its three per-iteration steps, each proved total; a
//! caller drives the recurrence. The crate's tests do exactly that and check
//! every inverse against an independent brute-force search.
#![no_std]

/// The value returned whenever a function has no residue to return: the
/// modulus was zero, an exponent was out of the supported range, or an operand
/// was not reduced where reduction was required.
///
/// `4294967295` is never a residue modulo any `u32` modulus `m >= 1`, because
/// a residue is at most `m - 1 <= 4294967294`. `0` would have been ambiguous
/// with a genuine answer; this is not.
pub const NOT_A_RESIDUE: u32 = 4294967295;

// ===========================================================================
// TIER 1 — contracted. Arithmetic-free bodies, discharged `ensures` clauses.
// ===========================================================================

/// The modulus, forced nonzero: `max(m, 1)`.
///
/// This is `num_partitions.max(1)` from
/// `crates/trust-ir-bridge/src/lower.rs:8421` with its side condition promoted
/// from a comment to a **checked proposition**: `result >= 1` is exactly the
/// nonzero-divisor precondition that a `%` by this value needs, and the
/// compiler discharges it. `>= 1` is not vacuous for an unsigned type.
///
/// The second clause, `result >= m`, is what stops the function from being
/// allowed to *lower* a perfectly good modulus. Together they say the result
/// is at least `max(m, 1)`.
///
/// **Wrong implementation still admitted:** returning `4294967295` always.
/// Both clauses hold. `modulus_floor_is_max_of_m_and_one` is what refuses it.
pub fn modulus_floor(m: u32) -> u32 ensures result >= 1 ensures result >= m {
    if m == 0 {
        return 1;
    }
    m
}

/// Saturate `v` into the inclusive residue range `[0, last]`.
///
/// `last` is the LARGEST residue, not the modulus — a strict `result < m`
/// cannot be stated, because no *total* function satisfies it at `m == 0`
/// (fragment map §1.2). Callers spell `last` as `mod_last(m)`.
///
/// Both clauses are variable bounds in the same direction, which pins the
/// result to `<= min(v, last)` — the exact value returned.
///
/// **Wrong implementation still admitted:** returning `0` always, or returning
/// `0` on the clamping arm only. Both clauses stay true. Gate mutation D is
/// the second of those, and it passes the strict lane at exit 0.
pub fn residue_clamp(v: u32, last: u32) -> u32 ensures result <= last ensures result <= v {
    if v > last {
        return last;
    }
    v
}

/// `1` when `m` is the degenerate modulus, `0` otherwise.
///
/// The crate's central side condition as a decision procedure; [`modulus_floor`]
/// is its repair.
///
/// **Wrong implementation still admitted:** returning `0` always.
pub fn is_zero_modulus(m: u32) -> u8 ensures result <= 1 {
    if m == 0 {
        return 1;
    }
    0
}

/// `1` when `v` is already a residue modulo `m` (`m >= 1` and `v < m`).
///
/// **Wrong implementation still admitted:** returning `0` always.
pub fn is_residue(v: u32, m: u32) -> u8 ensures result <= 1 {
    if m == 0 {
        return 0;
    }
    if v < m {
        return 1;
    }
    0
}

/// `1` when BOTH `a` and `b` are already residues modulo `m`.
///
/// This is the precondition of every `*_reduced` function in tier 2a, stated
/// as a checked proposition because `requires` is fatal under the strict lane
/// (fragment map §3). A caller that cannot establish it should route through
/// [`reduce`] instead.
///
/// **Wrong implementation still admitted:** returning `0` always.
pub fn is_reduced_pair(a: u32, b: u32, m: u32) -> u8 ensures result <= 1 {
    if m == 0 {
        return 0;
    }
    if a >= m {
        return 0;
    }
    if b >= m {
        return 0;
    }
    1
}

// ===========================================================================
// TIER 2a — `%`-FREE modular arithmetic. No contract, but BUNDLABLE: a
// verified function may call any of these.
//
// Each is correct for operands already in `[0, m)`. Out of that range they
// stay total and return either an unreduced value or NOT_A_RESIDUE; they never
// panic. [`is_reduced_pair`] is how a caller establishes the precondition.
// ===========================================================================

/// One conditional subtraction: `x - m` when `x >= m`, else `x`.
///
/// Correct as a full reduction when `x < 2 * m`, which is the state every
/// modular sum of two residues is in. `NOT_A_RESIDUE` at `m == 0`.
pub fn reduce_once(x: u32, m: u32) -> u32 {
    if m == 0 {
        return NOT_A_RESIDUE;
    }
    if x < m {
        return x;
    }
    x - m
}

/// `(x + y) mod m` for `x, y < m`, computed without `%`.
///
/// The sum is formed at `u64` — two widening casts, so the interval engine
/// sees `[0, 2^33 - 2]` with no guard at all (fragment map §2.1) — and reduced
/// by one conditional subtraction.
pub fn add_reduced(x: u32, y: u32, m: u32) -> u32 {
    if m == 0 {
        return NOT_A_RESIDUE;
    }
    let mm: u64 = m as u64;
    let s: u64 = (x as u64) + (y as u64);
    if s < mm {
        return s as u32;
    }
    let d: u64 = s - mm;
    if d > 4294967295 {
        return NOT_A_RESIDUE;
    }
    d as u32
}

/// `(x - y) mod m` for `x, y < m`, computed without `%`.
///
/// The borrow is `m - y`, guarded by `m < y` on the line before, and the
/// re-addition is two widening casts. This is
/// `crates/trust-js-value/src/binary.rs:26`'s `modu - u` with the underflow
/// discharged.
pub fn sub_reduced(x: u32, y: u32, m: u32) -> u32 {
    if m == 0 {
        return NOT_A_RESIDUE;
    }
    if x >= y {
        return x - y;
    }
    if m < y {
        return NOT_A_RESIDUE;
    }
    let d: u32 = m - y;
    let s: u64 = (d as u64) + (x as u64);
    if s > 4294967295 {
        return NOT_A_RESIDUE;
    }
    s as u32
}

/// `(-x) mod m` for `x < m`, computed without `%`.
pub fn neg_reduced(x: u32, m: u32) -> u32 {
    if m == 0 {
        return NOT_A_RESIDUE;
    }
    if x == 0 {
        return 0;
    }
    if m < x {
        return NOT_A_RESIDUE;
    }
    m - x
}

/// The per-step multiplier of a square-and-multiply: `base` when `bit` is
/// nonzero, `1` otherwise.
///
/// This exists as its own function for a measured reason, not for tidiness.
/// Spelled inline as `let f = if bit == 0 { 1 } else { base };`, the multiply
/// that consumes it leaves its `hardened_panic_boundary` row UNKNOWN — a
/// select between a constant and an UNGUARDED variable supplies the interval
/// engine no range, and the `f as u64` widening cast does not restore it.
/// Crossing a call boundary does (fragment map §11.1; §14.2 for this crate's
/// measurement, which is the first at a *widening cast*).
///
/// It carries no obligation of its own and bundles into any caller.
pub fn pow_factor(base: u32, bit: u32) -> u32 {
    if bit == 0 {
        return 1;
    }
    base
}

/// `(2 * x) mod m` for `x < m`, computed without `%`.
///
/// A verified caller composing a verified callee: this body has no obligation
/// of its own, and the whole of [`add_reduced`]'s Add and Sub are bundled into
/// it. That composition is only available because neither body contains `%`.
pub fn double_reduced(x: u32, m: u32) -> u32 {
    add_reduced(x, x, m)
}

// ===========================================================================
// TIER 2b — `%`- and `/`-bearing. Proved total; TERMINAL. No verified
// function may call one of these (fragment map §7.2), which is why several
// bodies below spell out a reduction that a call would otherwise share.
// ===========================================================================

/// `x mod m`, the mathematical residue in `[0, m)`.
///
/// `crates/trust-loop/src/scheduling.rs:209` and its two copies, with the
/// zero-divisor condition decided rather than restated.
pub fn reduce(x: u32, m: u32) -> u32 {
    if m == 0 {
        return NOT_A_RESIDUE;
    }
    let mm: u64 = m as u64;
    ((x as u64) % mm) as u32
}

/// `x mod m` for a **wide** dividend — the reduction a `u64` hash or a `u64`
/// accumulator needs before it can index anything.
pub fn reduce_wide(x: u64, m: u32) -> u32 {
    if m == 0 {
        return NOT_A_RESIDUE;
    }
    let mm: u64 = m as u64;
    (x % mm) as u32
}

/// The largest residue modulo `m`, i.e. `m - 1`; `NOT_A_RESIDUE` at `m == 0`.
///
/// This is the `last` that [`residue_clamp`] takes. It is tier 2 rather than
/// tier 1 because its honest bound is `result <= m - 1`, and the clause
/// language admits nothing built from an operator.
pub fn mod_last(m: u32) -> u32 {
    if m == 0 {
        return NOT_A_RESIDUE;
    }
    m - 1
}

/// `(a + b) mod m` for arbitrary `a`, `b`.
pub fn add_mod(a: u32, b: u32, m: u32) -> u32 {
    if m == 0 {
        return NOT_A_RESIDUE;
    }
    let mm: u64 = m as u64;
    let s: u64 = (a as u64) + (b as u64);
    (s % mm) as u32
}

/// `(2 * a) mod m` for arbitrary `a`.
pub fn double_mod(a: u32, m: u32) -> u32 {
    if m == 0 {
        return NOT_A_RESIDUE;
    }
    let mm: u64 = m as u64;
    let s: u64 = (a as u64) + (a as u64);
    (s % mm) as u32
}

/// `(a - b) mod m` for arbitrary `a`, `b`.
///
/// Both operands are reduced here and the difference is taken one call down in
/// [`sub_reduced`]. That is not tidiness: a guarded subtraction of two locals
/// derived from `%` in the *same* body leaves its `arithmetic_overflow_sub`
/// row UNKNOWN, and crossing a call boundary is what re-supplies the range
/// (fragment map §11.1, §13.3, and §14.4 for this crate's measurement).
pub fn sub_mod(a: u32, b: u32, m: u32) -> u32 {
    if m == 0 {
        return NOT_A_RESIDUE;
    }
    let mm: u64 = m as u64;
    let ar: u32 = ((a as u64) % mm) as u32;
    let br: u32 = ((b as u64) % mm) as u32;
    sub_reduced(ar, br, m)
}

/// `(-a) mod m` for arbitrary `a`.
pub fn neg_mod(a: u32, m: u32) -> u32 {
    if m == 0 {
        return NOT_A_RESIDUE;
    }
    let mm: u64 = m as u64;
    let r: u32 = ((a as u64) % mm) as u32;
    neg_reduced(r, m)
}

/// `(a * b) mod m`, through a `u64` intermediate.
///
/// The product peaks at `(2^32 - 1)^2 == 18446744065119617025`, which leaves
/// `4294967294` of slack under `u64::MAX`; both operands get their range from
/// a bare widening cast, so the multiply needs no guard (fragment map §2.1).
/// The 128-bit spelling `(a as u128) * (b as u128)` is **not** in the fragment
/// (§2.3), which is why the modulus is a `u32` and not a `usize`.
pub fn mul_mod(a: u32, b: u32, m: u32) -> u32 {
    if m == 0 {
        return NOT_A_RESIDUE;
    }
    let mm: u64 = m as u64;
    let p: u64 = (a as u64) * (b as u64);
    (p % mm) as u32
}

/// `(a * a) mod m`.
pub fn sqr_mod(a: u32, m: u32) -> u32 {
    if m == 0 {
        return NOT_A_RESIDUE;
    }
    let mm: u64 = m as u64;
    let p: u64 = (a as u64) * (a as u64);
    (p % mm) as u32
}

/// One square-and-multiply step: `(acc^2 * base^bit) mod m`, for `bit` in
/// `{0, 1}` (any nonzero `bit` is read as 1).
///
/// Chain this MSB-first to exponentiate by an exponent of any width, starting
/// from `acc = 1`. This is the same shape `trust-checksum` uses for a CRC over
/// more than one byte: a loop does not discharge, so the *step* is the
/// primitive and the caller drives the recurrence.
///
/// The multiplier is selected at `u32` and widened, never selected at `u64`: a
/// select supplies the interval engine no range, and the widening cast does
/// (fragment map §2.1, §11.1).
pub fn pow_mod_step(acc: u32, base: u32, bit: u32, m: u32) -> u32 {
    if m == 0 {
        return NOT_A_RESIDUE;
    }
    let f: u32 = pow_factor(base, bit);
    let mm: u64 = m as u64;
    let a: u64 = acc as u64;
    let s: u64 = a * a;
    let t: u32 = (s % mm) as u32;
    let w: u64 = t as u64;
    let p: u64 = w * (f as u64);
    (p % mm) as u32
}

/// `base^exp mod m` for `exp <= 15`, by four unrolled square-and-multiply
/// steps. `NOT_A_RESIDUE` for `exp > 15` or `m == 0`.
///
/// **Four steps is a measured ceiling, not a taste.** Measured 2026-08-30 in
/// one run: four steps is `32/32 proved`; five is `0 certified, 20 unknown,
/// 20 timeouts out of 40`; six and seven fail outright with `native
/// typed-TrustIr lowering did not complete`. See §14.3 of
/// `docs/STRICT_VERIFICATION_FRAGMENT.md`. For a wider exponent, chain
/// [`pow_mod_step`] — the crate's tests do exactly that over 32 bits.
pub fn pow_mod(base: u32, exp: u32, m: u32) -> u32 {
    if m == 0 {
        return NOT_A_RESIDUE;
    }
    if exp > 15 {
        return NOT_A_RESIDUE;
    }
    let f3: u32 = pow_factor(base, exp & 8);
    let f2: u32 = pow_factor(base, exp & 4);
    let f1: u32 = pow_factor(base, exp & 2);
    let f0: u32 = pow_factor(base, exp & 1);
    let mm: u64 = m as u64;

    let a3: u64 = 1;
    let s3: u64 = a3 * a3;
    let t3: u32 = (s3 % mm) as u32;
    let w3: u64 = t3 as u64;
    let p3: u64 = w3 * (f3 as u64);
    let c3: u32 = (p3 % mm) as u32;

    let a2: u64 = c3 as u64;
    let s2: u64 = a2 * a2;
    let t2: u32 = (s2 % mm) as u32;
    let w2: u64 = t2 as u64;
    let p2: u64 = w2 * (f2 as u64);
    let c2: u32 = (p2 % mm) as u32;

    let a1: u64 = c2 as u64;
    let s1: u64 = a1 * a1;
    let t1: u32 = (s1 % mm) as u32;
    let w1: u64 = t1 as u64;
    let p1: u64 = w1 * (f1 as u64);
    let c1: u32 = (p1 % mm) as u32;

    let a0: u64 = c1 as u64;
    let s0: u64 = a0 * a0;
    let t0: u32 = (s0 % mm) as u32;
    let w0: u64 = t0 as u64;
    let p0: u64 = w0 * (f0 as u64);
    (p0 % mm) as u32
}

/// `a / b`, the Euclidean quotient; `NOT_A_RESIDUE` at `b == 0`.
pub fn quotient(a: u32, b: u32) -> u32 {
    if b == 0 {
        return NOT_A_RESIDUE;
    }
    a / b
}

/// One Euclid step: `a mod b`, the next remainder in a gcd recurrence.
/// `NOT_A_RESIDUE` at `b == 0`, which is where the recurrence terminates.
pub fn gcd_step(a: u32, b: u32) -> u32 {
    if b == 0 {
        return NOT_A_RESIDUE;
    }
    a % b
}

/// One Bezout step of the extended Euclidean algorithm, carried modulo `m`:
/// `(t0 - q * t1) mod m`.
///
/// Chained alongside [`gcd_step`] and [`quotient`], this computes a modular
/// inverse; the crate's tests drive the recurrence and check every answer
/// against an independent brute-force search.
pub fn bezout_step(t0: u32, t1: u32, q: u32, m: u32) -> u32 {
    if m == 0 {
        return NOT_A_RESIDUE;
    }
    let mm: u64 = m as u64;
    let p: u64 = (q as u64) * (t1 as u64);
    let pr: u32 = (p % mm) as u32;
    let t0r: u32 = ((t0 as u64) % mm) as u32;
    sub_reduced(t0r, pr, m)
}

/// `1` when `x` is a multiplicative inverse of `a` modulo `m`, i.e.
/// `(a * x) mod m == 1`; `0` otherwise.
///
/// Tier 2 rather than tier 1: a contracted body may contain no arithmetic at
/// all, and this one multiplies (fragment map §1.1).
pub fn inv_check(a: u32, x: u32, m: u32) -> u8 {
    if m == 0 {
        return 0;
    }
    let mm: u64 = m as u64;
    let p: u64 = (a as u64) * (x as u64);
    let r: u64 = p % mm;
    if r == 1 {
        return 1;
    }
    0
}

/// `1` when `m` divides `a`; `0` otherwise (and `0` at `m == 0`).
pub fn is_divisible(a: u32, m: u32) -> u8 {
    if m == 0 {
        return 0;
    }
    let mm: u64 = m as u64;
    let r: u64 = (a as u64) % mm;
    if r == 0 {
        return 1;
    }
    0
}

/// `1` when `a` and `b` are congruent modulo `m`; `0` otherwise.
pub fn congruent(a: u32, b: u32, m: u32) -> u8 {
    if m == 0 {
        return 0;
    }
    let mm: u64 = m as u64;
    let ar: u64 = (a as u64) % mm;
    let br: u64 = (b as u64) % mm;
    if ar == br {
        return 1;
    }
    0
}

// ===========================================================================
// Tests. NONE of the expectations below is derived from the function under
// test: every reference answer comes from `u128` arithmetic, from repeated
// subtraction, from repeated addition, from a naive multiply loop, or from an
// exhaustive search — decision procedures written by a different method.
//
// The proofs above cover overflow, underflow and zero divisors on every input.
// They cover NOTHING about whether the answer is right: a truncating cast is
// not an overflow, and `ensures result <= last` is true of a function that
// always returns zero. That gap is what this module is for.
// ===========================================================================
#[cfg(test)]
mod tests {
    use super::*;

    // ---- independent oracles ---------------------------------------------

    /// `x mod m` by repeated subtraction. Uses no `%` and no `/`.
    fn oracle_reduce_by_subtraction(x: u64, m: u32) -> u32 {
        let mm = m as u64;
        let mut v = x;
        while v >= mm {
            v -= mm;
        }
        v as u32
    }

    /// `(a * b) mod m` by repeated addition. Uses no `*` and no `%`.
    fn oracle_mul_by_addition(a: u32, b: u32, m: u32) -> u32 {
        let mm = m as u64;
        let mut acc: u64 = 0;
        let mut i: u32 = 0;
        let base = oracle_reduce_by_subtraction(a as u64, m) as u64;
        while i < b {
            acc += base;
            while acc >= mm {
                acc -= mm;
            }
            i += 1;
        }
        acc as u32
    }

    /// `base^exp mod m` by a naive multiply loop at `u128`.
    fn oracle_pow(base: u32, exp: u32, m: u32) -> u32 {
        let mm = m as u128;
        let mut acc: u128 = 1 % mm;
        let mut i: u32 = 0;
        while i < exp {
            acc = (acc * (base as u128)) % mm;
            i += 1;
        }
        acc as u32
    }

    /// The multiplicative inverse of `a` modulo `m`, by exhaustive search.
    fn oracle_inverse(a: u32, m: u32) -> Option<u32> {
        let mm = m as u128;
        let mut x: u32 = 0;
        while x < m {
            if ((a as u128) * (x as u128)) % mm == 1 {
                return Some(x);
            }
            x += 1;
        }
        None
    }

    fn oracle_gcd(a: u32, b: u32) -> u32 {
        let mut x = a;
        let mut y = b;
        while y != 0 {
            let t = x % y;
            x = y;
            y = t;
        }
        x
    }

    /// Drive the extended Euclidean recurrence using ONLY this crate's step
    /// functions. Returns the inverse of `a` modulo `m`, or `None`.
    fn chain_inverse(a: u32, m: u32) -> Option<u32> {
        let mut r0 = m;
        let mut r1 = a;
        let mut t0: u32 = 0;
        let mut t1: u32 = 1;
        let mut guard = 0;
        while r1 != 0 {
            guard += 1;
            assert!(guard < 64, "euclid did not terminate");
            let q = quotient(r0, r1);
            let r2 = gcd_step(r0, r1);
            let t2 = bezout_step(t0, t1, q, m);
            r0 = r1;
            r1 = r2;
            t0 = t1;
            t1 = t2;
        }
        if r0 == 1 { Some(t0) } else { None }
    }

    /// `base^exp mod m` by chaining [`pow_mod_step`] MSB-first over 32 bits.
    fn chain_pow(base: u32, exp: u32, m: u32) -> u32 {
        let mut acc: u32 = reduce(1, m);
        let mut k: u32 = 32;
        while k > 0 {
            k -= 1;
            let bit = (exp >> k) & 1;
            acc = pow_mod_step(acc, base, bit, m);
        }
        acc
    }

    // ---- tier 1 -----------------------------------------------------------

    #[test]
    fn modulus_floor_is_max_of_m_and_one() {
        assert_eq!(modulus_floor(0), 1);
        assert_eq!(modulus_floor(1), 1);
        let probes: [u32; 6] = [2, 7, 1000, 65535, 4294967294, 4294967295];
        for m in probes {
            assert_eq!(modulus_floor(m), m, "modulus_floor must not lower a real modulus");
        }
        let mut m: u32 = 0;
        while m <= 300 {
            let got = modulus_floor(m);
            let want = if m == 0 { 1 } else { m };
            assert_eq!(got, want, "modulus_floor({m})");
            m += 1;
        }
    }

    #[test]
    fn residue_clamp_is_min_of_v_and_last() {
        let mut v: u32 = 0;
        while v <= 80 {
            let mut last: u32 = 0;
            while last <= 80 {
                let want = if v < last { v } else { last };
                assert_eq!(residue_clamp(v, last), want, "residue_clamp({v}, {last})");
                last += 1;
            }
            v += 1;
        }
        assert_eq!(residue_clamp(4294967295, 0), 0);
        assert_eq!(residue_clamp(0, 4294967295), 0);
        assert_eq!(residue_clamp(4294967295, 4294967295), 4294967295);
    }

    /// The CARRIER for the tier-1 mutations: every discharged clause, checked
    /// directly. A wrong-value mutation that keeps its contract true must
    /// leave this test GREEN, or it demonstrates nothing.
    #[test]
    fn tier1_bounds_hold_everywhere() {
        let probes: [u32; 9] = [0, 1, 2, 3, 17, 255, 65536, 4294967294, 4294967295];
        for m in probes {
            assert!(modulus_floor(m) >= 1, "modulus_floor({m}) >= 1");
            assert!(modulus_floor(m) >= m, "modulus_floor({m}) >= m");
            assert!(is_zero_modulus(m) <= 1);
            for v in probes {
                assert!(residue_clamp(v, m) <= m, "residue_clamp({v},{m}) <= last");
                assert!(residue_clamp(v, m) <= v, "residue_clamp({v},{m}) <= v");
                assert!(is_residue(v, m) <= 1);
                for b in probes {
                    assert!(is_reduced_pair(v, b, m) <= 1);
                }
            }
        }
    }

    #[test]
    fn predicates_decide_their_own_domain() {
        assert_eq!(is_zero_modulus(0), 1);
        assert_eq!(is_zero_modulus(1), 0);
        let mut m: u32 = 0;
        while m <= 64 {
            let mut v: u32 = 0;
            while v <= 70 {
                let want = if m != 0 && v < m { 1 } else { 0 };
                assert_eq!(is_residue(v, m), want, "is_residue({v}, {m})");
                let mut b: u32 = 0;
                while b <= 70 {
                    let want_pair = if m != 0 && v < m && b < m { 1 } else { 0 };
                    assert_eq!(is_reduced_pair(v, b, m), want_pair, "is_reduced_pair({v},{b},{m})");
                    b += 7;
                }
                v += 1;
            }
            m += 1;
        }
    }

    // ---- reduction --------------------------------------------------------

    #[test]
    fn reduce_matches_repeated_subtraction() {
        let mut m: u32 = 2;
        while m <= 64 {
            let mut x: u32 = 0;
            while x <= 4 * m + 3 {
                assert_eq!(
                    reduce(x, m),
                    oracle_reduce_by_subtraction(x as u64, m),
                    "reduce({x}, {m})"
                );
                x += 1;
            }
            m += 1;
        }
        assert_eq!(reduce(1, 1), 0);
        assert_eq!(reduce(4294967295, 4294967295), 0);
        assert_eq!(reduce(4294967294, 4294967295), 4294967294);
        assert_eq!(reduce(7, 0), NOT_A_RESIDUE);
    }

    #[test]
    fn reduce_wide_matches_u128() {
        let wides: [u64; 8] = [
            0,
            1,
            4294967295,
            4294967296,
            18446744073709551615,
            12345678901234567890,
            1000000007,
            9223372036854775808,
        ];
        let mods: [u32; 7] = [1, 2, 3, 97, 65537, 4294967294, 4294967295];
        for x in wides {
            for m in mods {
                let want = ((x as u128) % (m as u128)) as u32;
                assert_eq!(reduce_wide(x, m), want, "reduce_wide({x}, {m})");
            }
        }
        assert_eq!(reduce_wide(5, 0), NOT_A_RESIDUE);
        let mut m: u32 = 2;
        while m <= 64 {
            let mut x: u64 = 0;
            while x <= 3 * (m as u64) + 2 {
                assert_eq!(reduce_wide(x, m), oracle_reduce_by_subtraction(x, m));
                x += 1;
            }
            m += 1;
        }
    }

    #[test]
    fn mod_last_is_one_below_the_modulus() {
        assert_eq!(mod_last(0), NOT_A_RESIDUE);
        let mut m: u32 = 1;
        while m <= 300 {
            assert_eq!(mod_last(m), m - 1);
            m += 1;
        }
        assert_eq!(mod_last(4294967295), 4294967294);
    }

    // ---- the ring operations, exhaustive over every small modulus ---------

    #[test]
    fn add_sub_neg_double_match_u128() {
        let mut m: u32 = 2;
        while m <= 64 {
            let mm = m as u128;
            let mut a: u32 = 0;
            while a <= m + 2 {
                let want_neg = (((mm - ((a as u128) % mm)) % mm)) as u32;
                assert_eq!(neg_mod(a, m), want_neg, "neg_mod({a}, {m})");
                let want_dbl = ((2 * (a as u128)) % mm) as u32;
                assert_eq!(double_mod(a, m), want_dbl, "double_mod({a}, {m})");
                let mut b: u32 = 0;
                while b <= m + 2 {
                    let want_add = (((a as u128) + (b as u128)) % mm) as u32;
                    assert_eq!(add_mod(a, b, m), want_add, "add_mod({a},{b},{m})");
                    let want_sub = ((((a as u128) % mm) + mm - ((b as u128) % mm)) % mm) as u32;
                    assert_eq!(sub_mod(a, b, m), want_sub, "sub_mod({a},{b},{m})");
                    b += 1;
                }
                a += 1;
            }
            m += 1;
        }
        // The corners of the type, where a u32-only implementation overflows.
        assert_eq!(add_mod(4294967295, 4294967295, 4294967295), 0);
        assert_eq!(add_mod(4294967294, 4294967294, 4294967295), 4294967293);
        assert_eq!(double_mod(4294967294, 4294967295), 4294967293);
        assert_eq!(sub_mod(0, 1, 4294967295), 4294967294);
        assert_eq!(neg_mod(1, 4294967295), 4294967294);
        for f in [add_mod(1, 1, 0), sub_mod(1, 1, 0), neg_mod(1, 0), double_mod(1, 0)] {
            assert_eq!(f, NOT_A_RESIDUE);
        }
    }

    #[test]
    fn mul_mod_matches_repeated_addition() {
        let mut m: u32 = 2;
        while m <= 64 {
            let mut a: u32 = 0;
            while a <= m + 2 {
                let mut b: u32 = 0;
                while b <= m + 2 {
                    let want = oracle_mul_by_addition(a, b, m);
                    assert_eq!(mul_mod(a, b, m), want, "mul_mod({a},{b},{m})");
                    b += 1;
                }
                assert_eq!(sqr_mod(a, m), oracle_mul_by_addition(a, a, m), "sqr_mod({a},{m})");
                a += 1;
            }
            m += 1;
        }
        // A product that overflows `u32` and does not overflow `u64`.
        assert_eq!(mul_mod(4294967295, 4294967295, 4294967295), 0);
        assert_eq!(
            mul_mod(4294967295, 4294967294, 1000000007),
            ((4294967295u128 * 4294967294u128) % 1000000007u128) as u32
        );
        assert_eq!(sqr_mod(4294967295, 1000000007), ((4294967295u128 * 4294967295u128) % 1000000007u128) as u32);
        assert_eq!(mul_mod(3, 5, 0), NOT_A_RESIDUE);
        assert_eq!(sqr_mod(3, 0), NOT_A_RESIDUE);
    }

    #[test]
    fn reduced_core_matches_the_percent_forms() {
        let mut m: u32 = 2;
        while m <= 64 {
            let mm = m as u128;
            let mut a: u32 = 0;
            while a < m {
                assert_eq!(neg_reduced(a, m), neg_mod(a, m), "neg_reduced({a},{m})");
                assert_eq!(double_reduced(a, m), double_mod(a, m), "double_reduced({a},{m})");
                assert_eq!(reduce_once(a, m), a, "reduce_once below m");
                assert_eq!(reduce_once(a + m, m), a, "reduce_once one above");
                let mut b: u32 = 0;
                while b < m {
                    let want_add = (((a as u128) + (b as u128)) % mm) as u32;
                    let want_sub = (((a as u128) + mm - (b as u128)) % mm) as u32;
                    assert_eq!(add_reduced(a, b, m), want_add, "add_reduced({a},{b},{m})");
                    assert_eq!(sub_reduced(a, b, m), want_sub, "sub_reduced({a},{b},{m})");
                    b += 1;
                }
                a += 1;
            }
            m += 1;
        }
        // The reduced core at the top of the type, where a u32 sum overflows.
        assert_eq!(add_reduced(4294967293, 4294967293, 4294967294), 4294967292);
        assert_eq!(sub_reduced(0, 4294967293, 4294967294), 1);
        assert_eq!(neg_reduced(0, 97), 0);
        for f in [
            add_reduced(1, 1, 0),
            sub_reduced(1, 1, 0),
            neg_reduced(1, 0),
            double_reduced(1, 0),
            reduce_once(1, 0),
        ] {
            assert_eq!(f, NOT_A_RESIDUE);
        }
    }

    // ---- exponentiation ---------------------------------------------------

    #[test]
    fn pow_mod_matches_the_naive_loop() {
        let mut m: u32 = 2;
        while m <= 48 {
            let mut base: u32 = 0;
            while base <= m + 1 {
                let mut e: u32 = 0;
                while e <= 15 {
                    assert_eq!(pow_mod(base, e, m), oracle_pow(base, e, m), "pow_mod({base},{e},{m})");
                    e += 1;
                }
                base += 1;
            }
            m += 1;
        }
        assert_eq!(pow_mod(2, 10, 1000000007), 1024);
        assert_eq!(pow_mod(7, 0, 13), 1);
        assert_eq!(pow_mod(7, 1, 13), 7);
        assert_eq!(pow_mod(4294967295, 15, 1000000007), oracle_pow(4294967295, 15, 1000000007));
        // The bounded exponent refuses rather than answering the wrong question.
        assert_eq!(pow_mod(2, 16, 97), NOT_A_RESIDUE);
        assert_eq!(pow_mod(2, 4294967295, 97), NOT_A_RESIDUE);
        assert_eq!(pow_mod(2, 3, 0), NOT_A_RESIDUE);
    }

    #[test]
    fn chained_pow_step_matches_the_naive_loop() {
        let mut m: u32 = 2;
        while m <= 24 {
            let mut base: u32 = 0;
            while base <= m + 1 {
                let mut e: u32 = 0;
                while e <= 40 {
                    assert_eq!(chain_pow(base, e, m), oracle_pow(base, e, m), "chain_pow({base},{e},{m})");
                    e += 1;
                }
                base += 1;
            }
            m += 1;
        }
        // Wide exponents, still against the naive loop.
        let wides: [u32; 5] = [255, 4096, 65535, 100000, 999983];
        for e in wides {
            assert_eq!(chain_pow(3, e, 1000000007), oracle_pow(3, e, 1000000007), "chain_pow(3,{e})");
            assert_eq!(chain_pow(4294967295, e, 4294967291), oracle_pow(4294967295, e, 4294967291));
        }
        // Fermat: a^(p-1) == 1 mod p for a prime p not dividing a.
        assert_eq!(chain_pow(5, 1000000006, 1000000007), 1);
        assert_eq!(pow_mod_step(1, 3, 0, 0), NOT_A_RESIDUE);
        // The multiplier select, which has to live one call down.
        assert_eq!(pow_factor(7, 0), 1);
        assert_eq!(pow_factor(7, 1), 7);
        assert_eq!(pow_factor(7, 128), 7);
        assert_eq!(pow_factor(0, 1), 0);
    }

    // ---- extended Euclid --------------------------------------------------

    #[test]
    fn extended_euclid_chain_finds_every_inverse() {
        let mut m: u32 = 2;
        while m <= 64 {
            let mut a: u32 = 0;
            while a < m {
                let want = oracle_inverse(a, m);
                let got = chain_inverse(a, m);
                assert_eq!(got, want, "inverse of {a} mod {m}");
                if let Some(x) = got {
                    assert_eq!(inv_check(a, x, m), 1, "inv_check disagrees for {a} mod {m}");
                    assert_eq!(oracle_gcd(a, m), 1, "an inverse exists only for a coprime a");
                }
                a += 1;
            }
            m += 1;
        }
        // A large prime modulus, where a search oracle is not affordable.
        let p: u32 = 1000000007;
        let probes: [u32; 5] = [2, 3, 99991, 4294967295, 1000000006];
        for a in probes {
            let x = chain_inverse(a, p).expect("a nonzero residue mod a prime is invertible");
            assert_eq!(inv_check(a, x, p), 1, "inv_check for {a} mod {p}");
            assert_eq!(mul_mod(a, x, p), 1, "mul_mod cross-check for {a} mod {p}");
        }
        assert_eq!(chain_inverse(2, 4), None);
        assert_eq!(inv_check(2, 2, 4), 0);
    }

    #[test]
    fn gcd_and_quotient_are_the_euclid_step() {
        let mut a: u32 = 0;
        while a <= 200 {
            let mut b: u32 = 1;
            while b <= 200 {
                assert_eq!(gcd_step(a, b), a % b, "gcd_step({a},{b})");
                assert_eq!(quotient(a, b), a / b, "quotient({a},{b})");
                b += 1;
            }
            a += 1;
        }
        assert_eq!(gcd_step(5, 0), NOT_A_RESIDUE);
        assert_eq!(quotient(5, 0), NOT_A_RESIDUE);
        assert_eq!(quotient(4294967295, 1), 4294967295);
    }

    #[test]
    fn divisibility_and_congruence_agree_with_reduction() {
        let mut m: u32 = 1;
        while m <= 64 {
            let mut a: u32 = 0;
            while a <= 3 * m + 2 {
                let ra = reduce(a, m);
                assert_eq!(is_divisible(a, m), u8::from(ra == 0), "is_divisible({a},{m})");
                let mut b: u32 = 0;
                while b <= 3 * m + 2 {
                    assert_eq!(congruent(a, b, m), u8::from(ra == reduce(b, m)), "congruent({a},{b},{m})");
                    b += 1;
                }
                a += 1;
            }
            m += 1;
        }
        assert_eq!(is_divisible(0, 0), 0);
        assert_eq!(congruent(1, 1, 0), 0);
    }

    // ---- the sentinel -----------------------------------------------------

    #[test]
    fn sentinels_are_returned_and_are_never_residues() {
        assert_eq!(NOT_A_RESIDUE, 4294967295);
        assert_eq!(NOT_A_RESIDUE, u32::MAX);
        // A residue modulo any m >= 1 is at most m - 1 <= u32::MAX - 1, so the
        // sentinel can never collide with a real answer. Checked at the two
        // moduli where a collision would have to happen if it ever could.
        let mut m: u32 = 1;
        while m <= 64 {
            let mut x: u32 = 0;
            while x <= 2 * m {
                assert_ne!(reduce(x, m), NOT_A_RESIDUE);
                x += 1;
            }
            m += 1;
        }
        assert_ne!(reduce(4294967294, 4294967295), NOT_A_RESIDUE);
        assert_ne!(mul_mod(4294967294, 4294967294, 4294967295), NOT_A_RESIDUE);
        // Every entry point answers the degenerate modulus the same way.
        let zeros: [u32; 12] = [
            reduce(9, 0),
            reduce_wide(9, 0),
            mod_last(0),
            add_mod(1, 2, 0),
            sub_mod(1, 2, 0),
            neg_mod(1, 0),
            double_mod(1, 0),
            mul_mod(1, 2, 0),
            sqr_mod(2, 0),
            pow_mod(2, 3, 0),
            pow_mod_step(1, 2, 1, 0),
            bezout_step(1, 2, 3, 0),
        ];
        for z in zeros {
            assert_eq!(z, NOT_A_RESIDUE);
        }
    }
}
