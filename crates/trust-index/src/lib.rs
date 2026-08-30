//! Total, verified bounded-index, ring and slice-range arithmetic for `no_std`
//! Trust components.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0
//!
//! # Why this crate exists, and who calls it
//!
//! Indexing a buffer is the single most common panicking operation in this
//! tree, and the side condition that makes it safe is almost never a proved
//! proposition. It is a sentence in a doc comment, an `.expect` message naming
//! a check in a different function, or nothing at all. Six sites, each measured
//! against the current tree:
//!
//! **`crates/trust-convergence/src/termination.rs:702`** — a comment that
//! names itself as a proof, for eight separate facts:
//!
//! ```text
//! // ... the early return gives `n >= 1` to every `n - 1`, `% n`, and index
//! // below, so they PROVE.
//! if n == 0 { return None; }
//! ...
//! let primary_idx   = (attempt.saturating_sub(n)) % n;   // :722
//! let secondary_idx = (primary_idx + 1) % n;             // :723
//! let (var, _delta) = decreasing_vars[idx.min(n - 1)];   // :738  and again :747
//! ```
//!
//! Four modulo-by-`n` divisor facts, two `n - 1` underflow facts, and two
//! byte-identical inline `idx.min(n - 1)` clamps, all discharged by one
//! sentence twenty lines up. [`ring_offset`] is `(x + k) % n` with the divisor
//! fact carried by the function, and [`clamp_index`]`(idx, `[`last_index`]`(n))`
//! is that inline clamp with the underflow proved.
//!
//! **`crates/trust-backprop/src/validation/cargo_exec.rs:498`** — a hand-rolled
//! ring buffer whose private `copy_at` helper has no doc comment at all:
//!
//! ```text
//! let write_at = (self.start + self.len) % capacity;        // :485
//! self.start   = (self.start + chunk.len()) % capacity;     // :494
//! fn copy_at(&mut self, offset: usize, chunk: &[u8]) {
//!     let first = (capacity - offset).min(chunk.len());     // :500  underflow
//!     self.bytes[offset..offset + first]...                 // :501  range
//! ```
//!
//! `offset < capacity`, `offset + first <= capacity` and
//! `chunk.len() <= capacity` all hold only because of an early return and a
//! `capacity == 0` guard in the *caller*, restated nowhere. [`ring_offset`],
//! [`span_len`] and [`window_end`] are those three facts as signatures.
//!
//! **`crates/trust-ts-strip/src/erase.rs:39`** — a one-sided range defence,
//! which is the sharpest shape in the survey because the guard *creates* the
//! bug it is written to prevent:
//!
//! ```text
//! let en = en.min(bytes.len());
//! for byte in &mut bytes[s..en] {
//! ```
//!
//! `en` is clamped and `s` is not, so the range inverts — `s > en`, a panic —
//! for exactly the spans whose start exceeds `bytes.len()`, which is the case
//! line 40 introduces. [`subslice`] clamps **both** ends and is proved to
//! produce a non-inverting range on every input, including that one.
//!
//! **`crates/trust-ts-strip/src/erase.rs:72`** — three unstated facts on one
//! line, and the idiom this crate is named for:
//!
//! ```text
//! let i = (self.pos + k).min(self.toks.len() - 1);
//! ```
//!
//! `toks` non-empty (or `len() - 1` underflows), and `pos + k` does not
//! overflow. `crates/trust-loop/src/lib.rs:510` and `:519` spell the identical
//! idiom two different ways in one file — `saturating_sub(1)` on one line and a
//! raw `len() - 1` ten lines later — which is what an unproved convention looks
//! like when two people write it.
//!
//! **`crates/trust-clean/src/cfg_family/emit.rs:695`** — a modulo whose
//! divisor-nonzero fact is checked only in debug builds, and only *after* the
//! division:
//!
//! ```text
//! let wrong_target = (target_pc + 1) % block_count;
//! debug_assert_ne!(wrong_target, *target_pc, "a Br visit's family always has >= 2 blocks");
//! ```
//!
//! In release, `block_count == 0` is a divide-by-zero panic. Two lines on,
//! `&plan.spec.blocks[visit.pc]` is indexed with no justification whatsoever.
//!
//! **`crates/trust-temporal/src/fairness.rs:557`** — a fact that lives in
//! another module:
//!
//! ```text
//! replay_lasso_f_violation(sm, accepting, lasso_trace, cycle_start)?;
//! let cycle = &lasso_trace[cycle_start..];
//! let last  = *cycle.last().expect("replay validated a non-empty cycle");
//! ```
//!
//! The `expect` message asserts a property of a *different function's* early
//! returns (`liveness.rs:260` and `:263`), reachable only through a `?` on an
//! ordinary string error that any refactor could reorder. [`tail`] takes the
//! suffix with the bound applied at the call, so there is no `?` to preserve.
//!
//! `crates/trust-sha2/src/sha256.rs:131` is the same shape at its most
//! load-bearing: one prose sentence (*"Invariant: `< BLOCK_SIZE`"*) is the sole
//! discharge for a subtraction underflow at `:153`, a range at `:154`, an index
//! at `:192` and a `start <= end` at `:204` — and `:204`'s fact is not even the
//! invariant that was stated. `crates/trust-sha2/src/sha512.rs:180` is the
//! byte-identical index with the comment *dropped*.
//!
//! # Why not `trust-ratio`
//!
//! `crates/trust-ratio` already proves `clamp_upper`, `last_index` and
//! `saturating_diff` — **at `u32`**. Every site above is `usize`, and a `usize`
//! caller of a `u32` API has to cast at the boundary, which is exactly where
//! `crates/trust-js-interp/src/builtins_string.rs:353` compares in `u64` and
//! then subtracts in `usize`. This crate is the `usize` lane, plus the two
//! families `trust-ratio` has none of: **ring wrap-around** and **slices**.
//! Nothing here calls it — cross-crate composition mints a fatal absent-callee
//! row in the caller — so [`clamp_upper`] is re-declared and re-proved, which
//! is the standing cost of the four sibling crates and not an oversight.
//!
//! # Totality
//!
//! Every function is **total**: defined on all inputs, no panicking path, no
//! `requires`. A precondition is not available under the strict lane (both
//! spellings record `[ASSUMED] assumption:requires ... unsupported MIR
//! FullVerification::Precondition`, and an assumed row fails the gate), and
//! none is wanted — a precondition is precisely the thing every site above
//! already has and cannot discharge.
//!
//! Sentinels: an out-of-range index returns the nearest in-range one, an
//! out-of-range slice range returns the empty slice, and a zero capacity
//! returns `0`. `at` takes the fallback as an argument rather than choosing one.
//!
//! # Two tiers, marked per item
//!
//! **Tier 1 — proved bound.** A grammar `ensures` clause the compiler
//! discharges: [`clamp_index`], [`window_start`], [`window_end`], [`span_len`],
//! [`capped_len`]. A caller may rely on the clause; a body that broke it would
//! not compile. **The clamp is live in every one of them** — the argument can
//! genuinely exceed the bound — which is what separates a proved bound from a
//! wrapper reshaped until the encoder accepted it.
//!
//! **Tier 2 — proved totality, bound carried by the construction.** The ring
//! and slice functions. What is proved is that the body cannot panic: no index
//! is out of range, no range inverts, no subtraction underflows, no divisor is
//! zero. They carry no `ensures` because their bound is *structural* —
//! `ring_next` returns `0` or `i + 1 <= last` by construction, so a wrapper
//! clamping it to `last` would be dead code, and a dead clamp is a green row
//! that is not evidence.
//!
//! # What is NOT proved here, and is pinned by tests instead
//!
//! **Which end is which.** No obligation in this crate can see whether
//! [`window_end`] adds or subtracts, or whether [`ring_distance`] measures
//! forward or backward: both spellings keep every operand in range and both
//! discharge `ensures result <= len`. `trust_index_strict_gate.sh` mutation D
//! swaps `raw_sat_add` for `raw_sat_sub` inside a **contracted** function and
//! watches the strict lane stay at exit 0 with every row proved while the unit
//! tests go red. A proved contract is not a proved specification.
//!
//! **Truncating casts.** The `as usize` after a `u128` modulo is neither an
//! overflow nor a zero divisor, so it mints no obligation at all
//! (`STRICT_VERIFICATION_FRAGMENT.md` §2.5). [`ring_offset`] is correct because
//! `x % c < c <= usize::MAX`, and that step is carried by
//! `ring_offset_never_leaves_the_ring` rather than by the verifier.
//! [`ring_distance`] is pure `usize` and has no cast to be wrong about — it is
//! the only ring function in that position, and it is why the two are spelled
//! differently despite computing over the same ring.
//!
//! # The measured fragment boundary
//!
//! See [`docs/STRICT_VERIFICATION_FRAGMENT.md`] for the full checklist. What
//! THIS crate established, measured 2026-08-29 on the authenticated `targo
//! trust check` lane at stage1 driver `ba5e2cace25b69a8`:
//!
//! [`docs/STRICT_VERIFICATION_FRAGMENT.md`]: ../../../docs/STRICT_VERIFICATION_FRAGMENT.md
//!
//! * **`usize` is in the fragment, and so is `usize::MAX`.** The whole crate is
//!   `usize`; the saturating primitives widen to `u128` and compare against
//!   `usize::MAX as u128`, so nothing hard-codes a 64-bit word.
//! * **`%` is composition-opaque**, exactly like `>>`, `<<` and `/`. This is why
//!   every ring function is tier 2.
//! * **`x % c` does NOT supply the interval engine with `[0, c)`.** A `+ c` or
//!   a `- x` on a freshly-reduced value is UNKNOWN until it is guarded
//!   explicitly, which is why [`ring_distance`] carries a `back > cap` test
//!   that is mathematically dead and structurally required.
//! * **`-` is NOT composition-opaque**, and neither is a narrowing cast. A
//!   contracted wrapper over a callee that subtracts discharges normally.
//! * **A `u128` MULTIPLY does not verify**, though a `u128` add does and a
//!   `u64` multiply does. That is the single reason this crate offers no
//!   `chunk_start(idx, size, len)`.
//! * **A slice index and a slice RANGE both prove behind ordinary guards**,
//!   including `s.len()` and `s.is_empty()` in the guard.
//! * **A generic `fn f<T>(s: &[T])` is not an eligible body at all** — it emits
//!   no obligations and does not appear in coverage, so `Coverage: complete`
//!   says nothing about it. Every signature here is concrete.
//! * **A slice index proves only when the guard's other arm returns a LOCAL.**
//!   `if i >= s.len() { return default; } s[i]` leaves the bounds row and its
//!   hardened twin UNKNOWN when `default` is a *parameter*; `let d = default;
//!   ... return d;` proves both. Measured in one run against four variants, so
//!   arity (a three-parameter body with a literal fallback proves) and guard
//!   polarity are both ruled out. Same values, same guard, same index — a
//!   one-line respelling worth two rows.

#![no_std]

// ---------------------------------------------------------------------------
// Composition carrier.
//
// The only contract-carrying private body in the crate; every tier-1 bound is
// inherited from it. A contracted wrapper discharges its clause only when its
// callee ACTUALLY CARRIES a contract — the same wrapper over an uncontracted
// clamp measures UNKNOWN — which is why this exists as a separate, contracted
// function rather than as an inline comparison at each site.
// ---------------------------------------------------------------------------

/// `v`, clamped from above by `hi`.
fn clamp_upper(v: usize, hi: usize) -> usize ensures result <= hi {
    if v > hi { hi } else { v }
}

// ---------------------------------------------------------------------------
// Saturating primitives (uncontracted).
//
// `a as u128 + b as u128` cannot overflow for any `usize` width, so no guard is
// needed on the sum itself — a widening cast supplies the interval engine with
// a closed range by itself. The comparison is against `usize::MAX as u128`
// rather than a literal so the crate is correct on a 32-bit `usize`.
// ---------------------------------------------------------------------------

/// `a + b`, saturating at `usize::MAX`.
fn raw_sat_add(a: usize, b: usize) -> usize {
    let s: u128 = a as u128 + b as u128;
    let m: u128 = usize::MAX as u128;
    if s > m { return usize::MAX; }
    s as usize
}

/// `a - b`, saturating at `0`.
fn raw_sat_sub(a: usize, b: usize) -> usize {
    if a < b { return 0; }
    a - b
}

/// The length of `s`, unclamped. Exists so [`capped_len`] is a shape-(B)
/// wrapper whose clamp does the work.
fn raw_len(s: &[u8]) -> usize {
    s.len()
}

// ---------------------------------------------------------------------------
// Tier 1 — proved bounds.
//
// The clamp is LIVE in every one of these: the argument can genuinely exceed
// the bound, which is the whole reason the caller sites listed in the module
// docs are hazards. None of these wrappers contains dead code.
// ---------------------------------------------------------------------------

/// `i`, clamped so it is never past `last`.
///
/// **Tier 1.** `ensures result <= last` is checked.
///
/// This is the `idx.min(n - 1)` written out longhand at
/// `crates/trust-convergence/src/termination.rs:738` and `:747`, and the
/// `(self.pos + k).min(self.toks.len() - 1)` at
/// `crates/trust-ts-strip/src/erase.rs:72`. Pair it with [`last_index`], which
/// proves the `- 1` those sites leave unguarded:
/// `clamp_index(i, last_index(len))`.
///
/// The honest contract of a `clamp_index(i, len)` taking a *length* would be
/// `len == 0 || result < len`, and a disjunctive `ensures` is not discharged —
/// so the bound is spelled inclusively and the empty case is the caller's
/// separate `len == 0` test, as it already is at every site above.
pub fn clamp_index(i: usize, last: usize) -> usize ensures result <= last {
    clamp_upper(i, last)
}

/// A window start, clamped into `[0, len]`.
///
/// **Tier 1.** `ensures result <= len` is checked.
///
/// This is the guard `crates/trust-ts-strip/src/erase.rs:40` does not have: it
/// clamps the range *end* and leaves the start alone, so the range inverts for
/// exactly the spans this function bounds.
pub fn window_start(start: usize, len: usize) -> usize ensures result <= len {
    clamp_upper(start, len)
}

/// A window end: `start + count`, saturating, then clamped into `[0, len]`.
///
/// **Tier 1.** `ensures result <= len` is checked. Both hazards are discharged
/// — the sum cannot overflow (it is computed widened) and the result cannot
/// exceed `len`.
///
/// `crates/trust-backprop/src/validation/cargo_exec.rs:501` writes
/// `self.bytes[offset..offset + first]`, whose `offset + first <= capacity` is
/// stated nowhere; `crates/trust-js-parse/src/parser.rs:2486` writes
/// `chars[i + 1..(i + 3).min(chars.len())]`, which inverts unless
/// `i < chars.len()`.
pub fn window_end(start: usize, count: usize, len: usize) -> usize ensures result <= len {
    clamp_upper(raw_sat_add(start, count), len)
}

/// The length of the range `start..end`, saturating at `0`, clamped to `cap`.
///
/// **Tier 1.** `ensures result <= cap` is checked.
///
/// `crates/trust-backprop/src/validation/cargo_exec.rs:500` computes
/// `capacity - offset` with no proof that `offset <= capacity`;
/// `crates/trust-js-interp/src/builtins_string.rs:368` computes
/// `int_max - s.len()` after comparing the two in a *different type*.
pub fn span_len(start: usize, end: usize, cap: usize) -> usize ensures result <= cap {
    clamp_upper(raw_sat_sub(end, start), cap)
}

/// `s.len()`, clamped to `cap`.
///
/// **Tier 1.** `ensures result <= cap` is checked — the fact that makes the
/// result usable as a bound on a *different*, `cap`-sized buffer, which is what
/// `crates/trust-backprop/src/validation/cargo_exec.rs:503`'s
/// `self.bytes[..chunk.len() - first]` needs and does not have.
pub fn capped_len(s: &[u8], cap: usize) -> usize ensures result <= cap {
    clamp_upper(raw_len(s), cap)
}

// ---------------------------------------------------------------------------
// Tier 2 — index and ring arithmetic.
//
// No `ensures`, because the bound is structural rather than clamped: wrapping a
// clamp around `ring_next` would produce a green postcondition row over dead
// code. What IS proved is that no body here can panic.
//
// `%` on the widened value rather than on `usize` is forced: `%` is
// composition-opaque exactly like `>>`, `<<` and `/`, so a contracted wrapper
// over any of these fails outright with "member has a guarded or
// non-entry-prefix Assert". Tier 2 is the honest home for them.
// ---------------------------------------------------------------------------

/// The last valid index of a `len`-element buffer, or `0` when it is empty.
///
/// **Tier 2.** Proved: the `len - 1` cannot underflow — the exact failure the
/// open-coded `toks.len() - 1` at `crates/trust-ts-strip/src/erase.rs:72` and
/// `crates/trust-loop/src/lib.rs:519` are one empty buffer away from.
///
/// `0` is not an in-range answer when `len == 0`; nothing is. Callers must test
/// `len` separately, which is why this is tier 2 and why [`clamp_index`] takes
/// a `last` rather than a length.
pub fn last_index(len: usize) -> usize {
    if len == 0 { return 0; }
    len - 1
}

/// The next slot after `i` in a ring whose highest index is `last`.
///
/// **Tier 2.** Proved: the `i + 1` cannot overflow. Wraps to `0` at `last` and
/// for any `i` already past it, so a stale index cannot escape the ring.
pub fn ring_next(i: usize, last: usize) -> usize {
    if i >= last { return 0; }
    i + 1
}

/// The previous slot before `i` in a ring whose highest index is `last`.
///
/// **Tier 2.** Proved: the `i - 1` cannot underflow.
pub fn ring_prev(i: usize, last: usize) -> usize {
    if i == 0 { return last; }
    if i > last { return last; }
    i - 1
}

/// The slot `k` steps after `i` in a ring of `cap` slots; `0` when `cap == 0`.
///
/// **Tier 2.** Proved: the sum cannot overflow (it is computed widened) and the
/// divisor cannot be zero.
///
/// This is `(target_pc + 1) % block_count` at
/// `crates/trust-clean/src/cfg_family/emit.rs:696`, whose nonzero fact is a
/// `debug_assert` placed *after* the division; `(self.start + self.len) %
/// capacity` at `crates/trust-backprop/src/validation/cargo_exec.rs:485`; and
/// `(primary_idx + 1) % n` at
/// `crates/trust-convergence/src/termination.rs:723`.
///
/// The final `as usize` truncates and therefore mints no obligation at all; it
/// is sound because `x % c < c <= usize::MAX`, and that step is pinned by
/// `ring_offset_never_leaves_the_ring` rather than by the verifier.
pub fn ring_offset(i: usize, k: usize, cap: usize) -> usize {
    if cap == 0 { return 0; }
    let c: u128 = cap as u128;
    let s: u128 = i as u128 + k as u128;
    (s % c) as usize
}

/// How many steps forward from `head` to `tail` in a ring of `cap` slots;
/// `0` when `cap == 0`.
///
/// **Tier 2.** Proved: neither reduction divides by zero and neither
/// subtraction underflows — `t - h` behind `t >= h`, and `cap - back` behind
/// `back > cap`.
///
/// That second guard is mathematically dead (`back = h - t <= h < cap`) and
/// structurally required: `x % c` does not tell the interval engine that the
/// result is below `cap`, so without it the subtraction is UNKNOWN. It is a
/// guard, not a clamp — it makes a totality proof go through rather than
/// standing in for one, which is why it does not put this function in tier 1.
///
/// This is the length a ring buffer reports, computed at
/// `crates/trust-backprop/src/validation/cargo_exec.rs` by three separate
/// open-coded copies of the wrap arithmetic.
pub fn ring_distance(head: usize, tail: usize, cap: usize) -> usize {
    if cap == 0 { return 0; }
    let h: usize = head % cap;
    let t: usize = tail % cap;
    if t >= h { return t - h; }
    let back: usize = h - t;
    if back > cap { return 0; }
    cap - back
}

// ---------------------------------------------------------------------------
// Tier 2 — slices.
//
// A shared-slice read and a shared-slice RANGE both prove behind ordinary
// guards, including guards that call `len()` / `is_empty()`. A MUTABLE slice
// write does not prove (measured by `trust-hex`), so nothing here takes `&mut`.
// Every signature is concrete: a generic `fn f<T>(s: &[T])` emits no
// obligations and does not appear in coverage at all.
// ---------------------------------------------------------------------------

/// `s[i]`, or `default` when `i` is out of range.
///
/// **Tier 2.** Proved: the index is in bounds on every input.
///
/// `crates/trust-js-regexp/src/unicode.rs:86` indexes `input[pos]` in a public
/// function whose entire safety contract is the sentence *"`pos` must be `<`
/// len"* in its doc comment.
pub fn at(s: &[u8], i: usize, default: u8) -> u8 {
    // `let d = default;` is load-bearing, not style. Returning the PARAMETER
    // directly from this arm leaves the bounds row AND its hardened twin
    // UNKNOWN; binding it to a local first proves both. Measured 2026-08-29
    // against four variants in one run — see the module docs.
    let d: u8 = default;
    if i >= s.len() { return d; }
    s[i]
}

/// `&s[start..end]`, with **both** ends clamped and the range un-inverted.
///
/// **Tier 2.** Proved: the range is in bounds and does not invert, on every
/// input — including `start > end`, which returns empty.
///
/// This is the operation `crates/trust-ts-strip/src/erase.rs:41` performs with
/// only the *end* defended, so that the clamp on the line above is what makes
/// the range invert. Two guards, not one.
pub fn subslice(s: &[u8], start: usize, end: usize) -> &[u8] {
    if end > s.len() {
        if start > s.len() { return &[]; }
        return &s[start..];
    }
    if start > end { return &[]; }
    &s[start..end]
}

/// The first `n` bytes of `s`, or all of `s` when it is shorter.
///
/// **Tier 2.** Proved: the range is in bounds on every input.
pub fn head(s: &[u8], n: usize) -> &[u8] {
    if n > s.len() { return s; }
    &s[..n]
}

/// `s` with its first `n` bytes dropped, or empty when it is shorter.
///
/// **Tier 2.** Proved: the range is in bounds on every input.
///
/// `crates/trust-temporal/src/fairness.rs:557` takes `&lasso_trace[cycle_start..]`
/// whose bound is established by a `?` on a call into a different module.
pub fn tail(s: &[u8], n: usize) -> &[u8] {
    if n > s.len() { return &[]; }
    &s[n..]
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A deterministic 64-bit LCG (Knuth's MMIX constants). Not cryptographic
    /// and not meant to be — it is here so the sweeps above the exhaustive
    /// range are reproducible and dependency-free.
    fn lcg(state: &mut u64) -> u64 {
        *state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        *state
    }

    /// Values that bracket every boundary this crate has: zero, one, the
    /// interior, and both neighbours of `usize::MAX`.
    const EDGES: [usize; 8] = [0, 1, 2, 3, 100, usize::MAX - 2, usize::MAX - 1, usize::MAX];

    // -- Tier 1, against `core`'s own decision procedures.

    #[test]
    fn clamp_index_agrees_with_core_min() {
        for i in 0..64usize {
            for last in 0..64usize {
                assert_eq!(clamp_index(i, last), i.min(last), "{i},{last}");
            }
        }
        for i in EDGES {
            for last in EDGES {
                assert_eq!(clamp_index(i, last), i.min(last), "{i},{last}");
            }
        }
    }

    #[test]
    fn window_start_agrees_with_core_min() {
        for start in 0..64usize {
            for len in 0..64usize {
                assert_eq!(window_start(start, len), start.min(len), "{start},{len}");
            }
        }
        for start in EDGES {
            for len in EDGES {
                assert_eq!(window_start(start, len), start.min(len), "{start},{len}");
            }
        }
    }

    /// `window_end` is `start.saturating_add(count).min(len)`. `core` supplies
    /// both halves independently.
    #[test]
    fn window_end_agrees_with_core_saturating_add_then_min() {
        for start in 0..24usize {
            for count in 0..24usize {
                for len in 0..24usize {
                    assert_eq!(
                        window_end(start, count, len),
                        start.saturating_add(count).min(len),
                        "{start},{count},{len}"
                    );
                }
            }
        }
        for start in EDGES {
            for count in EDGES {
                for len in EDGES {
                    assert_eq!(
                        window_end(start, count, len),
                        start.saturating_add(count).min(len),
                        "{start},{count},{len}"
                    );
                }
            }
        }
    }

    #[test]
    fn span_len_agrees_with_core_saturating_sub_then_min() {
        for start in 0..24usize {
            for end in 0..24usize {
                for cap in 0..24usize {
                    assert_eq!(
                        span_len(start, end, cap),
                        end.saturating_sub(start).min(cap),
                        "{start},{end},{cap}"
                    );
                }
            }
        }
        for start in EDGES {
            for end in EDGES {
                for cap in EDGES {
                    assert_eq!(
                        span_len(start, end, cap),
                        end.saturating_sub(start).min(cap),
                        "{start},{end},{cap}"
                    );
                }
            }
        }
    }

    /// A second, independent characterisation of `window_end`: a window can
    /// only ever extend FORWARD from its own start. `core` is not consulted, so
    /// a direction error the oracle test above would catch only if `core`
    /// agreed is caught twice — and the `ensures result <= len` clause stays
    /// true under exactly that error, which is why the tests are evidence and
    /// not a convenience.
    #[test]
    fn a_window_never_ends_before_it_starts() {
        for start in 0..24usize {
            for count in 0..24usize {
                for len in 0..24usize {
                    assert!(
                        window_end(start, count, len) >= window_start(start, len),
                        "{start},{count},{len}"
                    );
                }
            }
        }
        for start in EDGES {
            for count in EDGES {
                for len in EDGES {
                    assert!(
                        window_end(start, count, len) >= window_start(start, len),
                        "{start},{count},{len}"
                    );
                }
            }
        }
    }

    #[test]
    fn capped_len_agrees_with_core_min() {
        let buf = [0u8; 40];
        for n in 0..=40usize {
            for cap in 0..48usize {
                assert_eq!(capped_len(&buf[..n], cap), n.min(cap), "{n},{cap}");
            }
            assert_eq!(capped_len(&buf[..n], usize::MAX), n, "{n}");
        }
    }

    /// The tier-1 contracts, restated as runtime properties over a sweep. The
    /// compiler checks them statically; this checks that the shipped behaviour
    /// and the checked proposition are about the same function.
    #[test]
    fn no_tier1_result_ever_exceeds_its_bound() {
        let buf = [0u8; 64];
        let mut s = 0x3141_5926_5358_9793u64;
        for _ in 0..200_000 {
            let a = lcg(&mut s) as usize;
            let b = lcg(&mut s) as usize;
            let c = lcg(&mut s) as usize;
            assert!(clamp_index(a, b) <= b);
            assert!(window_start(a, b) <= b);
            assert!(window_end(a, b, c) <= c);
            assert!(span_len(a, b, c) <= c);
            assert!(capped_len(&buf[..(a % 65)], b) <= b);
        }
    }

    // -- Tier 2: indices and rings, exhaustive over small capacities.

    #[test]
    fn last_index_agrees_with_core_saturating_sub() {
        for len in 0..256usize {
            assert_eq!(last_index(len), len.saturating_sub(1), "{len}");
        }
        for len in EDGES {
            assert_eq!(last_index(len), len.saturating_sub(1), "{len}");
        }
    }

    /// `ring_next`/`ring_prev` are exact inverses on the ring, and neither can
    /// leave it. Exhaustive for every ring up to 32 slots and every index up to
    /// twice the ring size, which covers the stale-index case.
    #[test]
    fn ring_step_is_a_bijection_on_the_ring() {
        for last in 0..32usize {
            for i in 0..=last {
                assert!(ring_next(i, last) <= last, "next {i},{last}");
                assert!(ring_prev(i, last) <= last, "prev {i},{last}");
                assert_eq!(ring_prev(ring_next(i, last), last), i, "roundtrip {i},{last}");
                assert_eq!(ring_next(ring_prev(i, last), last), i, "roundtrip {i},{last}");
            }
            // A stale index past the end must be pulled back into the ring.
            for i in (last + 1)..(2 * last + 4) {
                assert!(ring_next(i, last) <= last, "stale next {i},{last}");
                assert!(ring_prev(i, last) <= last, "stale prev {i},{last}");
            }
            assert_eq!(ring_next(last, last), 0, "wrap {last}");
            assert_eq!(ring_prev(0, last), last, "wrap {last}");
        }
    }

    /// `ring_offset` against `core`'s `%` on the reduced values, exhaustively
    /// for every ring up to 16 slots and every start/step up to 40.
    #[test]
    fn ring_offset_agrees_with_core_rem() {
        for cap in 1..17usize {
            for i in 0..40usize {
                for k in 0..40usize {
                    assert_eq!(ring_offset(i, k, cap), (i + k) % cap, "{i},{k},{cap}");
                }
            }
        }
        assert_eq!(ring_offset(7, 3, 0), 0, "cap 0 is total");
    }

    /// The step the verifier cannot see: the `as usize` after the `u128`
    /// modulo truncates and mints no obligation, so the in-ring property is
    /// pinned here — including at capacities near `usize::MAX`, where a wrong
    /// cast would be visible.
    #[test]
    fn ring_offset_never_leaves_the_ring() {
        let mut s = 0x0f1e_2d3c_4b5a_6978u64;
        for _ in 0..200_000 {
            let i = lcg(&mut s) as usize;
            let k = lcg(&mut s) as usize;
            let cap = (lcg(&mut s) as usize) | 1;
            assert!(ring_offset(i, k, cap) < cap, "{i},{k},{cap}");
        }
        for cap in [1usize, 2, usize::MAX - 1, usize::MAX] {
            for i in EDGES {
                for k in EDGES {
                    assert!(ring_offset(i, k, cap) < cap, "{i},{k},{cap}");
                }
            }
        }
    }

    #[test]
    fn ring_distance_agrees_with_core_rem() {
        for cap in 1..17usize {
            for head in 0..40usize {
                for tail in 0..40usize {
                    let want = ((tail % cap) + cap - (head % cap)) % cap;
                    assert_eq!(ring_distance(head, tail, cap), want, "{head},{tail},{cap}");
                }
            }
        }
        assert_eq!(ring_distance(3, 9, 0), 0, "cap 0 is total");
    }

    /// The characterisation that catches a swapped pair of ends: walking
    /// `ring_distance` steps forward from `head` with `ring_next` must arrive
    /// at `tail`. `core` is not consulted, so a direction error that the
    /// oracle above would only catch if `core` agreed is caught twice.
    #[test]
    fn ring_distance_counts_forward_steps() {
        for cap in 1..17usize {
            let last = cap - 1;
            for head in 0..cap {
                for tail in 0..cap {
                    let d = ring_distance(head, tail, cap);
                    let mut at_ = head;
                    for _ in 0..d {
                        at_ = ring_next(at_, last);
                    }
                    assert_eq!(at_, tail, "{head}->{tail} in {cap} took {d}");
                }
            }
        }
    }

    #[test]
    fn ring_distance_never_leaves_the_ring() {
        let mut s = 0x5151_2626_9797_3838u64;
        for _ in 0..200_000 {
            let h = lcg(&mut s) as usize;
            let t = lcg(&mut s) as usize;
            let cap = (lcg(&mut s) as usize) | 1;
            assert!(ring_distance(h, t, cap) < cap, "{h},{t},{cap}");
        }
    }

    // -- Tier 2: slices, exhaustive over every start/end of a 24-byte buffer
    //    plus the out-of-range and inverted cases `core` would panic on.

    #[test]
    fn at_agrees_with_core_get() {
        let buf: [u8; 24] = core::array::from_fn(|i| (i * 7 + 1) as u8);
        for n in 0..=24usize {
            let s = &buf[..n];
            for i in 0..40usize {
                assert_eq!(at(s, i, 0xAA), s.get(i).copied().unwrap_or(0xAA), "{n},{i}");
            }
            for i in EDGES {
                assert_eq!(at(s, i, 0xAA), s.get(i).copied().unwrap_or(0xAA), "{n},{i}");
            }
        }
    }

    /// `subslice` against `core`'s `get(a..b)`, which returns `None` on exactly
    /// the two inputs that would panic — out of range, and inverted.
    #[test]
    fn subslice_agrees_with_core_get_where_core_is_defined() {
        let buf: [u8; 24] = core::array::from_fn(|i| (i * 7 + 1) as u8);
        for n in 0..=24usize {
            let s = &buf[..n];
            for a in 0..28usize {
                for b in 0..28usize {
                    let got = subslice(s, a, b);
                    match s.get(a..b) {
                        Some(want) => assert_eq!(got, want, "defined {n},{a},{b}"),
                        None => {
                            // Undefined for `core`: either inverted or past the
                            // end. Both are clamped, and the clamped range must
                            // itself be one `core` accepts.
                            let ca = a.min(n);
                            let cb = b.min(n);
                            let want: &[u8] = if ca > cb { &[] } else { &s[ca..cb] };
                            assert_eq!(got, want, "clamped {n},{a},{b}");
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn head_and_tail_agree_with_core_and_partition_the_buffer() {
        let buf: [u8; 24] = core::array::from_fn(|i| (i * 7 + 1) as u8);
        for n in 0..=24usize {
            let s = &buf[..n];
            for k in 0..28usize {
                let h = head(s, k);
                let t = tail(s, k);
                assert_eq!(h, &s[..k.min(n)], "head {n},{k}");
                assert_eq!(t, &s[k.min(n)..], "tail {n},{k}");
                // The two halves partition the buffer exactly.
                assert_eq!(h.len() + t.len(), n, "partition {n},{k}");
            }
            for k in EDGES {
                assert_eq!(head(s, k), &s[..k.min(n)], "head edge {n},{k}");
                assert_eq!(tail(s, k), &s[k.min(n)..], "tail edge {n},{k}");
            }
        }
    }

    /// Every slice function is total: no input panics. The proofs say so
    /// statically; this reaches the same inputs at runtime, including the
    /// `usize::MAX` neighbourhood the exhaustive loops cannot enumerate.
    #[test]
    fn no_slice_function_panics_on_any_input() {
        let buf: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
        let mut s = 0xdead_beef_cafe_f00du64;
        for n in 0..=8usize {
            let sl = &buf[..n];
            for a in EDGES {
                for b in EDGES {
                    let _ = at(sl, a, 0);
                    let _ = subslice(sl, a, b);
                    let _ = head(sl, a);
                    let _ = tail(sl, b);
                }
            }
            for _ in 0..20_000 {
                let a = lcg(&mut s) as usize;
                let b = lcg(&mut s) as usize;
                let _ = at(sl, a, 0);
                let _ = subslice(sl, a, b);
                let _ = head(sl, a);
                let _ = tail(sl, b);
            }
        }
    }
}
