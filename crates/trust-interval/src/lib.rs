//! Total, verified interval / range algebra for `no_std` Trust components.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0
//!
//! # Why this crate exists, and who calls it
//!
//! A range is two numbers, and almost every operation on a pair of them has a
//! side condition — `lo <= hi` — that this tree writes down instead of
//! discharging. Four spellings of that, all re-read at the line cited:
//!
//! **`first-party/trust-cg/crates/trust-cg-regalloc/src/liveness.rs:32-45`** —
//! the whole hazard in one type:
//!
//! ```text
//! pub fn new(start: u32, end: u32) -> Self {
//!     debug_assert!(start < end, "empty live range: {start}..{end}");
//!     Self { start, end }
//! }
//! pub fn contains(&self, idx: u32) -> bool {
//!     self.start <= idx && idx < self.end
//! }
//! pub fn overlaps(&self, other: &LiveRange) -> bool {
//!     self.start < other.end && other.start < self.end
//! }
//! ```
//!
//! `debug_assert!` is compiled out of the build that ships, and both predicates
//! *depend* on it: for an inverted `LiveRange`, `overlaps` returns `true` for
//! two genuinely disjoint ranges. That is not a panic — it is a register
//! allocator deciding two live values interfere when they do not, or the
//! reverse. The failure is a wrong answer in released code, which is exactly
//! the class a `debug_assert!` cannot see.
//!
//! **`crates/trust-ts-strip/src/erase.rs:39-41`** — a clamp that *manufactures*
//! the inversion it was written to prevent:
//!
//! ```text
//! for &(s, en) in blanks {
//!     let en = en.min(bytes.len());
//!     for byte in &mut bytes[s..en] {
//! ```
//!
//! The **end** is clamped and the **start** is not. Any blank span with
//! `s > bytes.len()` is turned by line 40 into `s > en`, and line 41 panics
//! with *"slice index starts at .. but ends at .."*. One-sided clamping is
//! worse than no clamping here: without it the pair was merely out of range,
//! with it the pair is inverted.
//!
//! **`crates/trust-disasm/src/aarch64/decode.rs:19-22`** — the closed-interval
//! width, twice unguarded:
//!
//! ```text
//! /// Extract bits [hi:lo] (inclusive) from a 32-bit value.
//! fn bits(val: u32, hi: u32, lo: u32) -> u32 {
//!     (val >> lo) & ((1 << (hi - lo + 1)) - 1)
//! }
//! ```
//!
//! `hi - lo` underflows when `hi < lo`, and `hi - lo + 1 == 32` shifts by the
//! full width. The doc comment says *inclusive*; nothing says `hi >= lo`.
//!
//! **`crates/trust-types/src/smt_logic.rs:746` against `:222-225`** — the same
//! expression written both ways in one file:
//!
//! ```text
//! // :222-225, guarded
//! if high < low || *high >= width { return Err(FormulaSortError::InvalidExtract { .. }); }
//! Ok(Sort::BitVec(high - low + 1))
//!
//! // :746, not
//! Formula::BvExtract { high, low, .. } => Sort::BitVec(high - low + 1),
//! ```
//!
//! The unguarded form recurs at `crates/trust-clean/src/clean_bridge.rs:974`,
//! `crates/trust-cg-bridge/src/verify_output.rs:5181` and
//! `crates/trust-machine-sem/src/aarch64/mod.rs:2879`; the guarded form at
//! `crates/trust-router/src/interval_backend.rs:683` and
//! `crates/trust-report/src/binary.rs:3737`. A convention that is applied in
//! half the call sites is not a convention.
//!
//! Two more, for the record: `crates/trust-symex/src/byte_encoding.rs:496-497`
//! decides membership with `address < self.base + self.size`, which overflows
//! for a high-based region and then hands out `address - self.base` on the
//! strength of it; and `crates/trust-decompile/src/lib.rs:6904-6916` takes
//! `min` over starts and `max` over ends *independently*, so `end < start` is
//! representable, and patches it at the end with
//! `.max(start.saturating_add(1))` — a fixup, not a discharge.
//!
//! # The convention this crate is built on
//!
//! An interval is the **closed** pair `[lo, hi]` of `u32` endpoints.
//!
//! * **`lo > hi` means EMPTY.** It is not an error, not a panic and not a
//!   precondition — it is a representable value that every function here is
//!   defined on. That is what makes the functions total, and totality is what
//!   the strict lane requires: a `requires` clause is fatal under it
//!   (`docs/STRICT_VERIFICATION_FRAGMENT.md` §3), so a precondition is not
//!   available to be written even if one were wanted.
//! * **The canonical empty is `(1, 0)`.** [`cover_lo`] / [`cover_hi`] return it
//!   when both inputs are empty, so an empty result has one spelling.
//! * **Lengths are `u64`.** `hi - lo + 1` for `u32` endpoints peaks at `2^32`,
//!   which no `u32` holds — [`span_len`] returns the exact answer rather than
//!   an `Option` nobody unwraps correctly. Widening the *result* is an API move
//!   that deletes a fallible conversion from every caller.
//!
//! # Projection is not intersection
//!
//! Two different operations get spelled the same way, and `erase.rs` is what
//! happens when they are confused:
//!
//! * **[`intersect_lo`] / [`intersect_hi`]** are the *meet*: `max` of the low
//!   ends, `min` of the high ends. The result may be empty, and it is empty
//!   exactly when the inputs do not overlap. No special case is needed for an
//!   empty input — if `a` is empty then `max(alo, blo) >= alo > ahi >=
//!   min(ahi, bhi)`, so the meet is empty too, automatically.
//! * **[`clamp_lo_into`] / [`clamp_hi_into`]** are the *projection*: move each
//!   endpoint to the nearest point of the target. The result is never empty
//!   when the target is not. Clamping **both** ends is the whole point;
//!   clamping one is `erase.rs`.
//!
//! [`clamped_len`] and [`overlap_len`] are the two lengths those give, and they
//! differ — `clamped_len` of a source entirely above the target is `1`, not
//! `0`. A test pins that difference so neither can silently become the other.
//!
//! # Tiers
//!
//! * **Tier 1 — proved bound.** A grammar `ensures` clause the compiler checks.
//!   Sixteen functions: the ten predicates (`ensures result <= 1`), the four
//!   lattice endpoints, and the two projections. Every one of these bodies is
//!   arithmetic-free, so every row is a discharged postcondition
//!   (`docs/STRICT_VERIFICATION_FRAGMENT.md` §1.1 shape A) — except
//!   [`touches`], which is §1.1 shape B over a helper that returns only `0`
//!   or `1`.
//!
//!   The four lattice contracts are the four lattice laws, which is why they
//!   are worth stating: `intersect_lo` never lowers a low end
//!   (`result >= alo`), `intersect_hi` never raises a high end
//!   (`result <= ahi`), `hull_lo` never raises a low end, `hull_hi` never
//!   lowers a high end. Each is **live** — reachable with an argument that
//!   makes the returned value differ from the bounding one.
//!
//! * **Tier 2 — proved total.** No contract, every arithmetic obligation
//!   discharged. The seven arithmetic functions are here because a contract
//!   over them would be *dead*: [`span_len`] is structurally bounded by `2^32`,
//!   so `ensures result <= 4294967296` would be a green row over a clamp that
//!   can never fire, and `docs/STRICT_VERIFICATION_FRAGMENT.md` §5 rules that
//!   out. Measured 2026-08-29, it would not have discharged anyway: a
//!   contracted wrapper over an uncontracted *arithmetic* callee reports
//!   `0 certified, 2 unknown`.
//!
//! [`midpoint`] is tier 2 for a second, independent reason: it divides, and
//! `/` is opaque to bundling (§2.4), so any contracted wrapper over it fails
//! to lower — measured here, `refused Assert-bearing member
//! `trust_interval::raw_midpoint``.
//!
//! # What is NOT claimed
//!
//! Proofs here cover panic-freedom and the stated bounds. They do **not** cover
//! whether the answer is right: [`span_len`] returning `hi - lo + 2` would keep
//! every obligation in range. That is what the unit tests are for, and they are
//! written against counting oracles (`(lo..=hi).count()`,
//! `RangeInclusive::contains`, brute-force membership over a small domain)
//! rather than against a second copy of the same formula.

#![no_std]

// ---------------------------------------------------------------------------
// Tier 1 — predicates. Ordered guard chains returning CONSTANTS, so these
// bodies carry no arithmetic and every row is a discharged postcondition
// (`docs/STRICT_VERIFICATION_FRAGMENT.md` §1.1 shape A).
// ---------------------------------------------------------------------------

/// `1` when `[lo, hi]` is empty, i.e. when `lo > hi`.
///
/// **Tier 1.** `ensures result <= 1` is checked.
pub fn is_empty(lo: u32, hi: u32) -> u8 ensures result <= 1 {
    if lo > hi {
        return 1;
    }
    0
}

/// `1` when `[lo, hi]` contains at least one point.
///
/// **Tier 1.** `ensures result <= 1` is checked.
pub fn is_nonempty(lo: u32, hi: u32) -> u8 ensures result <= 1 {
    if lo > hi {
        return 0;
    }
    1
}

/// `1` when `[lo, hi]` contains exactly one point.
///
/// **Tier 1.** `ensures result <= 1` is checked.
pub fn is_degenerate(lo: u32, hi: u32) -> u8 ensures result <= 1 {
    if lo > hi {
        return 0;
    }
    if lo == hi {
        return 1;
    }
    0
}

/// `1` when `x` lies in `[lo, hi]`. Empty intervals contain nothing.
///
/// This is `liveness.rs:38-40`'s `contains` with the inverted case decided
/// rather than assumed.
///
/// **Tier 1.** `ensures result <= 1` is checked.
pub fn contains_point(lo: u32, hi: u32, x: u32) -> u8 ensures result <= 1 {
    if lo > hi {
        return 0;
    }
    if x < lo {
        return 0;
    }
    if x > hi {
        return 0;
    }
    1
}

/// `1` when `[blo, bhi]` is a subset of `[alo, ahi]`.
///
/// The empty interval is a subset of everything, including of itself, so an
/// empty `b` returns `1` before `a` is looked at.
///
/// **Tier 1.** `ensures result <= 1` is checked.
pub fn contains_range(alo: u32, ahi: u32, blo: u32, bhi: u32) -> u8 ensures result <= 1 {
    if blo > bhi {
        return 1;
    }
    if alo > ahi {
        return 0;
    }
    if blo < alo {
        return 0;
    }
    if bhi > ahi {
        return 0;
    }
    1
}

/// `1` when `[alo, ahi]` and `[blo, bhi]` share at least one point.
///
/// This is `liveness.rs:43-45`'s `overlaps` with the inverted case decided.
/// That function returns `true` for two disjoint ranges when either is
/// inverted; this one returns `0`, because an empty interval shares no point
/// with anything.
///
/// **Tier 1.** `ensures result <= 1` is checked.
pub fn overlaps(alo: u32, ahi: u32, blo: u32, bhi: u32) -> u8 ensures result <= 1 {
    if alo > ahi {
        return 0;
    }
    if blo > bhi {
        return 0;
    }
    if ahi < blo {
        return 0;
    }
    if bhi < alo {
        return 0;
    }
    1
}

/// `1` when `[alo, ahi]` and `[blo, bhi]` share no point. The exact negation of
/// [`overlaps`], spelled out rather than computed, so that both are shape (A).
///
/// **Tier 1.** `ensures result <= 1` is checked.
pub fn is_disjoint(alo: u32, ahi: u32, blo: u32, bhi: u32) -> u8 ensures result <= 1 {
    if alo > ahi {
        return 1;
    }
    if blo > bhi {
        return 1;
    }
    if ahi < blo {
        return 1;
    }
    if bhi < alo {
        return 1;
    }
    0
}

/// `1` when every point of `[alo, ahi]` is strictly below every point of
/// `[blo, bhi]`, and both are non-empty.
///
/// **Tier 1.** `ensures result <= 1` is checked.
pub fn is_before(alo: u32, ahi: u32, blo: u32, bhi: u32) -> u8 ensures result <= 1 {
    if alo > ahi {
        return 0;
    }
    if blo > bhi {
        return 0;
    }
    if ahi < blo {
        return 1;
    }
    0
}

/// `1` when the two intervals denote the same set of points. All empty
/// intervals are equal to each other whatever their endpoints.
///
/// **Tier 1.** `ensures result <= 1` is checked.
pub fn is_equal(alo: u32, ahi: u32, blo: u32, bhi: u32) -> u8 ensures result <= 1 {
    if alo > ahi {
        if blo > bhi {
            return 1;
        }
        return 0;
    }
    if blo > bhi {
        return 0;
    }
    if alo != blo {
        return 0;
    }
    if ahi != bhi {
        return 0;
    }
    1
}

/// `1` when `ahi` and `blo` are adjacent — `blo == ahi + 1` — so that
/// `[.., ahi]` and `[blo, ..]` abut with no point between them.
///
/// The `+ 1` is computed at `u64`, which is why this needs a helper: the
/// widening supplies the range that makes the add provable, and a contracted
/// body may not contain arithmetic. The helper returns only `0` or `1`, which
/// is what lets the wrapper discharge over it
/// (`docs/STRICT_VERIFICATION_FRAGMENT.md` §9.3).
fn raw_touches(ahi: u32, blo: u32) -> u8 {
    let a: u64 = ahi as u64;
    let b: u64 = blo as u64;
    if b <= a {
        return 0;
    }
    if b == a + 1 {
        return 1;
    }
    0
}

/// `1` when `blo == ahi + 1`. Never `1` at `ahi == u32::MAX`, where no
/// successor exists.
///
/// **Tier 1.** `ensures result <= 1` is checked.
pub fn touches(ahi: u32, blo: u32) -> u8 ensures result <= 1 {
    raw_touches(ahi, blo)
}

// ---------------------------------------------------------------------------
// Tier 1 — the endpoint lattice. Each contract is the corresponding lattice
// law, and each is LIVE: reachable with an argument that makes the returned
// value differ from the bounding one.
// ---------------------------------------------------------------------------

/// The low end of the intersection: `max(alo, blo)`.
///
/// Correct for empty inputs with no special case — if `a` is empty then
/// `max(alo, blo) >= alo > ahi >= min(ahi, bhi)`, so the meet is empty too.
///
/// **Tier 1.** `ensures result >= alo` — the meet never lowers a low end.
pub fn intersect_lo(alo: u32, blo: u32) -> u32 ensures result >= alo {
    if alo > blo {
        return alo;
    }
    blo
}

/// The high end of the intersection: `min(ahi, bhi)`.
///
/// **Tier 1.** `ensures result <= ahi` — the meet never raises a high end.
pub fn intersect_hi(ahi: u32, bhi: u32) -> u32 ensures result <= ahi {
    if ahi < bhi {
        return ahi;
    }
    bhi
}

/// The low end of the hull: `min(alo, blo)`.
///
/// This is the pure lattice join on endpoints and takes no view of emptiness;
/// [`cover_lo`] is the empty-aware form.
///
/// **Tier 1.** `ensures result <= alo` — the join never raises a low end.
pub fn hull_lo(alo: u32, blo: u32) -> u32 ensures result <= alo {
    if alo < blo {
        return alo;
    }
    blo
}

/// The high end of the hull: `max(ahi, bhi)`.
///
/// **Tier 1.** `ensures result >= ahi` — the join never lowers a high end.
pub fn hull_hi(ahi: u32, bhi: u32) -> u32 ensures result >= ahi {
    if ahi > bhi {
        return ahi;
    }
    bhi
}

// ---------------------------------------------------------------------------
// Tier 1 — projection into a target range. Both ends, always. This is the
// `erase.rs:40` repair: clamping one end is what creates the inversion.
// ---------------------------------------------------------------------------

/// Project a low endpoint into `[blo, bhi]`.
///
/// When the target is itself empty (`bhi < blo`) this returns `blo` and
/// [`clamp_hi_into`] returns `bhi`, so the projected pair is the target's own
/// crossed pair — still empty, never inverted into a different empty.
///
/// **Tier 1.** `ensures result >= blo` is checked.
pub fn clamp_lo_into(v: u32, blo: u32, bhi: u32) -> u32 ensures result >= blo {
    if bhi < blo {
        return blo;
    }
    if v < blo {
        return blo;
    }
    if v > bhi {
        return bhi;
    }
    v
}

/// Project a high endpoint into `[blo, bhi]`.
///
/// **Tier 1.** `ensures result <= bhi` is checked.
pub fn clamp_hi_into(v: u32, blo: u32, bhi: u32) -> u32 ensures result <= bhi {
    if bhi < blo {
        return bhi;
    }
    if v > bhi {
        return bhi;
    }
    if v < blo {
        return blo;
    }
    v
}

// ---------------------------------------------------------------------------
// Tier 2 — arithmetic. No contract; every overflow, underflow and
// zero-divisor obligation discharged. A contract over any of these would be
// dead (§5), and would not discharge in any case (see the module docs).
// ---------------------------------------------------------------------------

/// The number of points in the closed interval `[lo, hi]`, and `0` when it is
/// empty.
///
/// The return type is `u64` because the answer is not a `u32`:
/// `span_len(0, u32::MAX) == 4294967296`. This is `decode.rs:22`'s
/// `hi - lo + 1` with both the underflow and the width decided.
pub fn span_len(lo: u32, hi: u32) -> u64 {
    if lo > hi {
        return 0;
    }
    let d: u32 = hi - lo;
    (d as u64) + 1
}

/// The number of points in the half-open range `start..end`, and `0` when it is
/// empty. Fits `u32` — a half-open `u32` range has at most `u32::MAX` points.
pub fn half_open_len(start: u32, end: u32) -> u32 {
    if end <= start {
        return 0;
    }
    end - start
}

/// The number of points strictly between `ahi` and `blo` — the size of the gap
/// separating `[.., ahi]` from `[blo, ..]`. `0` when they overlap or abut.
///
/// The `if d == 0` test is mathematically dead: `blo > ahi` already gives
/// `d >= 1`. It is structurally required, because the interval engine does not
/// carry `blo > ahi` into a bound on `d - 1`
/// (`docs/STRICT_VERIFICATION_FRAGMENT.md` §2.5). A dead guard is fine; a dead
/// clamp under a tier-1 `ensures` would not be.
pub fn gap(ahi: u32, blo: u32) -> u32 {
    if blo <= ahi {
        return 0;
    }
    let d: u32 = blo - ahi;
    if d == 0 {
        return 0;
    }
    d - 1
}

/// The lower midpoint of `[lo, hi]`, and `0` when it is empty.
///
/// `(lo + hi) / 2` overflows at `u32`; `lo + (hi - lo) / 2` does not, but its
/// final add has no bound the interval engine can see (measured: `3 proved,
/// 2 unknown`). Widening both endpoints costs nothing and proves: the sum
/// peaks at `2^33 - 2` and the halved value is back inside `u32`, so the
/// narrowing cast cannot truncate.
pub fn midpoint(lo: u32, hi: u32) -> u32 {
    if lo > hi {
        return 0;
    }
    let s: u64 = (lo as u64) + (hi as u64);
    let m: u64 = s / 2;
    m as u32
}

/// The half-open `end` for a closed `hi`. `end_from_hi(u32::MAX)` is
/// `4294967296`, which is why the return type is `u64`.
pub fn end_from_hi(hi: u32) -> u64 {
    (hi as u64) + 1
}

/// The closed `hi` for a half-open `end`, and `0` for the empty `end == 0`
/// (where no closed high endpoint exists).
pub fn hi_from_end(end: u32) -> u32 {
    if end == 0 {
        return 0;
    }
    end - 1
}

// ---------------------------------------------------------------------------
// Tier 2 — composed. No arithmetic of their own; the obligations live in the
// leaf they call. Selecting endpoints in the CALLER and doing the arithmetic in
// the CALLEE is load-bearing: a subtraction whose operands are select-derived
// locals does not prove, however it is guarded
// (`docs/STRICT_VERIFICATION_FRAGMENT.md` §11.1).
// ---------------------------------------------------------------------------

/// The number of points the two intervals share.
pub fn overlap_len(alo: u32, ahi: u32, blo: u32, bhi: u32) -> u64 {
    let lo: u32 = if alo > blo { alo } else { blo };
    let hi: u32 = if ahi < bhi { ahi } else { bhi };
    span_len(lo, hi)
}

/// The low end of the smallest interval covering both — empty-aware, unlike
/// [`hull_lo`]. Returns the canonical empty's low end (`1`) when both inputs
/// are empty.
///
/// `decompile/src/lib.rs:6904-6916` is the shape this exists to replace: `min`
/// over starts and `max` over ends taken independently, so the pair can invert.
pub fn cover_lo(alo: u32, ahi: u32, blo: u32, bhi: u32) -> u32 {
    if alo > ahi {
        if blo > bhi {
            return 1;
        }
        return blo;
    }
    if blo > bhi {
        return alo;
    }
    if alo < blo {
        return alo;
    }
    blo
}

/// The high end of the smallest interval covering both. Returns the canonical
/// empty's high end (`0`) when both inputs are empty.
pub fn cover_hi(alo: u32, ahi: u32, blo: u32, bhi: u32) -> u32 {
    if alo > ahi {
        if blo > bhi {
            return 0;
        }
        return bhi;
    }
    if blo > bhi {
        return ahi;
    }
    if ahi > bhi {
        return ahi;
    }
    bhi
}

/// The number of points in the cover of both intervals.
pub fn cover_len(alo: u32, ahi: u32, blo: u32, bhi: u32) -> u64 {
    if alo > ahi {
        return span_len(blo, bhi);
    }
    if blo > bhi {
        return span_len(alo, ahi);
    }
    let lo: u32 = if alo < blo { alo } else { blo };
    let hi: u32 = if ahi > bhi { ahi } else { bhi };
    span_len(lo, hi)
}

/// The number of points separating two non-empty intervals, in whichever order
/// they fall. `0` when they overlap, abut, or either is empty.
pub fn distance(alo: u32, ahi: u32, blo: u32, bhi: u32) -> u32 {
    if alo > ahi {
        return 0;
    }
    if blo > bhi {
        return 0;
    }
    if blo > ahi {
        return gap(ahi, blo);
    }
    if alo > bhi {
        return gap(bhi, alo);
    }
    0
}

/// The number of points in `[alo, ahi]` after projecting both endpoints into
/// `[blo, bhi]`.
///
/// This is **not** [`overlap_len`]. Projection moves each endpoint to the
/// nearest point of the target, so a source entirely above the target collapses
/// to the single point `bhi` and this returns `1`, where the intersection is
/// empty and `overlap_len` returns `0`.
pub fn clamped_len(alo: u32, ahi: u32, blo: u32, bhi: u32) -> u64 {
    let lo: u32 = clamp_lo_into(alo, blo, bhi);
    let hi: u32 = clamp_hi_into(ahi, blo, bhi);
    span_len(lo, hi)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The domain every brute-force sweep runs over. Small enough that the
    /// membership oracle below is a `u16` bitmask, large enough to contain
    /// every ordering of two intervals.
    const N: u32 = 12;

    /// Independent oracle: the set of points of `[lo, hi]`, as a bitmask over
    /// `0..=N`. Built by *testing each point*, with no endpoint arithmetic at
    /// all, so it shares no code path with anything under test.
    fn mask(lo: u32, hi: u32) -> u16 {
        let mut m: u16 = 0;
        let mut x: u32 = 0;
        while x <= N {
            if lo <= x && x <= hi {
                m |= 1u16 << x;
            }
            x += 1;
        }
        m
    }

    /// Every ordered pair of intervals over `0..=N`, including inverted ones.
    fn pairs(mut f: impl FnMut(u32, u32, u32, u32)) {
        for alo in 0..=N {
            for ahi in 0..=N {
                for blo in 0..=N {
                    for bhi in 0..=N {
                        f(alo, ahi, blo, bhi);
                    }
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // Against `core`'s own decision procedures.
    // -----------------------------------------------------------------------

    #[test]
    fn contains_point_agrees_with_range_inclusive_contains() {
        for lo in 0..=N {
            for hi in 0..=N {
                for x in 0..=N {
                    let want = u8::from((lo..=hi).contains(&x));
                    assert_eq!(contains_point(lo, hi, x), want, "[{lo},{hi}] x={x}");
                }
            }
        }
        // `RangeInclusive::contains` is false on an inverted range too.
        assert_eq!(contains_point(5, 3, 4), 0);
        assert_eq!(contains_point(0, u32::MAX, u32::MAX), 1);
    }

    #[test]
    fn the_lattice_agrees_with_core_cmp_min_and_max() {
        for a in 0..=N {
            for b in 0..=N {
                assert_eq!(intersect_lo(a, b), core::cmp::max(a, b), "meet lo {a} {b}");
                assert_eq!(intersect_hi(a, b), core::cmp::min(a, b), "meet hi {a} {b}");
                assert_eq!(hull_lo(a, b), core::cmp::min(a, b), "join lo {a} {b}");
                assert_eq!(hull_hi(a, b), core::cmp::max(a, b), "join hi {a} {b}");
            }
        }
        assert_eq!(intersect_lo(0, u32::MAX), u32::MAX);
        assert_eq!(hull_lo(0, u32::MAX), 0);
    }

    #[test]
    fn span_len_counts_the_inclusive_range() {
        for lo in 0..=N {
            for hi in 0..=N {
                let want = (lo..=hi).count() as u64;
                assert_eq!(span_len(lo, hi), want, "[{lo},{hi}]");
            }
        }
        // The three values no `u32` return type could carry.
        assert_eq!(span_len(0, u32::MAX), 4294967296);
        assert_eq!(span_len(1, u32::MAX), 4294967295);
        assert_eq!(span_len(u32::MAX, u32::MAX), 1);
    }

    #[test]
    fn half_open_len_counts_the_half_open_range() {
        for start in 0..=N {
            for end in 0..=N {
                let want = (start..end).count() as u32;
                assert_eq!(half_open_len(start, end), want, "{start}..{end}");
            }
        }
        assert_eq!(half_open_len(0, u32::MAX), u32::MAX);
        assert_eq!(half_open_len(u32::MAX, 0), 0);
    }

    #[test]
    fn gap_counts_the_points_strictly_between() {
        for ahi in 0..=N {
            for blo in 0..=N {
                let want = if blo > ahi { (ahi + 1..blo).count() as u32 } else { 0 };
                assert_eq!(gap(ahi, blo), want, "gap({ahi},{blo})");
            }
        }
        assert_eq!(gap(0, u32::MAX), u32::MAX - 1);
        assert_eq!(gap(u32::MAX, 0), 0);
    }

    // -----------------------------------------------------------------------
    // Against brute-force set membership — a different method entirely.
    // -----------------------------------------------------------------------

    #[test]
    fn the_predicates_agree_with_brute_force_membership() {
        pairs(|alo, ahi, blo, bhi| {
            let a = mask(alo, ahi);
            let b = mask(blo, bhi);
            assert_eq!(is_empty(alo, ahi), u8::from(a == 0), "is_empty [{alo},{ahi}]");
            assert_eq!(is_nonempty(alo, ahi), u8::from(a != 0), "is_nonempty [{alo},{ahi}]");
            assert_eq!(
                is_degenerate(alo, ahi),
                u8::from(a.count_ones() == 1),
                "is_degenerate [{alo},{ahi}]"
            );
            assert_eq!(
                overlaps(alo, ahi, blo, bhi),
                u8::from(a & b != 0),
                "overlaps [{alo},{ahi}] [{blo},{bhi}]"
            );
            assert_eq!(
                is_disjoint(alo, ahi, blo, bhi),
                u8::from(a & b == 0),
                "is_disjoint [{alo},{ahi}] [{blo},{bhi}]"
            );
            assert_eq!(
                contains_range(alo, ahi, blo, bhi),
                u8::from(b & !a == 0),
                "contains_range [{alo},{ahi}] [{blo},{bhi}]"
            );
            assert_eq!(
                is_equal(alo, ahi, blo, bhi),
                u8::from(a == b),
                "is_equal [{alo},{ahi}] [{blo},{bhi}]"
            );
            assert_eq!(
                overlap_len(alo, ahi, blo, bhi),
                u64::from((a & b).count_ones()),
                "overlap_len [{alo},{ahi}] [{blo},{bhi}]"
            );
        });
    }

    #[test]
    fn is_before_and_touches_agree_with_brute_force_membership() {
        pairs(|alo, ahi, blo, bhi| {
            let a = mask(alo, ahi);
            let b = mask(blo, bhi);
            // Every point of `a` strictly below every point of `b`, both non-empty.
            let want = a != 0 && b != 0 && (15 - a.leading_zeros()) < b.trailing_zeros();
            assert_eq!(
                is_before(alo, ahi, blo, bhi),
                u8::from(want),
                "is_before [{alo},{ahi}] [{blo},{bhi}]"
            );
        });
        for ahi in 0..=N {
            for blo in 0..=N {
                assert_eq!(touches(ahi, blo), u8::from(blo == ahi + 1), "touches({ahi},{blo})");
            }
        }
        assert_eq!(touches(u32::MAX, 0), 0, "u32::MAX has no successor");
        assert_eq!(touches(u32::MAX - 1, u32::MAX), 1);
    }

    #[test]
    fn the_cover_is_the_smallest_interval_containing_both() {
        pairs(|alo, ahi, blo, bhi| {
            let a = mask(alo, ahi);
            let b = mask(blo, bhi);
            let lo = cover_lo(alo, ahi, blo, bhi);
            let hi = cover_hi(alo, ahi, blo, bhi);
            let c = mask(lo, hi);
            assert_eq!(c & (a | b), a | b, "cover must contain both: [{lo},{hi}]");
            if a == 0 && b == 0 {
                assert_eq!((lo, hi), (1, 0), "both empty -> the canonical empty");
            } else {
                // Smallest: every point of the cover is between two covered points.
                let want_lo = (a | b).trailing_zeros();
                let want_hi = 15 - (a | b).leading_zeros();
                assert_eq!(lo, want_lo, "cover_lo [{alo},{ahi}] [{blo},{bhi}]");
                assert_eq!(hi, want_hi, "cover_hi [{alo},{ahi}] [{blo},{bhi}]");
            }
            assert_eq!(cover_len(alo, ahi, blo, bhi), span_len(lo, hi), "cover_len");
        });
    }

    #[test]
    fn distance_counts_the_points_separating_two_intervals() {
        pairs(|alo, ahi, blo, bhi| {
            let a = mask(alo, ahi);
            let b = mask(blo, bhi);
            let want = if a == 0 || b == 0 || a & b != 0 {
                0
            } else {
                // Points in the cover that are in neither interval.
                let cover = mask(cover_lo(alo, ahi, blo, bhi), cover_hi(alo, ahi, blo, bhi));
                (cover & !(a | b)).count_ones()
            };
            assert_eq!(
                distance(alo, ahi, blo, bhi),
                want,
                "distance [{alo},{ahi}] [{blo},{bhi}]"
            );
        });
        assert_eq!(distance(0, 0, u32::MAX, u32::MAX), u32::MAX - 1);
    }

    // -----------------------------------------------------------------------
    // The tier-1 bounds, and that each clamp is LIVE.
    // -----------------------------------------------------------------------

    #[test]
    fn every_tier1_bound_holds_and_every_clamp_can_fire() {
        let mut meet_lo_fired = false;
        let mut meet_hi_fired = false;
        let mut join_lo_fired = false;
        let mut join_hi_fired = false;
        let mut proj_lo_fired = false;
        let mut proj_hi_fired = false;
        pairs(|alo, ahi, blo, bhi| {
            assert!(intersect_lo(alo, blo) >= alo, "meet lo bound");
            assert!(intersect_hi(ahi, bhi) <= ahi, "meet hi bound");
            assert!(hull_lo(alo, blo) <= alo, "join lo bound");
            assert!(hull_hi(ahi, bhi) >= ahi, "join hi bound");
            assert!(clamp_lo_into(alo, blo, bhi) >= blo, "proj lo bound");
            assert!(clamp_hi_into(ahi, blo, bhi) <= bhi, "proj hi bound");
            meet_lo_fired |= intersect_lo(alo, blo) != alo;
            meet_hi_fired |= intersect_hi(ahi, bhi) != ahi;
            join_lo_fired |= hull_lo(alo, blo) != alo;
            join_hi_fired |= hull_hi(ahi, bhi) != ahi;
            proj_lo_fired |= clamp_lo_into(alo, blo, bhi) != alo;
            proj_hi_fired |= clamp_hi_into(ahi, blo, bhi) != ahi;
            for x in 0..=N {
                assert!(contains_point(alo, ahi, x) <= 1);
            }
            assert!(overlaps(alo, ahi, blo, bhi) <= 1);
            assert!(is_equal(alo, ahi, blo, bhi) <= 1);
        });
        assert!(meet_lo_fired && meet_hi_fired, "a lattice bound was never reached");
        assert!(join_lo_fired && join_hi_fired, "a lattice bound was never reached");
        assert!(proj_lo_fired && proj_hi_fired, "a projection clamp never fired");
    }

    // -----------------------------------------------------------------------
    // The two hazards this crate exists for.
    // -----------------------------------------------------------------------

    #[test]
    fn projecting_one_end_inverts_the_pair_and_projecting_both_does_not() {
        // `erase.rs:40`: `en.min(bytes.len())` with `s` untouched. Source
        // [9, 11] against a target of [0, 4] — the buffer shrank.
        let (s, e) = (9u32, 11u32);
        let (tlo, thi) = (0u32, 4u32);
        let one_sided_hi = clamp_hi_into(e, tlo, thi);
        assert_eq!(one_sided_hi, 4);
        assert!(s > one_sided_hi, "clamping only the end MANUFACTURES the inversion");
        assert_eq!(is_empty(s, one_sided_hi), 1, "and `bytes[s..en]` would panic");

        let both_lo = clamp_lo_into(s, tlo, thi);
        let both_hi = clamp_hi_into(e, tlo, thi);
        assert!(both_lo <= both_hi, "projecting both ends cannot invert");
        assert_eq!((both_lo, both_hi), (4, 4));
    }

    #[test]
    fn projection_moves_each_endpoint_to_the_nearest_point_of_the_target() {
        // Oracle: scan the target for the nearest point. No endpoint
        // arithmetic, and both projections must agree with it — projecting is
        // one function applied to two ends, which is the whole repair.
        for v in 0..=N {
            for blo in 0..=N {
                for bhi in 0..=N {
                    let lo = clamp_lo_into(v, blo, bhi);
                    let hi = clamp_hi_into(v, blo, bhi);
                    if bhi < blo {
                        assert_eq!((lo, hi), (blo, bhi), "an empty target keeps its crossed pair");
                        continue;
                    }
                    let mut best = blo;
                    let mut best_d = if v > blo { v - blo } else { blo - v };
                    for c in blo..=bhi {
                        let d = if v > c { v - c } else { c - v };
                        if d < best_d {
                            best_d = d;
                            best = c;
                        }
                    }
                    assert_eq!(lo, best, "clamp_lo_into({v},{blo},{bhi})");
                    assert_eq!(hi, best, "clamp_hi_into({v},{blo},{bhi})");
                }
            }
        }
        assert_eq!(clamp_lo_into(0, 7, u32::MAX), 7);
        assert_eq!(clamp_hi_into(u32::MAX, 0, 7), 7);
    }

    #[test]
    fn projection_and_intersection_differ_and_neither_is_the_other() {
        // Source entirely above the target.
        let (alo, ahi, blo, bhi) = (9u32, 11u32, 0u32, 4u32);
        assert_eq!(overlap_len(alo, ahi, blo, bhi), 0, "the meet is empty");
        assert_eq!(clamped_len(alo, ahi, blo, bhi), 1, "the projection collapses to a point");
        assert_eq!(overlaps(alo, ahi, blo, bhi), 0);
        // Overlapping: the two agree.
        let (alo, ahi, blo, bhi) = (2u32, 8u32, 5u32, 11u32);
        assert_eq!(overlap_len(alo, ahi, blo, bhi), 4);
        assert_eq!(clamped_len(alo, ahi, blo, bhi), 4);
        // Empty target: both are empty, and the projected pair is the target's.
        assert_eq!(clamped_len(2, 8, 7, 3), 0);
    }

    #[test]
    fn an_inverted_range_does_not_overlap_anything_unlike_liveness_rs() {
        // `liveness.rs:44` is `self.start < other.end && other.start < self.end`.
        // For the inverted range [8, 2] and the disjoint [4, 5], that reads
        // 8 < 6 (false)... but for [8, 2] against [0, 9] it reads true both
        // ways, and for the inverted [8,2] against the inverted [9,3] it says
        // they interfere. This crate answers 0 in every such case.
        assert_eq!(overlaps(8, 2, 0, 9), 0, "an empty range shares no point");
        assert_eq!(overlaps(8, 2, 9, 3), 0, "two empty ranges share no point");
        assert_eq!(is_disjoint(8, 2, 0, 9), 1);
        assert_eq!(contains_point(8, 2, 5), 0, "and contains nothing");
        assert_eq!(span_len(8, 2), 0);
    }

    // -----------------------------------------------------------------------
    // Arithmetic that no obligation can see.
    // -----------------------------------------------------------------------

    #[test]
    fn midpoint_bisects_without_overflowing() {
        for lo in 0..=N {
            for hi in 0..=N {
                let m = midpoint(lo, hi);
                if lo > hi {
                    assert_eq!(m, 0, "empty [{lo},{hi}]");
                    continue;
                }
                assert!(lo <= m && m <= hi, "midpoint [{lo},{hi}] = {m} escaped");
                let below = (lo..=m).count();
                let above = (m..=hi).count();
                assert!(below <= above, "[{lo},{hi}] m={m}: {below} below, {above} above");
                assert!(above - below <= 1, "[{lo},{hi}] m={m} is not the LOWER midpoint");
            }
        }
        // `(lo + hi) / 2` at u32 would wrap here; the widened form does not.
        assert_eq!(midpoint(u32::MAX - 1, u32::MAX), u32::MAX - 1);
        assert_eq!(midpoint(0, u32::MAX), 2147483647);
        assert_eq!(midpoint(u32::MAX, u32::MAX), u32::MAX);
    }

    #[test]
    fn the_half_open_and_closed_forms_round_trip() {
        for hi in 0..=N {
            assert_eq!(hi_from_end(end_from_hi(hi) as u32), hi, "hi={hi}");
        }
        for end in 1..=N {
            assert_eq!(end_from_hi(hi_from_end(end)), u64::from(end), "end={end}");
        }
        for lo in 0..=N {
            for hi in 0..=N {
                let want = span_len(lo, hi);
                let got = if lo > hi { 0 } else { u64::from(half_open_len(lo, hi)) + 1 };
                assert_eq!(got, want, "[{lo},{hi}]");
            }
        }
        assert_eq!(end_from_hi(u32::MAX), 4294967296, "no u32 holds this");
        assert_eq!(hi_from_end(0), 0, "an empty half-open range has no closed hi");
    }

    /// A CONSISTENCY test — it computes its expectation by calling the same
    /// functions it checks, so it moves with them. It is kept, and named as
    /// such, because `scripts/trust_interval_strict_gate.sh` mutation G asserts
    /// that it CANNOT catch a wrong `span_len`. A test that derives its oracle
    /// from the code under test is not a test.
    #[test]
    fn overlap_len_agrees_with_span_len_of_the_meet_consistency_only() {
        pairs(|alo, ahi, blo, bhi| {
            let lo = intersect_lo(alo, blo);
            let hi = intersect_hi(ahi, bhi);
            assert_eq!(overlap_len(alo, ahi, blo, bhi), span_len(lo, hi));
        });
    }
}
