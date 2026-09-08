//! Fixed-width bit FIELDS inside a machine word, as descriptors — the first
//! Trust component built on top of another verified Trust crate.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0
//!
//! # Why this crate exists
//!
//! [`trust_bits`] owns the *word*: a power of two, a low mask, a population
//! count. This crate owns the *descriptor* — the pair `(lo, width)` that names
//! a field, the mask that field occupies, and the question of whether a value,
//! a field or a pair of fields actually fits. That layer is where the bugs are,
//! because it is where a caller writes the two numbers by hand:
//!
//! **`crates/trust-disasm/src/aarch64/decode.rs:20-22`** is the canonical site
//! and `trust-bits` already cites it for the shift half. The other half is the
//! descriptor:
//!
//! ```text
//! fn bits(val: u32, hi: u32, lo: u32) -> u32 {
//!     (val >> lo) & ((1 << (hi - lo + 1)) - 1)
//! }
//! ```
//!
//! Nothing here decides whether `[hi:lo]` lies inside the word at all. A field
//! that runs off the top is silently TRUNCATED — `bits(x, 35, 30)` returns six
//! bits of which two do not exist — and the caller cannot tell that from a
//! correct answer. [`field_fits`] decides it, [`extract`] refuses it, and
//! [`field_mask`] returns `0` for it rather than a mask of the wrong width.
//!
//! **`crates/trust-js-sem/src/typedarray.rs`** and every `#[repr(C)]` bitfield
//! reader in this tree carry the second descriptor bug: two fields written to
//! one word whose ranges silently OVERLAP, so the second write eats the first.
//! [`fields_overlap`] decides that, and it is decided from the masks rather
//! than from an interval comparison, so a field that does not fit cannot
//! spuriously overlap one that does.
//!
//! # The dependency is the point
//!
//! `trust-bitfield` calls [`trust_bits`] for **every** power of two, **every**
//! low mask, and both directions of the mask/descriptor conversion:
//! [`trust_bits::weight`], [`trust_bits::mask_below`],
//! [`trust_bits::leading_zeros_u32`], [`trust_bits::trailing_zeros_u32`] and
//! [`trust_bits::highest_set_index`]. There is no constant table in this file
//! and — inheriting `trust-bits`'s rule for the same reason — **not one shift**.
//! Delete the dependency and the crate does not compile; there is nothing to
//! copy back in, because the arithmetic that would replace those calls is
//! exactly the arithmetic `trust-bits` exists to have proved once.
//!
//! What crosses the crate boundary is MIR, never a verdict. Every obligation
//! below is minted and discharged by this crate's own compilation, over
//! `trust-bits`'s re-derived bodies, under this crate's own policy — see §15 of
//! `docs/STRICT_VERIFICATION_FRAGMENT.md`, whose entries were measured while
//! writing this file.
//!
//! # Two things `trust-bits` exports that this crate CANNOT call
//!
//! [`trust_bits::field`] and [`trust_bits::deposit`] are the closest functions
//! in the tree to [`extract`] and [`insert`], and calling either one is a hard
//! refusal:
//!
//! ```text
//! error: Trust full verification failed for `trust_bitfield::…`: native
//! typed-TrustIr lowering did not complete …
//!   = note: native TrustIr bundle for `…` refused Assert-bearing member
//!           `trust_bits::deposit`: member has a guarded or non-entry-prefix Assert
//! ```
//!
//! A `/`- or `*`-after-a-call body is TERMINAL — `trust-bits`'s own module docs
//! say so for its in-crate callers, and §15.3 measures that the same rule
//! crosses the crate boundary unchanged. So [`extract`] re-derives the division
//! here rather than delegating. That is not duplication for its own sake: this
//! crate's [`extract`] **refuses** a field that does not fit, where
//! `trust_bits::field` returns everything above `lo`. The two answers differ on
//! exactly the inputs the descriptor layer exists to catch.
//!
//! # Tiers
//!
//! * **Tier 1 — proved bound.** A grammar `ensures` the compiler checks. Four
//!   of them are **two-sided**: [`fit_width`], [`clamp_to_mask`], [`hull_lo`]
//!   and [`hull_end`] each carry two same-direction clauses, which pin a `min`
//!   or a `max` exactly (§14.1). Four are predicates at `ensures result <= 1`,
//!   and one ([`next_lo`]) is a one-sided clamp. Every clause's doc comment
//!   names the wrong implementation it still admits, because five crates in
//!   this tree have now shipped a clause that a constant function satisfies.
//!
//! * **Tier 2 — proved total.** No contract, every arithmetic obligation
//!   discharged: the mask constructors, [`extract`], [`place`], [`insert`] and
//!   the mask→descriptor direction. Their bounds are structural (a word), so a
//!   contract over them would be a green row over a clamp that can never fire
//!   (§5).
//!
//! # What is NOT claimed
//!
//! Proofs here cover panic-freedom and the stated bounds. They do **not** cover
//! whether the answer is right. `scripts/trust_bitfield_strict_gate.sh`
//! mutation F swaps which `trust-bits` lookup in [`place`] gets which argument:
//! both peaks are unchanged, so every obligation stays in range, the strict lane
//! stays at **exit 0** with a byte-identical kind split, and three named unit
//! tests go red. Mutation G does the same to a **discharged contract** —
//! [`fit_width`] returning `0` on its clamping arm keeps both `ensures` clauses
//! TRUE, all 23 postcondition rows still prove, and `fit_width(9, 3)` returns 0
//! instead of 3.
//!
//! Mutations C, D and E pin the three CROSS-CRATE boundaries §15 records, so
//! that a compiler change makes this crate's docs go red rather than stale; and
//! mutation H deletes the `trust-bits` dependency and asserts the crate stops
//! compiling in 15 places, which is the only thing that separates a
//! load-bearing edge from a decorative one.
//!
//! The unit tests are written against `u32::count_ones`, `trailing_zeros`,
//! `leading_zeros`, `checked_shl`, and brute-force loops over bit positions —
//! decision procedures written by someone else, by a different method — and are
//! exhaustive over every `(lo, width)` descriptor in the word (33 × 33 = 1089
//! pairs) wherever the domain allows.

#![no_std]

// ---------------------------------------------------------------------------
// Section 1 — the geometry of a descriptor.
//
// `room_at` is the whole section's foundation and it is DERIVED, not tabulated:
// `leading_zeros_u32(2^lo)` is `31 - lo` for every index the word has, so the
// room above `lo` is one more than that. Both halves come from `trust-bits`,
// which is why this file contains no constant table and no subtraction from a
// literal — §13.5 measures that `32 - lo` does not prove at any width with any
// guard, and this spelling never needs it.
// ---------------------------------------------------------------------------

/// The number of bits available at index `lo`: `32 - lo`, and `0` at or above
/// the top of the word.
///
/// **Tier 2.** The `<= 32` bound is structural — it is the width of the word —
/// so §5 rules out a contract over it. [`fit_width`] carries the bound that IS
/// worth stating, because it is bounded by a caller-supplied value too.
fn room_at(lo: u32) -> u32 {
    let w: u32 = trust_bits::weight(lo);
    if w == 0 {
        return 0;
    }
    // `leading_zeros_u32` of a non-zero `u32` is at most 31, so this guard is
    // mathematically DEAD and structurally REQUIRED: §2.2 records that the
    // interval engine bounds `z + 1` only from a guard adjacent to the use, and
    // a callee postcondition does not feed it. A dead guard is fine; a dead
    // CLAMP under a tier-1 `ensures` is not (§5), which is why this function
    // carries no clause.
    let z: u32 = trust_bits::leading_zeros_u32(w);
    if z > 31 {
        return 0;
    }
    z + 1
}

/// The width that actually fits where `room` bits are available: `min(width,
/// room)`.
///
/// **Tier 1, two-sided.** `result <= width` and `result <= room` are two
/// same-direction variable bounds, which §14.1 measures as discharging; together
/// they bound the result by `min(width, room)`, which is exactly the value
/// returned.
///
/// **The wrong implementation this still admits** is any function that returns
/// something too SMALL — `0` satisfies both clauses for every argument. The
/// value is pinned by `fit_width_is_exactly_min` over all 33 × 33 pairs.
pub fn fit_width(width: u32, room: u32) -> u32 ensures result <= width ensures result <= room {
    if width > room {
        return room;
    }
    width
}

/// The part of the field `(lo, width)` that lies inside the word.
///
/// `field_width(30, 8)` is `2`; `field_width(32, 8)` is `0`.
///
/// **Tier 2.** A dispatcher: it looks the room up and delegates the bound to
/// [`fit_width`], which states it.
pub fn field_width(lo: u32, width: u32) -> u32 {
    let room: u32 = room_at(lo);
    fit_width(width, room)
}

fn raw_field_fits(lo: u32, width: u32) -> u8 {
    // The two constants are spelled out in THIS body rather than delegated:
    // §12.4 measures that pinning does not compose through a call, so a body
    // that is a bare call to a pinning helper pins nothing.
    //
    // `lo > 32` is tested SEPARATELY from the room, and it is not redundant:
    // `room_at` is `0` for every `lo >= 32`, so without this test the EMPTY
    // field would "fit" at `lo == 40`. It is vacuously true that the empty set
    // lies inside the word, and it is not what a caller writing a descriptor
    // wants to be told. `32` itself is admitted because it is where `next_lo`
    // parks the packing cursor when the word is full.
    if lo > 32 {
        return 0;
    }
    let room: u32 = room_at(lo);
    if width > room {
        return 0;
    }
    1
}

/// `1` when the field `(lo, width)` lies wholly inside the word, `0` otherwise.
///
/// This is the condition `decode.rs:21` does not check and cannot report: a
/// field that runs off the top of the word is silently truncated there.
///
/// A descriptor must also NAME a position the word has: `field_fits(40, 0)` is
/// `0`, not `1`, even though an empty field occupies no bits.
///
/// **Tier 1.** `ensures result <= 1` is checked. **The wrong implementation this
/// admits is the constant `0`** — "no field ever fits" satisfies the clause for
/// every input. The value is pinned by `field_fits_agrees_with_a_bit_loop` over
/// all 33 × 33 descriptors against an independent per-bit oracle.
pub fn field_fits(lo: u32, width: u32) -> u8 ensures result <= 1 {
    raw_field_fits(lo, width)
}

/// The low index of the smallest field containing two fields: `min(lo0, lo1)`.
///
/// **Tier 1, two-sided.** Two same-direction variable bounds pin `min` exactly
/// (§14.1). **The wrong implementations this admits are the ones that return
/// something too small**, `0` among them; `hull_is_the_smallest_covering_field`
/// pins the value.
pub fn hull_lo(lo0: u32, lo1: u32) -> u32 ensures result <= lo0 ensures result <= lo1 {
    if lo0 > lo1 {
        return lo1;
    }
    lo0
}

/// The exclusive top index of the smallest field containing two fields:
/// `max(end0, end1)`.
///
/// **Tier 1, two-sided**, mirrored: two same-direction `>=` bounds pin `max`
/// exactly. **The wrong implementations this admits are the ones that return
/// something too large**, `u32::MAX` among them; the same test pins the value.
pub fn hull_end(end0: u32, end1: u32) -> u32 ensures result >= end0 ensures result >= end1 {
    if end0 < end1 {
        return end1;
    }
    end0
}

fn raw_next_lo(lo: u32, width: u32) -> u32 {
    // Widened, so the sum peaks at `2^33 - 2` and needs no guard on either
    // operand (§2.1's exception). The clamp is applied BEFORE the narrowing
    // cast, never after — §4.6.
    let s: u64 = (lo as u64) + (width as u64);
    if s > 32 {
        return 32;
    }
    s as u32
}

fn clamp_word_index(v: u32) -> u32 ensures result <= 32 {
    if v > 32 {
        return 32;
    }
    v
}

/// The index at which the next field begins after the field `(lo, width)`,
/// saturating at the top of the word.
///
/// This is the packing cursor: `next_lo(0, 5)` is `5`, and `next_lo(30, 8)` is
/// `32`, meaning "no room left".
///
/// **Tier 1.** `ensures result <= 32` is checked, and the clamp FIRES (§5) —
/// `next_lo(30, 8)` reaches it. **The wrong implementation this admits is the
/// constant `0`**, and also any function that saturates too early; the value is
/// pinned by `next_lo_is_saturating_sum` over all 33 × 33 pairs.
///
/// Note the clamp is spelled locally rather than delegated to
/// `trust_bits::clamp_width`, whose contract is the identical
/// `ensures result <= 32`. That is not an oversight — §15.2 measures that a
/// shape-(B) wrapper over a FOREIGN contracted callee does not discharge
/// (0 proved / 2 unknown against the local twin's 1 proved).
pub fn next_lo(lo: u32, width: u32) -> u32 ensures result <= 32 {
    clamp_word_index(raw_next_lo(lo, width))
}

// ---------------------------------------------------------------------------
// Section 2 — masks and fit.
//
// Every mask in this section is `trust_bits::mask_below(width)` scaled by
// `trust_bits::weight(lo)`. The scaling is a MULTIPLY rather than a shift,
// which is what makes it composable at all (§2.4), and it is done at `u64`
// where the peak is `(2^32-1) * 2^31` — inside `u64::MAX` — so the product's
// own overflow row proves with no guard (§9.3).
// ---------------------------------------------------------------------------

/// The low `width` bits of `v`, with the rest discarded.
///
/// **Tier 2.** A bitwise `&` cannot overflow, so this body carries no
/// obligation at all. In particular the honest bound `result <= mask` is NOT
/// stated here: §14.5 measures that a contracted wrapper over `v & mask` does
/// not discharge `ensures result <= mask` — the encoder refutes it and the
/// refutation is demoted to unknown. [`clamp_to_mask`] states the bound that IS
/// available, over a genuine clamp rather than a mask.
pub fn truncate_to_width(v: u32, width: u32) -> u32 {
    let m: u32 = trust_bits::mask_below(width);
    v & m
}

/// `min(v, mask)` — `v` clamped down to fit under `mask`, SATURATING rather
/// than truncating.
///
/// `clamp_to_mask(6, 3)` is `3`, where `6 & 3` is `2`. Saturating is the right
/// answer when a value is too wide for its field and the caller wants the
/// nearest representable one rather than the low bits of the wrong one.
///
/// **Tier 1, two-sided.** `result <= v` and `result <= mask` pin `min(v, mask)`
/// exactly. **The wrong implementations this admits return something too
/// small** — `0` satisfies both, and so does `v & mask`, which is the very
/// function this one exists NOT to be. `clamp_to_mask_saturates_and_is_not_and`
/// pins the difference on the values where they disagree.
pub fn clamp_to_mask(v: u32, mask: u32) -> u32 ensures result <= v ensures result <= mask {
    if v > mask {
        return mask;
    }
    v
}

/// `v` clamped to the largest value a `width`-bit field can hold.
///
/// **Tier 2.** A dispatcher over [`clamp_to_mask`], which states the bound.
pub fn saturate_to_width(v: u32, width: u32) -> u32 {
    let m: u32 = trust_bits::mask_below(width);
    clamp_to_mask(v, m)
}

fn raw_value_fits(v: u32, width: u32) -> u8 {
    if v & trust_bits::mask_below(width) == v {
        return 1;
    }
    0
}

/// `1` when `v` fits in `width` bits without loss, `0` otherwise.
///
/// **Tier 1.** `ensures result <= 1` is checked, over a helper that pins its
/// return to the two constants in its own body (§12.4) while CALLING
/// `trust-bits` for the mask — §15.1 measures that a foreign call inside the
/// pinning helper leaves the clause discharging exactly as a local one does.
///
/// **The wrong implementation this admits is the constant `0`**, "nothing ever
/// fits". `value_fits_agrees_with_checked_shl` pins the value against
/// `u32::checked_shl` over every width and a sweep of values.
pub fn value_fits(v: u32, width: u32) -> u8 ensures result <= 1 {
    raw_value_fits(v, width)
}

/// The word bits the field `(lo, width)` occupies, as a mask.
///
/// `0` when the field does not lie wholly inside the word — which is the
/// difference between this and `(1 << width) - 1 << lo`, whose two overflow
/// modes are `trust-bits`'s subject and whose truncation is this crate's.
///
/// **Tier 2.** Structurally a word.
pub fn field_mask(lo: u32, width: u32) -> u32 {
    // Load-bearing, and NOT implied by the `hole > u32::MAX` test below:
    // `trust_bits::mask_below` SATURATES, so `mask_below(33)` is the whole word
    // and `field_mask(0, 33)` would otherwise report a 33-bit field as fitting
    // in 32 bits. Saturation is the right total extension for a mask (a mask of
    // at least 32 low bits of a 32-bit word IS the whole word) and the wrong
    // answer for a descriptor, which is exactly the seam this crate owns. Found
    // by `field_mask_agrees_with_a_bit_loop`, not by reading the code.
    if raw_field_fits(lo, width) == 0 {
        return 0;
    }
    let d: u32 = trust_bits::weight(lo);
    let m: u32 = trust_bits::mask_below(width);
    if d == 0 {
        return 0;
    }
    // `u32 x u32 -> u64` peaks at `(2^32-1)^2`, inside `u64::MAX` (§9.3), and
    // widening is what supplies both operands their range — a mask on an
    // already-wide value supplies none (§9.4, §2.7).
    let hole: u64 = (m as u64) * (d as u64);
    if hole > 4294967295 {
        return 0;
    }
    hole as u32
}

// ---------------------------------------------------------------------------
// Section 3 — reading and writing a field.
//
// `extract` divides, so it is TERMINAL: no verified function may call it, here
// or in any consumer (§2.4, §12.5, §15.3). That is why there is no `unpack2`
// convenience — a caller writes `extract(x, 0, w0)` and
// `extract(x, next_lo(0, w0), w1)` at the site, exactly as `trust-bits` has no
// `field_at_index`.
// ---------------------------------------------------------------------------

/// The value of the field `(lo, width)` in `x`, moved down to index 0.
///
/// `0` when the field does not lie wholly inside the word. This is the
/// difference from [`trust_bits::field`], which returns everything above `lo`:
/// `extract(x, 30, 8)` is `0` here and two real bits there. Refusing is the
/// answer a descriptor layer owes its caller, because a truncated field is
/// indistinguishable from a correct one at the call site.
///
/// **Tier 2.** The honest bound is `result < 2^width` — a variable exponent in
/// the predicate, which the clause language does not admit (§1.2, §12.8).
pub fn extract(x: u32, lo: u32, width: u32) -> u32 {
    if raw_field_fits(lo, width) == 0 {
        return 0;
    }
    let d: u32 = trust_bits::weight(lo);
    let m: u32 = trust_bits::weight(width);
    if d == 0 {
        return 0;
    }
    let q: u32 = x / d;
    if m == 0 {
        return q;
    }
    q % m
}

/// The low `width` bits of `value`, moved up to index `lo`.
///
/// `0` when the field does not lie wholly inside the word.
///
/// **Tier 2.** Structurally a word.
pub fn place(value: u32, lo: u32, width: u32) -> u32 {
    if raw_field_fits(lo, width) == 0 {
        return 0;
    }
    let d: u32 = trust_bits::weight(lo);
    let m: u32 = trust_bits::mask_below(width);
    if d == 0 {
        return 0;
    }
    let hole: u64 = (m as u64) * (d as u64);
    if hole > 4294967295 {
        return 0;
    }
    // `value & m <= m`, so `placed <= hole <= u32::MAX` and this narrowing cast
    // cannot truncate. That is an ARGUMENT, not a proved row — a truncating
    // cast mints no obligation at all (§2.5) — so it is pinned by
    // `place_and_extract_are_inverse` instead. A second `if placed >
    // 4294967295` guard would look like evidence and be implied by the one
    // above, which is worse than saying this.
    let placed: u64 = ((value & m) as u64) * (d as u64);
    placed as u32
}

/// `x` with the field `(lo, width)` replaced by the low `width` bits of
/// `value`; `x` unchanged when the field does not lie wholly inside the word.
///
/// **Tier 2.** Composed from [`field_mask`] and [`place`], so this body is
/// arithmetic-free and carries no obligation of its own — the proofs are the
/// ones those two discharged.
pub fn insert(x: u32, value: u32, lo: u32, width: u32) -> u32 {
    let hole: u32 = field_mask(lo, width);
    let placed: u32 = place(value, lo, width);
    (x & !hole) | placed
}

// ---------------------------------------------------------------------------
// Section 4 — the mask -> descriptor direction.
//
// Both readings come from `trust-bits` (`trailing_zeros_u32` for the low index,
// `highest_set_index` for the top), and the round trip through `field_mask` is
// what DECIDES whether a mask is a field at all.
// ---------------------------------------------------------------------------

/// The low index of the mask `m`, and `32` for `m == 0` — one past the top
/// index, so a caller tests a value rather than handling an empty case.
///
/// **Tier 2.** The `<= 32` bound is structural.
pub fn mask_lo(m: u32) -> u32 {
    trust_bits::trailing_zeros_u32(m)
}

/// The width of the mask `m` read as a contiguous field: the number of bit
/// positions from its lowest set bit to its highest, inclusive. `0` for
/// `m == 0`.
///
/// This is NOT a population count — `mask_width(0b1010)` is `3`, not `2`. It is
/// the width of the *descriptor* that would have to cover `m`, which is the
/// number [`mask_is_field`] compares against.
///
/// **Tier 2.** Structurally at most 32.
pub fn mask_width(m: u32) -> u32 {
    if m == 0 {
        return 0;
    }
    let lo: u32 = trust_bits::trailing_zeros_u32(m);
    let hi: u32 = trust_bits::highest_set_index(m);
    if hi < lo {
        return 0;
    }
    let span: u32 = hi - lo;
    // Dead for a non-zero `m` (`hi <= 31`), and structurally required for the
    // `+ 1` below — the same §2.2 shape as `room_at`'s guard.
    if span > 31 {
        return 32;
    }
    span + 1
}

fn raw_mask_is_field(m: u32) -> u8 {
    let lo: u32 = trust_bits::trailing_zeros_u32(m);
    let w: u32 = mask_width(m);
    if field_mask(lo, w) == m {
        return 1;
    }
    0
}

/// `1` when `m` is the mask of some field — i.e. its set bits are contiguous
/// and lie inside the word — `0` otherwise. `0` is a field (the empty one).
///
/// Decided by the ROUND TRIP: read the descriptor off `m`, rebuild the mask
/// from it, and compare. `0b1110` is a field; `0b1010` is not.
///
/// **Tier 1.** `ensures result <= 1` is checked. **The wrong implementation this
/// admits is the constant `0`.** `mask_is_field_agrees_with_a_bit_loop` pins the
/// value against an independent scan over all 65536 low masks plus every
/// single-field mask in the word.
pub fn mask_is_field(m: u32) -> u8 ensures result <= 1 {
    raw_mask_is_field(m)
}

// ---------------------------------------------------------------------------
// Section 5 — records of more than one field.
//
// This is the layer `trust-bits` has no vocabulary for, and it is decided from
// MASKS rather than from interval arithmetic on the descriptors: a field that
// does not fit has mask `0`, so it cannot spuriously overlap one that does.
// ---------------------------------------------------------------------------

fn raw_fields_overlap(lo0: u32, w0: u32, lo1: u32, w1: u32) -> u8 {
    let m0: u32 = field_mask(lo0, w0);
    let m1: u32 = field_mask(lo1, w1);
    if m0 & m1 == 0 {
        return 0;
    }
    1
}

/// `1` when the fields `(lo0, w0)` and `(lo1, w1)` share at least one word bit.
///
/// A field that does not fit in the word occupies no bits, so it overlaps
/// nothing — which is the answer that keeps a caller from "repairing" an
/// out-of-range descriptor by moving the one it collides with.
///
/// **Tier 1.** `ensures result <= 1` is checked. **The wrong implementation this
/// admits is the constant `0`**, "nothing ever collides" — the most dangerous
/// constant this crate could return, which is why
/// `fields_overlap_agrees_with_a_bit_loop` checks it against a per-bit oracle
/// over a systematic sweep of descriptor pairs.
pub fn fields_overlap(lo0: u32, w0: u32, lo1: u32, w1: u32) -> u8 ensures result <= 1 {
    raw_fields_overlap(lo0, w0, lo1, w1)
}

/// Two fields packed from index 0: `v0` in `[0, w0)` and `v1` starting where
/// the first one ends.
///
/// **Tier 2.** Composed from [`place`] and [`next_lo`]; arithmetic-free here.
pub fn pack2(v0: u32, w0: u32, v1: u32, w1: u32) -> u32 {
    let a: u32 = place(v0, 0, w0);
    let lo1: u32 = next_lo(0, w0);
    let b: u32 = place(v1, lo1, w1);
    a | b
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---- independent oracles -------------------------------------------
    // None of these calls the function under test. `mask_oracle` walks bit
    // positions one at a time; `fits_oracle` uses `u32::checked_shl`.

    /// The mask of `(lo, width)` built one bit at a time, or `None` when the
    /// field does not lie wholly inside the word.
    fn mask_oracle(lo: u32, width: u32) -> Option<u32> {
        if lo > 32 || width > 32 || lo + width > 32 {
            return None;
        }
        let mut m: u32 = 0;
        let mut i: u32 = 0;
        while i < width {
            m |= 1u32 << (lo + i);
            i += 1;
        }
        Some(m)
    }

    /// `2^width - 1`, saturating, via `checked_shl`.
    fn value_mask_oracle(width: u32) -> u32 {
        match 1u32.checked_shl(width) {
            Some(v) => v.wrapping_sub(1),
            None => u32::MAX,
        }
    }

    #[test]
    fn room_at_is_the_bits_above_lo() {
        for lo in 0..40u32 {
            let want = if lo >= 32 { 0 } else { 32 - lo };
            assert_eq!(room_at(lo), want, "room_at({lo})");
        }
    }

    #[test]
    fn fit_width_is_exactly_min() {
        for width in 0..33u32 {
            for room in 0..33u32 {
                let want = if width < room { width } else { room };
                assert_eq!(fit_width(width, room), want, "fit_width({width},{room})");
            }
        }
        for lo in 0..40u32 {
            for width in 0..40u32 {
                let room = if lo >= 32 { 0 } else { 32 - lo };
                let want = if width < room { width } else { room };
                assert_eq!(field_width(lo, width), want, "field_width({lo},{width})");
            }
        }
    }

    #[test]
    fn field_fits_agrees_with_a_bit_loop() {
        for lo in 0..40u32 {
            for width in 0..40u32 {
                let want = u8::from(mask_oracle(lo, width).is_some());
                assert_eq!(field_fits(lo, width), want, "field_fits({lo},{width})");
            }
        }
    }

    #[test]
    fn hull_is_the_smallest_covering_field() {
        for a in 0..34u32 {
            for b in 0..34u32 {
                assert_eq!(hull_lo(a, b), a.min(b), "hull_lo({a},{b})");
                assert_eq!(hull_end(a, b), a.max(b), "hull_end({a},{b})");
            }
        }
        // The hull of two real fields covers both and nothing outside them.
        for lo0 in 0..8u32 {
            for lo1 in 0..8u32 {
                let (w0, w1) = (3u32, 5u32);
                let lo = hull_lo(lo0, lo1);
                let end = hull_end(lo0 + w0, lo1 + w1);
                let hull = mask_oracle(lo, end - lo).unwrap();
                let m0 = mask_oracle(lo0, w0).unwrap();
                let m1 = mask_oracle(lo1, w1).unwrap();
                assert_eq!(hull & m0, m0);
                assert_eq!(hull & m1, m1);
            }
        }
    }

    #[test]
    fn next_lo_is_saturating_sum() {
        for lo in 0..40u32 {
            for width in 0..40u32 {
                let s = lo as u64 + width as u64;
                let want = if s > 32 { 32 } else { s as u32 };
                assert_eq!(next_lo(lo, width), want, "next_lo({lo},{width})");
            }
        }
        // the clamp is LIVE, which is what makes the contract non-vacuous
        assert_eq!(next_lo(30, 8), 32);
        assert_ne!(next_lo(30, 8), 38);
    }

    #[test]
    fn truncate_and_value_mask_agree_with_checked_shl() {
        for width in 0..40u32 {
            let m = value_mask_oracle(width.min(32));
            for v in [0u32, 1, 2, 7, 255, 256, 65535, 0x1234_5678, u32::MAX] {
                assert_eq!(truncate_to_width(v, width), v & m, "truncate({v},{width})");
            }
        }
    }

    #[test]
    fn clamp_to_mask_saturates_and_is_not_and() {
        for mask in [0u32, 1, 3, 7, 15, 255, 65535, u32::MAX] {
            for v in [0u32, 1, 2, 3, 6, 9, 255, 256, u32::MAX] {
                assert_eq!(clamp_to_mask(v, mask), v.min(mask), "clamp({v},{mask})");
            }
        }
        // The two functions this crate deliberately keeps apart.
        assert_eq!(clamp_to_mask(6, 3), 3);
        assert_eq!(6u32 & 3u32, 2);
        assert_ne!(clamp_to_mask(6, 3), 6 & 3);
        for width in 0..33u32 {
            let m = value_mask_oracle(width);
            for v in [0u32, 5, 6, 255, u32::MAX] {
                assert_eq!(saturate_to_width(v, width), v.min(m));
            }
        }
    }

    #[test]
    fn value_fits_agrees_with_checked_shl() {
        for width in 0..40u32 {
            let m = value_mask_oracle(width.min(32));
            for v in [0u32, 1, 2, 3, 15, 16, 255, 256, 65535, 65536, u32::MAX] {
                assert_eq!(value_fits(v, width), u8::from(v <= m), "value_fits({v},{width})");
            }
        }
        assert_eq!(value_fits(0, 0), 1);
        assert_eq!(value_fits(1, 0), 0);
    }

    #[test]
    fn field_mask_agrees_with_a_bit_loop() {
        for lo in 0..40u32 {
            for width in 0..40u32 {
                let want = mask_oracle(lo, width).unwrap_or(0);
                assert_eq!(field_mask(lo, width), want, "field_mask({lo},{width})");
            }
        }
        assert_eq!(field_mask(0, 32), u32::MAX);
        assert_eq!(field_mask(31, 1), 0x8000_0000);
        assert_eq!(field_mask(31, 2), 0);
    }

    #[test]
    fn place_and_extract_are_inverse() {
        for lo in 0..33u32 {
            for width in 0..33u32 {
                if mask_oracle(lo, width).is_none() {
                    assert_eq!(place(7, lo, width), 0, "place({lo},{width})");
                    assert_eq!(extract(0xFFFF_FFFF, lo, width), 0, "extract({lo},{width})");
                    continue;
                }
                let m = value_mask_oracle(width);
                for v in [0u32, 1, 2, 5, 255, u32::MAX] {
                    let low = v & m;
                    let placed = place(v, lo, width);
                    // the placed value occupies exactly the field's bits ...
                    assert_eq!(placed & !field_mask(lo, width), 0, "place spill ({lo},{width})");
                    // ... and reading it back gives the low `width` bits.
                    assert_eq!(extract(placed, lo, width), low, "roundtrip ({v},{lo},{width})");
                }
            }
        }
    }

    #[test]
    fn extract_refuses_a_field_that_does_not_fit() {
        // The whole reason this crate does not delegate to `trust_bits::field`.
        assert_eq!(extract(u32::MAX, 30, 8), 0);
        assert_eq!(trust_bits::field(u32::MAX, 30, 8), 3);
        assert_eq!(extract(u32::MAX, 30, 2), 3);
    }

    #[test]
    fn insert_replaces_exactly_the_field_and_nothing_else() {
        for lo in 0..33u32 {
            for width in 0..33u32 {
                let m = field_mask(lo, width);
                for x in [0u32, 0xFFFF_FFFF, 0xA5A5_A5A5] {
                    for v in [0u32, 1, 5, u32::MAX] {
                        let out = insert(x, v, lo, width);
                        // outside the field, nothing moved
                        assert_eq!(out & !m, x & !m, "insert outside ({lo},{width})");
                        // inside it, the low `width` bits of `v`
                        assert_eq!(out & m, place(v, lo, width), "insert inside ({lo},{width})");
                        if mask_oracle(lo, width).is_none() {
                            assert_eq!(out, x, "insert must refuse ({lo},{width})");
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn mask_lo_and_width_agree_with_core() {
        for m in 0..65536u32 {
            assert_eq!(mask_lo(m), m.trailing_zeros(), "mask_lo({m})");
            let want = if m == 0 {
                0
            } else {
                32 - m.leading_zeros() - m.trailing_zeros()
            };
            assert_eq!(mask_width(m), want, "mask_width({m})");
        }
        assert_eq!(mask_lo(0), 32);
        assert_eq!(mask_width(0), 0);
        assert_eq!(mask_width(0b1010), 3);
        assert_eq!(mask_width(0x8000_0000), 1);
        assert_eq!(mask_width(u32::MAX), 32);
    }

    #[test]
    fn mask_is_field_agrees_with_a_bit_loop() {
        // contiguity decided independently: a mask is a field iff, scanning up,
        // it has exactly one run of set bits.
        fn runs(m: u32) -> u32 {
            let mut n = 0;
            let mut prev = false;
            for i in 0..32 {
                let cur = m & (1u32 << i) != 0;
                if cur && !prev {
                    n += 1;
                }
                prev = cur;
            }
            n
        }
        for m in 0..65536u32 {
            assert_eq!(mask_is_field(m), u8::from(runs(m) <= 1), "mask_is_field({m})");
        }
        for lo in 0..33u32 {
            for width in 0..33u32 {
                if let Some(m) = mask_oracle(lo, width) {
                    assert_eq!(mask_is_field(m), 1, "field mask ({lo},{width}) = {m:#x}");
                }
            }
        }
        assert_eq!(mask_is_field(0), 1);
        assert_eq!(mask_is_field(0b1010), 0);
        assert_eq!(mask_is_field(0x8000_0001), 0);
    }

    #[test]
    fn fields_overlap_agrees_with_a_bit_loop() {
        for lo0 in 0..34u32 {
            for w0 in 0..6u32 {
                for lo1 in 0..34u32 {
                    for w1 in 0..6u32 {
                        let m0 = mask_oracle(lo0, w0).unwrap_or(0);
                        let m1 = mask_oracle(lo1, w1).unwrap_or(0);
                        let want = u8::from(m0 & m1 != 0);
                        assert_eq!(
                            fields_overlap(lo0, w0, lo1, w1),
                            want,
                            "overlap({lo0},{w0},{lo1},{w1})"
                        );
                    }
                }
            }
        }
        // a field that does not fit occupies nothing, so it collides with nothing
        assert_eq!(fields_overlap(30, 8, 0, 32), 0);
        assert_eq!(fields_overlap(0, 4, 2, 4), 1);
        assert_eq!(fields_overlap(0, 4, 4, 4), 0);
    }

    #[test]
    fn pack2_lays_two_fields_end_to_end() {
        for w0 in 0..17u32 {
            for w1 in 0..17u32 {
                for v0 in [0u32, 1, 5, 255] {
                    for v1 in [0u32, 1, 6, 255] {
                        let x = pack2(v0, w0, v1, w1);
                        let lo1 = next_lo(0, w0);
                        assert_eq!(extract(x, 0, w0), v0 & value_mask_oracle(w0));
                        assert_eq!(extract(x, lo1, w1), v1 & value_mask_oracle(w1));
                        // and the two fields do not tread on each other
                        assert_eq!(fields_overlap(0, w0, lo1, w1), 0);
                    }
                }
            }
        }
    }

    /// The property every tier-1 clause in this crate claims, checked as a
    /// value rather than read off a report. It must keep PASSING under the
    /// gate's wrong-value mutations, or those mutations would be demonstrating
    /// "everything broke" rather than "a true contract over a wrong answer".
    #[test]
    fn no_tier1_result_ever_exceeds_its_bound() {
        for a in 0..40u32 {
            for b in 0..40u32 {
                assert!(fit_width(a, b) <= a && fit_width(a, b) <= b);
                assert!(hull_lo(a, b) <= a && hull_lo(a, b) <= b);
                assert!(hull_end(a, b) >= a && hull_end(a, b) >= b);
                assert!(next_lo(a, b) <= 32);
                assert!(field_fits(a, b) <= 1);
                assert!(value_fits(a, b) <= 1);
                assert!(clamp_to_mask(a, b) <= a && clamp_to_mask(a, b) <= b);
                assert!(fields_overlap(a, b, b, a) <= 1);
            }
        }
        for m in 0..4096u32 {
            assert!(mask_is_field(m) <= 1);
        }
    }
}
