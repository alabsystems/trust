//! Total, verified alignment / padding / layout-offset arithmetic for `no_std`
//! Trust components.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0
//!
//! # Why this crate exists, and who calls it
//!
//! Alignment arithmetic is where this tree most consistently writes a side
//! condition down instead of discharging it. The canonical spelling is four
//! tokens long and appears twice, verbatim.
//!
//! **`crates/trust-cg-bridge/src/module_to_lir.rs:1114-1117`**
//!
//! ```text
//! fn align_up_u32(value: u32, align: u32) -> u32 {
//!     debug_assert!(align.is_power_of_two());
//!     (value + align - 1) & !(align - 1)
//! }
//! ```
//!
//! **`compiler/rustc_arena/src/lib.rs:333-342`** — the same body at `usize`,
//! for both directions:
//!
//! ```text
//! fn align_down(val: usize, align: usize) -> usize {
//!     debug_assert!(align.is_power_of_two());
//!     val & !(align - 1)
//! }
//! fn align_up(val: usize, align: usize) -> usize {
//!     debug_assert!(align.is_power_of_two());
//!     (val + align - 1) & !(align - 1)
//! }
//! ```
//!
//! Two distinct arithmetic facts are asserted rather than proved there, and a
//! `debug_assert!` discharges neither, because it is compiled out of the build
//! that ships:
//!
//! 1. **`align` is a power of two.** If it is not, `& !(align - 1)` is not a
//!    round-up at all: `(5 + 3 - 1) & !(3 - 1)` is `7 & !2 == 5`, and
//!    `(6 + 3 - 1) & !2` is `8 & !2 == 8`. Neither is a multiple of 3. The
//!    formula silently returns a plausible-looking wrong offset.
//! 2. **`value + align - 1` does not overflow.** Nothing in either function, or
//!    in either caller, bounds `value`. Past `u32::MAX - align + 1` the add
//!    wraps and the "rounded up" offset comes out *below* its own input:
//!    `align_up_u32(u32::MAX - 8, 16)` is `0`.
//!
//! [`align_up`] is that computation performed where neither fact can be
//! assumed. The power-of-two side condition is **deleted rather than proved**:
//! `align - 1` is never computed, because the supported masks are the arms of
//! an ordered guard chain, so a non-power-of-two `align` cannot reach a mask at
//! all — and [`align_is_supported`] is the checked proposition that tells a
//! caller which case it is in, in the build that ships. The addition is
//! performed one width up, where it cannot wrap, and then saturated.
//!
//! **`crates/trust-cg-bridge/src/module_to_lir.rs:1237-1251`** is the loop that
//! consumes it — a declaration-order C-layout field walk whose running `offset`
//! is fed straight back into the same unguarded formula, and whose
//! `offset += f_size` has no bound either:
//!
//! ```text
//! let mut offset: u32 = 0;
//! for field_ty in &fields {
//!     let (f_size, f_align, f_lir) = scalar_field_size_align(field_ty, name)?;
//!     offset = align_up_u32(offset, f_align);
//!     field_offsets.push((offset, f_lir));
//!     offset += f_size;
//!     max_align = max_align.max(f_align);
//! }
//! let size = align_up_u32(offset, max_align);
//! ```
//!
//! [`field_offset2`], [`record_end2`] and [`record_size2`] are the unrolled,
//! saturating form of exactly that walk, checked against rustc's own
//! `size_of` / `align_of` / `offset_of!` on four `#[repr(C)]` structs.
//!
//! **`crates/trust-thir-lower/src/lib.rs:602-607`** states a layout fact of the
//! same algorithm as prose and then relies on it:
//!
//! ```text
//! /// * field 0 is at `align_up(0, a) == 0` for every alignment — ALWAYS, and
//! ///   with no dependence on any field type. A zero displacement at field 0 is
//! ///   a tautology on BOTH sides.
//! ```
//!
//! It is true, and it is load-bearing for `zero_displacement_agrees`, whose
//! other direction the same file calls "the fail-OPEN direction". Here it is
//! checked rather than asserted:
//! `align_up_of_zero_is_zero_at_every_supported_alignment`.
//!
//! **`crates/trust-js-sem/src/typedarray.rs:339`** — the bound check behind
//! every typed-array element access in the JS engine:
//!
//! ```text
//! f.byte_offset + f.length * f.elem.bytes() > d.bytes.len()
//! ```
//!
//! `byte_offset` and `length` are fields whose values come from JavaScript. The
//! multiply is unguarded and so is the add on top of it; a wrap makes the
//! comparison read *small*, so the out-of-bounds check passes.
//! **`typedarray.rs:370`** then indexes with `f.byte_offset + i *
//! f.elem.bytes()`, the same shape one element at a time. [`view_end`],
//! [`view_elem_offset`] and [`view_fits`] are that computation with the
//! multiply and the add both performed one width up.
//!
//! **`crates/trust-vcgen/src/generate/alloc_bounds.rs:26-28`** declines the
//! stride question outright — *"Tuple `(A, B, …)` — sum of field sizes (ignores
//! layout padding; an UNDER-estimate of the true size…)"*. [`array_stride`] and
//! [`array_bytes_padded`] compute it.
//!
//! # Two tiers, and what each one claims
//!
//! **Tier 1 — proved bound.** A grammar `ensures` clause the compiler
//! discharges. Twelve functions carry one.
//!
//! **Tier 2 — proved totality only.** No contract, but every arithmetic
//! obligation in the body is discharged: no overflow, no wrap, no panic path,
//! on any input. Nothing here is `unreachable`-shaped.
//!
//! A tier-1 clause is only worth writing where the clamp can actually FIRE
//! (`docs/STRICT_VERIFICATION_FRAGMENT.md` §5). That is why [`padding_to`] is
//! tier 2: `ensures result <= align` would be discharged and would be **dead**,
//! because a padding is bounded by `align - 1` by construction, and a green row
//! over a clause no input can approach is indistinguishable in the kind split
//! from one that constrains something.
//!
//! # The two conventions, stated once
//!
//! * **Supported alignments are `1, 2, 4, … 4096`.** Every other `align` —
//!   including `0`, `3`, and anything above `4096` — is **normalised to `1`**,
//!   which makes [`align_up`] the identity. That is the only fallback that is
//!   correct for *some* alignment and therefore never a wrong multiple of a
//!   different one; the `debug_assert!` sites above compute a wrong multiple
//!   instead. [`align_is_supported`] is the checked proposition, and a caller
//!   that cares must test it.
//!
//!   **The `4096` ceiling is a measured TRANSPORT limit, not a domain choice**
//!   — see `docs/STRICT_VERIFICATION_FRAGMENT.md` §9.2. At a `2^24` ceiling the
//!   four lattice chains carry 26 postcondition rows each, and `targo trust
//!   check` then exits 2 with `could not seal the final compiler rows …` and
//!   **no other diagnostic at all**: no `error:`, no `Gate:` line, no Summary.
//!   The crate verifies; the report cannot be published. Extending the ceiling
//!   is guard-chain arms plus a re-measurement, in that order.
//! * **Every `u32`-returning arithmetic function saturates at `u32::MAX`.** The
//!   exact answer is available one width up ([`align_up_wide`],
//!   [`padding_wide`]), where `align_up_wide(u32::MAX, 4096) == 4294967296` is
//!   representable and no `u32` form of it exists.

#![no_std]

// ---------------------------------------------------------------------------
// Tier 1 — the alignment lattice. Ordered guard chains over CONSTANTS, so these
// bodies carry no arithmetic at all and every row is a discharged
// postcondition (`docs/STRICT_VERIFICATION_FRAGMENT.md` §1.1 shape A).
// ---------------------------------------------------------------------------

/// The mask `align - 1` for a supported power-of-two `align`, and `0` — the
/// mask of `align == 1` — for every unsupported one.
///
/// **This function is why the `debug_assert!` is deleted rather than proved.**
/// `align - 1` is never computed; the thirteen supported masks are literals in
/// an ordered chain, so a non-power-of-two `align` cannot reach a mask.
///
/// **Tier 1.** `ensures result <= 4095` is checked.
pub fn align_mask(align: u32) -> u32 ensures result <= 4095 {
    if align == 1 {
        return 0;
    }
    if align == 2 {
        return 1;
    }
    if align == 4 {
        return 3;
    }
    if align == 8 {
        return 7;
    }
    if align == 16 {
        return 15;
    }
    if align == 32 {
        return 31;
    }
    if align == 64 {
        return 63;
    }
    if align == 128 {
        return 127;
    }
    if align == 256 {
        return 255;
    }
    if align == 512 {
        return 511;
    }
    if align == 1024 {
        return 1023;
    }
    if align == 2048 {
        return 2047;
    }
    if align == 4096 {
        return 4095;
    }
    0
}

/// The alignment this crate actually applies: `align` when it is a supported
/// power of two, and `1` otherwise.
///
/// **Tier 1.** `ensures result <= 4096` is checked.
pub fn align_norm(align: u32) -> u32 ensures result <= 4096 {
    if align == 2 {
        return 2;
    }
    if align == 4 {
        return 4;
    }
    if align == 8 {
        return 8;
    }
    if align == 16 {
        return 16;
    }
    if align == 32 {
        return 32;
    }
    if align == 64 {
        return 64;
    }
    if align == 128 {
        return 128;
    }
    if align == 256 {
        return 256;
    }
    if align == 512 {
        return 512;
    }
    if align == 1024 {
        return 1024;
    }
    if align == 2048 {
        return 2048;
    }
    if align == 4096 {
        return 4096;
    }
    1
}

/// `log2(align)` for a supported power-of-two `align`; the sentinel `32`
/// otherwise. `32` is one past the top of every shift a `u32` alignment can
/// have, so it is inside the contracted bound and outside the answer space
/// (`docs/STRICT_VERIFICATION_FRAGMENT.md` §1.4).
///
/// **Tier 1.** `ensures result <= 32` is checked.
pub fn align_shift(align: u32) -> u32 ensures result <= 32 {
    if align == 1 {
        return 0;
    }
    if align == 2 {
        return 1;
    }
    if align == 4 {
        return 2;
    }
    if align == 8 {
        return 3;
    }
    if align == 16 {
        return 4;
    }
    if align == 32 {
        return 5;
    }
    if align == 64 {
        return 6;
    }
    if align == 128 {
        return 7;
    }
    if align == 256 {
        return 8;
    }
    if align == 512 {
        return 9;
    }
    if align == 1024 {
        return 10;
    }
    if align == 2048 {
        return 11;
    }
    if align == 4096 {
        return 12;
    }
    32
}

/// `2^shift` for `shift <= 12`, and `1` for every other `shift`.
///
/// This is the inverse of [`align_shift`] on the supported set, and it is
/// spelled as constants rather than as `1 << shift` on purpose: `<<` mints its
/// own shift-overflow obligation and is composition-opaque
/// (`docs/STRICT_VERIFICATION_FRAGMENT.md` §2.4), so a shifted spelling could
/// not be called from anything that has to bundle.
///
/// **Tier 1.** `ensures result <= 4096` is checked.
pub fn align_from_shift(shift: u32) -> u32 ensures result <= 4096 {
    if shift == 0 {
        return 1;
    }
    if shift == 1 {
        return 2;
    }
    if shift == 2 {
        return 4;
    }
    if shift == 3 {
        return 8;
    }
    if shift == 4 {
        return 16;
    }
    if shift == 5 {
        return 32;
    }
    if shift == 6 {
        return 64;
    }
    if shift == 7 {
        return 128;
    }
    if shift == 8 {
        return 256;
    }
    if shift == 9 {
        return 512;
    }
    if shift == 10 {
        return 1024;
    }
    if shift == 11 {
        return 2048;
    }
    if shift == 12 {
        return 4096;
    }
    1
}

/// `1` when `align` is one of the supported power-of-two alignments, `0`
/// otherwise. This is `debug_assert!(align.is_power_of_two())` as a value the
/// caller can branch on in the build that ships.
///
/// **Tier 1.** `ensures result <= 1` is checked.
pub fn align_is_supported(align: u32) -> u8 ensures result <= 1 {
    if align_norm(align) == 1 {
        if align == 1 {
            return 1;
        }
        return 0;
    }
    1
}

/// `1` when `n` is a power of two (`n >= 1`), `0` otherwise — including at
/// `n == 0`, where `n - 1` would underflow and where `core`'s
/// `u32::is_power_of_two` also answers `false`.
///
/// **Tier 1.** `ensures result <= 1` is checked.
pub fn is_power_of_two(n: u32) -> u8 ensures result <= 1 {
    raw_is_power_of_two(n)
}

fn raw_is_power_of_two(n: u32) -> u8 {
    if n == 0 {
        return 0;
    }
    let m: u32 = n - 1;
    if (n & m) == 0 { 1 } else { 0 }
}

/// `1` when `value` is a multiple of `align`, `0` otherwise. An unsupported
/// `align` normalises to `1`, under which every value is aligned.
///
/// **Tier 1.** `ensures result <= 1` is checked.
pub fn is_aligned(value: u32, align: u32) -> u8 ensures result <= 1 {
    raw_is_aligned(value, align)
}

fn raw_is_aligned(value: u32, align: u32) -> u8 {
    let m: u32 = align_mask(align);
    if (value & m) == 0 { 1 } else { 0 }
}

/// The larger of two normalised alignments — the aggregate alignment of a
/// record with fields of alignment `a` and `b`. This is
/// `max_align = max_align.max(f_align)` from `module_to_lir.rs:1248`, with the
/// normalisation that site does not have.
///
/// **Tier 1.** `ensures result <= 4096` is checked.
///
/// Both arms return LOCALS, and `align_norm` runs before the comparison rather
/// than inside the returned expression. The un-normalised spelling — two arms
/// returning the bare parameters `a`/`b` — measured UNKNOWN x3 while probing
/// this crate; that measurement is CONFOUNDED and is recorded as such, because
/// the same edit also makes `result <= 4096` genuinely false at `a > 4096`. It
/// is a lead toward `docs/STRICT_VERIFICATION_FRAGMENT.md` §2.6's
/// local-vs-parameter rule, not a second instance of it.
pub fn align_max(a: u32, b: u32) -> u32 ensures result <= 4096 {
    let x: u32 = align_norm(a);
    let y: u32 = align_norm(b);
    if x >= y {
        return x;
    }
    y
}

// ---------------------------------------------------------------------------
// Tier 2 — the arithmetic. Uncontracted; every row is a discharged safety
// obligation.
//
// `raw_up_from_mask` takes the MASK, not the alignment, and that is
// load-bearing rather than stylistic: a bundle member whose arithmetic Assert
// sits AFTER a call is refused with `member has a guarded or non-entry-prefix
// Assert`, so folding the `align_mask` lookup into this body makes every caller
// below fail to lower. Measured 2026-08-29;
// `docs/STRICT_VERIFICATION_FRAGMENT.md` §9.1.
// ---------------------------------------------------------------------------

fn raw_up_from_mask(value: u32, mask: u32) -> u64 {
    let m: u64 = mask as u64;
    let s: u64 = (value as u64) + m;
    s & !m
}

fn raw_sat_add(a: u32, b: u32) -> u32 {
    let s: u64 = (a as u64) + (b as u64);
    if s > 4294967295 {
        return 4294967295;
    }
    s as u32
}

fn raw_sat_mul(a: u32, b: u32) -> u32 {
    let p: u64 = (a as u64) * (b as u64);
    if p > 4294967295 {
        return 4294967295;
    }
    p as u32
}

fn clamp_u32(v: u32, hi: u32) -> u32 ensures result <= hi {
    if v > hi { hi } else { v }
}

/// `value` rounded up to the next multiple of `align`, **exactly**, one width
/// up. The true answer ranges over `[0, 2^32]`, which is why this returns
/// `u64`: `align_up_wide(u32::MAX, 4096)` is `4294967296`, and no `u32` form of
/// it exists.
///
/// This is `module_to_lir.rs:1116` and `rustc_arena/src/lib.rs:341` with both
/// side conditions discharged — the mask comes from [`align_mask`], so there is
/// no `align - 1`, and the addition happens at `u64`, so there is no wrap.
///
/// **Tier 2.**
pub fn align_up_wide(value: u32, align: u32) -> u64 {
    raw_up_from_mask(value, align_mask(align))
}

/// `value` rounded up to the next multiple of `align`, saturating at
/// `u32::MAX`. The saturation is reachable only from `value > u32::MAX - align
/// + 1` — precisely the region where the two cited sites wrap and return a
/// value *below* their own input.
///
/// **Tier 2.**
pub fn align_up(value: u32, align: u32) -> u32 {
    let r: u64 = raw_up_from_mask(value, align_mask(align));
    if r > 4294967295 {
        return 4294967295;
    }
    r as u32
}

/// `value` rounded DOWN to a multiple of `align` — `rustc_arena/src/lib.rs:335`
/// with the power-of-two side condition deleted. It needs no widening, because
/// a mask can only ever decrease its operand.
///
/// **Tier 2**, and it carries no obligation at all: a bitwise `&` cannot
/// overflow, so there is nothing to prove. That is a fact about the operator,
/// not a gap in coverage.
pub fn align_down(value: u32, align: u32) -> u32 {
    let m: u32 = align_mask(align);
    value & !m
}

/// The number of padding bytes between `value` and the next multiple of
/// `align`, exactly, one width up.
///
/// **Tier 2**, deliberately: the honest clause is `result <= align - 1`, and a
/// tier-1 `ensures result <= align` would be discharged over a clamp that no
/// input can make fire (`docs/STRICT_VERIFICATION_FRAGMENT.md` §5).
pub fn padding_wide(value: u32, align: u32) -> u64 {
    let up: u64 = raw_up_from_mask(value, align_mask(align));
    let v: u64 = value as u64;
    if up < v {
        return 0;
    }
    up - v
}

/// The number of padding bytes between `value` and the next multiple of
/// `align`, saturating at `u32::MAX`.
///
/// **Tier 2.**
pub fn padding_to(value: u32, align: u32) -> u32 {
    let up: u32 = align_up(value, align);
    if up < value {
        return 0;
    }
    up - value
}

/// The byte offset of field 1 in a declaration-order C layout whose field 0
/// occupies `[0, size0)` and whose field 1 has alignment `align1` — one
/// unrolled step of `module_to_lir.rs:1240-1249`.
///
/// **Tier 2.**
pub fn field_offset2(size0: u32, align1: u32) -> u32 {
    align_up(size0, align1)
}

/// The first byte past field 1 in that layout — `field_offset2 + size1`,
/// saturating. `module_to_lir.rs:1247` spells this `offset += f_size`, with
/// nothing bounding either operand.
///
/// **Tier 2.**
pub fn record_end2(size0: u32, align1: u32, size1: u32) -> u32 {
    let off: u32 = align_up(size0, align1);
    raw_sat_add(off, size1)
}

/// The total size of that two-field record: the end offset rounded up to the
/// record's own alignment, which is the larger of the two field alignments.
/// This is `module_to_lir.rs:1250`'s `align_up_u32(offset, max_align)`.
///
/// Note the shape: every intermediate is narrowed back to `u32` before the next
/// step, so each widening cast re-supplies a range the preceding `& !m`
/// destroyed. Keeping the chain at `u64` leaves the second round-up
/// RUNTIME CHECKED (`docs/STRICT_VERIFICATION_FRAGMENT.md` §9.1).
///
/// **Tier 2.**
pub fn record_size2(size0: u32, align0: u32, size1: u32, align1: u32) -> u32 {
    let off: u32 = align_up(size0, align1);
    let end: u32 = raw_sat_add(off, size1);
    let ra: u32 = align_max(align0, align1);
    align_up(end, ra)
}

/// The stride of an array element: its size rounded up to its alignment. This
/// is what `alloc_bounds.rs:26-28` declines to compute.
///
/// **Tier 2.**
pub fn array_stride(elem_size: u32, align: u32) -> u32 {
    align_up(elem_size, align)
}

/// `stride * count`, saturating at `u32::MAX`.
///
/// **Tier 2.**
pub fn array_bytes(stride: u32, count: u32) -> u32 {
    raw_sat_mul(stride, count)
}

/// The byte size of `count` elements of size `elem_size` and alignment
/// `align`, with inter-element padding, saturating at `u32::MAX`.
///
/// **Tier 2.**
pub fn array_bytes_padded(elem_size: u32, align: u32, count: u32) -> u32 {
    let st: u32 = align_up(elem_size, align);
    raw_sat_mul(st, count)
}

/// The first byte past a typed-array view — `byte_offset + count * elem_bytes`,
/// saturating at `u32::MAX`. This is `typedarray.rs:339`'s left-hand side with
/// the multiply and the add both performed one width up.
///
/// **Tier 2.**
pub fn view_end(byte_offset: u32, count: u32, elem_bytes: u32) -> u32 {
    raw_view_end(byte_offset, count, elem_bytes)
}

fn raw_view_end(byte_offset: u32, count: u32, elem_bytes: u32) -> u32 {
    let e: u64 = (byte_offset as u64) + (count as u64) * (elem_bytes as u64);
    if e > 4294967295 {
        return 4294967295;
    }
    e as u32
}

/// The byte offset of element `index` of a typed-array view —
/// `typedarray.rs:370`'s `f.byte_offset + i * f.elem.bytes()`, saturating.
///
/// **Tier 2.**
pub fn view_elem_offset(byte_offset: u32, index: u32, elem_bytes: u32) -> u32 {
    raw_view_end(byte_offset, index, elem_bytes)
}

/// `1` when a view of `count` elements of `elem_bytes` bytes starting at
/// `byte_offset` lies inside a buffer of `buffer_len` bytes, `0` otherwise.
/// This is `typedarray.rs:339` as a total proposition rather than as an
/// unguarded comparison whose left-hand side can wrap below its own operands.
///
/// **Tier 1.** `ensures result <= 1` is checked.
pub fn view_fits(byte_offset: u32, count: u32, elem_bytes: u32, buffer_len: u32) -> u8
ensures result <= 1 {
    raw_view_fits(byte_offset, count, elem_bytes, buffer_len)
}

fn raw_view_fits(byte_offset: u32, count: u32, elem_bytes: u32, buffer_len: u32) -> u8 {
    let e: u32 = raw_view_end(byte_offset, count, elem_bytes);
    if e > buffer_len { 0 } else { 1 }
}

// ---------------------------------------------------------------------------
// Tier 1 — bound-carrying wrappers. Every clamp here is LIVE: an argument
// exists that exceeds the bound and is clamped to it
// (`docs/STRICT_VERIFICATION_FRAGMENT.md` §5).
// ---------------------------------------------------------------------------

/// `align_up(value, align)`, clamped to `cap`. The clamp fires whenever the
/// aligned offset runs past the buffer: `align_up_within(4000, 4096, 100)` is
/// `100`, not `4096`.
///
/// **Tier 1.** `ensures result <= cap` is checked.
pub fn align_up_within(value: u32, align: u32, cap: u32) -> u32 ensures result <= cap {
    clamp_u32(align_up(value, align), cap)
}

/// `array_bytes(stride, count)`, clamped to `cap`.
///
/// **Tier 1.** `ensures result <= cap` is checked.
pub fn array_bytes_within(stride: u32, count: u32, cap: u32) -> u32 ensures result <= cap {
    clamp_u32(raw_sat_mul(stride, count), cap)
}

/// `view_end(byte_offset, count, elem_bytes)`, clamped to `cap`.
///
/// **Tier 1.** `ensures result <= cap` is checked.
pub fn view_end_within(byte_offset: u32, count: u32, elem_bytes: u32, cap: u32) -> u32
ensures result <= cap {
    clamp_u32(raw_view_end(byte_offset, count, elem_bytes), cap)
}

/// `record_size2(..)`, clamped to `cap`.
///
/// **Tier 1.** `ensures result <= cap` is checked.
pub fn record_size2_within(size0: u32, align0: u32, size1: u32, align1: u32, cap: u32) -> u32
ensures result <= cap {
    clamp_u32(record_size2(size0, align0, size1, align1), cap)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The supported alignment set, spelled out. Every sweep below runs over
    /// this and over a set of unsupported values chosen to include `0`, an odd
    /// number, two non-power-of-two even numbers, and one past the ceiling.
    const SUPPORTED: [u32; 13] = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096];
    const UNSUPPORTED: [u32; 8] = [0, 3, 5, 6, 12, 100, 4097, 8192];

    // -----------------------------------------------------------------------
    // Against `core`'s own decision procedures — written by someone else, by a
    // different method.
    // -----------------------------------------------------------------------

    #[test]
    fn is_power_of_two_agrees_with_core_over_an_exhaustive_sweep_and_every_bit() {
        for n in 0u32..=8192 {
            let want = u8::from(n != 0 && n.is_power_of_two());
            assert_eq!(is_power_of_two(n), want, "n={n}");
        }
        for bit in 0u32..32 {
            let n = 1u32 << bit;
            assert_eq!(is_power_of_two(n), 1, "2^{bit}");
            assert_eq!(is_power_of_two(n.wrapping_add(1)), u8::from(bit == 0), "2^{bit}+1");
        }
        assert_eq!(is_power_of_two(0), 0, "core::u32::is_power_of_two(0) is false too");
        assert_eq!(is_power_of_two(u32::MAX), 0);
    }

    #[test]
    fn align_shift_agrees_with_core_trailing_zeros_on_the_supported_set() {
        for a in SUPPORTED {
            assert_eq!(align_shift(a), a.trailing_zeros(), "align={a}");
        }
        for a in UNSUPPORTED {
            assert_eq!(align_shift(a), 32, "unsupported align={a} must take the sentinel");
        }
    }

    #[test]
    fn align_from_shift_agrees_with_core_shl_and_inverts_align_shift() {
        for s in 0u32..=12 {
            assert_eq!(align_from_shift(s), 1u32 << s, "shift={s}");
        }
        for s in [13u32, 24, 31, 32, 33, 1000, u32::MAX] {
            assert_eq!(align_from_shift(s), 1, "out-of-range shift={s} normalises to 1");
        }
        for a in SUPPORTED {
            assert_eq!(align_from_shift(align_shift(a)), align_norm(a), "round trip at {a}");
        }
        for a in UNSUPPORTED {
            assert_eq!(align_from_shift(align_shift(a)), 1, "unsupported round trip at {a}");
        }
    }

    /// The lattice chains must agree with each other and with `core`, and
    /// `align_is_supported` must say exactly which inputs are in the set.
    #[test]
    fn the_lattice_chains_agree_with_each_other_and_with_core() {
        for a in SUPPORTED {
            assert_eq!(align_mask(a), a - 1, "mask of {a}");
            assert_eq!(align_norm(a), a, "norm of {a}");
            assert_eq!(align_is_supported(a), 1, "{a} is supported");
            assert_eq!(is_power_of_two(a), 1);
        }
        for a in UNSUPPORTED {
            assert_eq!(align_mask(a), 0, "unsupported {a} masks to 0");
            assert_eq!(align_norm(a), 1, "unsupported {a} normalises to 1");
            assert_eq!(align_is_supported(a), 0, "{a} is not supported");
        }
        // The whole domain below twice the ceiling, exhaustively: supported iff
        // a power of two at most 4096.
        for a in 0u32..=8192 {
            let want = u8::from(a != 0 && a.is_power_of_two() && a <= 4096);
            assert_eq!(align_is_supported(a), want, "align_is_supported({a})");
        }
    }

    #[test]
    fn align_max_reproduces_core_max_on_the_supported_set() {
        for a in SUPPORTED {
            for b in SUPPORTED {
                assert_eq!(align_max(a, b), a.max(b), "align_max({a},{b})");
            }
            for b in UNSUPPORTED {
                assert_eq!(align_max(a, b), a, "an unsupported {b} contributes alignment 1");
                assert_eq!(align_max(b, a), a);
            }
        }
    }

    // -----------------------------------------------------------------------
    // Against an independent oracle: a repeated-addition round-up, which shares
    // no operator with the masking implementation.
    // -----------------------------------------------------------------------

    /// `value` rounded up to a multiple of `align`, by counting. No mask, no
    /// `+ align - 1`, no `&`.
    fn oracle_align_up(value: u64, align: u64) -> u64 {
        let mut x: u64 = 0;
        while x < value {
            x += align;
        }
        x
    }

    #[test]
    fn align_up_wide_matches_the_counting_oracle_over_every_supported_alignment() {
        for a in SUPPORTED {
            for v in [0u32, 1, 2, 3, 7, 8, 15, 16, 17, 31, 63, 64, 65, 4095, 4096, 4097] {
                assert_eq!(
                    align_up_wide(v, a),
                    oracle_align_up(u64::from(v), u64::from(a)),
                    "align_up_wide({v}, {a})"
                );
            }
            assert_eq!(
                align_up_wide(u32::MAX, a),
                oracle_align_up(u64::from(u32::MAX), u64::from(a)),
                "at u32::MAX, align {a}"
            );
        }
    }

    #[test]
    fn align_up_matches_core_checked_next_multiple_of() {
        for a in SUPPORTED {
            for v in [0u32, 1, 5, 63, 64, 100, 4095, 4096, 100_000, u32::MAX - 1, u32::MAX] {
                let want = v.checked_next_multiple_of(a).unwrap_or(u32::MAX);
                assert_eq!(align_up(v, a), want, "align_up({v}, {a})");
            }
        }
    }

    /// **The overflow `module_to_lir.rs:1116` and `rustc_arena/src/lib.rs:341`
    /// have nothing bounding.** `(value + align - 1)` wraps and the "rounded
    /// up" offset comes out BELOW its own input.
    #[test]
    fn align_up_saturates_where_the_unguarded_formula_wraps_below_its_input() {
        for a in SUPPORTED {
            if a == 1 {
                continue;
            }
            // `u32::MAX` is the one input that wraps at EVERY alignment >= 2;
            // `u32::MAX - a/2` only wraps from a == 4 up, which is why the two
            // cases are separated rather than merged into one sweep.
            let wrapped = u32::MAX.wrapping_add(a - 1) & !(a - 1);
            assert!(wrapped < u32::MAX, "the unguarded formula must wrap at (u32::MAX, {a})");
            assert_eq!(align_up(u32::MAX, a), u32::MAX, "trust-align saturates instead");
            assert_eq!(
                align_up_wide(u32::MAX, a),
                oracle_align_up(u64::from(u32::MAX), u64::from(a))
            );
            if a >= 4 {
                let v = u32::MAX - a / 2;
                let w = v.wrapping_add(a - 1) & !(a - 1);
                assert!(w < v, "the unguarded formula must wrap below its input at ({v}, {a})");
                assert_eq!(align_up(v, a), u32::MAX, "trust-align saturates instead");
                assert!(align_up(v, a) >= v, "and never returns less than its input");
                assert_eq!(align_up_wide(v, a), oracle_align_up(u64::from(v), u64::from(a)));
            }
        }
        // The exact instance named in the module docs.
        assert_eq!((u32::MAX - 8).wrapping_add(16 - 1) & !(16 - 1), 0, "wraps to 0");
        assert_eq!(align_up(u32::MAX - 8, 16), u32::MAX);
    }

    /// **`trust-thir-lower/src/lib.rs:605-607` as a test rather than as prose:**
    /// *"field 0 is at `align_up(0, a) == 0` for every alignment — ALWAYS"*.
    #[test]
    fn align_up_of_zero_is_zero_at_every_supported_alignment() {
        for a in SUPPORTED {
            assert_eq!(align_up(0, a), 0, "align_up(0, {a})");
            assert_eq!(align_up_wide(0, a), 0);
            assert_eq!(field_offset2(0, a), 0, "a leading zero-sized field displaces nothing");
        }
        for a in UNSUPPORTED {
            assert_eq!(align_up(0, a), 0);
        }
    }

    #[test]
    fn align_up_is_idempotent_monotone_and_aligned_on_the_supported_set() {
        for a in SUPPORTED {
            for v in [0u32, 1, 7, 63, 64, 1000, 65_535, 1_000_000] {
                let up = align_up(v, a);
                assert!(up >= v, "align_up({v},{a})={up} must not decrease");
                assert!(up - v < a, "align_up({v},{a}) must move by less than {a}");
                assert_eq!(is_aligned(up, a), 1, "align_up({v},{a})={up} must be aligned");
                assert_eq!(align_up(up, a), up, "idempotent at ({v},{a})");
                assert_eq!(align_down(up, a), up, "align_down of an aligned value is itself");
                assert!(align_down(v, a) <= v);
                assert_eq!(is_aligned(align_down(v, a), a), 1);
                assert_eq!(align_down(v, a), v & !(a - 1), "core's own mask");
            }
        }
    }

    /// The `debug_assert!` the two cited sites rely on, and what happens without
    /// it: for a NON-power-of-two `align` the mask formula returns something
    /// that is not a multiple of `align`. `trust-align` returns the identity and
    /// says so through `align_is_supported`.
    #[test]
    fn a_non_power_of_two_align_breaks_the_mask_formula_and_normalises_here() {
        // The counterexample from the module docs, both halves.
        let five = 5u32.wrapping_add(3 - 1) & !(3 - 1);
        assert_eq!(five, 5, "the unguarded formula returns 5 for align_up(5, 3)");
        assert_ne!(five % 3, 0, "which is not a multiple of 3");
        let six = 6u32.wrapping_add(3 - 1) & !(3 - 1);
        assert_eq!(six, 8, "and 8 for align_up(6, 3)");
        assert_ne!(six % 3, 0, "also not a multiple of 3");

        for a in UNSUPPORTED {
            assert_eq!(align_is_supported(a), 0, "align={a}");
            for v in [0u32, 1, 5, 1000, u32::MAX] {
                assert_eq!(align_up(v, a), v, "an unsupported align is the identity");
                assert_eq!(align_down(v, a), v);
                assert_eq!(padding_to(v, a), 0);
                assert_eq!(is_aligned(v, a), 1, "every value is aligned to 1");
            }
        }
    }

    #[test]
    fn padding_is_the_difference_and_always_lands_below_the_alignment() {
        for a in SUPPORTED {
            for v in [0u32, 1, 7, 63, 64, 4095, 4096, 100_000] {
                let p = padding_to(v, a);
                assert_eq!(p, align_up(v, a) - v, "padding_to({v},{a})");
                assert!(p < a, "padding_to({v},{a})={p} must be < {a}");
                assert_eq!(padding_wide(v, a), u64::from(p));
                assert_eq!(is_aligned(v + p, a), 1);
            }
            let top = u64::from(u32::MAX);
            assert_eq!(padding_wide(u32::MAX, a), align_up_wide(u32::MAX, a) - top);
        }
    }

    // -----------------------------------------------------------------------
    // Against rustc's OWN layout: `size_of` / `align_of` / `offset_of!` are a
    // second, independent implementation of the same C-layout algorithm.
    // -----------------------------------------------------------------------

    #[repr(C)]
    struct ByteThenWord {
        a: u8,
        b: u32,
    }
    #[repr(C)]
    struct WordThenByte {
        a: u32,
        b: u8,
    }
    #[repr(C)]
    struct ShortThenLong {
        a: u16,
        b: u64,
    }
    #[repr(C)]
    struct ByteThenByte {
        a: u8,
        b: u8,
    }

    #[test]
    fn field_offset2_and_record_size2_reproduce_rustc_repr_c_layout() {
        macro_rules! check {
            ($t:ty, $f0:ty, $f1:ty) => {{
                let s0 = core::mem::size_of::<$f0>() as u32;
                let a0 = core::mem::align_of::<$f0>() as u32;
                let s1 = core::mem::size_of::<$f1>() as u32;
                let a1 = core::mem::align_of::<$f1>() as u32;
                assert_eq!(
                    field_offset2(s0, a1),
                    core::mem::offset_of!($t, b) as u32,
                    concat!("offset of ", stringify!($t), ".b")
                );
                assert_eq!(
                    record_size2(s0, a0, s1, a1),
                    core::mem::size_of::<$t>() as u32,
                    concat!("size_of ", stringify!($t))
                );
                assert_eq!(
                    align_max(a0, a1),
                    core::mem::align_of::<$t>() as u32,
                    concat!("align_of ", stringify!($t))
                );
                assert_eq!(record_end2(s0, a1, s1), core::mem::offset_of!($t, b) as u32 + s1);
            }};
        }
        check!(ByteThenWord, u8, u32);
        check!(WordThenByte, u32, u8);
        check!(ShortThenLong, u16, u64);
        check!(ByteThenByte, u8, u8);
    }

    /// The published layout values, spelled out rather than computed, so this
    /// test does not move with the code under test.
    #[test]
    fn the_published_layout_check_values_are_reproduced_exactly() {
        // #[repr(C)] { u8, u32 }: field 1 at 4, total 8, align 4.
        assert_eq!(field_offset2(1, 4), 4);
        assert_eq!(record_size2(1, 1, 4, 4), 8);
        assert_eq!(align_max(1, 4), 4);
        // #[repr(C)] { u32, u8 }: field 1 at 4, total 8, align 4.
        assert_eq!(field_offset2(4, 1), 4);
        assert_eq!(record_size2(4, 4, 1, 1), 8);
        // #[repr(C)] { u16, u64 }: field 1 at 8, total 16, align 8.
        assert_eq!(field_offset2(2, 8), 8);
        assert_eq!(record_size2(2, 2, 8, 8), 16);
        // #[repr(C)] { u8, u8 }: field 1 at 1, total 2, align 1.
        assert_eq!(field_offset2(1, 1), 1);
        assert_eq!(record_size2(1, 1, 1, 1), 2);
        // ELF64 program-header p_align == 0x1000 (ELF gABI).
        assert_eq!(align_up(1, 0x1000), 0x1000);
        assert_eq!(align_up(0x1001, 0x1000), 0x2000);
        assert_eq!(align_shift(0x1000), 12);
        assert_eq!(padding_to(0x1001, 0x1000), 0xFFF);
        // AArch64 AAPCS64: SP is 16-byte aligned at a public interface.
        assert_eq!(align_up(20, 16), 32);
        assert_eq!(padding_to(20, 16), 12);
        assert_eq!(align_down(20, 16), 16);
        // A 64-byte cache line.
        assert_eq!(align_up(65, 64), 128);
        assert_eq!(align_shift(64), 6);
    }

    // -----------------------------------------------------------------------
    // Arrays, strides and views.
    // -----------------------------------------------------------------------

    #[test]
    fn array_stride_and_bytes_agree_with_core_size_of_arrays() {
        assert_eq!(array_stride(core::mem::size_of::<u8>() as u32, 1), 1);
        assert_eq!(array_stride(core::mem::size_of::<u32>() as u32, 4), 4);
        assert_eq!(array_bytes_padded(1, 1, 16), core::mem::size_of::<[u8; 16]>() as u32);
        assert_eq!(array_bytes_padded(4, 4, 16), core::mem::size_of::<[u32; 16]>() as u32);
        assert_eq!(array_bytes_padded(8, 8, 3), core::mem::size_of::<[u64; 3]>() as u32);
        // A padded element: a 3-byte payload at alignment 4 strides by 4.
        assert_eq!(array_stride(3, 4), 4);
        assert_eq!(array_bytes_padded(3, 4, 10), 40);
        assert_eq!(array_bytes(3, 10), 30, "unpadded, for contrast");
    }

    #[test]
    fn array_bytes_saturates_where_the_unguarded_multiply_wraps() {
        assert_eq!(0x10000u32.wrapping_mul(0x10000), 0, "the unguarded product is 0");
        assert_eq!(array_bytes(0x10000, 0x10000), u32::MAX, "2^32 saturates instead");
        assert_eq!(array_bytes(u32::MAX, 2), u32::MAX);
        assert_eq!(array_bytes(u32::MAX, 1), u32::MAX);
        assert_eq!(array_bytes(1, 0), 0);
        assert_eq!(array_bytes(0, u32::MAX), 0);
        assert_eq!(array_bytes_padded(3, 4, 0x4000_0000), u32::MAX, "4 * 2^30 saturates");
    }

    /// **`typedarray.rs:339` as it behaves today, and as it behaves here.** The
    /// unguarded `byte_offset + length * elem` wraps to a small number and the
    /// out-of-bounds test passes; `view_fits` refuses.
    #[test]
    fn view_fits_refuses_the_wrapping_bound_check_that_typedarray_accepts() {
        // 2^28 elements of 16 bytes is exactly 2^32 — zero after a u32 wrap.
        let (off, count, elem) = (0u32, 0x1000_0000u32, 16u32);
        let wrapped = off.wrapping_add(count.wrapping_mul(elem));
        assert_eq!(wrapped, 0, "the unguarded end wraps to 0");
        assert!(wrapped <= 8, "so a wrapping check reads this view as fitting in 8 bytes");
        assert_eq!(view_fits(off, count, elem, 8), 0, "trust-align refuses it");
        assert_eq!(view_end(off, count, elem), u32::MAX, "and saturates the end");

        // Ordinary in-range behaviour, and the exact boundary.
        assert_eq!(view_end(4, 10, 8), 84);
        assert_eq!(view_fits(4, 10, 8, 84), 1, "an exactly-full view fits");
        assert_eq!(view_fits(4, 10, 8, 83), 0, "one byte short does not");
        assert_eq!(view_fits(0, 0, 8, 0), 1, "an empty view fits an empty buffer");
        assert_eq!(view_elem_offset(4, 0, 8), 4);
        assert_eq!(view_elem_offset(4, 9, 8), 76);
        // Every element of a fitting view is itself inside the buffer.
        for i in 0u32..10 {
            assert!(view_elem_offset(4, i, 8) + 8 <= 84, "element {i}");
        }
    }

    // -----------------------------------------------------------------------
    // The tier-1 bounds themselves.
    // -----------------------------------------------------------------------

    /// Every contracted clamp must be able to FIRE, or its green postcondition
    /// row constrains nothing (`docs/STRICT_VERIFICATION_FRAGMENT.md` §5).
    #[test]
    fn every_tier1_clamp_is_live_and_no_result_ever_exceeds_its_bound() {
        assert_eq!(align_up_within(4000, 4096, 100), 100, "the align clamp fires");
        assert_eq!(align_up_within(4000, 4096, 99_999), 4096, "and is transparent otherwise");
        assert_eq!(array_bytes_within(1000, 1000, 100), 100, "the array clamp fires");
        assert_eq!(array_bytes_within(10, 10, 100_000), 100, "and is transparent otherwise");
        assert_eq!(view_end_within(0, 1000, 8, 100), 100, "the view clamp fires");
        assert_eq!(view_end_within(0, 10, 8, 100), 80);
        assert_eq!(record_size2_within(1, 1, 4, 4, 2), 2, "the record clamp fires");
        assert_eq!(record_size2_within(1, 1, 4, 4, 99), 8);

        for a in SUPPORTED {
            for cap in [0u32, 1, 7, 4096, u32::MAX] {
                for v in [0u32, 1, 4000, u32::MAX] {
                    assert!(align_up_within(v, a, cap) <= cap);
                    assert!(array_bytes_within(v, a, cap) <= cap);
                    assert!(view_end_within(v, a, 8, cap) <= cap);
                    assert!(record_size2_within(v, a, 4, 4, cap) <= cap);
                }
            }
            assert!(align_mask(a) <= 4095);
            assert!(align_norm(a) <= 4096);
            assert!(align_shift(a) <= 32);
            assert!(align_from_shift(align_shift(a)) <= 4096);
            assert!(align_max(a, 4096) <= 4096);
            assert!(is_aligned(0, a) <= 1);
            assert!(align_is_supported(a) <= 1);
            assert!(is_power_of_two(a) <= 1);
            assert!(view_fits(0, 1, a, 0) <= 1);
        }
    }

    /// A CONSISTENCY test — it computes its expectation from the very function
    /// it checks, so it moves with it. Kept because it pins the masking
    /// identity across the whole supported set, and recorded here as unable to
    /// catch a wrong constant in `align_mask`: gate mutation E changes
    /// `align_mask(16)` from `15` to `7` and **this test still passes**.
    /// A test that derives its oracle from the code under test is not a test.
    #[test]
    fn align_up_agrees_with_the_mask_identity_it_is_built_from() {
        for a in SUPPORTED {
            let m = align_mask(a);
            for v in [0u32, 1, 7, 63, 1000, 65_535] {
                assert_eq!(align_up(v, a), (v + m) & !m);
                assert_eq!(align_down(v, a), v & !m);
            }
        }
    }
}
