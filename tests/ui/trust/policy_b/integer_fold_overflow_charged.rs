//@ needs-trust-verify
//@ edition: 2021
//@ revisions: refused bounded map_unmodeled
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[refused] check-fail
//@[bounded] check-pass
//@[map_unmodeled] check-fail
//@[map_unmodeled] forbid-output: guaranteed Level 0 safety violation
//@[map_unmodeled] forbid-output: [overflow:add] FAILED
//@[map_unmodeled] forbid-output: [overflow:mul] FAILED
//! INTEGER `sum`/`product` OVERFLOW (measured 2026-09-25 on stage-1
//! `ab7e41892`): a FALSE ACCEPT class. `v.iter().sum::<u32>()` built rc=0 with
//! NO verification output at all and panicked "attempt to add with overflow" on
//! `[u32::MAX, 1]`; `(1..=n).product::<i32>()` did the same at `n = 20`.
//!
//! vcgen HAD a recognizer for this (`iterator_integer_fold_call`), and it never
//! fired: it matched the bare `…::Iterator::sum` spelling, while rustc renders
//! `<core::slice::iter::Iter<'_, u32> as core::iter::traits::iterator::Iterator>
//! ::sum::<u32>`, whose second-to-last segment is `Iterator>`.
//!
//! The row is now a caller-value overflow, like `a + b`:
//!
//!   * `refused` — sums and products whose item count is not bounded, or whose
//!     count a guard does not bound, are refused. That includes the ordinary
//!     sweep programs `t19` and `s24` (a sum of widened bytes over a slice of
//!     any length), which really overflow at ~8.5M pairs.
//!   * `bounded` — a float sum (saturates, never panics), `Wrapping` (wraps), a
//!     range whose count a guard bounds, and a constant range still verify; so
//!     does a one-item `map` source, whose single item cannot overflow whatever
//!     the closure returns.
//!   * `map_unmodeled` (CL-FOLD-MAP-FORCED-1, 2026-10-11) — a range whose items
//!     pass through `map` (or `filter_map`/`map_while`/`scan`) has a bounded
//!     COUNT but items whose range is not modelled. The lane defaulted each item
//!     to the accumulator's MAX and minted an ordinary refutable row, so with a
//!     constant count of 4 `4 * MAX > MAX` folded to true: on the stage 1 of
//!     `2bf0ad72e3` (`scratchpad/stage1-w22probe`) every function below printed
//!     `[overflow:add] FAILED` (`[overflow:mul] FAILED` for the product) with a
//!     "counterexample" holding only the range's fields, plus "Trust verification
//!     found 1 guaranteed Level 0 safety violation(s)", although none of them can
//!     overflow (`ones` returns 4). They are now the same honest
//!     `iterator-fold-overflow` Unknown as a slice source: still refused (no
//!     runtime fallback), never refuted.
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14). The soundness line's fold
//! preprocessing (the map summary of the closure, fed into CL-FOLD-MAP-FORCED-1's
//! match) now bounds the item when the closure's result is: `ones`
//! (`(0..4).map(|_| 1u32).sum()`, kernel-certified) and `take_after_map` (whose fold
//! row is proved; the `RangeFrom`/`Take` members it bundles keep their own
//! `runtime_checked` rows, a default-policy warning) verify, and are the controls of
//! that bound. A map whose result is a constant that DOES overflow is refuted, not
//! proved (`refused`: `mapped_quarters`, `take_mapped_quarters`, each witnessed by
//! arithmetic: 4 items of `2^30` is `2^32`); the remaining `map_unmodeled` shapes
//! still bound nothing (`map_fn_item`, `mapped_product`, `signed_map`).

use std::num::Wrapping;

// ---- refused ----

#[cfg(refused)]
pub fn slice_sum_u32(v: &[u32]) -> u32 {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `integer_fold_overflow_charged::slice_sum_u32`
    v.iter().sum::<u32>()
}

#[cfg(refused)]
pub fn range_product_i32(n: i32) -> i32 {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `integer_fold_overflow_charged::range_product_i32`
    (1..=n).product::<i32>()
}

/// Sweep `t19`: every item is at most 510, but the slice has no length bound.
#[cfg(refused)]
pub fn sum_widened_pairs(v: &[(u8, u8)]) -> u32 {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `integer_fold_overflow_charged::sum_widened_pairs`
    v.iter().map(|(a, b)| *a as u32 + *b as u32).sum()
}

/// `Sum<Option<U>> for Option<T>` runs `T`'s own overflowing fold.
#[cfg(refused)]
pub fn option_sum(v: &[u32]) -> Option<u32> {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `integer_fold_overflow_charged::option_sum`
    v.iter().map(|x| Some(*x)).sum::<Option<u32>>()
}

/// The direct trait spelling of the same fold.
#[cfg(refused)]
pub fn sum_trait_direct(v: &[u64]) -> u64 {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `integer_fold_overflow_charged::sum_trait_direct`
    <u64 as std::iter::Sum<&u64>>::sum(v.iter())
}

/// A range whose count nothing bounds.
#[cfg(refused)]
pub fn unguarded_range_sum(a: u64, b: u64) -> u64 {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `integer_fold_overflow_charged::unguarded_range_sum`
    (a..b).sum::<u64>()
}

/// The NEGATIVES of the mapped-item bound (2026-10-15): a constant item that does
/// overflow. Four items of `2^30` sum to `2^32`.
#[cfg(refused)]
pub fn mapped_quarters() -> u32 {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `integer_fold_overflow_charged::mapped_quarters`
    (0..4usize).map(|_i| 0x4000_0000u32).sum::<u32>()
}

#[cfg(refused)]
pub fn take_mapped_quarters() -> u32 {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `integer_fold_overflow_charged::take_mapped_quarters`
    (0usize..).map(|_| 0x4000_0000u32).take(4).sum::<u32>()
}

// ---- bounded: must still verify ----

#[cfg(bounded)]
pub fn float_sum(v: &[f64]) -> f64 {
    v.iter().sum::<f64>()
}

#[cfg(bounded)]
pub fn wrapping_sum(v: &[u32]) -> Wrapping<u32> {
    v.iter().copied().map(Wrapping).sum::<Wrapping<u32>>()
}

#[cfg(bounded)]
pub fn guarded_range_sum(n: u64) -> u64 {
    if n <= 1000 { (0..n).sum::<u64>() } else { 0 }
}

#[cfg(bounded)]
pub fn constant_range_sum() -> u32 {
    (1..=100u32).sum::<u32>()
}

#[cfg(bounded)]
pub fn one_mapped_item() -> u32 {
    (0..1usize).map(|_| 7u32).sum::<u32>()
}

// ---- map_unmodeled: refused, never refuted ----

#[cfg(map_unmodeled)]
pub fn ones() -> u32 {
    (0..4usize).map(|_i| 1u32).sum::<u32>()
}

#[cfg(map_unmodeled)]
pub fn map_fn_item() -> u32 {
    //[map_unmodeled]~^ ERROR Trust Level 0 safety verification incomplete for `integer_fold_overflow_charged::map_fn_item`
    (0..4u32).map(u32::from).sum::<u32>()
}

#[cfg(map_unmodeled)]
pub fn mapped_product() -> u32 {
    //[map_unmodeled]~^ ERROR Trust Level 0 safety verification incomplete for `integer_fold_overflow_charged::mapped_product`
    (0..4usize).map(|_i| 2u32).product::<u32>()
}

#[cfg(map_unmodeled)]
pub fn take_after_map() -> u32 {
    (0usize..).map(|_| 1u32).take(4).sum::<u32>()
}

#[cfg(map_unmodeled)]
pub fn signed_map() -> i32 {
    //[map_unmodeled]~^ ERROR Trust Level 0 safety verification incomplete for `integer_fold_overflow_charged::signed_map`
    (0..3i32).map(|x| x - 1).sum::<i32>()
}
