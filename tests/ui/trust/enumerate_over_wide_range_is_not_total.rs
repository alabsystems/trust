//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[default] check-pass
//@[certify] check-fail
//@ dont-check-compiler-stderr
//! `Enumerate` counts its items in a `usize`, so it is total only over a base that
//! yields at most `usize::MAX` items (ITER-RECV-1).
//!
//! std's `Enumerate::next` does `count += 1` and `nth(n)` does `count + n` then
//! `+ 1`, under `#[rustc_inherit_overflow_checks]`. `ty_is_slice_iterator_receiver`
//! recursed through `Enumerate` (and `Skip`/`Take`/`Peekable`/... over it) into any
//! all-`Int` `Range`, so `(0u128..u128::MAX).enumerate().skip(usize::MAX).next()`
//! read `unreach proved` only and was Clean-kernel certified (`1 kernel-certified`).
//! It panics `attempt to add with overflow` in core's enumerate.rs (the witness,
//! `enumerate_over_wide_range_is_not_total_run.rs`). `step` and `skip_first` are the
//! receiver-typed forms of the same lie.
//!
//! BEFORE (stage 1 of `38e6c69b1c`, `scratchpad/stage1-w11fix`, 2026-10-04; each
//! revision's flags with `--emit=metadata`): both revisions built exit 0 with no
//! Trust diagnostic; every function read `unreach proved` only. The annotations
//! below did not fire.
//!
//! AFTER (predicted, then measured): under an `Enumerate` a base must meet a
//! yield bound: a slice/array/`Vec`/map/set iterator always does; a `Range<IntN>`
//! only when `N` is at most the `usize` width the `Enumerate`'s own `count` field
//! shows (64 here), a `RangeInclusive<IntN>` only when `N` is below it. A
//! `Range<u128>` fails, so the `skip`/`next` calls fall to the bundled std members,
//! whose internal overflow `Assert` is charged. The annotations are what the BEFORE
//! compiler prints for a twin of this file with `Range<u128>` replaced by
//! `RangeFrom<u128>` (which no total arm recognizes): default `runtime-checked`
//! rows `bundled std member <Enumerate<…> as Iterator>::{next,nth}` and
//! `<u128 as Step>::forward` with three WARNs per function, certify three ERRORs per
//! function. A second twin with `RangeInclusive<u64>` printed the same diagnostics.
//! Measured on the stage 1 of `4463aeeb6d` (2026-10-04): the lie is gone, but not by the
//! predicted path. The `Range<u128>` calls are not bundled: each lie function's one
//! non-proved row is `[trust-absent-callee-assumption] call to absent callee
//! <Enumerate<Range<u128>> as Iterator>::skip` (`::next` for `step`, `<Skip<…>>::next`
//! for `skip_first`), runtime-checked, so default prints two WARNs per function (Level 0,
//! advisory) and certify two ERRORs (Level 0, strict). The twins' third diagnostic (a
//! bundled std member's internal `Assert`) does not appear, and its annotations were
//! removed. The controls still read `unreach proved`.
//!
//! Measured on the stage 1 of Trust `db99bd5238b` (2026-10-10), which carries DC-1's
//! compiler half (`total_std_iterator_ty` asks an `Enumerate`'s yield bound, so
//! `Enumerate<Range<u128>>` no longer enters the total-iterator registry): the calls are
//! bundled again, the path first predicted. Default prints three WARNs per function
//! (Level 0; the advisory for the one row; the bundled std member's internal
//! obligation), certify three ERRORs (Level 0; strict; certify's bundled-member
//! `Assert`), and the annotations name each. The controls are unchanged.
//!
//! The controls carry no annotation and read `unreach proved` in both revisions,
//! BEFORE and in both twins: `(0u32..10).enumerate()`, `(0..n).enumerate()` over a
//! `usize` range (64 bits, at most `usize::MAX` items) and `v.iter().enumerate()`
//! over a slice.

pub fn always_panics() -> usize {
    //[default]~^ WARN Trust Level 0 safety verification incomplete for `enumerate_over_wide_range_is_not_total::always_panics`
    //[default]~^^ WARN Trust verification advisory for `enumerate_over_wide_range_is_not_total::always_panics`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `enumerate_over_wide_range_is_not_total::always_panics`
    //[certify]~^^^^ ERROR Trust strict verification failed for `enumerate_over_wide_range_is_not_total::always_panics`
    //[default]~^^^^^ WARN Trust verification advisory for `enumerate_over_wide_range_is_not_total::always_panics`: a bundled std/core/alloc member's internal obligation was not statically discharged
    //[certify]~^^^^^^ ERROR Trust certify verification failed for `enumerate_over_wide_range_is_not_total::always_panics`: a bundled std/core/alloc member's internal Assert is left to a runtime check
    let mut e = (0u128..u128::MAX).enumerate().skip(usize::MAX);
    match e.next() {
        Some((i, _)) => i,
        None => 0,
    }
}

pub fn step(e: &mut core::iter::Enumerate<core::ops::Range<u128>>) -> usize {
    //[default]~^ WARN Trust Level 0 safety verification incomplete for `enumerate_over_wide_range_is_not_total::step`
    //[default]~^^ WARN Trust verification advisory for `enumerate_over_wide_range_is_not_total::step`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `enumerate_over_wide_range_is_not_total::step`
    //[certify]~^^^^ ERROR Trust strict verification failed for `enumerate_over_wide_range_is_not_total::step`
    //[default]~^^^^^ WARN Trust verification advisory for `enumerate_over_wide_range_is_not_total::step`: a bundled std/core/alloc member's internal obligation was not statically discharged
    //[certify]~^^^^^^ ERROR Trust certify verification failed for `enumerate_over_wide_range_is_not_total::step`: a bundled std/core/alloc member's internal Assert is left to a runtime check
    match e.next() {
        Some((i, _)) => i,
        None => 0,
    }
}

pub fn skip_first(mut e: core::iter::Skip<core::iter::Enumerate<core::ops::Range<u128>>>) -> usize {
    //[default]~^ WARN Trust Level 0 safety verification incomplete for `enumerate_over_wide_range_is_not_total::skip_first`
    //[default]~^^ WARN Trust verification advisory for `enumerate_over_wide_range_is_not_total::skip_first`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `enumerate_over_wide_range_is_not_total::skip_first`
    //[certify]~^^^^ ERROR Trust strict verification failed for `enumerate_over_wide_range_is_not_total::skip_first`
    //[default]~^^^^^ WARN Trust verification advisory for `enumerate_over_wide_range_is_not_total::skip_first`: a bundled std/core/alloc member's internal obligation was not statically discharged
    //[certify]~^^^^^^ ERROR Trust certify verification failed for `enumerate_over_wide_range_is_not_total::skip_first`: a bundled std/core/alloc member's internal Assert is left to a runtime check
    match e.next() {
        Some((i, _)) => i,
        None => 0,
    }
}

pub fn std_u32_range() -> usize {
    let mut last = 0usize;
    for (i, _x) in (0u32..10).enumerate() {
        last = i;
    }
    last
}

pub fn std_usize_range(n: usize) -> usize {
    let mut last = 0usize;
    for (i, _x) in (0..n).enumerate() {
        last = i;
    }
    last
}

pub fn std_slice(v: &[u8]) -> usize {
    let mut last = 0usize;
    for (i, _x) in v.iter().enumerate() {
        last = i;
    }
    last
}
