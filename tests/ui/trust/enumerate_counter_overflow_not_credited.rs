//@ needs-trust-verify
//@ revisions: certify strict
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[strict] compile-flags: -Ztrust-policy=strict
//@ rustc-env:TRUST_PF_REG_TRACE=1
//@ rustc-env:TRUST_PF_MATCH_TRACE=1
//@[certify] check-fail
//@[strict] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: fn=enumerate_counter_overflow_not_credited::skip_enumerate_u128 established=true
//@ forbid-output: fn=enumerate_counter_overflow_not_credited::enumerate_u128 established=true
//@ forbid-output: fn=enumerate_counter_overflow_not_credited::enumerate_rev_i128 established=true
//@ forbid-output: fn=enumerate_counter_overflow_not_credited::enumerate_zip_u128 established=true
//@ forbid-output: fn=enumerate_counter_overflow_not_credited::step_by_enumerate_u128 established=true
//@ forbid-output: fn=enumerate_counter_overflow_not_credited::skip_enumerate_inclusive_u64 established=true
//@ forbid-output: fn=enumerate_counter_overflow_not_credited::caller established=true
//@ forbid-output: fn=enumerate_counter_overflow_not_credited::skip_enumerate_u128 arm=registry
//@ forbid-output: fn=enumerate_counter_overflow_not_credited::enumerate_u128 arm=registry
//@ forbid-output: fn=enumerate_counter_overflow_not_credited::enumerate_rev_i128 arm=registry
//@ forbid-output: fn=enumerate_counter_overflow_not_credited::enumerate_zip_u128 arm=registry
//@ forbid-output: fn=enumerate_counter_overflow_not_credited::step_by_enumerate_u128 arm=registry
//@ forbid-output: fn=enumerate_counter_overflow_not_credited::skip_enumerate_inclusive_u64 arm=registry
//! DC-1: `Enumerate` COUNTS, and its counter can overflow. `Enumerate::next` runs
//! `self.count += 1` and `Enumerate::nth` runs `self.count = (self.count + n) + 1`,
//! both under `#[rustc_inherit_overflow_checks]`, i.e. in the CALLER's profile.
//! Over an inner iterator that can yield more than `usize::MAX` items the add
//! overflows, and `Skip::next` (which calls the inner `nth`) reaches it in ONE call.
//!
//! MEASURED before the fix (stage-1 `trustc` at `3fbce29e33a`): the body of
//! `skip_enumerate_u128` below, as `adv` in a one-function crate, built under certify
//! (exit 0) with `[PF_REG] fn=…::adv established=true nrows=1`, "1 proved … out of
//! 1 obligation(s)", and a caller inherited the credit
//! (`zero-obligation gate: all_calls_proven=true`, `established=true`). The bundle
//! trace showed why: `[ENQUEUE_SKIP] reason=gate@line53817 callee=…Iterator::next`,
//! i.e. `total_std_iterator_ty` admitted `Skip<Enumerate<Range<u128>>>` as a total
//! std iterator, so the body was never looked at. The same call in a verify-off
//! binary at `-Copt-level=0`,
//! `adv(&mut (0u128..u128::MAX).enumerate().skip(usize::MAX))`, panics with
//! `enumerate.rs:96:22: attempt to add with overflow` (exit 101); a verify-on strict
//! binary built (exit 0) and panicked the same way.
//!
//! The fix: `total_std_iterator_ty` admits `Enumerate<I>` only when `I` also passes
//! `total_std_iterator_len_fits_usize` (at most `usize::MAX` items: a slice, array or
//! str iterator, a `Range` no wider than the target pointer, a `Take`, or an adapter
//! over one of those). The bridge's `ty_is_slice_iterator_receiver` has the same
//! rule (ITER-RECV-1's `YieldBound`, 7c7d4d84989, unit-tested in
//! `crates/trust-ir-bridge/src/lower/type_shape_recognizer_tests.rs`).
//!
//! Pinned per revision, two independent ways, because the false credit needed BOTH
//! halves to be wrong (measured: with only the compiler conjunct reverted, the
//! bridge's keeps an unproved panic-freedom row and every function still reads
//! `established=false`, so the end result alone would not catch that reversion):
//!  - the COMPILER half: no call here is admitted to the type-verified total set
//!    (`forbid-output: … arm=registry`, the zero-obligation gate's trace of that set;
//!    with the compiler conjunct reverted, five of the six direct shapes print it);
//!  - the end result: no function here is registered panic-free (`forbid-output: …
//!    established=true`), and each one's registration gate is shown to have run and
//!    declined (`RAW`), so the forbids are not vacuous.
//!
//! `certify` refuses the crate; `strict` builds it with the counter's assert left to
//! the runtime check rustc keeps.
//! `step_by_enumerate_u128` and `skip_enumerate_inclusive_u64` were already refused
//! before the fix, each by ONE half: the compiler did credit the `StepBy` call, but
//! the bridge never modeled a `StepBy` advance total, so its panic-freedom row stayed
//! unproved; `total_std_iterator_ty` excludes `RangeInclusive`, so that body was
//! bundled and its members' runtime checks withheld registration. They are pinned so
//! a widening of either gate cannot bring the overflow back. Their runtime panics are real too:
//! the 2nd `next` of `(0u128..u128::MAX).enumerate().step_by(usize::MAX)` and the 1st
//! of `(0u64..=u64::MAX).enumerate().skip(usize::MAX)` panic at the same line.
//! Controls that must stay credited: `enumerate_over_bounded_iterator_stays_total.rs`.
use std::iter::{Enumerate, Rev, Skip, StepBy, Zip};
use std::ops::{Range, RangeInclusive};

/// The measured shape: `Skip::next` -> `Enumerate::nth(n)`, whose `i + 1` overflows
/// when the `n`-th item exists at index `usize::MAX`.
pub fn skip_enumerate_u128(it: &mut Skip<Enumerate<Range<u128>>>) -> Option<usize> {
    match it.next() {
        Some((i, _)) => Some(i),
        None => None,
    }
}

/// `Enumerate::next` itself: the `2^64`-th item overflows `count += 1`.
pub fn enumerate_u128(it: &mut Enumerate<Range<u128>>) -> Option<usize> {
    match it.next() {
        Some((i, _)) => Some(i),
        None => None,
    }
}

/// `Rev` does not shorten its inner.
pub fn enumerate_rev_i128(it: &mut Enumerate<Rev<Range<i128>>>) -> Option<usize> {
    match it.next() {
        Some((i, _)) => Some(i),
        None => None,
    }
}

/// A `Zip` is as long as its shorter side; both sides here are over-long.
pub fn enumerate_zip_u128(it: &mut Enumerate<Zip<Range<u128>, Range<u128>>>) -> Option<usize> {
    match it.next() {
        Some((i, _)) => Some(i),
        None => None,
    }
}

/// The generic `StepBy::next` calls the inner `nth` too.
pub fn step_by_enumerate_u128(it: &mut StepBy<Enumerate<Range<u128>>>) -> Option<usize> {
    match it.next() {
        Some((i, _)) => Some(i),
        None => None,
    }
}

/// `0u64..=u64::MAX` has `2^64` items, one more than a 64-bit `usize` can count.
pub fn skip_enumerate_inclusive_u64(
    it: &mut Skip<Enumerate<RangeInclusive<u64>>>,
) -> Option<usize> {
    match it.next() {
        Some((i, _)) => Some(i),
        None => None,
    }
}

/// A caller must not inherit a credit its callee does not have.
pub fn caller(it: &mut Skip<Enumerate<Range<u128>>>) -> bool {
    skip_enumerate_u128(it).is_some()
}

//~? RAW [PF_REG] fn=enumerate_counter_overflow_not_credited::skip_enumerate_u128 established=false
//~? RAW [PF_REG] fn=enumerate_counter_overflow_not_credited::enumerate_u128 established=false
//~? RAW [PF_REG] fn=enumerate_counter_overflow_not_credited::enumerate_rev_i128 established=false
//~? RAW [PF_REG] fn=enumerate_counter_overflow_not_credited::enumerate_zip_u128 established=false
//~? RAW [PF_REG] fn=enumerate_counter_overflow_not_credited::step_by_enumerate_u128 established=false
//~? RAW [PF_REG] fn=enumerate_counter_overflow_not_credited::skip_enumerate_inclusive_u64 established=false
//~? RAW [PF_REG] fn=enumerate_counter_overflow_not_credited::caller established=false
