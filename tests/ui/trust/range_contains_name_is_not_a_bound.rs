//@ revisions: default certify memsafe
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[memsafe] compile-flags: -Ztrust-policy=memory-safe
//@ check-fail
//@ dont-check-compiler-stderr
//! A type NAMED `RangeInclusive` is not std's range (EXTRACT-REWRITE-1).
//!
//! The extractor's proof-only `rewrite_range_contains_calls` turned
//! `r = <range>.contains(&x)` into `r = (x >= lo) & (x <= hi)`, reading `lo`/`hi`
//! from the range constant. It identified the range by the RENDERED callee path:
//! `ends_with("::contains")` and `contains("RangeInclusive")` (or `contains("ops::")`
//! and `contains("Range")`). `victim` below calls the inherent `contains` of a USER
//! `struct RangeInclusive<T>(T, T)` that answers `true` for every item; the rewrite
//! wrote `x <= 10` into the guard, and `arr[x as usize]` was proved in bounds.
//! `victim_exclusive` is the same through a user `ops::Range`.
//!
//! BEFORE (stage 1 of `38e6c69b1c`, `scratchpad/stage1-w11fix`, each revision's flags
//! with `--emit=metadata`, 2026-10-04): in every revision `victim` and
//! `victim_exclusive` read `bounds proved` (ay-in-process), the report counted the row
//! "kernel-certified by the clean CIC kernel", and neither function had a diagnostic,
//! so none of their annotations below fired. The bounds check itself is kept (only
//! overflow checks are elided), so `victim(1001)` still panics at run time
//! (`range_contains_name_is_not_a_bound_run.rs`): the lie is the verdict.
//!
//! For std the rewrite was DEAD. std's `contains` is generic over the item type, so its
//! rendering always ends in a turbofish (`core::ops::range::RangeInclusive::<u32>::
//! contains::<u32>`) and never ends with `::contains`. `std_const_inclusive` (a `const`
//! std range) is refused BEFORE with exactly the diagnostics annotated below.
//!
//! AFTER (predicted, then measured): the rewrite is deleted, so nothing is
//! rewritten and each victim's bounds row is refuted. The annotations are what the
//! BEFORE compiler prints for a twin of this file, line for line, in which the two user
//! types are renamed (`RngIncl`, `opz::Rng`) so that the old name test cannot match:
//! exactly the "no rewrite" behaviour the deletion leaves. Under memory-safe a refuted
//! bounds row is a reachable panic, which that policy reports as a warning.
//! `std_const_inclusive` prints the same before and after; a future revival of the
//! rewrite for std (DECISION_QUEUE EXTRACT-REWRITE-1) moves it, and must re-pin it.
//! `guarded` is the control: a genuine `x <= 10` guard proves in every revision.
//! Measured on the stage 1 of `4463aeeb6d` (2026-10-04): every annotation below fires in
//! every revision and nothing else is reported. Both victims read `bounds failed` under
//! default and certify (memory-safe: the panic is skipped as an assumption); `guarded`
//! stays proved.

// A user type literally named `RangeInclusive`, whose inherent `contains` answers
// `true` for every item.
pub struct RangeInclusive<T>(pub T, pub T);

impl RangeInclusive<u32> {
    #[inline(never)]
    pub fn contains(&self, _x: &u32) -> bool {
        true
    }
}

const R: RangeInclusive<u32> = RangeInclusive(0, 10);

pub fn victim(x: u32) -> u8 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `range_contains_name_is_not_a_bound::victim`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `range_contains_name_is_not_a_bound::victim`: 1 obligation(s) were not fully verified
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `range_contains_name_is_not_a_bound::victim`: 1 obligation(s) were not proved
    let arr = [7u8; 11];
    if R.contains(&x) { arr[x as usize] } else { 0 }
}

// The exclusive spelling: a user `ops::Range`.
pub mod ops {
    pub struct Range<T>(pub T, pub T);

    impl Range<u32> {
        #[inline(never)]
        pub fn contains(&self, _x: &u32) -> bool {
            true
        }
    }
}

const RX: ops::Range<u32> = ops::Range(0, 11);

pub fn victim_exclusive(x: u32) -> u8 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `range_contains_name_is_not_a_bound::victim_exclusive`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `range_contains_name_is_not_a_bound::victim_exclusive`: 1 obligation(s) were not fully verified
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `range_contains_name_is_not_a_bound::victim_exclusive`: 1 obligation(s) were not proved
    let arr = [7u8; 11];
    if RX.contains(&x) { arr[x as usize] } else { 0 }
}

// std's own `contains` on a `const` std range: never rewritten, before or after.
const SR: core::ops::RangeInclusive<u32> = 0..=10;

pub fn std_const_inclusive(x: u32) -> u8 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `range_contains_name_is_not_a_bound::std_const_inclusive`: 2 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `range_contains_name_is_not_a_bound::std_const_inclusive`: 2 obligation(s) were not fully verified
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `range_contains_name_is_not_a_bound::std_const_inclusive`: 2 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `range_contains_name_is_not_a_bound::std_const_inclusive`: at least one result is not an authenticated memory-safe assumption
    let arr = [7u8; 11];
    if SR.contains(&x) { arr[x as usize] } else { 0 }
}

// Control: the bounds lane proves a genuinely guarded index.
pub fn guarded(x: u32) -> u8 {
    let arr = [7u8; 11];
    if x <= 10 { arr[x as usize] } else { 0 }
}
