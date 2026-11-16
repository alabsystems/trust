//@ needs-trust-verify
//@ edition: 2021
//@ aux-crate: core=numeric_family_impostor/core.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A FORGED `core` THAT RENDERS THE NUMERIC FAMILY'S SPELLINGS STAYS REFUSED (wave 23,
//! STAMPED-CORE-MINT-1 residual, 2026-10-11).
//!
//! `numeric_panic::numeric_value_panic_row` and `numeric_overflow_call` now read the
//! callee past ONE well-formed leading extractor stamp, so a STAMPED GENUINE core keeps
//! its `ilog2`, `strict_add` and `Ord::clamp` rows
//! (`stamped_genuine_core_rows_kept.rs`, revision `family`). The extractor gives a
//! FORGED core the same spelling behind a stamp of its own id. This crate is
//! `#![no_core]`, and the auxiliary (`auxiliary/numeric_family_impostor/core.rs`,
//! crate name `core`, verify-off, `--extern core=`) defines `num::<impl u32>::ilog2`,
//! `num::<impl u32>::strict_add` and `cmp::Ord::clamp` for `i32`. Each panics on an
//! argument that core's own method accepts. So the forged calls render
//! `__trust_crate@<id>::core::num::<impl u32>::ilog2` and
//! `__trust_crate@<id>::<i32 as core::cmp::Ord>::clamp`, exactly the spellings the
//! family now reads past.
//!
//! What this pins: reading past the stamp only ADDS rows. Under the guard in each
//! `*_guarded` function, the row that core's method would owe is provable, and it must
//! not let the call through. The forged body's own panic is charged only by the
//! call's absent-callee row, which the default policy does not tolerate for a
//! non-resident `core`, so every function stays refused. An unguarded call may now
//! also carry the row core's method would owe: a false red at worst, and it is refused
//! either way.
//!
//! MEASURED on the stage 1 of `5911b1325f` (before the fix), this file's flags plus
//! `--emit=metadata`, the aux built with its own flags: exit 1, and each function is
//! refused with "Trust strict verification failed for `…`: 1 obligation(s) were not
//! fully verified", on the `[trust-absent-callee-assumption]` row of
//! `__trust_crate@<id>::core::num::<impl u32>::ilog2` (and of `strict_add`
//! and `<i32 as core::cmp::Ord>::clamp`). MEASURED after the fix (stage 1 of `999b006b87`):
//! the same refusals, with the minted row beside the absent-callee row (proved under
//! the guards, open without them). Fix the compiler, not this file.
#![feature(no_core)]
#![no_core]

extern crate core;

use core::cmp::Ord;

pub fn forged_ilog2_guarded(x: u32) -> u32 {
    //~^ ERROR Trust strict verification failed for `stamped_forged_core_numeric_family_refused::forged_ilog2_guarded`
    if x > 0 { x.ilog2() } else { 0 }
}

pub fn forged_strict_add_guarded(a: u32, b: u32) -> u32 {
    //~^ ERROR Trust strict verification failed for `stamped_forged_core_numeric_family_refused::forged_strict_add_guarded`
    if a < 1000 && b < 1000 { a.strict_add(b) } else { 0 }
}

pub fn forged_clamp_guarded(x: i32, lo: i32, hi: i32) -> i32 {
    //~^ ERROR Trust strict verification failed for `stamped_forged_core_numeric_family_refused::forged_clamp_guarded`
    if lo <= hi { x.clamp(lo, hi) } else { lo }
}

pub fn forged_ilog2_unguarded(x: u32) -> u32 {
    //~^ ERROR Trust strict verification failed for `stamped_forged_core_numeric_family_refused::forged_ilog2_unguarded`
    x.ilog2()
}

pub fn forged_strict_add_unguarded(a: u32, b: u32) -> u32 {
    //~^ ERROR Trust strict verification failed for `stamped_forged_core_numeric_family_refused::forged_strict_add_unguarded`
    a.strict_add(b)
}

pub fn forged_clamp_unguarded(x: i32, lo: i32, hi: i32) -> i32 {
    //~^ ERROR Trust strict verification failed for `stamped_forged_core_numeric_family_refused::forged_clamp_unguarded`
    x.clamp(lo, hi)
}
