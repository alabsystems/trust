//@ needs-trust-verify
//@ edition: 2021
//@ revisions: int_cast_store
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
#![allow(dead_code)]
//! Trust (2026-10-01, raw-store soundness): a store through a raw pointer keeps
//! its four `[unsafe:sep:*]` rows (null, allocation validity, alignment, write
//! permission) WHATEVER its source is.
//!
//! The separation engine's `interpret_assign` used to match the RVALUE before the
//! store: the raw-read, pointer-arithmetic, cast and address-of arms all came
//! before the raw-write arm, so a store whose source matched one of them minted no
//! row for the store at all. A `Cast` is the source rustc does not stage in a
//! temp, so `*p = x as u32` reached it end to end: on main it kept no
//! `[unsafe:sep:*]` row, and only the extractor's two Unknown rows kept it red.
//! The revision pins the failed-row COUNT that includes the store's four
//! (measured: 0 failed, 2 unknown on the stage-1 `trustc` of main 123f22d17).
//! A pointer cast (`*pp = q as *const u32`) does not reach the gap: rustc stages
//! that value in a temp, and the store kept its four rows on main.

#[cfg(int_cast_store)]
pub unsafe fn store(p: *mut u32, x: u64) { unsafe { *p = x as u32; } }
//[int_cast_store]~^ ERROR safety verification incomplete
//[int_cast_store]~| NOTE 4× [hardened_unsafe_operation] FAILED

