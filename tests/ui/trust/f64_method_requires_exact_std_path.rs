//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//! A std `f64` method's interval is licensed only for a callee DEFINED in a real
//! sysroot crate (its compiler-minted key) whose rendering is EXACTLY
//! `{core,std}::f64::<impl f64>::{method}`, with a float destination
//! (NUM-METHOD-ANCHOR-1).
//!
//! `float_range::f64_std_method_name` wanted a `core`/`std`/`alloc` root and
//! `::f64::` ANYWHERE, then read the method off the LAST segment with its `<…>` cut
//! off. `core::cmp::max_by_key::<f64, {closure}, PhantomData<…::m::f64::cos<1>>>` — a
//! real core callee whose generic argument names a user type at `m::f64::cos` — came
//! out as `cos`, so its result got `[-1, 1]` and `v * 4.0` lost its
//! `float_overflow_to_infinity (Mul)` row (`lie1`); through `pick`, the same false
//! interval reached the caller `lie2`. `lie1(0.5, 1e308)` returns `inf`
//! (`scratchpad/scout13/S-F64METHOD/run.rs`).
//!
//! BEFORE (`scratchpad/stage1-w11fix`, the flags below plus `-Zui-testing
//! -Zdeduplicate-diagnostics=no -A unused --emit=metadata`, 2026-10-04): exit 1 (for
//! `std_sin`'s absent `sinf64` row, before and after), and `lie1`'s and `lie2`'s
//! advisory warnings say "1 obligation(s)" where the annotations say 2: the overflow
//! row is missing.
//!
//! AFTER (predicted, then measured): the annotations were derived on the
//! BEFORE compiler from a twin of this file with the module renamed `f64x` (nothing
//! else changed), which the BEFORE recognizer already refuses; checked the way
//! compiletest checks, it matches. The std controls (`std::f64::<impl f64>::{sin,
//! tanh,sqrt}` keyed `std`, `core::f64::<impl f64>::clamp` and
//! `core::time::Duration::as_secs_f64` keyed `core`) keep their intervals before and
//! after: no overflow row on `* 4.0`.
//! Measured on the stage 1 of `4463aeeb6d` (2026-10-04): every annotation below fires in
//! every revision and nothing else is reported. `lie1` and `lie2` carry the
//! `float_overflow_to_infinity` row (unknown).
//!
//! Runs with `TRUST_NO_SYSROOT_CENSUS=1` (2026-10-08, std-absent-callee): this file
//! measures float intervals, and its one fatal row was `std_sin`'s absent `sinf64`
//! call, which the sysroot panic census derives panic-free (a `#[rustc_nounwind]`
//! intrinsic); withholding the census (it only removes proof) kept that anchor.
//!
//! Trust (std-call-summaries P2, 2026-10-11): `sinf64` now carries the
//! panic-freedom-only intrinsic stamp (`tcx_marked_panic_free_intrinsic_path`), so
//! even with the census withheld that row is gone and nothing in this file is
//! fatal: `check-pass`, and `std_sin` reports the same advisory as its siblings.
//! The stamp grants no value fact, so the interval annotations below are
//! unchanged (MEASURED on the stage 1 of this change: the only diff from the
//! previous expectation is `std_sin`'s ERROR becoming its advisory WARN).
//!
//! RE-PINNED 2026-10-18 (the 1.101 toolchain migration): upstream replaced
//! the sized float intrinsics with one generic `sin` whose fallback body
//! dispatches into `libm`, which the stamp's pin cannot follow, so the
//! stamp is LOST for the transcendentals (docs/DECISION_QUEUE.md,
//! "transcendental panic-free stamp lost"). With the census withheld,
//! `std_sin`'s absent generic-intrinsic row is fatal again exactly as in
//! the BEFORE above: `check-fail`, its annotation back to ERROR. The
//! interval rows this file exists to measure are unchanged.

#![allow(non_camel_case_types)]
use core::marker::PhantomData;
use std::time::Duration;

/// A user type at the path `m::f64::cos`.
pub mod m {
    pub mod f64 {
        pub struct cos<const N: usize>;
    }
}

/// `core::cmp::max_by_key::<f64, {closure}, PhantomData<…::m::f64::cos<1>>>` — a
/// real core callee whose rendering contains `::f64::` and whose last segment is
/// `cos<1>>>` — got `cos`'s `[-1, 1]`, and `v * 4.0` lost its overflow row.
pub fn lie1(a: f64, b: f64) -> f64 {
    //~^ WARN Trust Level 0 safety verification incomplete for `f64_method_requires_exact_std_path::lie1`: 1 obligation(s) were not proved
    //~^^ WARN Trust verification advisory for `f64_method_requires_exact_std_path::lie1`: 2 obligation(s) were not fully verified
    let v = core::cmp::max_by_key(a, b, |_x| PhantomData::<m::f64::cos<1>>);
    v * 4.0
}

/// The same through a helper whose return interval is traced into `lie2`.
#[inline(never)]
pub fn pick(b: f64) -> f64 {
    //~^ WARN Trust Level 0 safety verification incomplete for `f64_method_requires_exact_std_path::pick`: 1 obligation(s) were not proved
    //~^^ WARN Trust verification advisory for `f64_method_requires_exact_std_path::pick`: 1 obligation(s) were not fully verified
    core::cmp::max_by_key(0.5, b, |_x| PhantomData::<m::f64::cos<1>>)
}

pub fn lie2(b: f64) -> f64 {
    //~^ WARN Trust Level 0 safety verification incomplete for `f64_method_requires_exact_std_path::lie2`: 1 obligation(s) were not proved
    //~^^ WARN Trust verification advisory for `f64_method_requires_exact_std_path::lie2`: 2 obligation(s) were not fully verified
    let v = pick(b);
    v * 4.0
}

// std's own `f64` methods and `Duration::as_secs_f64` keep their intervals: no
// `float_overflow_to_infinity` row on `* 4.0`.
pub fn std_sin(x: f64) -> f64 {
    //~^ WARN Trust Level 0 safety verification incomplete for `f64_method_requires_exact_std_path::std_sin`: 1 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `f64_method_requires_exact_std_path::std_sin`
    x.sin() * 4.0
}

pub fn std_tanh(x: f64) -> f64 {
    //~^ WARN Trust Level 0 safety verification incomplete for `f64_method_requires_exact_std_path::std_tanh`: 1 obligation(s) were not proved
    //~^^ WARN Trust verification advisory for `f64_method_requires_exact_std_path::std_tanh`: 1 obligation(s) were not fully verified
    x.tanh() * 4.0
}

pub fn std_sqrt(x: f64) -> f64 {
    //~^ WARN Trust Level 0 safety verification incomplete for `f64_method_requires_exact_std_path::std_sqrt`: 1 obligation(s) were not proved
    //~^^ WARN Trust verification advisory for `f64_method_requires_exact_std_path::std_sqrt`: 1 obligation(s) were not fully verified
    x.clamp(0.0, 4.0).sqrt() * 4.0
}

pub fn std_secs(d: Duration) -> f64 {
    //~^ WARN Trust Level 0 safety verification incomplete for `f64_method_requires_exact_std_path::std_secs`: 1 obligation(s) were not proved
    //~^^ WARN Trust verification advisory for `f64_method_requires_exact_std_path::std_secs`: 1 obligation(s) were not fully verified
    d.as_secs_f64() * 4.0
}
