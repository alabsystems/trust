//@ run-fail
//@ edition: 2021
//@ revisions: div rem div64 rem64
//@ compile-flags: -O -Coverflow-checks=off -Ztrust-verify=off
//@[div] error-pattern: attempt to divide with overflow
//@[div64] error-pattern: attempt to divide with overflow
//@[rem] error-pattern: attempt to calculate the remainder with overflow
//@[rem64] error-pattern: attempt to calculate the remainder with overflow
//@ ignore-emscripten no processes
//! RBCE-OPTIONAL-DOMINATOR-1: a MANDATORY overflow check deleted under an OPTIONAL one.
//!
//! `x / -1` and `x % -1` overflow at `MIN`, and that check is mandatory: it panics
//! whatever `-Coverflow-checks` says. `x.neg()` is core's `Neg::neg`, marked
//! `#[rustc_inherit_overflow_checks]`, whose `OverflowNeg` assert is OPTIONAL: codegen
//! erases it when overflow checks are off. After inlining, GVN gives both asserts one
//! condition local, `Eq(x, MIN)`, and the negate assert dominates.
//!
//! BEFORE (a pre-fix stage 1, `scratchpad/stage1-w22probe`, measured 2026-10-11; the
//! pass source there is byte-identical to `2bf0ad72e3`): `RedundantBoundsCheckElim`
//! read the dominating negate assert as a guarantee and turned the mandatory overflow
//! assert into a `goto`. Codegen then erased the negate assert, so `x / -1` at `MIN`
//! ran an unguarded `sdiv` (UB in safe Rust). Every revision exited 0, printing `0`
//! (`div`, `div64`) or `MIN` (`rem`, `rem64`). The same program built with
//! `-Zmir-enable-passes=-RedundantBoundsCheckElim` panics, as stock rustc does.
//!
//! AFTER: an optional overflow assert never counts as a dominator, the mandatory check
//! survives, and the program panics (exit 101).

use std::hint::black_box;
use std::ops::Neg;

#[cfg(div)]
#[inline(never)]
fn f(x: i32) -> i32 {
    let n = x.neg();
    n.wrapping_add(x / -1)
}

#[cfg(rem)]
#[inline(never)]
fn f(x: i32) -> i32 {
    let n = x.neg();
    n.wrapping_add(x % -1)
}

#[cfg(div64)]
#[inline(never)]
fn f(x: i64) -> i64 {
    let n = x.neg();
    n.wrapping_add(x / -1)
}

#[cfg(rem64)]
#[inline(never)]
fn f(x: i64) -> i64 {
    let n = x.neg();
    n.wrapping_add(x % -1)
}

fn main() {
    #[cfg(any(div, rem))]
    let r = f(black_box(i32::MIN)) as i64;
    #[cfg(any(div64, rem64))]
    let r = f(black_box(i64::MIN));
    // Reaching this line means the mandatory overflow check was deleted.
    println!("{r}");
}
