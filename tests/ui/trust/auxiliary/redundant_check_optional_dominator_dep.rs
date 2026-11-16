//@ compile-flags: --crate-type=rlib -O -Coverflow-checks=on -Ztrust-verify=off
//@ edition: 2021
//@ no-prefer-dynamic
//! RBCE-OPTIONAL-DOMINATOR-1, the dependency half. Built with overflow checks ON, so
//! its own codegen would keep the optional `OverflowNeg` assert of the inlined core
//! `Neg::neg`. Before the fix, `RedundantBoundsCheckElim` (on at -O) deleted the
//! mandatory `x / -1` overflow check under that assert, in the `#[inline]` MIR this
//! crate encodes. A consumer built with overflow checks OFF codegens that MIR and
//! erases the negate assert.

use std::ops::Neg;

#[inline]
pub fn f(x: i32) -> i32 {
    let n = x.neg();
    n.wrapping_add(x / -1)
}
