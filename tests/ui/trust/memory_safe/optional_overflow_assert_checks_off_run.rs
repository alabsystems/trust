//@ revisions: inherit inline
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=off
//@[inline] compile-flags: -Zinline-mir=yes
//@ run-pass
//@ ignore-emscripten no processes
//! The runtime WITNESS for `optional_overflow_assert_checks_off.rs`
//! (OVF-ASSERT-ERASED-1): the same liars, built with verification OFF and overflow
//! checks OFF. The optional overflow asserts in their MIR (inherited, or inlined
//! from core) are compiled as always-succeeding, so each one WRAPS and returns a
//! value its `ensures` excludes, without a panic. The binary does not depend on the
//! verifier; this file pins the fact the sibling's annotations rest on. MEASURED
//! 2026-10-06 on the stage 1 of `0ac7a96d9f` (`inherit_run.rs`, `inline_abs_run.rs`
//! and `inline_add_run.rs` in the review probes) with these flags.

#![cfg_attr(inherit, feature(rustc_attrs))]
#![cfg_attr(inherit, allow(internal_features))]

#[cfg(inherit)]
#[inline(never)]
#[rustc_inherit_overflow_checks]
pub fn abs_like(x: i32) -> i32
    ensures result >= 0
{
    if x < 0 { -x } else { x }
}

#[cfg(inherit)]
#[inline(never)]
#[rustc_inherit_overflow_checks]
pub fn add1(x: i32) -> i32
    ensures result > x
{
    x + 1
}

#[cfg(inline)]
#[inline(never)]
pub fn inline_abs(x: i32) -> i32
    ensures result >= 0
{
    x.abs()
}

#[cfg(inline)]
#[inline(never)]
pub fn inline_add(x: i32) -> i32
    ensures result > x
{
    core::ops::Add::add(x, 1)
}

#[cfg(inline)]
#[inline(never)]
pub fn inline_neg(x: i32) -> i32
    ensures x >= 0 || result > 0
{
    core::ops::Neg::neg(x)
}

fn main() {
    #[cfg(inherit)]
    {
        assert_eq!(abs_like(std::hint::black_box(i32::MIN)), i32::MIN);
        assert_eq!(add1(std::hint::black_box(i32::MAX)), i32::MIN);
    }
    #[cfg(inline)]
    {
        assert_eq!(inline_abs(std::hint::black_box(i32::MIN)), i32::MIN);
        assert_eq!(inline_add(std::hint::black_box(i32::MAX)), i32::MIN);
        assert_eq!(inline_neg(std::hint::black_box(i32::MIN)), i32::MIN);
    }
}
