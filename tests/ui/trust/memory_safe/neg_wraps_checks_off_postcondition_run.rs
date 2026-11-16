//@ revisions: ens idx
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=off
//@[ens] run-pass
//@[idx] run-fail
//@[idx] error-pattern: index out of bounds: the len is 8 but the index is 18446744071562067968
//@ ignore-emscripten no processes
//! The runtime WITNESS for `neg_wraps_checks_off_postcondition.rs` (NEG-WRAP-OFF-1):
//! the same liars and the same `idx`, built with verification OFF and overflow
//! checks OFF. `-MIN` wraps to `MIN` without a panic, so every liar returns a value
//! its `ensures` excludes (`ens`), and `idx(i32::MIN)` reaches `a[n as usize]` with
//! `n == i32::MIN` (`idx`). Before the fix the sibling's `off_liars` revision PROVED
//! every one of those postconditions and its `off_idx` revision PROVED the bounds row.
//!
//! MEASURED 2026-10-05 on scratchpad `stage1-w16` with these flags: `ens` exits 0
//! (every assertion below holds) and `idx` panics with the pattern above, exit 101.
//! The binary does not depend on the verifier, so the fix does not change it; the
//! file pins the fact the sibling's annotations rest on.

#[inline(never)]
pub fn abs_like(x: i32) -> i32
    ensures result >= 0
{
    if x < 0 { -x } else { x }
}

#[inline(never)]
pub fn neg_post(x: i32) -> i32
    ensures x >= 0 || result > 0
{
    -x
}

#[inline(never)]
pub fn neg_ne(x: i32) -> i32
    ensures result != x || x == 0
{
    -x
}

#[inline(never)]
pub fn neg_i8(x: i8) -> i8
    ensures x >= 0 || result > 0
{
    -x
}

#[inline(never)]
pub fn neg_i64(x: i64) -> i64
    ensures x >= 0 || result > 0
{
    -x
}

#[inline(never)]
pub fn neg_isize(x: isize) -> isize
    ensures x >= 0 || result > 0
{
    -x
}

#[inline(never)]
pub fn idx(x: i32) -> u8 {
    let a = [1u8; 8];
    if x < 0 {
        let n = -x;
        if n > 0 { 0 } else { a[n as usize] }
    } else {
        0
    }
}

fn main() {
    use std::hint::black_box;
    if cfg!(ens) {
        assert_eq!(abs_like(black_box(i32::MIN)), i32::MIN);
        assert_eq!(neg_post(black_box(i32::MIN)), i32::MIN);
        assert_eq!(neg_ne(black_box(i32::MIN)), i32::MIN);
        assert_eq!(neg_i8(black_box(i8::MIN)), i8::MIN);
        assert_eq!(neg_i64(black_box(i64::MIN)), i64::MIN);
        assert_eq!(neg_isize(black_box(isize::MIN)), isize::MIN);
        // Every other negative input really is negated.
        assert_eq!(abs_like(black_box(-5)), 5);
        assert_eq!(idx(black_box(-5)), 0);
    } else {
        println!("{}", idx(black_box(i32::MIN)));
    }
}
