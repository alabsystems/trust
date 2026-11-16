//@ run-pass
//@ edition: 2021
//@ revisions: o1 o3
//@ compile-flags: -Coverflow-checks=off -Ztrust-verify=off
//@[o1] compile-flags: -O
//@[o3] compile-flags: -Copt-level=3
//! The second site the RBCE-OPTIONAL-DOMINATOR-1 audit found: `SsaRangePropagation`
//! read the success edge of an OPTIONAL overflow assert as a fact. The fix backports
//! rust-lang/rust a9b28d3 ("Skip optional asserts in SsaRangePropagation", 2026-10-05).
//!
//! `Add::add(a, b)` (core, `#[rustc_inherit_overflow_checks]`) inlines an
//! `AddWithOverflow` and an optional `Overflow(Add)` assert on its flag. GVN makes the
//! later `a.overflowing_add(b).1` read the same flag. With overflow checks off, codegen
//! erases the assert, so the flag can be `true`.
//!
//! BEFORE (a pre-fix stage 1, `scratchpad/stage1-w22probe`, measured 2026-10-11; the
//! pass source there is byte-identical to `2bf0ad72e3`): the pass folded the flag to
//! `false` after the assert, `f(u32::MAX, 1)` returned `false`, and the first assert
//! below failed (exit 101). Built with `-Zmir-enable-passes=-SsaRangePropagation` it
//! returns `true`. Stock rustc 1.97.1 and nightly-2026-07-09, run only as oracles,
//! also return `false`: they predate the upstream fix.
//!
//! AFTER: an optional overflow assert is not a range source; `f(u32::MAX, 1)` is `true`.

#[inline(never)]
fn f(a: u32, b: u32) -> bool {
    let _ = std::ops::Add::add(a, b);
    a.overflowing_add(b).1
}

fn main() {
    let a = std::hint::black_box(u32::MAX);
    let b = std::hint::black_box(1u32);
    assert!(f(a, b), "u32::MAX.overflowing_add(1) must report the overflow");
    assert!(!f(std::hint::black_box(1), b));
}
