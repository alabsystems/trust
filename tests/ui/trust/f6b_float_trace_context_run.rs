//@ run-pass
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -C overflow-checks=on
//! The WITNESS for `f6b_float_trace_context.rs` (F6B-FIELD-OVERRIDE-UNSTABLE-1
//! and F6B-TRACE-MEMO-KEY-1).
//!
//! It is built with verification off and overflow checks on. The functions are
//! the fixture's lie cases and their callees, with `#[inline(never)]` added,
//! and this program asserts what they compute. On the verified fixture, the
//! BEFORE compiler discharged each of their `float_overflow_to_infinity` rows,
//! and under the default policy it dropped `pre_lie`'s precondition row for
//! `scaled`:
//!
//! * `lie_struct`, `lie_tuple_mut` and `pre_lie` return infinity, and the value
//!   that `pre_lie` passes to `scaled` is 1e300, outside its `requires`;
//! * `twice(2.0, f64::MAX)` and `caller(2.0, f64::MAX)` satisfy their
//!   `requires` (x = 2) and return infinity.
//!
//! The fix changes verdicts, not code, so this program passes BEFORE and AFTER.
//! BEFORE (stage 1 of `4ccd862830`, `--edition 2021 -Ztrust-verify=off -C
//! overflow-checks=on`, measured 2026-10-06): it builds and exits 0. The
//! scout measured the same values on the probes `c2.rs` (`lie_small() = inf`,
//! `pre_lie() = inf`, `t_tuple() = inf`) and `m3main.rs`
//! (`twice(2.0, f64::MAX) = inf`) on the same compiler.

use std::hint::black_box;

#[derive(Clone, Copy)]
pub struct P {
    pub a: f64,
}

#[inline(never)]
fn bump(mut p: P) -> f64 {
    p.a = 1.0e300;
    p.a
}

#[inline(never)]
pub fn lie_struct() -> f64 {
    let p = P { a: 0.5 };
    bump(p) * 1.0e300
}

#[inline(never)]
fn set(r: &mut f64) {
    *r = 1.0e300;
}

#[inline(never)]
fn via_mut(mut p: (f64, f64)) -> f64 {
    set(&mut p.0);
    p.0
}

#[inline(never)]
pub fn lie_tuple_mut() -> f64 {
    via_mut((0.5, 0.5)) * 1.0e300
}

#[inline(never)]
pub fn scaled(x: f64) -> f64 requires x >= 0.0 && x <= 1.0 {
    x * 1.0e300
}

#[inline(never)]
pub fn pre_lie() -> f64 {
    let p = P { a: 0.5 };
    scaled(bump(p))
}

#[inline(never)]
fn inner(v: f64) -> f64 {
    v
}

#[inline(never)]
fn outer(w: f64) -> f64 {
    inner(w)
}

#[inline(never)]
pub fn twice(x: f64, y: f64) -> f64 requires x >= 2.0 && x <= 2.0 {
    let a = outer(x);
    let b = outer(y);
    a * b
}

#[inline(never)]
pub fn caller(x: f64, y: f64) -> f64 requires x >= 2.0 && x <= 2.0 {
    let a = inner(x);
    let b = outer(y);
    a * b
}

fn main() {
    assert!(lie_struct().is_infinite());
    assert!(lie_tuple_mut().is_infinite());
    // `scaled` requires `0.0 <= x <= 1.0`; `pre_lie` passes it 1e300.
    let passed = bump(black_box(P { a: 0.5 }));
    assert!(passed > 1.0);
    assert!(pre_lie().is_infinite());
    // Both callers satisfy `requires x >= 2.0 && x <= 2.0`.
    assert!(twice(2.0, black_box(f64::MAX)).is_infinite());
    assert!(caller(2.0, black_box(f64::MAX)).is_infinite());
}
