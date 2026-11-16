//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The F6b callee re-trace may use only facts about the callee context it is
//! tracing (wave 20, 2026-10-06).
//!
//! F6B-FIELD-OVERRIDE-UNSTABLE-1. `float_callee_trace_range` bound each
//! struct/tuple formal to the caller's actual. The projected-place branch of
//! `float_range` returned the caller's interval for a formal leaf before it
//! checked whether the callee had written that leaf. `bump` overwrites `p.a`
//! before it reads it, and `via_mut` passes `&mut p.0` to `set`. Both were
//! traced as returning the caller's `0.5`. The result was that the
//! `float_overflow_to_infinity` rows of `lie_struct` and `lie_tuple_mut` were
//! discharged, and under the default policy F5 dropped `pre_lie`'s precondition
//! row for `scaled`. At run time `scaled` receives 1e300.
//!
//! F6B-TRACE-MEMO-KEY-1. Every nested callee context shared one trace memo.
//! Its key (call block, callee, args, suffix) is spelled in the traced
//! function's own local names, and it does not name the overrides in force.
//! Tracing `outer` under `x = 2` cached the inner `inner(copy _1)` as `[2, 2]`.
//! The second trace, `outer(y)` with `y` unbounded, hit that key and reused
//! `[2, 2]`. In `caller`, the root-level `inner(x)` call has the same key as the
//! `inner(copy _1)` call inside `outer`.
//!
//! BEFORE (stage 1 of `4ccd862830` at `scratchpad/stage1-w18b`, each revision's
//! own flags plus `--cfg <revision> --emit=metadata` and compiletest's `-A`
//! lint flags, measured 2026-10-06): both revisions report nothing for
//! `lie_struct`, `lie_tuple_mut`, `twice` or `caller`. The default revision
//! exits 0. The certify revision exits 1, but only on the controls. Under the
//! default policy `pre_lie` reports two warnings and no error, because its
//! precondition row is missing.
//!
//! AFTER (predicted, not built): each formal leaf override needs an
//! entry-stable formal (`param_place_is_entry_stable`, checked when the binder
//! runs and again in `param_field_override`), and each callee context gets its
//! own trace memo. Each annotated lie then reports the row it was missing, like
//! its control. The prediction was measured on the BEFORE compiler with a
//! proxy: each lie's callee was replaced, line for line, by a `#[no_mangle]`
//! copy whose body no lane can read, so its trace refuses as the fixed trace
//! does. The float rows are a WARN under the default policy and an ERROR under
//! certify. `pre_lie` gains its precondition row, which makes it an ERROR under
//! the default policy too. Under certify it was already an ERROR, on the call's
//! runtime-checked row.
//!
//! Controls: the `keep_*` callers, `pre_keep` and `twice_same` show that a
//! callee that does not write its formal, or a second trace under the same
//! bound, still uses the caller's interval. They report the same thing before
//! and after. `once`, `twice_ba` and `nocollide` are the shapes the scout
//! measured keeping the row before the fix. They keep it after the fix.
//!
//! The run witness is `f6b_float_trace_context_run.rs`. The trust-vcgen test
//! `crates/trust-vcgen/tests/f6b_trace_context_realmir.rs` runs vcgen on this
//! file's MIR as the BEFORE compiler dumped it; it fails on the base trust-vcgen
//! and passes with the fix.

#[derive(Clone, Copy)]
pub struct P {
    pub a: f64,
}

// ---- F6B-FIELD-OVERRIDE-UNSTABLE-1 ----

// The callee writes the formal's field before it reads it.
fn bump(mut p: P) -> f64 {
    p.a = 1.0e300;
    p.a
}

pub fn lie_struct() -> f64 {
    //[default]~^ WARN Trust verification advisory
    //[certify]~^^ ERROR Trust strict verification failed
    let p = P { a: 0.5 };
    bump(p) * 1.0e300
}

fn set(r: &mut f64) {
    *r = 1.0e300;
}

// The callee passes `&mut p.0` to another function before it reads `p.0`.
fn via_mut(mut p: (f64, f64)) -> f64 {
    set(&mut p.0);
    p.0
}

pub fn lie_tuple_mut() -> f64 {
    //[default]~^ WARN Trust verification advisory
    //[certify]~^^ ERROR Trust strict verification failed
    via_mut((0.5, 0.5)) * 1.0e300
}

pub fn scaled(x: f64) -> f64 requires x >= 0.0 && x <= 1.0 {
    x * 1.0e300
}

// `bump` returns 1e300, so `scaled`'s `requires` is violated.
pub fn pre_lie() -> f64 {
    //[default]~^ WARN Trust Level 0 safety verification incomplete
    //[default]~| ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    let p = P { a: 0.5 };
    scaled(bump(p))
}

// Controls: a callee that does not write its formal keeps the caller's
// interval.
fn keep(p: P) -> f64 {
    p.a
}

pub fn keep_struct() -> f64 {
    let p = P { a: 0.5 };
    keep(p) * 1.0e300
}

fn keep_t(p: (f64, f64)) -> f64 {
    p.0
}

pub fn keep_tuple() -> f64 {
    keep_t((0.5, 0.5)) * 1.0e300
}

// The precondition row is discharged; the two diagnostics are the call's
// runtime-checked row, as for `pre_lie` before the fix.
pub fn pre_keep() -> f64 {
    //[default]~^ WARN Trust Level 0 safety verification incomplete
    //[default]~| WARN Trust verification advisory
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    let p = P { a: 0.5 };
    scaled(keep(p))
}

// ---- F6B-TRACE-MEMO-KEY-1 ----

fn inner(v: f64) -> f64 {
    v
}

fn outer(w: f64) -> f64 {
    inner(w)
}

fn outer2(_u: f64, w: f64) -> f64 {
    inner(w)
}

// `outer` is traced twice; the bounded trace's inner result was reused for
// `outer(y)`.
pub fn twice(x: f64, y: f64) -> f64 requires x >= 2.0 && x <= 2.0 {
    //[default]~^ WARN Trust verification advisory
    //[certify]~^^ ERROR Trust strict verification failed
    let a = outer(x);
    let b = outer(y);
    a * b
}

// The caller's own `inner(x)` has the key of the `inner(copy _1)` inside
// `outer`.
pub fn caller(x: f64, y: f64) -> f64 requires x >= 2.0 && x <= 2.0 {
    //[default]~^ WARN Trust verification advisory
    //[certify]~^^ ERROR Trust strict verification failed
    let a = inner(x);
    let b = outer(y);
    a * b
}

// Controls that keep the row before and after the fix: the unbounded trace
// alone, the unbounded trace first (a refusal is never cached), and a bounded
// trace whose inner call has a different key.
pub fn once(x: f64, y: f64) -> f64 requires x >= 2.0 && x <= 2.0 {
    //[default]~^ WARN Trust verification advisory
    //[certify]~^^ ERROR Trust strict verification failed
    let b = outer(y);
    x * b
}

pub fn twice_ba(x: f64, y: f64) -> f64 requires x >= 2.0 && x <= 2.0 {
    //[default]~^ WARN Trust verification advisory
    //[certify]~^^ ERROR Trust strict verification failed
    let a = outer(x);
    let b = outer(y);
    b * a
}

pub fn nocollide(x: f64, y: f64) -> f64 requires x >= 2.0 && x <= 2.0 {
    //[default]~^ WARN Trust verification advisory
    //[certify]~^^ ERROR Trust strict verification failed
    let a = outer2(0.0, x);
    let b = outer(y);
    a * b
}

// Control that stays silent: both traces run under the same bound.
pub fn twice_same(x: f64) -> f64 requires x >= 2.0 && x <= 2.0 {
    let a = outer(x);
    let b = outer(x);
    a * b
}
