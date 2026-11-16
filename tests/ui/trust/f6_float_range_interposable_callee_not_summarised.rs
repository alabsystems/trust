//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! IDENTITY GATE of the F6 float result-interval lane and of the callee-body
//! (tracing) lane (F6-INTERPOSE-1, 2026-10-04).
//!
//! INTERPOSE-SUM-1 (wave 11) refused six body-derived callee summaries for a
//! callee whose symbol can be interposed at link time (`#[no_mangle]`,
//! `#[export_name]`, `#[linkage]`): another object can define the same symbol,
//! and the call binds to it. Two more lanes read such a callee's body without
//! that gate:
//!
//! * `f6_derived_callee_result_range` gave `x * f6i_scale()` the interval
//!   `[2, 2]` from `f6i_scale`'s body, so the `float_overflow_to_infinity` row
//!   was discharged. A binary that linked another `f6_scale` returning `1e10`
//!   computed `g(1e300) = inf` (measured by the wave-14 scout on macOS);
//! * `extracted_callee_body_for_tracing` attached the body to the call's
//!   summary. The float tracer re-traced it (`x * f6i_ident(2.0)`, directly or
//!   through a plain `f6i_outer`), and the callee write-set lane derived from it
//!   that `f6i_bump` writes only `s.a`, so `s.b = 5` survived the call and
//!   `10 / s.b` was certified. A verify-off binary that defined its own
//!   `#[no_mangle] ws_bump` setting `s.b = 0` panicked with `attempt to divide by
//!   zero` inside the certified `h` (measured 2026-10-04 by the wave-14
//!   implementer on the same shape).
//!
//! BEFORE (the wave-14 scout's `stage1-w12`, each revision's own flags plus
//! `--cfg <revision> --emit=metadata`, measured 2026-10-04): both revisions exit
//! 0, and no annotated row is reported in either.
//!
//! AFTER (predicted, not built): `body_summary_identity_refused` refuses each
//! exported callee in both lanes, so each annotated caller is refused as it is
//! over a callee whose body no lane can read. The prediction was measured on the
//! BEFORE compiler with that proxy: every exported callee's body rewritten
//! through `std::hint::black_box`, line for line. The float rows are a WARN
//! under the default policy (it reports, rather than fails, an IEEE-754 outcome)
//! and an ERROR under certify; the division row is an ERROR in both.
//!
//! Controls: the `*_plain` twins, the same bodies not exported, prove before and
//! after, so neither revision may report anything for them. If an annotated row
//! starts to prove again, an interposable body has started to lend a fact.

// The static F6 interval: `#[no_mangle]`.
#[no_mangle]
pub fn f6i_scale() -> f64 {
    2.0
}

pub fn scale_nm(x: f64) -> f64 requires x >= 0.0 && x <= 1.0e300 {
    //[default]~^ WARN Trust verification advisory
    //[certify]~^^ ERROR Trust strict verification failed
    x * f6i_scale()
}

// The static F6 interval: `#[export_name]`.
#[export_name = "f6i_six_scale_symbol"]
pub fn f6i_six_scale() -> f64 {
    2.0
}

pub fn scale_export(x: f64) -> f64 requires x >= 0.0 && x <= 1.0e300 {
    //[default]~^ WARN Trust verification advisory
    //[certify]~^^ ERROR Trust strict verification failed
    x * f6i_six_scale()
}

// The tracing lane alone: an identity has no static interval; the call-site
// re-trace of its body under the actual `2.0` is what discharged the row.
#[no_mangle]
pub fn f6i_ident(y: f64) -> f64 {
    y
}

pub fn scale_ident_nm(x: f64) -> f64 requires x >= 0.0 && x <= 1.0e300 {
    //[default]~^ WARN Trust verification advisory
    //[certify]~^^ ERROR Trust strict verification failed
    x * f6i_ident(2.0)
}

// The transitive trace worklist: a plain `f6i_outer` calls the exported
// `f6i_inner`, whose body the worklist attached.
#[no_mangle]
pub fn f6i_inner() -> f64 {
    2.0
}

pub fn f6i_outer() -> f64 {
    f6i_inner()
}

pub fn scale_transitive(x: f64) -> f64 requires x >= 0.0 && x <= 1.0e300 {
    //[default]~^ WARN Trust verification advisory
    //[certify]~^^ ERROR Trust strict verification failed
    x * f6i_outer()
}

// The callee write-set lane, which reads the same attached body: `f6i_bump`
// writes only `s.a`, so `s.b == 5` survived the call.
pub struct S {
    pub a: u32,
    pub b: u32,
}

#[no_mangle]
pub fn f6i_bump(s: &mut S) {
    s.a = 1;
}

pub fn div_after_bump(s: &mut S) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    s.b = 5;
    f6i_bump(s);
    10 / s.b
}

// Controls: the same bodies, not exported.
pub fn f6i_scale_plain() -> f64 {
    2.0
}

pub fn scale_plain(x: f64) -> f64 requires x >= 0.0 && x <= 1.0e300 {
    x * f6i_scale_plain()
}

pub fn f6i_ident_plain(y: f64) -> f64 {
    y
}

pub fn scale_ident_plain(x: f64) -> f64 requires x >= 0.0 && x <= 1.0e300 {
    x * f6i_ident_plain(2.0)
}

pub fn f6i_inner_plain() -> f64 {
    2.0
}

pub fn f6i_outer_plain() -> f64 {
    f6i_inner_plain()
}

pub fn scale_transitive_plain(x: f64) -> f64 requires x >= 0.0 && x <= 1.0e300 {
    x * f6i_outer_plain()
}

pub fn f6i_bump_plain(s: &mut S) {
    s.a = 1;
}

pub fn div_after_bump_plain(s: &mut S) -> u32 {
    s.b = 5;
    f6i_bump_plain(s);
    10 / s.b
}
