//@ needs-trust-verify
//@ proc-macro: pm1_boundary_derive.rs
//@ revisions: strict advisory unbounded
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-session=pm1-ui --crate-type=lib
//@[strict] compile-flags: -Ztrust-proc-macro-boundary
//@[advisory] compile-flags: -Ztrust-proc-macro-boundary -Ztrust-policy=advisory
//@[strict] check-fail
//@[advisory] check-pass
//@[unbounded] check-pass
//@ normalize-stderr: "(lib)?pm1_boundary_derive\.(dylib|so|dll)" -> "libpm1_boundary_derive.DYLIB"
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Trust (PM-1, 2026-10-01): with Targo's `-Ztrust-proc-macro-boundary`, rustc's crate
//! loader admits only the proc-macro dylibs `-Ztrust-audited-proc-macro` names, and
//! decides BEFORE opening the dylib (its load-time initializers run at `dlopen`).
//!
//! * `strict`: the unaudited `pm1_boundary_derive` is refused.
//! * `advisory`: it loads, and the unit forfeits proof authority (a warning).
//! * `unbounded`: no boundary flag (raw `trustc`, the lanes that do not opt in) —
//!   unchanged.
//!
//! The admitted case (an audited path) is exercised end to end by verified Targo,
//! which passes each audited provider's exact dylib.

//[strict]~? ERROR verified Targo refuses to load proc-macro crate `pm1_boundary_derive`

extern crate pm1_boundary_derive;

#[derive(pm1_boundary_derive::Pm1Sentinel)]
pub struct Marked;
