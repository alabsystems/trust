//@ needs-trust-verify
//@ aux-build:clean_origin_aux_deferred_suffix.rs
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr

//! E9-DEFERRED-SUFFIX-ENV-2 (TG15 residual 3): calling a Clean-origin def of a
//! library whose last island names one of that library's own `trust_import_*`
//! admissions. The importer used to re-elaborate EVERY transported island in a
//! fresh session, where the suffix's import constant does not exist, so the
//! batch was rejected and the call stopped with "cannot import the Clean-origin
//! certificate … no longer elaborate under this compiler's Clean kernel". It now
//! re-elaborates the pre-admission prefix, the environment the exporter's gate and
//! digest were built over, and readmission compares every digest field against it.
//! Genuine kernel skew stays refused (`tests/run-make/trust-clean-origin-kernel-skew`).
//!
//! `-Z trust-verify=off` here for the same reason as `clean_origin_cross_crate_call.rs`:
//! readmission and the local re-gate are not behind the verification switch.

extern crate clean_origin_aux_deferred_suffix;

fn main() {
    let v = clean_origin_aux_deferred_suffix::m::pick(41, 7);
    assert_eq!(v, 41, "the imported body must be the projection `pick` denotes (parameter 0)");
}
