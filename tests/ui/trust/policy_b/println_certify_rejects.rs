//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! The `certify` twin of `println_default_run_pass.rs`. `-Ztrust-policy=certify`
//! is the release gate: it demands full static discharge, so the unproved
//! `_print` panic-freedom row is fatal here. If this ever passes, `certify` was
//! weakened — the two fixtures are a controlled pair, one variable (the policy).
//!
//! 2026-09-14: the expected message changed from `Trust full verification failed`
//! to `Trust strict verification failed`. NOT a weakening — the compile still exits
//! 1 — the ERROR now comes from the strict-policy path instead of the
//! lowering-failure path, because the reference-validity discharges closed the
//! bundled `ReentrantLock` completeness gap and the bundle lowers cleanly. The
//! unproved `_print` row is the same row; only which gate refuses it moved.
fn main() {
    //~^ ERROR Trust strict verification failed
    println!("hello");
}
