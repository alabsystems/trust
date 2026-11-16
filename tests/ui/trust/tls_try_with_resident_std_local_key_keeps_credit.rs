//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ edition: 2021
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! THE CAPABILITY CONTROL for the `LocalKey` residency conjunct
//! (`adt_is_resident_std_local_key`; the refutation it pairs with is
//! `tls_try_with_local_key_diagnostic_item_impostor_refuted.rs`).
//!
//! std's own `thread_local!` key, const-initialized, read through `try_with` with
//! a closure this crate proves panic-free: the const-init TLS lane erases the call
//! as total, so `resident_key_total_closure` carries no error under `certify`.
//! If the residency conjunct ever declined the REAL std (the sysroot resolved from
//! somewhere this compiler does not call its own), the call would fall back to
//! its absent-callee obligation and this function would gain the two errors the
//! impostor's `victim` has: an unannotated error fails this file.
//!
//! The file is `check-fail` only because of the `thread_local!` expansion's
//! OTHER accessor (`{closure#0}`, the lazy one the const selects away), whose
//! own `Assert` is `runtime_checked`, never statically proved: measured on the
//! stage-1 `trustc` of main 8e8e84edfa3 with a release-like std, it is the only
//! refused body, and `resident_key_total_closure` reports 2 proved of 2.

thread_local! {
    //~^ ERROR Trust Level 0 safety verification incomplete for `tls_try_with_resident_std_local_key_keeps_credit::K::{constant#0}::{closure#0}`
    //~| ERROR Trust strict verification failed for `tls_try_with_resident_std_local_key_keeps_credit::K::{constant#0}::{closure#0}`
    static K: u32 = const { 5 };
}

pub fn resident_key_total_closure() -> u32 {
    match K.try_with(|v| *v) {
        Ok(v) => v,
        Err(_) => 0,
    }
}
