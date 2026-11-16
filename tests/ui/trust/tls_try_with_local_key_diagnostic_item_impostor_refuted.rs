//@ needs-trust-verify
//@ aux-build: no_std_local_key_impostor_dep.rs
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! THE PLANTED REFUTATION for the const-init TLS lane's `LocalKey` identity
//! (`callee_is_local_key_try_with`, `tls_local_key_accessor_instance`).
//!
//! The lane erases a `KEY.try_with(f)` call as total (`compiler_total_callees`)
//! when the key's ADT carries the `LocalKey` diagnostic item, is not in this
//! crate, its accessor reads a thread-local and nothing else, `f` is proved
//! panic-free, and `try_with`'s own MIR passes a structural drift pin. A
//! diagnostic item is a source ATTRIBUTE. This crate is `#![no_std]`, so the
//! auxiliary crate's `#[rustc_diagnostic_item = "LocalKey"]` is uncontested, and
//! its `try_with` calls a panicking helper of its own: a non-local, non-diverging
//! callee, which the drift pin admits.
//!
//! MEASURED before the fix (stage-1 `trustc` of main 8e8e84edfa3):
//! `[TLS_DISCHARGE] ADMIT fn=..::victim .. key=no_std_local_key_impostor_dep::LocalKey::<u32>::try_with`,
//! `victim` reported "1 proved", `-Ztrust-policy=certify` exited 0, and a
//! `#![no_std]` binary calling `victim()` panicked in the dependency (exit 134).
//!
//! The fix anchors the ADT on the compiler's OWN std by artifact residency
//! (`adt_is_resident_std_local_key` = the diagnostic item AND
//! `is_real_sysroot_crate`, the R2 discipline), which no attribute can claim. The
//! call keeps its absent-callee obligation, and under `certify` that is an error.
//! `tls_try_with_resident_std_local_key_keeps_credit.rs` pins that std's own key
//! keeps the credit.
//!
//! IF THIS FILE EVER COMPILES CLEAN, the lane is admitting an identity on an
//! attribute again.
#![no_std]

extern crate no_std_local_key_impostor_dep;

use no_std_local_key_impostor_dep::KEY;

pub fn victim() -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete for `tls_try_with_local_key_diagnostic_item_impostor_refuted::victim`
    //~| ERROR Trust strict verification failed for `tls_try_with_local_key_diagnostic_item_impostor_refuted::victim`
    match KEY.try_with(|v| *v) {
        Ok(v) => v,
        Err(_) => 0,
    }
}
