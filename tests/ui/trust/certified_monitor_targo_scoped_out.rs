//@ needs-trust-verify
//@ no-prefer-dynamic
//@ revisions: targo plain vanilla
//@ compile-flags: -Ztrust-verify=off -Awarnings
//@[targo] compile-flags: -Ztrust-verify-session=monitor-only-ui -Ztrust-targo-test-monitor
//@[targo] rustc-env:TRUST_TARGO_TEST_MONITOR_SESSION=monitor-only-ui
//@[targo] run-crash
//@[targo] error-pattern: kernel-certified Trust monitor failed
//@[targo] forbid-output: TRUST_MONITOR_RETURNED
//@[plain] unset-rustc-env:TRUST_TARGO_TEST_MONITOR_SESSION
//@[plain] run-pass
//@[vanilla] compile-flags: --test
//@[vanilla] unset-rustc-env:TRUST_TARGO_TEST_MONITOR_SESSION
//@[vanilla] run-pass
//@ dont-check-compiler-stderr
//! Certified-monitor installation remains independent of the static verifier
//! off-switch: this direct-driver fixture deliberately supplies
//! `-Ztrust-verify=off` to isolate that property. Native Targo does *not* scope
//! selected runtime Build/Test views out; it verifies each exact Cargo unit as
//! its own proof root so integration-test libraries cannot borrow `cfg(test)`
//! evidence. The unmarked revisions pin ordinary compatibility behavior.

fn bad_identity(x: u8) -> u8
    ensures result == x + x
{
    x
}

#[cfg(any(targo, plain))]
fn main() {
    let _ = bad_identity(7);
    println!("TRUST_MONITOR_RETURNED");
}

#[cfg(vanilla)]
#[test]
fn explicit_vanilla_no_verify_stays_uninstrumented() {
    let _ = bad_identity(7);
}
