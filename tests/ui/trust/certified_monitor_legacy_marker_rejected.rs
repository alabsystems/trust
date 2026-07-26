//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@ compile-flags: -Ztrust-certified-test-monitors -Ztrust-verify-session=legacy-monitor-ui
//@ compile-flags: -Ztrust-verify-package-name=legacy_monitor -Ztrust-verify-crate-role=dependency
//@ check-fail
//@ dont-check-compiler-stderr
//~? ERROR -Ztrust-certified-test-monitors requires Targo's authenticated tracked -Ztrust-targo-test-monitor selection

//! The legacy phase-A marker is tracked inventory, not independent monitor
//! authority. In particular it cannot bypass the nonce/sysroot/runtime-closure
//! checks owned by the phase-B Targo selector.

fn main() {}
