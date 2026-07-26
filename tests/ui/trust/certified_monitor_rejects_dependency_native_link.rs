//@ needs-trust-verify
//@ dont-check-compiler-stderr
//@ no-prefer-dynamic
//@ aux-build:certified_monitor_native_dependency.rs
//@ compile-flags: -Ztrust-verify=off -Ztrust-verify-session=dependency-native-ui
//@ compile-flags: -Ztrust-targo-test-monitor -Awarnings
//@ rustc-env:TRUST_TARGO_TEST_MONITOR_SESSION=dependency-native-ui
//@ check-fail
//~? ERROR certified-monitor tests reject unauthenticated native linkage

extern crate certified_monitor_native_dependency;

fn main() {
    certified_monitor_native_dependency::ordinary_rust_symbol();
}
