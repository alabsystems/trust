//@ needs-trust-verify
//@ dont-check-compiler-stderr
//@ no-prefer-dynamic
//@ aux-build:certified_monitor_symbol_dependency.rs
//@ compile-flags: -Ztrust-verify=off -Ztrust-verify-session=dependency-symbol-ui
//@ compile-flags: -Ztrust-targo-test-monitor -Awarnings
//@ rustc-env:TRUST_TARGO_TEST_MONITOR_SESSION=dependency-symbol-ui
//@ check-fail
//~? ERROR certified-monitor tests reject source-controlled symbols or retained sections in dependencies

extern crate certified_monitor_symbol_dependency;

fn main() {
    certified_monitor_symbol_dependency::ordinary_rust_symbol();
}
