//@ needs-trust-verify
//@ dont-check-compiler-stderr
//@ needs-asm-support
//@ no-prefer-dynamic
//@ aux-build:certified_monitor_startup_dependency.rs
//@ revisions: global_asm startup_section global_allocator
//@ compile-flags: -Ztrust-verify=off -Ztrust-verify-session=dependency-startup-ui
//@ compile-flags: -Ztrust-targo-test-monitor -Awarnings
//@ rustc-env:TRUST_TARGO_TEST_MONITOR_SESSION=dependency-startup-ui
//@ check-fail
//[global_asm]~? ERROR certified-monitor tests reject unauthenticated global assembly in dependency
//[startup_section]~? ERROR certified-monitor tests reject source-controlled symbols or retained sections in dependencies
//[global_allocator]~? ERROR certified-monitor tests reject source-controlled runtime roles in dependencies

extern crate certified_monitor_startup_dependency;

fn main() {
    certified_monitor_startup_dependency::ordinary_rust_symbol();
}
