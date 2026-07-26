//@ needs-trust-verify
//@ dont-check-compiler-stderr
//@ needs-dynamic-linking
//@ compile-flags: -Ztrust-verify=off -Ztrust-verify-session=dynamic-link-ui
//@ compile-flags: -Ztrust-targo-test-monitor -Cprefer-dynamic -Awarnings
//@ rustc-env:TRUST_TARGO_TEST_MONITOR_SESSION=dynamic-link-ui
//@ check-fail
//~? ERROR certified-monitor tests require a static Rust dependency closure

// The gate checks rustc's resolved dependency format, not only the original
// command spelling, so dynamic transitive Rust linkage cannot enter the test
// process outside the executable manifest.
fn main() {}
