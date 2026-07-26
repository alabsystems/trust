//@ needs-trust-verify
//@ dont-check-compiler-stderr
//@ no-prefer-dynamic
//@ revisions: targo plain
//@ compile-flags: -Ztrust-verify=off -Awarnings
//@[targo] compile-flags: -Ztrust-verify-session=native-link-ui -Ztrust-targo-test-monitor
//@[targo] rustc-env:TRUST_TARGO_TEST_MONITOR_SESSION=native-link-ui
//@[targo] check-fail
//[targo]~? ERROR certified-monitor tests reject unauthenticated native linkage
//@[plain] unset-rustc-env:TRUST_TARGO_TEST_MONITOR_SESSION
//@[plain] check-pass

// A source `#[link]` declaration does not appear in Targo's audited rustc
// arguments. Even an unused declaration can add constructors to the final
// process, so authenticated monitor units reject it before codegen.
#[link(name = "trust_untrusted_native", kind = "dylib")]
unsafe extern "C" {}

fn main() {}
