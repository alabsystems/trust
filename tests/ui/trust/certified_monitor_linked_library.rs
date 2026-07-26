//@ needs-trust-verify
//@ no-prefer-dynamic
//@ run-crash
//@ aux-build:certified_monitor_linked_on.rs
//@ aux-build:certified_monitor_linked_off.rs
//@ compile-flags: -Ztrust-verify=off
//@ error-pattern: kernel-certified Trust monitor failed
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN

extern crate certified_monitor_linked_off as monitor_off;
extern crate certified_monitor_linked_on as monitor_on;

fn main() {
    // The control rlib has the same native Trust contract but no tracked
    // monitor codegen option, so the invalid call remains ordinary Rust.
    assert_eq!(monitor_off::guarded(8), 8);

    // This call crosses into a separately compiled, non-`--test` rlib. Its
    // failure proves the monitor option changed the linked library artifact,
    // rather than merely instrumenting this caller or a test harness.
    let _ = monitor_on::guarded(8);
}
