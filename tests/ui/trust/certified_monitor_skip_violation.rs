//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --test -Awarnings
//@ run-crash
//@ error-pattern: kernel-certified Trust monitor failed
//@ dont-check-compiler-stderr
//! An advisory `#[trust::skip]` suppresses static verification only. A certified
//! monitor for the skipped function must still be injected and executed in test
//! mode, so the user opt-out cannot silently suppress runtime evidence as well.

#![feature(register_tool)]
#![register_tool(trust)]

#[trust::skip]
fn skipped_bad_identity(x: u8) -> u8
    ensures result > x
{
    x
}

#[test]
fn certified_monitor_survives_advisory_skip() {
    let _ = skipped_bad_identity(7);
}
