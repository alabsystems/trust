//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --test -Awarnings
//@ run-crash
//@ error-pattern: kernel-certified Trust monitor failed
//@ forbid-output: TRUST_REQUIRES_BODY_RAN_SENTINEL
//@ dont-check-compiler-stderr
//! A certified `requires` monitor runs before the first user-body statement.
//! The false call must therefore abort in the monitor. If injection ever moves
//! after entry, the forbidden panic sentinel makes this regression fail even
//! though the process still exits unsuccessfully.

fn positive_only(x: u8) -> u8
    requires x > 0
{
    panic!("TRUST_REQUIRES_BODY_RAN_SENTINEL");
}

#[test]
fn certified_requires_monitor_precedes_the_body() {
    let _ = positive_only(0);
}
