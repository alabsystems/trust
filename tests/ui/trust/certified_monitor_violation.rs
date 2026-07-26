//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --test -Awarnings
//@ run-crash
//@ error-pattern: kernel-certified Trust monitor failed
//@ dont-check-compiler-stderr
//! A statically unproved but executable clause must be enforced in test mode.
//! The monitor is admitted only by a kernel-checked equivalence certificate;
//! there is no placeholder `true` or separate executable projection.

fn bad_identity(x: u8) -> u8
    ensures result > x
{
    x
}

#[test]
fn certified_monitor_aborts_on_violation() {
    let _ = bad_identity(7);
}
