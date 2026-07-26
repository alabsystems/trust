//@ needs-trust-verify
//@ revisions: wrapping mismatch_control
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --test -Coverflow-checks=no -Awarnings
//@[wrapping] run-pass
//@[mismatch_control] run-crash
//@[mismatch_control] error-pattern: kernel-certified Trust monitor failed
//@ dont-check-compiler-stderr
//! Fixed-width certified monitors use the same wrapping carrier as Rust.
//! `200u8 + 200u8` is 144 when overflow checks are disabled, so a monitor
//! accidentally evaluating the clause over `Nat` would reject this call. The
//! mismatch revision proves the `ensures` monitor is actually present rather
//! than letting the run-pass case pass vacuously.

fn wrapping_double(x: u8) -> u8
    ensures result == x + x
{
    #[cfg(wrapping)]
    return x + x;
    #[cfg(mismatch_control)]
    return 0;
}

#[test]
fn certified_u8_monitor_uses_machine_wrapping() {
    assert_eq!(wrapping_double(200), 144);
}
