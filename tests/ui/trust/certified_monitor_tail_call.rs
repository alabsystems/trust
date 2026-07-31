//@ needs-trust-verify
//@ revisions: pass mismatch
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --test -Awarnings
//@[pass] run-pass
//@[mismatch] run-crash
//@[mismatch] error-pattern: kernel-certified Trust monitor failed
//@ dont-check-compiler-stderr
#![expect(incomplete_features)]
#![feature(explicit_tail_calls)]

//! A `become` is a normal source-level return but remains a `TailCall` in
//! optimized MIR. The monitor-enabled test artifact lowers this exit to an
//! ordinary call, checks RETURN_PLACE, then returns. The production artifact
//! remains an explicit tail call.

fn identity(x: u8) -> u8 {
    #[cfg(mismatch)]
    return x + 1;
    #[cfg(pass)]
    x
}

fn tail_identity(x: u8) -> u8
    ensures result == x
{
    become identity(x);
}

#[inline(never)]
fn panics() -> u8 {
    panic!("tail callee panic")
}

fn tail_panics() -> u8
    ensures result == 0
{
    become panics();
}

#[test]
fn certified_ensures_monitor_covers_explicit_tail_call_returns() {
    assert_eq!(tail_identity(7), 7);
}

#[test]
fn expanded_tail_call_preserves_unwinding() {
    assert!(std::panic::catch_unwind(tail_panics).is_err());
}
