//@ revisions: default certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify -Cpanic=abort
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! D5-A's OVER-HOLD controls: the same-crate call-destination screen
//! (`call_dest_refutation_held.rs`) must not swallow a GENUINE refutation.
//! Each function below is a real bug, refuted with a grounded witness before
//! the screen existed (stage-1 `a8c853de6f`, both revisions, measured), and each
//! must keep its `FAILED … counterexample` row — the trailing NOTE pins vanish if
//! the screen ever holds one of them.
//!
//! * `unguarded_after_call`: `let _ = guard_bad(bit)` — the call's result is
//!   never read, so the query never mentions it; `x >> bit` overflows at 64.
//! * `div_one_bad`: `one()` has a crate-wide CONSTANT-SET summary (`{1}`), so
//!   its destination is pinned and `x / (one() - 1)` really divides by zero.
//! * `shift_ens_bad`: `guard_ens` carries `ensures result == (bit < 65)`, so
//!   the caller's contract-summary DB names it and its destination is pinned by
//!   the injected postcondition; `guard_ens(64)` really is `true`.

pub fn guard_bad(bit: u32) -> bool {
    bit < 65
}

pub fn unguarded_after_call(x: u64, bit: u32) -> u64 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE [shift:right] FAILED (ay-in-process); counterexample:
    let _ = guard_bad(bit);
    x >> bit
}

pub fn one() -> u32 {
    1
}

pub fn div_one_bad(x: u32) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE [divzero] FAILED (ay-in-process); counterexample:
    x / (one() - 1)
}

pub fn guard_ens(bit: u32) -> bool
    ensures result == (bit < 65)
{
    bit < 65
}

pub fn shift_ens_bad(x: u64, bit: u32) -> Option<u64> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE [shift:right] FAILED (ay-in-process); counterexample:
    if !guard_ens(bit) {
        return None;
    }
    Some(x >> bit)
}
