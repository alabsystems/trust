//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! THE SOUNDNESS HALF of the bitwise functions in
//! `plain_binaryop_return_value_proves.rs`.
//!
//! Those rows prove because trust-mc's signed-bridge lowering now admits a
//! COPY of a decoded value (`_0 = _4`) to its pure-bit-vector rewrite
//! (DECISION_QUEUE BRIDGE-COPY-ADMISSIBLE-1). The rewrite is equisatisfiable,
//! so it must refute a false clause over the same bodies exactly as it proves
//! a true one: `x & 1023` is 0 at `x = 1024`, and `x | 1` is 1 at `x = 0`.
//! Each clause below is false, and each build must be refused with the row
//! FAILED, not merely unknown.

pub fn masked_claims_positive(x: i32) -> i32
//~^ ERROR Trust strict verification failed
//~| NOTE 2 failed, 0 unknown
    ensures result >= 1
{
    if x < 0 { 1 } else { x & 1023 }
}

pub fn ored_claims_at_least_two(x: i32) -> i32
//~^ ERROR Trust strict verification failed
//~| NOTE 2 failed, 0 unknown
    requires x >= 0
    ensures result >= 2
{
    if x < 0 { 2 } else { x | 1 }
}
