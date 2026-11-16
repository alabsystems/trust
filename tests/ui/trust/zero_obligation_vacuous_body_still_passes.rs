//@ revisions: default strict certify memory_safe
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json
//@ compile-flags: -Copt-level=0 --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@[memory_safe] compile-flags: -Ztrust-policy=memory-safe
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: HELP
//@ forbid-output: native-verification-gap
//@ forbid-output: "outcome":"unknown"
//! ZERO-ROW-GATE control (twin of `zero_obligation_undischarged_call_fails_closed.rs`):
//! a body with no obligation AND no call is genuinely vacuous. The publisher calls it
//! vacuously clean and mints the proved `no_obligations` row, and every fail-closed
//! lane still accepts it on its empty inventory. The gate change keys the accept on
//! the publisher's verdict; it must not refuse what the publisher proves.

pub fn id(x: i32) -> i32 {
    x
}

pub fn konst() -> u128 {
    7
}

pub fn pair(a: u8, b: u8) -> (u8, u8) {
    (b, a)
}
