//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-fail
//! The snippet surface is not Rust typechecked. Helper expansion must therefore
//! authenticate exact formal/actual/result domains before erasing the call to
//! text. Coarse "integer" agreement would make each false-domain spelling below
//! collapse to a true postcondition.

fn id_i64(v: i64) -> i64 {
    v
}

pub fn signedness_mismatch(x: u64) -> u64 ensures result == id_i64(x) { //~ ERROR safety verification incomplete
    //~| ERROR strict verification failed
    x
}
fn id_u32(v: u32) -> u32 {
    v
}

pub fn width_mismatch(x: u64) -> u64 ensures result == id_u32(x) { //~ ERROR safety verification incomplete
    //~| ERROR strict verification failed
    x
}

fn id_u8(v: u8) -> u8 {
    v
}

pub fn untyped_out_of_range_literal() -> u8 ensures result == id_u8(256) { //~ ERROR safety verification incomplete
    //~| ERROR strict verification failed
    0
}

fn one_from_u64(_v: u64) -> u64 {
    1
}

pub fn bool_integer_mismatch(flag: bool) -> bool //~ ERROR safety verification incomplete
    //~| ERROR strict verification failed
    ensures result == (one_from_u64(flag) == 1)
{
    true
}

fn zero_i64() -> i64 {
    0
}

pub fn zero_arg_return_mismatch() -> u64 ensures result == zero_i64() { //~ ERROR safety verification incomplete
    //~| ERROR strict verification failed
    0
}
