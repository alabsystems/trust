//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-pass
//@ dont-check-compiler-stderr
//! `(a as i128) * (b as i128)` over two `i64` (or narrower) values cannot overflow
//! `i128`: a widening integer cast keeps the value, so each operand lies in its
//! source type's range. The signed-128 multiply's operand box had no cast arm and the
//! product was refused (sweep `m20`).
pub fn wmul(a: i64, b: i64) -> i128 {
    (a as i128) * (b as i128)
}

pub fn wmul_mixed(a: u32, b: i8) -> i128 {
    (a as i128) * (b as i128)
}
