//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify -Cpanic=abort
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
// Trust: following a numeric dependency is not a nonzero assumption. The
// checked original body returns zero on a real input, so division must refuse.

pub fn maybe_zero(value: u32) -> u32 {
    value
}

pub fn forwarded_maybe_zero(value: u32) -> u32 {
    maybe_zero(value)
}

pub fn divide_by_forwarded_maybe_zero(numerator: u32, divisor: u32) -> u32 {
    numerator / forwarded_maybe_zero(divisor)
}
