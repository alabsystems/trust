//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify -Cpanic=abort
//@ check-pass
//@ dont-check-compiler-stderr
// Trust: a numeric forwarding helper needs the same checked dependency walk
// as a Boolean caller. Each original leaf and forwarding-body proof is still
// required before its result may establish a nonzero divisor.

pub fn nonzero(value: u32) -> u32 {
    if value == 0 { 1 } else { value }
}

pub fn forwarded_nonzero(value: u32) -> u32 {
    nonzero(value)
}

pub fn divide_by_forwarded_nonzero(numerator: u32, divisor: u32) -> u32 {
    numerator / forwarded_nonzero(divisor)
}
