//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Twin of `scan_last_drive_only_consumer.rs`: this scanner's `+=` overflows on
//! `[u32::MAX, 1]`, so `last` reaches a panic and must not be granted.
pub fn running_sum(v: &[u32]) -> Option<u32> { //~ ERROR verification
    v.iter().scan(0u32, |st, &x| {
        *st += x;
        Some(*st)
    })
    .last()
}
