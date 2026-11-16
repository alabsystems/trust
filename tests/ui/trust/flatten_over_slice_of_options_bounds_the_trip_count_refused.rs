//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Twin of `flatten_over_slice_of_options_bounds_the_trip_count.rs`: a `Vec<()>`
//! can hold `usize::MAX` items, so flattening two of them overflows this counter;
//! the one-item-per-element bound must not apply to it.
pub fn count_units(v: &[Vec<()>]) -> usize { //~ ERROR verification
    let mut n = 1usize;
    for _ in v.iter().flatten() {
        n += 1;
    }
    n
}
