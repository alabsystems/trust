//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The refusing twin of `lazy_adapter_consumers.rs`: the premise those
//! consumers now keep is that each `windows(2)` item has length EXACTLY 2, so a
//! map closure reading `w[2]` is refuted under it — and really panics on any
//! slice of two or more elements. A green here is a false proof.

pub fn fold_past_the_end(v: &[u8]) -> u8 {
    v.windows(2).map(|w| w[2]).fold(0u8, |a, b| a ^ b)
    //~^ ERROR failed for `lazy_consumer_past_the_end_refused::fold_past_the_end::{closure#0}`
}

pub fn any_past_the_end(v: &[u8]) -> bool {
    v.windows(2).map(|w| w[2]).any(|x| x == 0)
    //~^ ERROR failed for `lazy_consumer_past_the_end_refused::any_past_the_end::{closure#0}`
}
