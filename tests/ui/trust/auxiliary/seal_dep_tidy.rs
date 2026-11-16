//@ edition: 2021
//@ aux-build: seal_dep_visit.rs
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_third.rs` and `_third_holds.rs` (crate
//! A): generic code over `seal_dep_visit`'s traits, which runs what the
//! type's impl says, whatever that is. Safe to call, and sound.

extern crate seal_dep_visit;

pub fn tidy<T: seal_dep_visit::Settle>(a: &mut T, b: &mut T) {
    T::settle(a, b)
}

pub fn run<V: seal_dep_visit::Visit>(v: &mut V) {
    seal_dep_visit::drive(v)
}
