//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_shape_entries.rs` and its twin: an
//! unsafe marker trait at `seal_dep_pod_one::marker::Pod`, whose path ends as
//! the other's does.

pub mod marker {
    pub unsafe trait Pod {}
}
