//@ needs-trust-verify
//@ check-pass
//@ compile-flags: -Z trust-verify=off
//! **I8 — THE SEAM PIN.** A `#[cfg]`'d-out `clean mod` must never demand its
//! file from disk: there is deliberately NO
//! `clean_unit_never_exists_helper.clean` anywhere, and this test must PASS.
//!
//! This is the property that decided WHERE units load. cfg-stripping happens
//! in `InvocationCollector::flat_map_node`, BEFORE the out-of-line-module
//! loading seam (`wrap_flat_map_node_walk_flat_map`) is reached — so loading
//! there gets cfg parity with `mod foo;` for free, and loading at parse time
//! could not have it at any price. If this test ever starts failing with
//! "file not found", the load has moved to the wrong side of cfg processing.

#[cfg(any())] // never true, mirrors platform-conditional units
clean mod clean_unit_never_exists_helper;

fn main() {}
