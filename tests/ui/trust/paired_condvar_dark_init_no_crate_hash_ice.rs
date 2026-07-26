//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//! Regression: whole-crate certified-monitor initialization runs during the
//! analysis query, before rustc finalizes the local crate hash. The optional
//! paired-condvar lane is dark, and constructing its empty certificate must
//! neither demand that late query nor ICE an otherwise empty verified crate.

fn main() {}
