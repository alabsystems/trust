//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_foreign_impl.rs` and
//! `_foreign_impl_holds.rs`: an unsafe trait with a provided method.
pub unsafe trait RawOk {
    fn tag(&self) -> u8 {
        0
    }
}
