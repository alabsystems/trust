//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_dyn_upcast.rs` and `_dyn_upcast_holds.rs`:
//! a component trait whose `dyn` may be upcast to a `dyn Any`, and a fn that is not
//! generic, and so is never read, that swaps two boxed `dyn Any`. Safe, and sound.
#![forbid(unsafe_code)]

pub trait Component: std::any::Any {
    fn label(&self) -> u8 {
        0
    }
}
pub fn exchange(a: &mut Box<dyn std::any::Any>, b: &mut Box<dyn std::any::Any>) {
    std::mem::swap(a, b)
}
