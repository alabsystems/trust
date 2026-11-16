//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `r6_rob_f3_dead_polyrec_collector_e0275.rs` (review 6 of the
//! review-14 build): a trait with a provided method, and generic fns that run
//! it or box a value as a `dyn` of it.
pub trait Tr { fn m(&self) -> u32 { 0 } }
impl Tr for u8 {}
pub fn go<T: Tr>(x: &T) -> u32 { x.m() + 1 }
pub fn boxit<T: Tr + 'static>(x: T) -> Box<dyn Tr> { Box::new(x) }
