//@ trust-ladder-dep-flags: -Ztrust-verify=off
//! OD-1 phase 2: a verify-off DEPENDENCY that DEFINES the open generic dispatch
//! (`f`) and also holds a panicking impl (`Boom`). Its generic's instances are
//! created by the consumer, which re-derives `f`'s site from this crate's encoded
//! MIR and charges each instance it names.
#![crate_name = "libgen"]
pub trait Tr { fn m(&self) -> u32; }
pub fn f<X: Tr>(x: &X) -> u32 { x.m() }
pub struct Boom;
impl Tr for Boom { fn m(&self) -> u32 { panic!("boom") } }
