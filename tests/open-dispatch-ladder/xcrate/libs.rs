//@ trust-ladder-dep-flags: -Ztrust-verify=off
//! A verify-off DEPENDENCY's trait with one provable and one panicking impl,
//! for the C-FLOW rows (`user_dyn_*`). No `#[trust::panic_free]`: the value-flow
//! case split, not the impl-set certificate, is what D4-A serves.
#![crate_name = "libs"]
pub trait Shape { fn area(&self) -> u32; }
pub struct Sq(pub u32);
impl Shape for Sq { fn area(&self) -> u32 { self.0 & 0xff } }
pub struct Boom;
impl Shape for Boom { fn area(&self) -> u32 { panic!("boom") } }
