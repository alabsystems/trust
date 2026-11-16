//@ trust-ladder-dep-flags: -Ztrust-verify=off
//! A verify-off DEPENDENCY's trait WITHOUT Phi and its one provable impl, for
//! rung 2 over a FOREIGN trait (D4 increment B): the impl set is closed by
//! enumeration in a whole-program consumer, not by a declaration.
#![crate_name = "libss"]
pub trait Shape { fn area(&self) -> u32; }
pub struct Sq(pub u32);
impl Shape for Sq { fn area(&self) -> u32 { self.0 & 0xff } }
