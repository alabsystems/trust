//@ trust-ladder-dep-flags: -Ztrust-verify=off
//! `libtimpl` plus a PANICKING impl, `Bad`, that no consumer constructs. Built
//! verify-off (a verifying build would refuse `Bad` at the impl). The
//! foreign-trait closure (D4 increment B) quantifies over the impl set, so
//! `user_phi_generic_bin_bad` must refuse.
#![feature(register_tool)]
#![register_tool(trust)]
#![crate_name = "libtbad"]
pub trait T { #[trust::panic_free] fn m(&self) -> u32; }
pub struct Good(pub u32);
impl T for Good { fn m(&self) -> u32 { self.0 & 0xff } }
pub struct Bad;
impl T for Bad { fn m(&self) -> u32 { panic!("boom") } }
