//@ trust-ladder-dep-flags: -Ztrust-verify=off
//! A verify-off DEPENDENCY declaring a Phi-carrying trait AND one provable impl
//! of it (`Good`). D4 increment B: a whole-program consumer that DECLARES this
//! crate relies on Phi at a generic call site by enumerating the trait's impl set
//! and re-deriving `Good` here (`user_phi_generic_bin_declared`); nothing this
//! crate's own build decided is read.
#![feature(register_tool)]
#![register_tool(trust)]
#![crate_name = "libtimpl"]
pub trait T { #[trust::panic_free] fn m(&self) -> u32; }
pub struct Good(pub u32);
impl T for Good { fn m(&self) -> u32 { self.0 & 0xff } }
