//! The Phi-carrying trait, in its OWN crate. Its impls live in a downstream
//! crate that never sees this source — only the rlib's metadata.
#![feature(register_tool)]
#![register_tool(trust)]
#![crate_name = "libt"]
pub trait T { #[trust::panic_free] fn m(&self) -> u32; }
