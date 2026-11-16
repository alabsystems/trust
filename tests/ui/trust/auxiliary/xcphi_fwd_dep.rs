//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! `xcphi_dep.rs` plus a FORWARDING impl, `impl<S: T> T for W<S>`, in the
//! dependency. Its body's own call `<S as T>::m` is a reliance on the very
//! closure being computed, which D4 increment B DECLINES (self-reliance), so the
//! closure refuses: a recorded completeness cost, not a panic.
#![feature(register_tool)]
#![register_tool(trust)]
#![crate_name = "xcphi_fwd_dep"]

pub trait T {
    #[trust::panic_free]
    fn m(&self) -> u32;
}

pub struct Good(pub u32);
impl T for Good {
    fn m(&self) -> u32 {
        self.0 & 0xff
    }
}

pub struct W<S>(pub S);
impl<S: T> T for W<S> {
    fn m(&self) -> u32 {
        self.0.m()
    }
}
