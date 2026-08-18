//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Rung 1 §(a): the completeness rule, enforced.
//!
//! `#[trust::panic_free]` on an IMPLEMENTATION is refused. This is not a style
//! preference. An implementation-site opt-in cannot support reliance: a call
//! site would have to check that EVERY implementation opted in, which is the
//! enumeration problem the contract exists to remove. Declaring on the trait
//! DEFINITION inverts the quantifier — a crate cannot write `impl Sink for X`
//! without naming `Sink`, and cannot name `Sink` without loading its metadata,
//! which carries the contract. That is the one structural property the whole
//! rule rests on, and it is enforced by the language rather than by Trust.
//!
//! Refusing loudly matters more than it looks: an annotation that silently did
//! nothing would read to its author exactly like one that was being enforced.
//!
//! The second case below — the contract on an ordinary free function — is
//! refused for a different reason. A free function's panic-freedom is already
//! the subject of its own verification verdict; there is no dispatch, so there
//! is nothing for a contract to move anywhere.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![feature(register_tool)]
#![register_tool(trust)]

pub trait Sink {
    fn absorb(&mut self, x: u32) -> u32;
}

pub struct Quarter(u32);

impl Sink for Quarter {
    #[trust::panic_free]
    fn absorb(&mut self, x: u32) -> u32 {
        //~^ ERROR must be declared on a trait method DEFINITION
        self.0 = x / 4;
        self.0
    }
}

#[trust::panic_free]
pub fn free_function(x: u32) -> u32 {
    //~^ ERROR must be declared on a trait method DEFINITION
    x / 4
}

fn main() {
    let mut quarter = Quarter(0);
    let _ = quarter.absorb(9);
    let _ = free_function(9);
}
