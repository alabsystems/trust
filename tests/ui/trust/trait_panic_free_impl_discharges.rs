//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! Rung 1, the positive case: a `#[trust::panic_free]` trait method whose every
//! implementation discharges the inherited obligation.
//!
//! Two things must hold for this fixture to be evidence of anything:
//!
//!   * every impl of `Sink::absorb` is verified panic-free where its BODY is
//!     written, which is what the contract on the trait method obliges; and
//!   * `drive` calls `<S as Sink>::absorb` on a bare type parameter, so trait
//!     selection cannot pick an impl and `Instance::try_resolve` returns
//!     `Ok(None)`. Before rung 1 that call was the R3 frontier — "at mono an
//!     impl may supply a body that panics" — and `drive` could not verify.
//!     It verifies now because the obligation was MOVED to the implementors,
//!     not because it was waived: the trait is local and this is a
//!     whole-program artifact, so the impls checked above are every impl that
//!     can ever reach the call.
//!
//! If this fixture ever fails, either per-impl discharge stopped crediting a
//! genuinely proved body, or the reliance gate stopped applying to a case it
//! covers. If it ever passes while `trait_panic_free_impl_todo_fails.rs` also
//! passes, the rule has become a false promise and both must be read together.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![feature(register_tool)]
#![register_tool(trust)]

pub trait Sink {
    #[trust::panic_free]
    fn absorb(&mut self, x: u32) -> u32;
}

pub struct Quarter(u32);

impl Sink for Quarter {
    fn absorb(&mut self, x: u32) -> u32 {
        // A real, discharged obligation: division by a nonzero literal. A body
        // with ZERO obligations is refused by the discharge predicate, because
        // "no obligations" is indistinguishable from "never verified".
        self.0 = x / 4;
        self.0
    }
}

pub struct Masked(u32);

impl Sink for Masked {
    fn absorb(&mut self, x: u32) -> u32 {
        self.0 = x % 8;
        self.0
    }
}

/// `<S as Sink>::absorb` is statically unresolvable here.
pub fn drive<S: Sink>(sink: &mut S, x: u32) -> u32 {
    sink.absorb(x)
}

// `main` deliberately does NOT call `drive`. A caller of a local GENERIC
// function currently keeps an absent-callee panic-freedom obligation for the
// monomorphized callee — measured identically before and after this change, so
// it is a pre-existing cross-function modularity gap and not rung 1's subject.
// Mixing it in here would make this fixture fail for a reason it is not about.
fn main() {
    let mut quarter = Quarter(0);
    let mut masked = Masked(0);
    let _ = quarter.absorb(9);
    let _ = masked.absorb(9);
}
