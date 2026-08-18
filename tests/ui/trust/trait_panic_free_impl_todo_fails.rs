//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Rung 1, the refutation: an implementation of a `#[trust::panic_free]` trait
//! method whose body is `todo!()`.
//!
//! The point of this fixture is WHERE the error lands. The obligation was
//! declared on `Sink::absorb`, but the body that fails to honor it belongs to
//! `<NotDone as Sink>::absorb`, and that is where the diagnostic must point —
//! naming the trait method whose contract it failed. A call-site error would be
//! useless to the person who has to fix the body, and a `dyn` call site is not
//! even in this file.
//!
//! `todo!()` is `panic!("not yet implemented")`: an unconditional, non-call
//! panic instruction in the impl's OWN body. That is precisely the case the
//! innermost-frame soundness argument says a contract can never launder — the
//! frame that raises is the frame whose own proof had to cover it.
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
        self.0 = x / 4;
        self.0
    }
}

pub struct NotDone;

impl Sink for NotDone {
    fn absorb(&mut self, _x: u32) -> u32 {
        //~^ ERROR this implementation of `#[trust::panic_free]` trait method
        todo!()
    }
}

fn main() {
    let mut quarter = Quarter(0);
    let _ = quarter.absorb(9);
}
