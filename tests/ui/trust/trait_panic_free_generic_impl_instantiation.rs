//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Rung 1 §(b2): an implementation that is panic-free in one instantiation and
//! not in another — and where the design says the error must land.
//!
//! `Fwd<S>` is that implementation. `Fwd<Quarter>::absorb` never panics;
//! `Fwd<Panicky>::absorb` always does. The design does NOT resolve this by
//! monomorphizing and blaming `Fwd`. `Fwd` discharges POLYMORPHICALLY: its
//! body's only call is `<S as Sink>::absorb` with `S` bounded by `Sink`, and
//! that call's obligation is discharged from the contract itself
//! (reliance-inside-discharge). The apparent circularity — relying on Φ while
//! proving Φ — is not circular, because the soundness argument takes the
//! INNERMOST frame at the moment of the panic in one step and never inducts on
//! call depth. `Fwd<Fwd<...<Panicky>>>` terminates at the frame that actually
//! raises, and that frame is `Panicky`'s.
//!
//! So the expected behavior is exactly one rung-1 refutation, at
//! `<Panicky as Sink>::absorb`, and NONE at `<Fwd<S> as Sink>::absorb`. The
//! forwarding impl is correct code and must not be blamed for its instantiation.
//! If `Fwd` is ever the one reported, reliance-inside-discharge has regressed
//! and every forwarding/blanket impl in the ecosystem becomes unprovable. If
//! NEITHER is reported, the contract laundered a panic through a wrapper, which
//! is the M5 mutant and a soundness regression.
//!
//! `Fwd` does still carry a separate, honestly-reported failure of its own: its
//! TERMINATION obligation is refuted, because the verifier cannot bound a call
//! whose target is not pinned until monomorphization. That is a different lane
//! and rung 1 neither fixes nor suppresses it. It is also exactly why the
//! contract is panic-freedom and NOT total correctness: if Φ promised
//! termination, `Fwd` could never discharge it, reliance-inside-discharge would
//! be circular, and the rule would be unsound. Divergence satisfies a safety
//! property vacuously — a function that never returns also never panics.
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

pub struct Panicky(u32);

impl Sink for Panicky {
    fn absorb(&mut self, x: u32) -> u32 {
        //~^ ERROR this implementation of `#[trust::panic_free]` trait method
        assert!(x < 4, "a trait method is user code, and user code panics");
        self.0 = x;
        self.0
    }
}

/// The instantiation-dependent implementation. Proved once, for all `S`.
pub struct Fwd<S>(S);

impl<S: Sink> Sink for Fwd<S> {
    fn absorb(&mut self, x: u32) -> u32 {
        self.0.absorb(x)
    }
}

fn main() {
    let mut good = Fwd(Quarter(0));
    let mut bad = Fwd(Panicky(0));
    let _ = good.absorb(9);
    let _ = bad.absorb(9);
}
