//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Rung 1 §(b3): the user opt-outs are REFUSED on an implementation of a
//! `#[trust::panic_free]` trait method — not demoted, not recorded as an
//! assumption, refused.
//!
//! This is the single most attackable point in the rule. A skipped body has no
//! proof, so it can be the innermost frame in the soundness argument, and the
//! argument collapses. Every other escape in the enumeration fails CLOSED
//! (an unsealed dependency, an unresolvable flow) and merely costs completeness;
//! this one would fail OPEN, because the call site would still credit the
//! contract while nothing behind it was ever proved.
//!
//! Note the policy: `-Ztrust-policy=advisory` is the lane in which
//! `#[trust::skip]` is an ACCEPTED unverified assumption for ordinary bodies.
//! That acceptance must not extend to a body that inherited a contract. If this
//! fixture ever compiles, the opt-out has become a way to mint the premise
//! without paying for it.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![feature(register_tool)]
#![register_tool(trust)]

pub trait Sink {
    #[trust::panic_free]
    fn absorb(&mut self, x: u32) -> u32;
}

pub struct Skipped(u32);

impl Sink for Skipped {
    #[trust::skip]
    fn absorb(&mut self, x: u32) -> u32 {
        //~^ ERROR cannot be applied to an implementation of `#[trust::panic_free]` trait method
        assert!(x < 4, "unreachable only if you trust the skip");
        self.0 = x;
        self.0
    }
}

fn main() {
    let mut skipped = Skipped(0);
    let _ = skipped.absorb(1);
}
