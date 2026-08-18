//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! Rung 1 §(b): an implementation whose panic freedom RESTS ON a user axiom does
//! not discharge Φ — the axiom is one frame down, where §(b3)'s attribute check
//! cannot see it.
//!
//! `trait_panic_free_skip_is_refused.rs` pins the opt-out written ON the impl
//! body. This fixture is the frame BELOW that: `Counter::emit` carries no
//! attribute at all, and its body's only panic risk is a call to a
//! `#[trust::assume_total]` callee. Its verdict is therefore CONDITIONAL, and
//! MEASURED on pristine main its ledger is byte-identical to a genuinely
//! obligation-free body — so §(b)'s evidence bar credited it and the contract was
//! discharged from an axiom.
//!
//! Why that is fail-OPEN rather than merely incomplete: Φ's whole purpose is to
//! let a `dyn`/generic call site rely on the contract WITHOUT enumerating impls
//! (C-UNIVERSAL). That reliance never consults the case-split evidence bar, so
//! an unsound Φ discharge is spent at every virtual call to the trait. `drive`
//! below verifies clean on pristine main and then panics at runtime.
//!
//! MEASURED on stage-equivalent main `0a3cd01520`: rc=0 (ACCEPTED). With the
//! assumption-root conjunct in the shared bar the error lands AT THE IMPL, which
//! is where its author can fix it.
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(trust)]

/// An axiom the author asserted and nobody proved — and it is FALSE.
#[trust::assume_total]
fn boom() {
    panic!("boom");
}

pub trait Emitter {
    #[trust::panic_free]
    fn emit(&mut self, byte: u8);
}

pub struct Counter {
    seen: u32,
}

impl Emitter for Counter {
    // The error lands on this method's own name — §(b) reports a contract failure
    // at the impl, never at the distant call site.
    fn emit(&mut self, byte: u8) {
        boom();
        self.seen = self.seen.wrapping_add(byte as u32);
    }
}

// The virtual call C-UNIVERSAL discharges from the contract alone.
pub fn drive(emitter: &mut dyn Emitter) {
    emitter.emit(7);
}

fn main() {
    let mut counter = Counter { seen: 0 };
    drive(&mut counter);
}
