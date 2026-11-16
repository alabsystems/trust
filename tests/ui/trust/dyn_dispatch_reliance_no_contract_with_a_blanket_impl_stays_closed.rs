//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: this function has no obligation of its own
//! THE Φ MUTANT, REBUILT 2026-09-19 on a shape the SEAL cannot reach.
//!
//! `dyn_dispatch_reliance_no_contract_stays_closed.rs` used to be this test: drop
//! Φ from a whole-program program and watch the virtual call stay closed. It no
//! longer isolates Φ, and the reason is not a regression — C-SEALED discharges
//! that program on the seal alone, which is a second certificate of the same
//! strength, not a hole. See that file's header.
//!
//! A BLANKET impl is what separates the two certificates, and it is the only
//! thing changed here. `dyn_trait_sealedness` returns `Open` the moment a trait
//! has one (unboundedly many impl types, no enumeration), so rung 2 and C-SEALED
//! are both unavailable. Rung 1 is not: Φ is discharged polymorphically at the
//! blanket impl's own definition, which is exactly why its doc says it "accepts
//! blanket and generic impls" where rung 2 cannot.
//!
//! So this file and `dyn_dispatch_reliance_contract_over_a_blanket_impl_discharges.rs`
//! differ by the attribute and nothing else, and they measure opposite verdicts.
//! If THIS file ever passes, the reliance gate has stopped reading the contract —
//! the assertion the old mutant carried, restated where it still bites.
#![allow(dead_code)]

pub trait Base {
    fn base(&self) -> u32;
}

pub trait Emitter {
    fn emit(&mut self, byte: u8);
}

impl<T: Base> Emitter for T {
    fn emit(&mut self, _byte: u8) {}
}

pub struct Counter {
    seen: u32,
}

impl Base for Counter {
    fn base(&self) -> u32 {
        self.seen
    }
}

pub fn drive(emitter: &mut dyn Emitter) {
    emitter.emit(7);
    //~^^ ERROR Trust strict verification failed
}

fn main() {
    let mut c = Counter { seen: 0 };
    drive(&mut c);
}

// ZERO-ROW-GATE (2026-10-10): this rail must refuse for its OWN reason; a refusal by the
// zero-row gate (whose note is forbidden here) would mean the gate under test regressed
// into discharging and the zero-row gate masked it.
