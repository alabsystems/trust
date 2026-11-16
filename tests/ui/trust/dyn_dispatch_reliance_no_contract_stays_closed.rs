//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! ZERO-ROW-GATE AMENDMENT (2026-10-10, docs/DECISION_QUEUE.md ZERO-ROW-GATE): "THIS FILE NOW VERIFIES" below
//! no longer describes the exit status. `drive` still DISCHARGES its dyn call (it has
//! zero obligations of its own; the pinned NOTE says so), but the discharge is a
//! reliance certificate no authenticated panic-freedom registry records, so the body
//! publishes an `unknown` row and trustc refuses it (check-fail). Read "verifies"
//! below as "discharges". It recovers when the reliance lane mints an evidence row.
//!
//! THIS FILE NOW VERIFIES. The name is kept on purpose — it was the Φ mutant's
//! own record, and the measurement that flipped it belongs with it rather than
//! in a deleted file.
//!
//! WHAT IT USED TO RECORD (and the sentence that has to be retracted). It was
//! `dyn_dispatch_reliance_contract_discharges.rs` with Φ dropped and nothing
//! else changed, and its header said: "Without the declaration there is no
//! obligation on impls, so nothing was proved about the ones that exist and
//! nothing binds the ones a future crate could write… If this file ever passes,
//! the reliance gate has stopped reading the contract."
//!
//! BOTH HALVES OF THAT PREMISE ARE FALSE FOR THIS PROGRAM, and neither was when
//! it was written. "Nothing was proved about the ones that exist": `Counter::emit`
//! is `wrapping_add` and carries its own verdict. "Nothing binds the ones a
//! future crate could write": this is a BIN, so there is no future crate — which
//! is exactly what `dyn_trait_sealedness` means by `Sealed`.
//!
//! So C-SEALED discharges it (`TRUST_DYN_RELIANCE_PROBE` prints
//! `C-FLOW declined: trait Emitter poisoned` and then `C-SEALED trait=Emitter`),
//! on the enumerated impl set and each member's independent verdict — lattice
//! rung 2's certificate, which the generic twin `w4` has ridden since it was
//! wired. The conclusion is not that the gate stopped reading the contract; it
//! is that in a whole-program artifact the SEAL already gives what Φ gives, so
//! dropping Φ alone can no longer change the verdict. Rung 1's own comment says
//! it "subsumes" rung 2 whenever it applies; here rung 2 applies unaided.
//!
//! THE ASSERTION IS NOT LOST — it moved to a shape where it still bites.
//! `dyn_dispatch_reliance_no_contract_with_a_blanket_impl_stays_closed.rs` is the
//! same mutant over a trait with a BLANKET impl, which puts sealedness at `Open`
//! and leaves Φ as the only certificate available. That file is red, its
//! Φ-carrying twin is green, and the pair differs by the attribute alone.
//!
//! What is still pinned HERE is narrower and worth keeping: a virtual call in a
//! sealed whole program, whose one impl verifies, discharges — and `main`'s
//! remaining `[assert]` row is reported rather than fatal, because policy B
//! fails a function closed only on an unproved ASSUMPTION-panic row and this one
//! no longer has any.
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(trust)]

pub trait Emitter {
    fn emit(&mut self, byte: u8);
}

pub struct Counter {
    seen: u32,
}

impl Emitter for Counter {
    fn emit(&mut self, byte: u8) {
        self.seen = self.seen.wrapping_add(byte as u32);
    }
}

// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//~vv ERROR Trust strict verification failed for `dyn_dispatch_reliance_no_contract_stays_closed::drive`
//~v NOTE this function has no obligation of its own
pub fn drive(emitter: &mut dyn Emitter) {
    emitter.emit(7);
}

fn main() {
    let mut counter = Counter { seen: 0 };
    drive(&mut counter);
}
