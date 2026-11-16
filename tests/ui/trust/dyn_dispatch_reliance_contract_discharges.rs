//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! C-UNIVERSAL: a call through `InstanceKind::Virtual` discharges FROM the trait
//! method's `#[trust::panic_free]` contract.
//!
//! `drive` takes `&mut dyn Emitter` as its OWN parameter, so the receiver's
//! vtable was built by a caller this bundle never sees. C-FLOW therefore poisons
//! `Emitter` and contributes nothing — this fixture isolates the contract lane.
//!
//! What makes the reliance sound is not the annotation but the obligation it
//! creates: Φ sits on the trait DEFINITION, so every impl anywhere is bound at
//! the point it is written (an impl must name the trait, and naming it loads the
//! metadata that carries Φ), and `trait_panic_free`'s §(b) makes each impl's
//! discharge a compile error at the impl. The remaining escape — a crate compiled
//! later adding an impl — is closed by the whole-program crate type, which this
//! test has and `dyn_dispatch_reliance_contract_rlib_stays_closed.rs` does not.
//!
//! Before this rule the virtual call reported:
//!
//! ```text
//! error: an unproven panic-freedom obligation for a call to an absent callee ...
//! error: Trust strict verification failed for `drive`
//! ```
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(trust)]

pub trait Emitter {
    #[trust::panic_free]
    fn emit(&mut self, byte: u8);
}

pub struct Counter {
    seen: u32,
}

impl Emitter for Counter {
    // Discharges Φ: `wrapping_add` has no panic edge and the widening cast is
    // total, so this body carries no panic-capable construct.
    fn emit(&mut self, byte: u8) {
        self.seen = self.seen.wrapping_add(byte as u32);
    }
}

pub struct Latch {
    last: u8,
}

impl Emitter for Latch {
    fn emit(&mut self, byte: u8) {
        self.last = byte;
    }
}

// The virtual call. Its receiver is erased; the contract is what discharges it.
// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//~vv ERROR Trust strict verification failed for `dyn_dispatch_reliance_contract_discharges::drive`
//~v NOTE this function has no obligation of its own
pub fn drive(emitter: &mut dyn Emitter) {
    emitter.emit(7);
}

fn main() {
    let mut counter = Counter { seen: 0 };
    drive(&mut counter);
    let mut latch = Latch { last: 0 };
    drive(&mut latch);
}
