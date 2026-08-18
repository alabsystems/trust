//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! MUTANT of `dyn_dispatch_reliance_contract_discharges.rs`: drop Φ from the trait
//! method. Everything else — the impls, their bodies, the whole-program crate
//! type — is byte-identical.
//!
//! Without the declaration there is no obligation on impls, so nothing was
//! proved about the ones that exist and nothing binds the ones a future crate
//! could write. The virtual call must keep its fail-closed absent-callee
//! obligation.
//!
//! This is the test that separates "the contract discharged the call" from "the
//! call was quietly waved through because it was virtual". If this file ever
//! passes, the reliance gate has stopped reading the contract.
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

pub fn drive(emitter: &mut dyn Emitter) {
    emitter.emit(7);
    //~^^ ERROR Trust strict verification failed
}

fn main() {
    let mut counter = Counter { seen: 0 };
    drive(&mut counter);
}
