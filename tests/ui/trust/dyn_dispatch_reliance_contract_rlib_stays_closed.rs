//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! MUTANT of `dyn_dispatch_reliance_contract_discharges.rs`: same Φ, same impls,
//! compiled as an RLIB.
//!
//! The impl set is no longer closed. A downstream crate can name `Emitter`, write
//! its own impl, and link against this one — and although Φ binds that impl too,
//! THIS compilation has no evidence the downstream crate was compiled under a
//! toolchain that enforces the discharge. Closing that needs the per-crate
//! discharge seal plus a deferred link-closure obligation; neither exists, and
//! an rlib must not be allowed to assume them.
//!
//! So the certificate fails on the whole-program condition alone and the virtual
//! call keeps its obligation. Every leaf crate in a workspace is an rlib, which
//! is exactly why this refusal is the one that matters most in practice.
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
    fn emit(&mut self, byte: u8) {
        self.seen = self.seen.wrapping_add(byte as u32);
    }
}

pub fn drive(emitter: &mut dyn Emitter) {
    emitter.emit(7);
    //~^^ ERROR Trust strict verification failed
}
