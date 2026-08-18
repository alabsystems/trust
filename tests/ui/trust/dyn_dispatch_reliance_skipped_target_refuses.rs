//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! MUTANT: a case-split member the user `#[trust::skip]`'d must REFUSE the
//! discharge, not launder it.
//!
//! A skipped body is unverified by decree and produces a zero-obligation
//! artifact, which is shape-identical to "trivially panic-free". If the case
//! split read that shape as evidence, `#[trust::skip]` on an impl would silently
//! buy panic-freedom for every `dyn` call that can reach it — the exact
//! escape-hatch-turned-proof hazard the rung-2 gate already refuses by checking
//! the attribute explicitly. `dyn_target_is_verified_panic_free` checks it too,
//! and the same refusal covers `#[trust::assume_total]`, which is an axiom rather
//! than a proof.
//!
//! So `render` keeps its absent-callee obligation and fails, even though the
//! provenance analysis enumerated the target set perfectly.
#![no_std]
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(trust)]

use core::fmt;

pub struct Sink {
    written: u32,
}

impl fmt::Write for Sink {
    #[trust::skip]
    fn write_str(&mut self, s: &str) -> fmt::Result { //~ ERROR Trust full verification skipped
        self.written = self.written.wrapping_add(s.len() as u32);
        Ok(())
    }
}

pub fn render(sink: &mut Sink) -> fmt::Result {
    use fmt::Write as _;
    write!(sink, "constant")
    //~^^^ ERROR Trust strict verification failed
}
