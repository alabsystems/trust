//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! MUTANT: the `write!` reduction must REFUSE a `write_str` whose own panic
//! freedom RESTS ON a `#[trust::assume_total]` axiom.
//!
//! `boom` is an axiom, not a proof: `#[trust::assume_total]` records the callee's
//! totality as an audited user declaration and is deliberately non-fatal in every
//! policy. `<Sink as Write>::write_str` therefore verifies — CONDITIONALLY on that
//! declaration — and the reduction used to read the conditional verdict as
//! panic-freedom.
//!
//! What makes the reduction worse than an ordinary caller is where the axiom ENDS
//! UP. Written directly (`sink.write_str("constant")`) `write_str` is bundled into
//! the caller, so the caller's own bundle carries the axiom. Through `write!` the
//! target is reached via core frames (`Write::write_fmt` -> `spec_write_fmt` ->
//! `fmt::write`) that are NOT in the caller's bundle, so the reduction consumed
//! the axiom and MINTED a discharge from it: the absent-callee row was dropped and
//! `render` came out with ZERO obligations. The axiom vanished.
//!
//! MEASURED on stage-equivalent main `0a3cd01520` (the compiler WITHOUT the
//! assumption-root gate): this file compiles CLEAN, rc=0, and
//! `TRUST_DYN_RELIANCE_PROBE=1` prints
//! `write_fmt site=<Sink as core::fmt::Write>::write_fmt (1 site(s)) => DISCHARGED`.
//! With the gate the same probe prints `=> kept (reduction target … is proved only
//! CONDITIONALLY: …)`.
//!
//! Everything else here is the DISCHARGING shape — the `Arguments` is
//! `from_str`-backed, the callee key names exactly one bundled call, the receiver
//! is concrete, and the arithmetic is `wrapping_add` — so the axiom underneath the
//! reduction target is the only thing keeping `render` red. Delete `boom()` from
//! the body and the file goes green, which is
//! `static_str_write_fmt_concrete_sink`-style discharge working as designed.
#![no_std]
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(trust)]

use core::fmt;

/// An axiom the author asserted and nobody proved — and it is FALSE.
#[trust::assume_total]
fn boom() {
    panic!("boom");
}

pub struct Sink {
    written: u32,
}

impl fmt::Write for Sink {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        boom();
        self.written = self.written.wrapping_add(s.len() as u32);
        Ok(())
    }
}

pub fn render(sink: &mut Sink) -> fmt::Result {
    use fmt::Write as _;
    write!(sink, "constant")
}
