//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! The `write_fmt` reduction is keyed by the CALLEE NAME, so one unbacked site
//! must veto the whole name — including the literal site beside it.
//!
//! `trust_verify::static_str_write_fmt` discharges a `write!(w, "literal")` call
//! by reducing core's default `fmt::Write::write_fmt` to the receiver's own
//! `write_str`. That reduction is valid ONLY for an `Arguments` that
//! `Arguments::from_str` built: such a value's `as_str()` is `Some` by
//! construction, so both `spec_write_fmt` arms bottom out at exactly one
//! `write_str` call and `fmt::write`'s template loop — the part that runs user
//! `Display` impls — is unreachable.
//!
//! Both `write!`s below go through the SAME monomorphic
//! `<Sink as fmt::Write>::write_fmt`, and the discharge channel the bridge reads
//! is a set of callee STRINGS. The second one's `Arguments` carries a placeholder
//! whose `Display` panics, so the reduction does not hold there. Discharging the
//! name on the strength of the literal site alone would silently cover the
//! panicking one — a false proof of exactly the class `810baa6c4c` shipped.
//!
//! This file is the planted violation for that gate — but MEASURE what it pins
//! before trusting it. With the veto falsified (`all` => `any`, on a patched
//! compiler) the probe does discharge the name:
//!
//! ```text
//! TRUST_DYN_RELIANCE_PROBE: write_fmt site=<Sink as core::fmt::Write>::write_fmt => DISCHARGED
//! ```
//!
//! and `render` STILL fails — but its row changes from
//! `0 failed, 1 runtime-checked` (an honest fail-closed absent-callee row) to
//! `1 failed, 0 runtime-checked`: removing the fail-closed `Assert(false)` lets
//! the solver reach `Boom`'s panic and REFUTE the obligation. So the veto's
//! observable here is the ROW KIND, not the exit code, and this file is a
//! regression pin rather than a pass/fail guard. It stays red either way, which
//! is why its raw error-pattern annotation cannot by itself prove the veto is
//! present. (Do not spell that annotation literally in prose: compiletest scans
//! for the marker ANYWHERE in the file, comments included, and would register
//! this sentence as a second expected diagnostic.)
#![no_std]
#![allow(dead_code)]

use core::fmt::{self, Write as _};

pub struct Sink {
    written: u32,
}

impl fmt::Write for Sink {
    // Provably panic-free — so gate 4 (the reduction target's own independent
    // verdict) PASSES here, and this fixture isolates the all-sites veto.
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.written = self.written.wrapping_add(s.len() as u32);
        Ok(())
    }
}

pub struct Boom;

impl fmt::Display for Boom {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        panic!()
    }
}

pub fn render(sink: &mut Sink) -> fmt::Result {
    // Reducible on its own: `Arguments::from_str`-backed.
    let _ = write!(sink, "constant");
    // NOT reducible: `Arguments::new_v1` with a placeholder that runs `Boom`.
    write!(sink, "{}", Boom)
}
