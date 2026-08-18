//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! TRANSITIVITY: the axiom is not in the reduction target's body at all — it is in
//! a helper the target calls.
//!
//! `write_str` calls only `helper`, an ordinary local function with no attribute.
//! `helper` calls the axiom. The refusal must still fire, because the property the
//! gate tests is "does this VERDICT rest on a user axiom", and `helper` is a member
//! of the bundle `write_str` was verified as — its axiom is in the same census.
//!
//! This is the fixture that would go green under a gate written as "does the target
//! body contain a call to an `#[trust::assume_total]` callee". Depth is unbounded:
//! the census is taken over the ROOT BODY AND EVERY BUNDLED MEMBER, and a member
//! the census could not read (no MIR, stolen with no snapshot) makes the whole
//! verdict unspendable rather than clean.
//!
//! MEASURED on stage-equivalent main `0a3cd01520`: rc=0 (ACCEPTED).
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

/// No attribute of its own. The axiom is BELOW this frame.
fn helper(n: u32) -> u32 {
    boom();
    n.wrapping_add(1)
}

pub struct Sink {
    written: u32,
}

impl fmt::Write for Sink {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.written = helper(s.len() as u32);
        Ok(())
    }
}

pub fn render(sink: &mut Sink) -> fmt::Result {
    use fmt::Write as _;
    write!(sink, "constant")
}
