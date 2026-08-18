//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! MUTANT: the `write!` reduction must refuse a `write_str` that reaches a
//! `#[trust::assume_total]` axiom through a REIFIED FUNCTION POINTER.
//!
//! The sibling `static_str_write_fmt_assumed_total_root_stays_closed.rs` calls the
//! axiom directly. This one spells the same dependency `let f: fn() = boom; f();`,
//! which lowers to a `ReifyFnPointer` cast plus an INDIRECT call. There is no
//! `FnDef` call operand, so no key reaches the bridge's `assumed_total` set and the
//! bundle's user-axiom census — which read only call operands — came back EMPTY.
//!
//! MEASURED, both states, on two compilers built from this tree: with the
//! call-operand census alone the bundle publishes
//! `axiom census root=<Sink as core::fmt::Write>::write_str axiom_free=true` and
//! `write_fmt site=… => DISCHARGED`, and this file compiles rc=0. With
//! `collect_user_axiom_value_mentions` the same probe prints `axiom_free=false`
//! (`user_axiom_keys=1, assumed_total=0` — the axiom is CENSUSED without being
//! SPENT) and the reduction is `kept`.
//!
//! The census half this exercises writes NO bridge set, so it cannot change how
//! any call lowers: the only verdict it can move is this one, and only to refuse.
//! Delete the `#[trust::assume_total]` attribute and `boom` is verified on its own
//! merits instead of assumed — which is the control this fixture is graded against.
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
        let f: fn() = boom;
        f();
        self.written = self.written.wrapping_add(s.len() as u32);
        Ok(())
    }
}

pub fn render(sink: &mut Sink) -> fmt::Result {
    use fmt::Write as _;
    write!(sink, "constant")
}
