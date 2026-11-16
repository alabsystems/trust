//@ only-apple
//@ proc-macro: forger.rs
//@ revisions: in_process isolated
//@[isolated] compile-flags: -Ztrust-proc-macro-isolation
//@ check-pass
//! Trust (D21): a macro that writes a complete JSON diagnostic to stderr.
//!
//! * `in_process` is the control: the macro shares rustc's stderr, so the forged
//!   line arrives as a compiler diagnostic. This harness, which reads rustc's
//!   diagnostics from that stream, accepts it as one: the `WARN` annotation below
//!   is matched by the macro's text, not by anything rustc said.
//! * `isolated`: the worker's stderr and stdout are the null device, so rustc's
//!   streams carry only what rustc wrote. No annotation, no expected stderr: one
//!   forged byte arriving would fail this revision as an unexpected diagnostic.

extern crate forger;

forger::forge_compiler_message!();

fn main() {}

//[in_process]~? WARN forged by a proc macro: all obligations proved
