//@ needs-trust-verify
//@ edition: 2021
//@ revisions: default opt ascii certify controls
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[opt] compile-flags: -Copt-level=3
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[default] check-fail
//@[opt] check-fail
//@[ascii] check-fail
//@[certify] check-fail
//@[controls] check-pass
//! **Advancing an open `x..` range over a non-integer core `Step` type is charged
//! (STEP-ELEM-RANGEFROM-1; docs/KNOWN_HAZARDS.md and docs/DECISION_QUEUE.md,
//! STEP-ELEM-RANGEFROM-1).**
//!
//! `RangeFrom::next` (and `nth`, and every consumer that calls them) runs
//! `Step::forward(start, 1)`, which panics past the type's `MAX` for EVERY core `Step`
//! type: `Ipv4Addr`, `Ipv6Addr` and `AsciiChar` run core's default body,
//! ``forward_checked(start, n).expect("overflow in `Step::forward`")``, and `NonZero<uN>`
//! evaluates `uN::MAX + 1` under `#[rustc_inherit_overflow_checks]`
//! (`library/core/src/iter/range.rs`). trust-vcgen's `numeric_panic` charged the
//! `RangeFrom` iteration only for an integer or `char` element, so these calls got no
//! row: only the call's tolerated `runtime_checked` row, and the default policy accepted
//! a function whose binary panics (`range_from_step_types_charged_run.rs`).
//!
//! # Before (`scratchpad/stage1-w25f`, the wave-25 stage 1, tree of `a971311ee2`;
//! measured 2026-10-13 with exactly these revisions' flags plus `--cfg <revision>`,
//! outside compiletest)
//!
//! `default`, `opt` and `ascii` built rc=0: each function got only "Trust Level 0 safety
//! verification incomplete … 1 runtime-checked" (or "2 runtime-checked" for
//! `nonzero_next2`, whose second row is the bundled `<NonZero<u8> as Step>::forward`
//! member), so every annotated error was missing. `certify` built rc=1 (it refuses the
//! runtime-checked rows already). `controls` built rc=0.
//!
//! # After (FIX PREPARED 2026-10-13, not built; predicted)
//!
//! `numeric_panic::is_core_step_elem` (factored out of `step_call_can_panic`) is the
//! element test of the `RangeFrom` arms: a primitive integer, `char`, or core's
//! `NonZero<int>`, `AsciiChar`, `Ipv4Addr`, `Ipv6Addr` (authenticated root, exact type
//! token). Every advancing call over these types takes the fail-closed
//! `range-from-step-overflow-unmodeled` row its `u8` twin takes, so `default`, `opt` and
//! `ascii` are refused with every annotated error, as the `u8` twin is on the BEFORE
//! compiler (`scout26/openlies/step-confirm/ctl.rs`, rc=1). `certify` is unchanged.
//! `controls` (a bounded `x..=MAX` range, `checked_add`) stays rc=0. Predicted from
//! `crates/trust-vcgen/tests/std_numeric_family_realmir.rs`
//! (`core_step_elem_range_iteration_is_charged`, these bodies' real MIR dumped by the
//! BEFORE compiler).

#![allow(unused)]
#![cfg_attr(ascii, feature(ascii_char))]
use std::net::{Ipv4Addr, Ipv6Addr};
use std::num::NonZero;

#[cfg(any(default, opt, certify))]
pub fn ipv4_next2(x: Ipv4Addr) -> Option<Ipv4Addr> {
    //[default,opt,certify]~^ ERROR `range_from_step_types_charged::ipv4_next2`
    //[default,opt]~| NOTE unsupported MIR `range-from-step-overflow-unmodeled`
    let mut it = x..;
    it.next();
    it.next()
}

#[cfg(any(default, opt, certify))]
pub fn nonzero_next2(x: NonZero<u8>) -> Option<NonZero<u8>> {
    //[default,opt,certify]~^ ERROR `range_from_step_types_charged::nonzero_next2`
    let mut it = x..;
    it.next();
    it.next()
}

#[cfg(any(default, opt, certify))]
pub fn ipv4_find(x: Ipv4Addr) -> Option<Ipv4Addr> {
    //[default,opt,certify]~^ ERROR `range_from_step_types_charged::ipv4_find`
    (x..).find(|a| a.octets()[3] == 7)
}

#[cfg(any(default, opt, certify))]
pub fn ipv6_next2(x: Ipv6Addr) -> Option<Ipv6Addr> {
    //[default,opt,certify]~^ ERROR `range_from_step_types_charged::ipv6_next2`
    let mut it = x..;
    it.next();
    it.next()
}

// The by-value iterator of the stable `core::range::RangeFrom` (`RangeFromIter`).
#[cfg(any(default, opt, certify))]
pub fn newrange_v4_next2(x: Ipv4Addr) -> Option<Ipv4Addr> {
    //[default,opt,certify]~^ ERROR `range_from_step_types_charged::newrange_v4_next2`
    let mut it = core::range::RangeFrom::from(x..).into_iter();
    it.next();
    it.next()
}

// `core::ascii::Char` is nightly (`ascii_char`).
#[cfg(ascii)]
pub fn ascii_next2(x: core::ascii::Char) -> Option<core::ascii::Char> {
    //[ascii]~^ ERROR `range_from_step_types_charged::ascii_next2`
    let mut it = x..;
    it.next();
    it.next()
}

// ---- controls: a bounded range never steps past `MAX`, and `checked_add` is total ----

#[cfg(controls)]
pub fn ipv4_bounded(x: Ipv4Addr) -> Option<Ipv4Addr> {
    let mut it = x..=Ipv4Addr::BROADCAST;
    it.next();
    it.next()
}

#[cfg(controls)]
pub fn nonzero_checked(x: NonZero<u8>) -> Option<NonZero<u8>> {
    x.checked_add(1)
}

#[cfg(controls)]
pub fn ipv4_checked(x: Ipv4Addr) -> Option<Ipv4Addr> {
    x.to_bits().checked_add(1).map(Ipv4Addr::from_bits)
}
