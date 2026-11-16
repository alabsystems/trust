//@ needs-trust-verify
//@ edition: 2021
//@ revisions: step certify guarded_loss controls
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[step] check-fail
//@[certify] check-fail
//@[guarded_loss] check-fail
//@[controls] check-pass
//! **A direct `Step::forward` / `Step::backward` call is charged (STEP-TRAIT-DIRECT-
//! UNCHARGED-1; docs/KNOWN_HAZARDS.md, "FIX PREPARED 2026-10-11 … a direct
//! `Step::forward`/`Step::backward` call"; docs/DECISION_QUEUE.md,
//! STEP-TRAIT-DIRECT-UNCHARGED-1).**
//!
//! The nightly `step_trait` methods `Step::forward(start, n)` and `Step::backward(start,
//! n)` panic on the caller's value: `char`'s run core's default body,
//! `forward_checked(start, n).expect("overflow in `Step::forward`")` (and its `backward`
//! twin), and the integers' evaluate `Self::MAX + 1` / `Self::MIN - 1` under
//! `#[rustc_inherit_overflow_checks]` exactly when the checked form fails. The numeric
//! value-panic family charged this panic when it is reached through `RangeFrom::next`,
//! but had no arm for the trait method called directly: the `char` calls were admitted
//! `vanilla=true`, and the integer calls' check was reported only as a bundled member's
//! internal obligation.
//!
//! # Before (stage 1 of `1213387e6d`, `scratchpad/stage1-w24probe`, measured 2026-10-11
//! with exactly these revisions' flags plus `--cfg <revision> --emit=metadata`)
//!
//! `step` built rc=0 with 14 warnings: each function (and the closure
//! `closure_fwd::{closure#0}`) got "Trust Level 0 safety verification incomplete … 1
//! runtime-checked", so every annotated error was missing. `certify` built rc=1 (14 errors).
//! `guarded_loss` and `controls` built rc=0. The run twin
//! `std_step_trait_value_panics_charged_run.rs` (verification OFF) exits 101 on every body
//! here, with the same exit codes and messages as stock nightly rustc (`14cae6813`,
//! `nightly-2026-07-09`, run by path; stable cannot build `step_trait`).
//!
//! # After (predicted, not built)
//!
//! `numeric_panic` gains `const STEP` (`core::iter::range::Step`, the trait half
//! authenticated) and `step_call_can_panic`: `forward`/`backward` on a primitive integer,
//! `char`, or core's `NonZero<int>`, `AsciiChar`, `Ipv4Addr`, `Ipv6Addr`. The name-level
//! gate answers `true` (a fn item is withheld), and the call mints the fail-closed
//! `step-forward-overflow-unmodeled` / `step-backward-overflow-unmodeled` row. `step` is
//! refused with every annotated error; `certify` is unchanged; `controls` (the total
//! `forward_checked`/`backward_checked`) stays rc=0. Predicted from
//! `crates/trust-vcgen/tests/std_numeric_family_realmir.rs` (`step_trait_direct_calls_are_charged`,
//! these bodies' real MIR dumped by the BEFORE compiler) and from the `RangeFrom` row the
//! BEFORE compiler already refuses with the same kind of fail-closed row.
//!
//! `guarded_loss` pins the cost (rc=0 before, predicted refused after): no linear row is
//! built for a direct `Step` call, so a guarded call that cannot panic is refused.

#![allow(unused)]
#![feature(step_trait)]
use std::iter::Step;

#[cfg(any(step, certify))]
pub fn fwd_char(c: char, n: usize) -> char {
    //[step,certify]~^ ERROR `std_step_trait_value_panics_charged::fwd_char`
    Step::forward(c, n)
}

#[cfg(any(step, certify))]
pub fn bwd_char(c: char, n: usize) -> char {
    //[step,certify]~^ ERROR `std_step_trait_value_panics_charged::bwd_char`
    Step::backward(c, n)
}

#[cfg(any(step, certify))]
pub fn fwd_u8(x: u8, n: usize) -> u8 {
    //[step,certify]~^ ERROR `std_step_trait_value_panics_charged::fwd_u8`
    Step::forward(x, n)
}

#[cfg(any(step, certify))]
pub fn bwd_i32(x: i32, n: usize) -> i32 {
    //[step,certify]~^ ERROR `std_step_trait_value_panics_charged::bwd_i32`
    Step::backward(x, n)
}

#[cfg(any(step, certify))]
pub fn closure_fwd(o: Option<(char, usize)>) -> Option<char> {
    o.map(|(c, n)| Step::forward(c, n))
    //[step,certify]~^ ERROR `std_step_trait_value_panics_charged::closure_fwd::{closure#0}`
}

// ---- guarded_loss: the recorded over-refusal (DECISION_QUEUE STEP-TRAIT-DIRECT-UNCHARGED-1) ----

// A guarded call cannot panic; no linear row is built for a direct `Step` call, so it is
// refused.
#[cfg(guarded_loss)]
pub fn guarded_fwd_char(c: char) -> char {
    //[guarded_loss]~^ ERROR `std_step_trait_value_panics_charged::guarded_fwd_char`
    if c >= 'a' && c < 'z' { Step::forward(c, 1) } else { c }
}

#[cfg(guarded_loss)]
pub fn guarded_fwd_u8(x: u8) -> u8 {
    //[guarded_loss]~^ ERROR `std_step_trait_value_panics_charged::guarded_fwd_u8`
    if x < 255 { Step::forward(x, 1) } else { x }
}

// ---- controls: the total siblings stay accepted ----

#[cfg(controls)]
pub fn fwd_checked(c: char, n: usize) -> Option<char> {
    Step::forward_checked(c, n)
}

#[cfg(controls)]
pub fn bwd_checked(x: u8, n: usize) -> Option<u8> {
    Step::backward_checked(x, n)
}
