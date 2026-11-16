//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: requires_callee_dep_off.rs
//@ compile-flags: -Ztrust-verify=off
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//! The WITNESS for `reject_foreign_requires_callee_as_value.rs` (residual L2,
//! docs/KNOWN_HAZARDS.md, the 2026-09-30 entry on "the fn-pointer `requires`
//! residuals"): the same `p`, built with verification OFF against the verify-off
//! build of `add1`, reaches `add1` with `u32::MAX` — outside its `requires x <
//! 100` — through the fn pointer, and the overflow check panics.
//!
//! With `add1` VERIFIED (`auxiliary/requires_callee_dep.rs`, the default policy)
//! that check is elided under the `requires`, and the same call RETURNS 0 instead
//! (measured 2026-09-30, a stage 1 of `3c29e31164`: a `p` built
//! `-Ztrust-policy=memory-safe` exit 0, linked into a verify-off `main`, printed
//! `p(u32::MAX) = 0`). So a verifier that admits `p` on any lane is admitting a
//! wrong value, not only a panic.

extern crate requires_callee_dep_off as dep;

pub fn p(y: u32) -> u32 {
    let fp: fn(u32) -> u32 = dep::add1;
    fp(y)
}

fn main() {
    println!("p(u32::MAX) = {}", p(std::hint::black_box(u32::MAX)));
}
