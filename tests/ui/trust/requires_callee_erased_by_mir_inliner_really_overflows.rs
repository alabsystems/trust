//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Copt-level=3 -Zmir-opt-level=2 -Coverflow-checks=on
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//! The WITNESS for `requires_callee_erased_by_mir_inliner.rs` (residual L3,
//! docs/KNOWN_HAZARDS.md, "FIX PREPARED 2026-09-30 … — under an explicit
//! `-Zmir-opt-level=2` …"): the same `add1` and `f`, at the same inliner flags,
//! built with verification OFF. The MIR inliner still folds `map`, the `FnOnce`
//! shim and `add1` into `f`, but nothing elided `add1`'s overflow check, so
//! `f(u32::MAX)` — outside `requires x < 100` — panics.
//!
//! Verified BEFORE the fix, the check was elided under the `requires` in the body
//! the inliner copied, and nothing charged the erased call: that `f`, built under
//! `-Ztrust-policy=certify` at these flags and linked into a verify-off `main`,
//! RETURNED `f(u32::MAX) = Some(0)` (measured 2026-09-30, a stage 1 of
//! `fbc6068e3`). So admitting it was admitting a wrong value, not only a panic.
//! `-Coverflow-checks=on` keeps this build's check: at `-Copt-level=3` a
//! verify-off session has overflow checks off, and `x + 1` would wrap here too.

pub fn add1(x: u32) -> u32
    requires x < 100
{
    x + 1
}

pub fn f(y: u32) -> Option<u32> {
    Some(y).map(add1)
}

fn main() {
    println!("f(u32::MAX) = {:?}", f(std::hint::black_box(u32::MAX)));
}
