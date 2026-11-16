//@ revisions: override_runs default_body_panics
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=on
//@[override_runs] run-pass
//@[default_body_panics] run-fail
//@[default_body_panics] error-pattern: attempt to divide by zero
//@ ignore-emscripten no processes
//! The runtime WITNESS for `trait_default_requires_override_not_charged.rs`
//! (DEFAULT-REQUIRES-OVERRIDE-CHARGE-1): the same trait `Tq`, whose default body
//! owes `requires x != 0`, built with verification OFF.
//!
//! * `override_runs`: `C`'s override is total. `c.q(0)`, `<C as Tq>::q(&C, 0)` and
//!   `C::q(&C, 0)` run it and return 0, so the default's clause, which the verified
//!   build charged at those calls before the fix, guards nothing that runs there.
//! * `default_body_panics`: `impl Tq for A {}` runs the default body, and `A.q(0)`
//!   divides by zero. That is the call the fix keeps charged.
//!
//! MEASURED 2026-10-06 on `scratchpad/stage1-w21before` (the stage 1 of
//! `46e9afaf95`) with these flags: `override_runs` exits 0 and `default_body_panics`
//! exits 101 with the pattern above. The binary does not depend on the verifier, so
//! the fix does not change it.

pub trait Tq {
    fn q(&self, x: u32) -> u32
        requires x != 0
    {
        100 / x
    }
}

#[cfg(override_runs)]
pub struct C;
#[cfg(override_runs)]
impl Tq for C {
    fn q(&self, x: u32) -> u32 {
        x
    }
}

#[cfg(default_body_panics)]
pub struct A;
#[cfg(default_body_panics)]
impl Tq for A {}

#[cfg(override_runs)]
fn main() {
    let zero = std::hint::black_box(0u32);
    assert_eq!(C.q(zero), 0);
    assert_eq!(<C as Tq>::q(&C, zero), 0);
    assert_eq!(C::q(&C, zero), 0);
}

#[cfg(default_body_panics)]
fn main() {
    let zero = std::hint::black_box(0u32);
    println!("A.q(0) = {}", A.q(zero));
}
