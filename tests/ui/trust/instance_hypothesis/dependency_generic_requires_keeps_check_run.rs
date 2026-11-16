//@ revisions: advisory off
//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: od2_requires_dep.rs
//@ compile-flags: -Coverflow-checks=on
//@[advisory] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-bundle-foreign-crate=od2_requires_dep
//@[off] compile-flags: -Ztrust-verify=off
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//! OD-1 PHASE 2 x ADVISORY-REQUIRES-CROSS-CRATE (2026-10-05). The dependency's
//! generic `fr` carries an open dispatch AND a `requires i < 100` that proves its
//! `i + 1`. This consumer instantiates `fr::<Good>` (advisory: the instance's
//! discharge row is minted from the re-derived site and reads `assumed`; the
//! precondition row against `fr` FAILS, a warning) or is verify-off (no rows), and
//! calls it with `u32::MAX`. The elision gate is keyed on reachability from
//! another crate, not on the dependency's policy or on any phase-2 row, so the
//! check runs in BOTH lanes and the program panics instead of returning 0.

extern crate od2_requires_dep as dep;

pub struct Good;

impl dep::Tr for Good {
    fn m(&self) -> u32 {
        1
    }
}

fn main() {
    let i = std::hint::black_box(u32::MAX);
    println!("{}", dep::fr(&Good, i));
}
