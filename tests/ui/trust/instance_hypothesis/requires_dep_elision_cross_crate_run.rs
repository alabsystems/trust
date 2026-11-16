//@ revisions: advisory_direct advisory_pointer advisory_method off_direct off_pointer
//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: requires_dep_default_policy.rs
//@ compile-flags: -Coverflow-checks=on
//@[advisory_direct] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[advisory_pointer] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[advisory_method] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[off_direct] compile-flags: -Ztrust-verify=off
//@[off_pointer] compile-flags: -Ztrust-verify=off
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//! ADVISORY-REQUIRES-CROSS-CRATE (KNOWN_HAZARDS, CLOSED 2026-10-05). The in-crate
//! fix (`trait_impl_requires_advisory_keeps_check_run.rs`) keys the elision on the
//! policy of the crate that DEFINES the `requires` body, but a call from another
//! crate is charged under the CALLER's policy. `dep` is verified on the default
//! policy; this consumer is built advisory (its `Precondition` row against
//! `dep::add1` is FAILED, a warning) or verify-off (no row at all).
//!
//! BEFORE (stage 1 of `71fc7a07cc`, 2026-10-05): every revision built exit 0 and
//! printed `0` (the dependency's `x + 1` check had been elided under `x < 100`);
//! base stage 1 `1177c327fa` printed the same for the advisory direct call. A
//! verify-off build of BOTH crates panics. AFTER: a `requires` body reachable from
//! another crate keeps every check its clause proved, in every lane, so each run
//! panics with the overflow message. Verdicts are unchanged.

extern crate requires_dep_default_policy as dep;

#[inline(never)]
fn run(y: u32) -> u32 {
    #[cfg(any(advisory_direct, off_direct))]
    let r = dep::add1(y);
    #[cfg(any(advisory_pointer, off_pointer))]
    let r = {
        let fp: fn(u32) -> u32 = dep::add1;
        fp(y)
    };
    #[cfg(advisory_method)]
    let r = dep::S.add1m(y);
    r
}

fn main() {
    let y = std::hint::black_box(u32::MAX);
    println!("{} {}", run(y), dep::outer(y));
}
