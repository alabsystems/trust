//@ revisions: advisory_via off_via advisory_chain off_method off_assoc
//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: requires_dep_transitive_default_policy.rs
//@ compile-flags: -Coverflow-checks=on
//@[advisory_via] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[off_via] compile-flags: -Ztrust-verify=off
//@[advisory_chain] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[off_method] compile-flags: -Ztrust-verify=off
//@[off_assoc] compile-flags: -Ztrust-verify=off
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//! ADVISORY-REQUIRES-TRANSITIVE-1 (KNOWN_HAZARDS). ADVISORY-REQUIRES-CROSS-CRATE
//! (`requires_dep_elision_cross_crate_run.rs`) keeps the checks a `requires` clause
//! proved in a body another crate can call. A PRIVATE `requires` body reached
//! through a `pub` `requires` body still elided: its calls are charged in the
//! dependency, but under the `pub` entry's clause, which this consumer breaks. An
//! advisory consumer only warns on its failed `[precond]` row; a verify-off one
//! charges nothing.
//!
//! BEFORE (the stage 1 `scratchpad/stage1-w16`, 2026-10-05): the dependency builds
//! rc=0 with each private leaf's check elided, every revision here builds rc=0, and
//! each binary prints `0` and exits 0, where a verify-off build of both crates
//! panics. AFTER (measured 2026-10-06 on the stage 1 of `0ac7a96d9f`,
//! `integ/wave18`): a `requires` body named by a chain of `requires` bodies that
//! starts at one another crate can call keeps every check its clause proved; the
//! dependency prints no `TRUST_ELIDE` line for any leaf or for `hop`, and each
//! binary panics "attempt to add with overflow" (exit 101). One route
//! per revision, so a route the rule misses fails alone: a call (`*_via`), a chain
//! of two private bodies (`advisory_chain`), a method call (`off_method`) and a
//! type-relative path (`off_assoc`). Verdicts are unchanged.

extern crate requires_dep_transitive_default_policy as dep;

#[inline(never)]
fn run(y: u32) -> u32 {
    #[cfg(any(advisory_via, off_via))]
    let r = dep::add1_via(y);
    #[cfg(advisory_chain)]
    let r = dep::add1_chain(y);
    #[cfg(off_method)]
    let r = dep::S.add1m_via(y);
    #[cfg(off_assoc)]
    let r = dep::add1_assoc(y);
    r
}

fn main() {
    let y = std::hint::black_box(u32::MAX);
    println!("{}", run(y));
}
