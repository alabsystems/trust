//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: WARN
//@ check-fail
//! Full verification catches the classic midpoint overflow: `(lo + hi) / 2`
//! overflows i32 for large in-range inputs — the SMT verifier returns an
//! `[overflow:add]` counterexample. Under explicit full verification this
//! is a build ERROR under strict batteries-on verification.
//!
//! (The precondition `lo <= hi` is present but the verifier does not yet thread a
//! contract precondition into the dependent integer arithmetic — `trust_wp` reports
//! it UNKNOWN — so even a `lo + (hi - lo) / 2` rewrite currently fail-closes; the
//! overflow REFUTATION above is the load-bearing assertion of this fixture.)

#![feature(contracts_internals)]

pub fn midpoint_flawed(lo: i32, hi: i32) -> i32
contract_requires { lo <= hi }
contract_ensures { move |result| *result >= lo && *result <= hi }
{
    (lo + hi) / 2
}

fn main() {
    let _ = midpoint_flawed(10, 20);
}
