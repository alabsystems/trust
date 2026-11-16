//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-timeout-ms=2000
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: WARN
//@ check-fail
// The 2 s per-obligation budget (default 20 s) removes most of this file's
// cost, because some engine runs out the budget on an obligation it cannot
// decide. It is safe: every per-function verdict was measured identical at
// 0.5 s, 2 s and 20 s (2026-09-23, 96f2019566). No verdict annotations here: this file
// is in the scorecard's frozen [in-pool] sample, which admits no annotated file.
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
