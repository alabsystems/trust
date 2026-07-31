// Trust test: postcondition violation
// VcKind: Postcondition
// Expected: Postcondition FAILED
// The refutation is a witnessed counterexample, exit 1.
//   The postcondition (result >= 0) is genuinely violated for negative inputs.
//   This example previously asserted a fail-closed unknown, because the fieldless
//   Refuted demoted to unknown and the def-site catalog marker
//   (obligation:...:postcondition:0, same public kind `postcond`) stayed unknown
//   beside it. Both preconditions that header named have since been met: the
//   typed `TrustSpecPredicate` of a body-aware `#[ensures]` VC is admitted to
//   trust-mc's CHC lane (`trust_mc_can_emit_direct_typed_chc_input`), and the
//   acyclic direct-SMT refutation returns a witnessed Failed. Both rows —
//   `obligation:...:postcondition:0` and `vc:...:postcondition:0` — now report
//   failed under solver `trust-full-verifier`.
// NOTE: This single-file regression example still uses the legacy contracts
// surface. New crate-based public examples should prefer `trust-spec` and
// `#[trust::ensures(...)]`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![feature(contracts)]

extern crate core;

use core::contracts::ensures;

#[ensures(|ret: &i32| *ret >= 0)]
fn abs_broken(x: i32) -> i32 {
    x // BUG: returns negative values for negative inputs
}

fn main() {
    // Argv-derived (unknown) inputs: safe constants here would let the R1
    // caller-propagation lane prove the whole program safe and discharge the
    // isolated refutation this example exists to demonstrate.
    let n = std::env::args().len() as i32;
    let _ = abs_broken(n);
}
