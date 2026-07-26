// Trust test: postcondition violation
// VcKind: Postcondition
// Expected: Postcondition UNKNOWN
// Current expectation: fail-closed unknown, exit 1.
//   The postcondition (result >= 0) is genuinely violated for negative inputs
//   and the trust-mc typed-CHC lane still REFUTES the body VC, but at tip the
//   fieldless Refuted demotes to unknown (the 47ffee63479 merge dropped the
//   b62 `bundle_is_certified_havoc_free` Refuted->Failed arm; the v1/ay bridge
//   deliberately substitutes only Proved for VcKind::Postcondition because SAT
//   of an under-approximating ensures goal is not a sound refutation), and the
//   def-site catalog marker (obligation:...:postcondition:0, same public kind
//   `postcond`) stays unknown: the failed-rekey that flipped it alongside a
//   refuted body row (`failed_postcondition_refutations`, live at 4788dfc13d0)
//   is gone at tip. "Postcondition FAILED" becomes assertable again once a
//   sound Failed lane returns AND the def-site marker rekey is restored.
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
