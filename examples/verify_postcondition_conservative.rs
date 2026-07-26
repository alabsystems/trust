// Trust test: postcondition -- conservative variant (correct abs implementation)
// VcKind: Postcondition
// Expected: Postcondition UNKNOWN
// Current expectation: fail-closed on the def-site marker only. All FOUR body-aware
//   postcondition branch VCs are Proved and clean-kernel-certified (the -x
//   branch via certify_negated_return_via_neg_bound), so the ensures clause
//   itself is machine-proven. The redundant def-site restatement marker stays
//   UNKNOWN by design: the EnsuresMarkerReconciled mint requires the S1
//   finalizer's body-bound witness, which exists only for the blueprint's
//   accepted body fragment (single entry block, copy/const return) -- this abs
//   body is branchy. Widening the mint to branchy bodies on kernel-certified
//   branch VCs alone is unsound (vcgen postcondition formulas are Int-modeled;
//   an Int-theorem like `result + 1 > result` kernel-certifies while false at
//   the type's wrap boundary -- pinned by s1c_arith_ensures_no_false_pass).
//   Exit 1 is the honest verdict until a bit-faithful witness lane lands.
//   Renamed from *_safe: that suffix carries an exit-0 contract in trust-extra.
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
fn abs_correct(x: i32) -> i32 {
    if x == i32::MIN {
        i32::MAX
    } else if x < 0 {
        -x // SAFE: negates negative values to make them positive
    } else {
        x // already non-negative
    }
}

fn main() {
    let _ = abs_correct(5);
    let _ = abs_correct(-5);
}
