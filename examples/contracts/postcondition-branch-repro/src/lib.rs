// Trust regression: a postcondition on a function with TWO return paths must
// constrain the joined return slot on every predecessor path.
//
// Run (from this directory):
//   cargo clean && targo trust check --allow-l0-gaps
//
// Required result:
//   one_path [VERIFIED]  (one postcondition proved)
//   two_path [VERIFIED]  (both predecessor postconditions proved)
//
// `two_path` returns only 1 or 2, so `*r >= 0` holds on every path. The model
// must therefore never admit a counterexample that assigns the joined return
// SSA name some unrelated value. The VC generator emits one L1 postcondition
// per predecessor, including that predecessor's guard and return definition;
// the Trust-IR bridge independently reconstructs the same formulas, and the
// Clean checker replays the resulting proofs. This crate keeps that complete
// public `targo trust` path pinned in addition to the lower-level fixture tests.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![feature(contracts)]
#![allow(incomplete_features)]

extern crate core;
use core::contracts::ensures;

/// CONTROL: one return path. Proves.
#[ensures(|r: &i32| *r >= 0)]
pub fn one_path(_x: i32) -> i32 {
    7
}

/// REGRESSION: two return paths, both trivially satisfying the postcondition.
#[ensures(|r: &i32| *r >= 0)]
pub fn two_path(x: i32) -> i32 {
    if x < 0 { 1 } else { 2 }
}
