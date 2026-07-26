// break/nested-corpus — two REAL MIR fixtures that exercise the wired
// break/early-exit and inner-modifies-outer (monotone-nested) loop RULES via the
// per-function prove dispatch (prove::extract_break_loop_function /
// extract_monotone_nested_loop_function → mirsem break/monotone witnesses).
//
// Dump with:
//   trustc -Ztrust-policy=advisory -Ztrust-dump=mir-only:<dir> \
//     --crate-type=lib SOURCE.rs
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
#![feature(contracts)]
#![allow(internal_features)]
#![allow(incomplete_features)]
#![allow(unused)]

// BREAK / EARLY-EXIT — a loop whose body has an `if cond { break }` before the
// increment. The synthesized guard-aware upper bound `i <= n` holds at BOTH exit
// points (guard-false AND break), discharging `ret <= n`.
#[core::contracts::ensures(move |ret: &u32| *ret <= n)]
pub fn find_le(n: u32) -> u32 {
    let mut i = 0;
    while i < n {
        if i == 3 {
            break;
        }
        i = i + 1;
    }
    i
}

// MONOTONE-NESTED — an outer loop with an inner loop that INCREMENTS the
// outer-invariant accumulator `s`. The lower-bound invariant `0 <= s` is preserved
// through the inner loop by the inner loop's own monotone lower bound.
#[core::contracts::ensures(move |ret: &u32| *ret >= 0)]
pub fn sum2d(n: u32) -> u32 {
    let mut s = 0;
    let mut i = 0;
    while i < n {
        let mut j = 0;
        while j < n {
            s = s + 1;
            j = j + 1;
        }
        i = i + 1;
    }
    s
}
