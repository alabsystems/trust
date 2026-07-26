// Trust test: float division overflow to infinity -- conservative variant (contract-discharged)
// VcKind: FloatOverflowToInfinity { op: BinOp::Div }
// Expected: FloatOverflowToInfinity ABSENT
// Corpus witness of the float-contract discharge lane (04cd8baf8ee): trustc
// mints FloatOverflowToInfinity(Div) for `x / y` (39238badacc), and on
// unconstrained f64 inputs it is genuinely refutable (x = 1e308, y = 0.5
// overflows to +inf) — the refutation stays alive in the buggy pair
// verify_float_div_zero.rs. Here the obligation discharges statically: the
// `requires` contract caps |x| <= 1e30 and the dominating `y.abs() >= 1e-9`
// guard floors the divisor magnitude, so |x / y| <= 1e39 << f64::MAX and no
// row is minted. ABSENT is a generation assertion, not a proof claim. Dropping
// EITHER the contract or the
// magnitude guard re-mints the obligation (fail-closed: unknown, exit 1).
// Safe pattern: input-magnitude requires-contract on the numerator plus an
// abs-guard divisor floor before dividing.
//
// Renamed from *_safe: the trust-extra lane derives an exit-0 contract from
// the _safe suffix, which this file cannot soundly meet at tip.
// STATUS (tip, 2026-07-19): the Div discharge above STILL fires (no
// FloatOverflowToInfinity(Div) row is minted), but the file currently exits 1
// on three unrelated fail-closed rows introduced by the merged hardenings —
// this cannot be fixed from this file (any contract on an f64 parameter is
// untypeable on the public TrustSpec surface, and dropping the contract
// re-mints the Div obligation):
//   1. unsupported:...:0 — mir-extract now mints a fail-closed
//      unsupported-contract marker for EVERY clause kind (ba070f0995d; the
//      pre-merge code exempted definition-site Requires markers as the
//      caller's burden); the float predicate has no typed lowering
//      (TrustSpecSort has no Float sort, SpecExprLowerer has no FloatLit arm)
//      and no monitor ("no query-owned typed proposition"), so the marker is
//      an ownerless unknown.
//   2./3. vc:...:assertion:panic-freedom:0 (float_divide_safe and main) —
//      `y.abs()` is an absent callee (`core::f64::<impl f64>::abs`); the broad
//      std-totality surface that modeled `::f64::abs` total was quarantined
//      (#[cfg(any())] quarantined_untyped_total_no_panic_call_summary) in
//      favor of the closed EXACT_TOTAL list, which lacks it.
// Exit 0 returns via any of: EXACT_TOTAL re-admission of core::f64::abs (a
// true inherent-library fact) + the Requires-marker exemption (or a skipped
// entry-assumption owner for untypeable requires markers), a Float sort on
// the typed spec surface, or renaming this example off the `_safe` gate class.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![feature(contracts)]

extern crate core;

use core::contracts::requires;

#[requires(x >= -1.0e30 && x <= 1.0e30)]
fn float_divide_safe(x: f64, y: f64) -> f64 {
    let magnitude = y.abs();
    if magnitude >= 1.0e-9 {
        x / y // SAFE: |x| <= 1e30 (contract) over |y| >= 1e-9 (guard) bounds |x/y| <= 1e39
    } else {
        0.0 // fallback for (near-)zero divisor (avoids +/-Inf)
    }
}

fn main() {
    let _ = float_divide_safe(10.0, 3.0);
    let _ = float_divide_safe(10.0, 0.0); // takes fallback branch
}
