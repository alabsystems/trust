// Assert-guard-corpus NEGATIVE CONTROLS — real trustc MIR. Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0 OR MIT
//
// Three shapes the generalized divergence-chain navigation
// (`assert_guard_happy_path_blocks` in prove.rs) MUST decline, with teeth:
//   - `either`: a genuine two-arm branch — BOTH arms return a live value, NEITHER
//     diverges. Must NOT be absorbed by the straight-line recognizer (that is the
//     separate guarded-return frontier's territory).
//   - `weird_guard`: the "guard" arm calls a NON-panic function that actually
//     RETURNS (does not diverge). Silently treating this arm as divergence would
//     be UNSOUND (it would drop a live second value). Must decline.
//   - `unsafe_double`: the SAME `x + x` shape as `bounded_double`, but with NO
//     leading `assert!` guard at all, so its own overflow `Assert` has nothing to
//     discharge it. The shape still recovers/reflects (adequacy), but the safety
//     VC must stay UNDISCHARGED, so the function must NOT be counted fully
//     faithful.
pub fn either(c: bool, x: u64, y: u64) -> u64 { if c { x } else { y } }

#[inline(never)]
pub fn non_panic_helper(x: u64) -> u64 { x + 1 }

pub fn weird_guard(x: u64) -> u64 { if x < 1000000000 { x } else { non_panic_helper(x) } }

pub fn unsafe_double(x: u64) -> u64 { x + x }
