//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ forbid-output: was not discharged
//! CLOSE CONTROL for `source_clause_conditional_postcondition_frontier.rs`.
//!
//! The clause here is BYTE-IDENTICAL to the one that stays pending there; only
//! the body differs — two return paths instead of three. Measured on stage2
//! `db07002ff` as battery probe `p8`, and RE-MEASURED on this exact source with
//! stage1 built from this branch at `8113b3a0a81` (2026-09-17): exit 0,
//! "3 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 3
//! obligation(s)". `-Ztrust-verify-output=both` on that stage1, row by row:
//!
//! ```text
//! obligation:two_path__clamp:postcondition:0  proved  trust-exact-source-clause-discharge
//! vc:two_path__clamp:postcondition:0          proved  trust-full-verifier
//! vc:two_path__clamp:postcondition:1          proved  trust-full-verifier
//! ```
//!
//! The three-path twin is identical except that `vc:…:postcondition:1` comes
//! back UNKNOWN. That single row is the whole observed delta.
//!
//! THIS FILE ALSO REFUTES the "trust-mc returns unknown, so no exact-direct
//! CHC/PDR receipt can be minted" story that an earlier draft of the frontier's
//! header told: this PASSING run carries "PDR invariant candidates require fresh
//! private consumer replay before proof-grade admission" twice and discharges
//! its marker anyway. The marker can only discharge if BOTH body rows carried an
//! accepted sealed authority, so a receipt is plainly minted despite that
//! message.
//!
//! WHAT THIS CONTROLS, stated correctly. This file isolates the axis to the
//! return-path count: `p7` (`ensures result == a || result == 1000000`) and `p6`
//! (a conjunction) prove on this same two-path body, so the connective is not
//! the axis either. It is a regression control against a future TIGHTENING —
//! anything that stops this clause discharging goes red here. It is NOT a canary
//! against a weakening: a weakening leaves a passing test passing, and the row
//! that goes red under a weakening is the FRONTIER fixture, whose follow-on
//! NOTE annotation disappears the moment the marker starts discharging. (The
//! first draft of this comment claimed the opposite; it was wrong.)
//!
//! The `forbid-output` is the second half of the same assertion: on a
//! compilation that proves everything, the pending-marker diagnosis must not
//! fire at all. It costs one line and catches a future change that starts
//! refining reasons on green rows.
//!
//! AMENDMENT 2026-09-18 — WHAT THIS FILE NOW CONTROLS. Each of this body's two
//! Return-block predecessors is reached by exactly ONE guard path, so the
//! per-path postcondition split (which replaces a predecessor reached by `n`
//! guard paths with `n` flat rows) must NOT fire here: two rows, spelled
//! exactly as before. That makes this the regression control against the split
//! widening into shapes that already worked — measured at the formula level in
//! `crates/trust-vcgen/src/generate/per_path_postcondition_tests.rs`
//! (`two_path_body_is_untouched`).
//!
//! The paragraph above is also now out of date in one respect: the three-path
//! twin `..._frontier.rs` is a `check-pass` POSITIVE, not a `check-fail`
//! frontier, so it no longer carries a follow-on NOTE that a weakening would
//! erase. The row that goes red under a weakening of the composition rule is
//! the FALSE twin `..._false_one_path.rs`.

pub fn clamp(a: u32) -> u32
    ensures a <= 1000000 ==> result >= a
{
    if a >= 1000000 { 1000000 } else { a }
}
