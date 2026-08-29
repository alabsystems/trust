//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! REGRESSION GUARD for the *shape* of the issue #213 remedy: a bundled std
//! member's division obligation must be charged **PER CALL SITE**, not as a
//! whole-function aggregate.
//!
//! # Why this file exists
//!
//! `native_bundle_std_trait_impl_stays_fail_closed.rs` guards the SOUNDNESS
//! half — `probe_bundled_member_div` must be refused. It cannot guard the
//! COMPLETENESS half, and the completeness half is where the first attempt at
//! this fix died.
//!
//! The history is specific and worth not repeating. Commit `bfcddfe309` closed
//! the same false PROVE by emitting a whole-function aggregate row for any
//! bundled member (index != 0) carrying any `Terminator::Assert`:
//!
//!     let bundled_member_assert = ctx.current_function.index() != 0
//!         && body.blocks.iter().any(|bb| matches!(bb.terminator,
//!                                                Terminator::Assert { .. }));
//!
//! That predicate is context-insensitive: it fires on the *callee's* body and
//! knows nothing about what the *caller* passes or guards. Measured, it turned
//! "verifies clean" into "1 obligation not proved" in **18 previously-green
//! tests**, and the whole three-commit stack was reverted by `1795a95f20`,
//! whose own post-mortem named the successor: *"recover a bundled member's
//! PER-SITE obligations instead of surfacing a whole-function aggregate. The
//! aggregate is strictly weaker than per-site guard reasoning, which is exactly
//! why it refuses 18 bodies whose asserts the engine could otherwise
//! discharge."*
//!
//! `ac6d5162f9` landed that successor: the bridge derives a synthetic
//! `requires` from a would-be-bundled member's unguarded entry-prefix div/rem
//! asserts, and the existing call-site machinery mints one
//! `VcKind::Precondition` per call site with the caller's actuals substituted
//! and the caller's path guards in scope.
//!
//! **Every function below is a case the reverted aggregate REFUSED and the
//! per-site remedy PROVES.** So this file is the instrument that tells the two
//! remedies apart. Without it, the only thing standing between a future
//! "simplification" and a silent return of that 18-test regression is a full
//! suite run that nobody attributes correctly.
//!
//! # Measured (stage1 `trustc`, this tree)
//!
//! Each function reports `1 proved, 0 failed, 0 unknown ... out of 1
//! obligation(s)` — note **1**, not 0. The obligation is CHARGED and then
//! DISCHARGED. That distinction is the entire point:
//!
//!   * 0 obligations would mean the #213 false PROVE is back (the member's
//!     assert charged to nobody);
//!   * 1 obligation refuted would mean the aggregate is back (context-
//!     insensitive over-refusal);
//!   * 1 obligation proved is the correct answer, and it is what this file
//!     pins.
//!
//! The refuting twin — the same call with an unconstrained divisor — lives in
//! `native_bundle_std_trait_impl_stays_fail_closed.rs` and is measured there as
//! `[precond] FAILED (ay-in-process); counterexample: b.0 = 0`.
//!
//! # What a future reader must not weaken
//!
//!   1. **Do not make this file `check-fail` to accommodate a refusal.** A
//!      refusal here is the aggregate regression, not a stricter compiler.
//!      Trust proves these today; if a change stops proving them, the change
//!      lost per-site guard reasoning.
//!   2. **Do not delete `control_div_guarded`.** The literal cases can be
//!      discharged by constant folding alone; only the guarded case shows the
//!      caller's PATH CONDITION reaching the derived precondition, which is the
//!      specific capability the aggregate lacked.
//!   3. If bundling or the derivation envelope legitimately narrows so that
//!      these stop being charged at all, re-measure and say so here — a silent
//!      drop back to 0 obligations is the original defect.

use std::num::Wrapping;

// The divisor is a nonzero literal at the call site. The derived requires
// (`other.0 != 0`) is substituted with the actual and discharged.
pub fn control_div_nonzero_literal(a: Wrapping<u8>) -> Wrapping<u8> {
    a / Wrapping(3u8)
}

// The divisor is a PARAMETER, made nonzero by a caller-side guard. This is the
// case the whole-function aggregate could never prove: the safety fact lives in
// the caller's path condition, not in the callee's body.
pub fn control_div_guarded(a: Wrapping<u8>, b: Wrapping<u8>) -> Wrapping<u8> {
    if b.0 == 0 {
        return Wrapping(0);
    }
    a / b
}

// The remainder arm of the same derivation (`AssertMessage::RemainderByZero`).
pub fn control_rem_nonzero_literal(a: Wrapping<u8>) -> Wrapping<u8> {
    a % Wrapping(7u8)
}
