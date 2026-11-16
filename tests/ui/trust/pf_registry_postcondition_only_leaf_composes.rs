//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@ build-pass
//@ dont-check-compiler-stderr
//! Regression pin for the 2026-09-12 strict-lane regression (16 of the 19
//! reference crates in `docs/STRICT_VERIFICATION_FRAGMENT.md` failed on it).
//!
//! `clamp_upper` is the fragment's two-call building block: its ONLY rows are
//! its `ensures` postcondition rows — proved, kernel-certified, unconditional —
//! and its body has no panic site, so it emits no arithmetic/bounds/catch-all
//! row at all. b62's positive-evidence guard in
//! `results_establish_unconditional_panic_freedom` ("at least one proved
//! NON-postcondition row") keyed on the row KIND rather than on whether the
//! unproved-postcondition exemption had been used, so this leaf stopped
//! entering the unconditional panic-free registry. Every composing caller
//! (`span_width` here; `span_width`/`saturating_diff`/`capped_sum` in
//! `trust-ratio`) then grew a `[assert] panic freedom: no assertion,
//! `unreachable!`, or panic is reachable` catch-all row that the callee-closure
//! seam could not discharge (`[PF_CALLGATE] … UNREGISTERED callee blocks
//! discharge: …::clamp_upper`), and under the default strict policy that is
//! `error: Trust strict verification failed for …: 1 obligation(s) were not
//! fully verified` — so this fixture is `build-pass`: it cannot compile at all
//! while the leaf is unregistered.
//!
//! The fix registers the postcondition-only leaf through
//! `postcondition_only_run_establishes_unconditional_panic_freedom`, gated the
//! way the zero-obligation twin is gated (every call to an already-registered
//! callee, no assumption-panic row, exact native authorities, complete
//! lowering). Measured on this shape: the caller's catch-all row is no longer
//! minted (`rows=2 pf_idxs=[]`), exactly as the `(30 total)` recorded in
//! `scripts/trust_ratio_strict_gate.sh` requires.

/// The postcondition-only leaf: two proved `ensures` rows, no panic site.
pub fn clamp_upper(v: u32, hi: u32) -> u32 ensures result <= hi {
    if v > hi { hi } else { v }
}

/// A leaf WITH a panic-site row (the guarded subtraction), registered by the
/// ordinary lane — the control that the composing caller has two callees of
/// different registration lanes.
fn raw_span(lo: u32, hi: u32) -> u32 {
    if lo >= hi {
        return 0;
    }
    hi - lo
}

/// The composing caller. Its `ensures` is discharged from `clamp_upper`'s, and
/// its whole-function panic freedom rests on BOTH callees being registered.
pub fn span_width(lo: u32, hi: u32) -> u32 ensures result <= hi {
    clamp_upper(raw_span(lo, hi), hi)
}

/// `a - b` saturating at 0 — the second composing shape from `trust-ratio`,
/// with a panic-site row of its own (the subtraction) ahead of the call.
///
/// NO `ensures` here, deliberately, and the reason is a SEPARATE completeness
/// gap this fixture must not silently pin: with `ensures result <= a` the
/// crate fails `saturating_diff: 2 obligation(s) were not fully verified` on
/// its own `postcondition:0` row even though `clamp_upper(_, a)` ensures
/// exactly `result <= a` — the caller's postcondition is not discharged from
/// the callee's at this shape (measured 2026-09-12 on the stage1 built from
/// this tree; `span_width` above, whose `ensures` names the same parameter it
/// passes as `hi`, IS discharged). That is a postcondition-composition gap,
/// not a panic-freedom-registry one, and pinning it here would make this
/// fixture fail for a reason it does not diagnose.
pub fn saturating_diff(a: u32, b: u32) -> u32 {
    clamp_upper(if a > b { a - b } else { 0 }, a)
}
