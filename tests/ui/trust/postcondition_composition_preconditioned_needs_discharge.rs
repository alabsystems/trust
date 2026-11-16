//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Trust (postcondition composition, slice 2 — THE FALSE-PROVE MACHINE, kept shut).
//!
//! A callee's `ensures` is guaranteed only WHEN ITS `requires` HELD. A caller
//! may therefore assume the postcondition only where the precondition is
//! DISCHARGED AT THAT CALL SITE. This file is the case where it is not.
//!
//! `positive_part` promises `result > 0` — but only for `x > 0`. Its body is
//! the identity, so the promise is FALSE for every `x <= 0`. `triple` calls it
//! with its own unconstrained parameter, so `x > 0` is not derivable at the
//! call site and the caller must learn NOTHING about `y`.
//!
//! THIS IS NOT A COMPLETENESS NICETY — it has a runtime witness.
//! `triple(i32::MIN)` calls `positive_part(i32::MIN)` (out of contract, so the
//! callee's promise does not apply), gets `i32::MIN` back, takes the
//! `y < 100` arm, and `y * 3` UNDERFLOWS. If the caller inherited `y > 0`
//! unconditionally, the `Mul` obligation would be reported PROVED for a
//! program that panics — a false PROVE with a witness, not a missed proof.
//!
//! CORRECTED 2026-09-17 — this paragraph used to read "the `Mul` is also the only
//! thing that can catch it here ... the call-site precondition row is FILTERED OUT
//! before any solver sees it". The second half is now FALSE and the first half
//! follows it down. `VcKind::Precondition` is still hardcoded `L1Functional`
//! (`trust-types` `vc_kind.rs` `proof_level`) and `triple` still declares no
//! contract, so the call-site precondition row is still excluded from the
//! LEVEL 0 GATING SUMMARY — measured, that summary reads `1 failed, 1
//! runtime-checked` while the function's own report counts two failures. But the
//! row is NOT withheld from the solver: it is generated, decided, and REFUTED,
//! and it is counted by the strict-verification error (3 obligations not fully
//! verified). So the call-site guard on the assumption is no longer the only
//! thing standing between this file and the false prove above — the refuted
//! precondition row now names the same defect directly, and both are pinned below.
//!
//! Companions: `postcondition_composition_preconditioned_at_call_site.rs` adds
//! the `x > 0` guard and must PASS;
//! `postcondition_composition_preconditioned_upper_bound_only.rs` keeps the
//! guard and weakens the clause, and must still FAIL.
//!
//! POLICY RE-PINNED 2026-09-16 — HISTORICAL. Superseded by the 2026-09-17 block
//! at the end of this comment: the row it describes is no longer runtime-checked.
//! It is kept because it records why the file sits on the `certify` lane.
//! This file measures whether the caller DISCHARGES
//! its obligation, and it read that off the DEFAULT lane's exit code. That stopped
//! being the same question on 2026-09-14, when policy B landed as ruled
//! (docs/design/2026-07-25-completeness-gap-policy-ruling.md): an unproved
//! arithmetic row that keeps rustc's runtime check is now REPORTED and the build
//! SUCCEEDS. The row here is exactly that — `[overflow:mul] runtime-checked:
//! compiler retained the existing overflow check because the proof is not yet
//! static` — so the default lane stopped failing while the obligation stayed
//! exactly as unproved as before.
//!
//! `-Ztrust-policy=certify` is the lane where full static discharge IS the
//! contract, so that is where this question belongs and that is what the flag
//! above now selects. Nothing about the property changed and nothing was blessed:
//! the same row, still unproved, still named in the same two errors.
//!
//! The vacuity guard survives the move, which is the thing to check before
//! trusting it. If the caller-side lane stopped EMITTING the obligation, the
//! body would report zero obligations, certify would have nothing to refuse, and
//! this file would go red on the missing errors — the same way it would have on
//! the default lane. What the move gives up is detecting a row that silently
//! becomes runtime-checked-and-tolerated, and the `NOTE` pin below is there so
//! that is not given up either: it asserts the row EXISTS and is unproved,
//! independently of which policy decides the exit code.
//!
//! RE-BLESSED 2026-09-17 — TWO ROWS BECAME REFUTATIONS, AND THE FILE NOW PROVES
//! ITS OWN NAME. `first-party/ay` moved to c187eb99d and the solver decides queries
//! it used to decline. Measured on stage1 `trustc` with exactly the flags above,
//! `triple` reports three rows where it reported one refutation-free set before:
//!
//!     [assert] runtime-checked: compiler retained the existing assertion
//!     [overflow:mul] FAILED (ay-in-process); counterexample:
//!     _3 = -715827883, _4 = true, x = 0
//!     [precond] FAILED (ay-in-process); counterexample: x = 0
//!
//! The VC handed to the solver is byte-identical across the pin move — A/B in
//! reports/2026-09-17-nine-ui-reds-follow-the-ay-pin-move.md — so the obligation
//! and this file's property are unchanged; the answer moved.
//!
//! BOTH MODELS ARE ADMISSIBLE, CHECKED RATHER THAN ASSUMED. `triple` declares no
//! `requires`, so `x = 0` is an input it must accept. `positive_part`'s
//! `requires x > 0` is therefore VIOLATED at that call site, its `ensures result > 0`
//! does not apply, and the caller learns nothing about `y` — so `_3 = -715827883`
//! (with `_4`, the `y < 100` test, true) is a value the caller cannot exclude, and
//! `-715827883 * 3` is `-2147483649`, one past `i32::MIN`. That is the refutation
//! this file has always been about, now exhibited instead of deferred to a runtime
//! check. The `[precond]` model `x = 0` fails `x > 0` for the same reason, which is
//! not a verifier defect but the file's thesis: at THIS call site the precondition
//! genuinely is not discharged. (The stronger runtime witness in the prose above,
//! `triple(i32::MIN)`, remains the real-execution version of the same story; the
//! solver simply picked the smallest input that breaks the contract.)
//!
//! WHICH BOUNDARY THIS NOW DEMONSTRATES. Before, the only load-bearing assertion
//! was "the caller did not inherit `y > 0`, so the `Mul` stayed unproved". Now the
//! file asserts the call-site precondition is REFUTED with a witness. It does NOT
//! assert anything about the retained `[assert]` row: that row carries no pin here,
//! so nothing in this file would go red if it stopped being emitted. Claiming it
//! did was written and withdrawn on 2026-09-17 — an unpinned row in a fixture with
//! `dont-require-annotations` is invisible, and saying otherwise manufactures
//! coverage. Measured today the default
//! lane emits the same two errors as `certify`, so `-Ztrust-policy=certify` is no
//! longer load-bearing and is kept deliberately: if the solver weakens back to
//! `runtime-checked` it keeps the build red while the pinned notes below go red on
//! the changed text. A `[precond]` row that ever reported PROVED here would be the
//! false prove this file exists to catch, and the pin below now catches it directly.
//!
//! RE-PINNED 2026-09-28 (MEASURED on the Track B stage 1). The D5-A
//! call-destination screen now lets a solver model over a same-crate call
//! result stand only where an injected clause DETERMINES that result with no
//! `requires` guard (`trust_vcgen::generate::summary_pins_result`). Here
//! the clause arrives as `x > 0 -> result > 0` and this caller never establishes `x > 0`, so the `[overflow:mul]` model picks a
//! value the contract admits but no execution of `positive_part` returns (MEASURED
//! shape: `e9_requires_hypothesis_callee_reuse::use_outside_sub`, whose model
//! `r = 4` for `rmax(0, 5)` had the guard false). The row is therefore HELD — `UNKNOWN`
//! naming `positive_part`, a fail-closed gap with no runtime-check tolerance — where it
//! read `FAILED`. It still does not prove and the build still fails, which is
//! the whole of what this file asks.

pub fn positive_part(x: i32) -> i32
    requires x > 0
    ensures result > 0
{
    x
}

pub fn triple(x: i32) -> i32 {
//~^ ERROR Trust Level 0 safety verification incomplete for `postcondition_composition_preconditioned_needs_discharge::triple`
//~| ERROR Trust strict verification failed for `postcondition_composition_preconditioned_needs_discharge::triple`
//~| NOTE generic solver counterexample withheld: query depends on the unmodeled return of same-crate `postcondition_composition_preconditioned_needs_discharge::positive_part`
//~| NOTE [precond] FAILED
    let y = positive_part(x);
    if y < 100 { y * 3 } else { 0 }
}
